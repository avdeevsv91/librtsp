#include <sys/socket.h>
#include <sys/types.h>
#include <sys/time.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <errno.h>
#include <fcntl.h>
#include "rtsp_server.h"
#include "common.h"
#include "rtsp.h"
#include "list.h"
#include "hash.h"
#include "mime.h"
#include "thread.h"
#include "rfc.h"
#include "rtcp.h"
#include "bufpool.h"
#include <netinet/in.h>
#include <sys/ioctl.h>

/******************************************************************************
 *              PRIVATE DEFINITIONS
 ******************************************************************************/
#define __STR_OPTIONS  "OPTIONS"
#define __STR_CSEQ  "CSEQ"
#define __STR_DESCRIBE  "DESCRIBE"
#define __STR_SETUP  "SETUP"
#define __STR_PLAY  "PLAY"
#define __STR_TEARDOWN  "TEARDOWN"
#define __STR_TRANSPORT  "TRANSPORT"
#define __STR_CLIENTPORT  "client_port"
#define __STR_SESSION  "SESSION"
#define __STR_PAUSE "PAUSE"
#define __STR_RECORDING "RECORDING"
#define __STR_RANGE  "RANGE"
#define __SPACE " "

#define __RESPONCE_STR_OK "200 OK"
#define __RESPONCE_STR_BADREQUEST "400 Bad Request"
#define __RESPONCE_STR_METHODINVAL "455 Method Not Valid in This State"
#define __RESPONCE_STR_METHODNOTALLOWED "405 Method Not Allowed"
#define __RESPONCE_STR_MOVEDPERM "301 Moved Permanently"
#define __RESPONCE_STR_SERVERERROR "500 Internal Server Error"
#define __RESPONCE_STR_OPTIONUNSUPPORTED "551 Option not supported"

#define __PARSE_ERROR(p) do {ERR("cannot parse '%s' in %s\n", buf, __FUNCTION__); p->parser_state = __PARSER_S_ERROR;}while(0)

/******************************************************************************
 *              PRIVATE DECLARATION
 ******************************************************************************/
static inline int __bind_rtp(struct connection_item_t *con );
static inline int __bind_rtcp(struct connection_item_t *con );
static inline int __bind_tcp(unsigned short port);

static void __parse_head(struct connection_item_t *p, char *buf);
static void __parse_cseq(struct connection_item_t *p, char *buf);
static void __parse_transport(struct connection_item_t *p, char *buf);
static void __parse_session(struct connection_item_t *p, char *buf);
static void __parse_range(struct connection_item_t *p, char *buf);

static void __method_options(struct connection_item_t *p, rtsp_handle h);
static void __method_describe(struct connection_item_t *p, rtsp_handle h);
static void __method_setup(struct connection_item_t *p, rtsp_handle h);
static void __method_play(struct connection_item_t *p, rtsp_handle h);
static void __method_pause(struct connection_item_t *p, rtsp_handle h);
static void __method_record(struct connection_item_t *p, rtsp_handle h);
static void __method_error(struct connection_item_t *p, rtsp_handle h);

static void *rtspThrFxn(void *v);

static inline int __connection_list_add(bufpool_handle con_pool, struct list_head_t *head,int fd, struct sockaddr_in addr);
static int __connection_reset(void *v);
static inline int __accept_proc_sock(rtsp_handle h, int server_fd, struct sock_select_t *p_socks);
static int __message_proc_sock(struct list_t *e, void *p);
static inline int __set_select_sock(struct list_t *p, void *param);
static inline int __find_fd_max(struct list_head_t *head);

static inline bufpool_handle __connectionpool_create(int num);
static int __connection_is_dead(struct list_t *l);

/******************************************************************************
 *              PRIVATE DATA
 ******************************************************************************/
/* parser finite state machine jump table */
static void (*__state_table[__METHOD_COUNT][__PARSER_S_COUNT]) (struct connection_item_t *p, char *buf) = 
{[__METHOD_OPTIONS] = {
    [__PARSER_S_HEAD] = __parse_cseq,
    [__PARSER_S_CSEQ] = NULL},
[__METHOD_DESCRIBE] = {
    [__PARSER_S_HEAD] = __parse_cseq,
    [__PARSER_S_CSEQ] = NULL},
[__METHOD_SETUP] = {
    [__PARSER_S_HEAD] = __parse_cseq,
    [__PARSER_S_CSEQ] = __parse_transport,
    [__PARSER_S_TRANSPORT] = NULL},
[__METHOD_PLAY] = {
    [__PARSER_S_HEAD] = __parse_cseq,
    [__PARSER_S_CSEQ] = __parse_session,
    [__PARSER_S_SESSION] = __parse_range,
    [__PARSER_S_RANGE] = NULL},
[__METHOD_PAUSE] = {
    [__PARSER_S_HEAD] = __parse_cseq,
    [__PARSER_S_CSEQ] = __parse_session,
    [__PARSER_S_SESSION] = NULL},
[__METHOD_RECORDING] = {
    [__PARSER_S_HEAD] = __parse_cseq,
    [__PARSER_S_CSEQ] = __parse_session,
    [__PARSER_S_SESSION] = NULL},
[__METHOD_TEARDOWN] = {
    [__PARSER_S_HEAD] = __parse_cseq,
    [__PARSER_S_CSEQ] = __parse_session,
    [__PARSER_S_SESSION] = NULL}};

static struct connection_item_t __connection_pool[RTSP_MAXIMUM_CONNECTIONS] = {};

static struct transfer_item_t __transfer_pool[RTSP_MAXIMUM_CONNECTIONS] = {};

/******************************************************************************
 *              PRIVATE FUNCTIONS
 ******************************************************************************/
static void *__bufgetter_connection(int i)
{
    return (void *)&(__connection_pool[i]);
}

static inline bufpool_handle __connectionpool_create(int num)
{
    bufpool_handle h = bufpool_create(num, (__bufgetter_connection), (__connection_reset), sizeof(struct connection_item_t));

    if (h) {
        int i;
        for(i = 0; i < num; i++) {
            __connection_pool[i].pool = h;
            __connection_pool[i].con_state = __CON_S_DISCONNECTED;
        }
    }

    return h;
}

static void *__bufgetter_trans(int i)
{
    return (void *)&(__transfer_pool[i]);
}

static inline bufpool_handle __transpool_create(int num)
{
    bufpool_handle h = bufpool_create(num, (__bufgetter_trans), NULL, sizeof(struct transfer_item_t));

    if (h) {
        int i;
        for(i = 0; i < num; i++) {
            __transfer_pool[i].pool = h;
            __transfer_pool[i].list_entry.cleaner = (__transfer_item_cleaner);
        }
    }

    return h;
}

/******************************************************************************
 *              PARSER IMPLEMENTATIONS
 ******************************************************************************/
static void __parse_head(struct connection_item_t *p, char *buf)
{
    if (SCMP(__STR_OPTIONS,buf))            { p->method = __METHOD_OPTIONS;
		STR_KEY_NUM(buf, "ch=", p->ch);
		STR_KEY_NUM(buf, "dwtype=", p->dwtype);
    } else if (SCMP(__STR_DESCRIBE,buf))    { p->method = __METHOD_DESCRIBE;
    } else if (SCMP(__STR_SETUP, buf))      { p->method = __METHOD_SETUP;
		STR_KEY_NUM(buf, "trackID=", p->track_id);
    } else if (SCMP(__STR_PLAY, buf))       { p->method = __METHOD_PLAY;
    } else if (SCMP(__STR_RECORDING, buf))  { p->method = __METHOD_RECORDING;
    } else if (SCMP(__STR_PAUSE, buf))      { p->method = __METHOD_PAUSE;
    } else if (SCMP(__STR_TEARDOWN, buf))   { p->method = __METHOD_TEARDOWN;
    }

    p->parser_state = __PARSER_S_HEAD;
}

static void __parse_cseq(struct connection_item_t *p, char *buf)
{
    char *tok;
    char *last;

    if (SCMP(__STR_CSEQ,buf)) {
        ASSERT(tok = strtok_r(buf,": ",&last), goto error); 
        ASSERT(tok = strtok_r(NULL,": ",&last), goto error);
        ASSERT((p->cseq = atoi(tok)) > 0, goto error);

        p->parser_state = __PARSER_S_CSEQ;
    } else if(SCMP(__STR_TRANSPORT,buf)) { // ffmpeg fix
        __parse_transport(p, buf);
    }

    return;
error:
    __PARSE_ERROR(p);
}

static void __parse_session(struct connection_item_t *p, char *buf)
{
    unsigned long long session_id;
    char *tok;
    char *last;

    if (SCMP(__STR_SESSION,buf)) {
        ASSERT(tok = strtok_r(buf,": ",&last), goto error);
        ASSERT(tok = strtok_r(NULL,": ",&last), goto error);
        ASSERT(sscanf(tok,"%llx",&session_id) > 0, goto error);

        p->given_session_id = session_id;
        p->parser_state= __PARSER_S_SESSION;
    }

    return;
error:
    __PARSE_ERROR(p);
}

static void __parse_range(struct connection_item_t *p, char *buf)
{
    p->parser_state = __PARSER_S_RANGE;
}


static void __parse_transport(struct connection_item_t *p, char *buf)
{
    char *tok;
    char *last;

    if (SCMP(__STR_TRANSPORT,buf)) {
        for(tok = strtok_r(buf,"; ",&last); tok != NULL; tok = strtok_r(NULL,"; ",&last)) {
            if (SCMP(__STR_CLIENTPORT,tok)) {

                ASSERT(sscanf(tok, __STR_CLIENTPORT "=%u-%u", &p->trans[p->track_id].client_port_rtp,&p->trans[p->track_id].client_port_rtcp) > 0,
                        goto error);

                p->parser_state = __PARSER_S_TRANSPORT;

                break;
            }
        }
    }
    return;
error:
    __PARSE_ERROR(p);
}

static void __method_options(struct connection_item_t *p, rtsp_handle h)
{
    fprintf(p->fp_tcp_write, "RTSP/1.0 200 OK\r\n"
            "CSeq: %d\r\n"
            "Public: OPTIONS, DESCRIBE, SETUP, TEARDOWN, PLAY, PAUSE\r\n"
            "\r\n", p->cseq);
}

static void __method_describe(struct connection_item_t *p, rtsp_handle h)
{
    char sdp[__RTSP_TCP_BUF_SIZE];

    if(((h->video_type[p->dwtype] == RTSP_PAYLOAD_TYPE_H264) || h->sprop_vps_b64) && h->sprop_sps_b64 && h->sprop_sps_b16 && h->sprop_pps_b64) {
        if(h->video_type[p->dwtype] == RTSP_PAYLOAD_TYPE_H265) {
            DASSERT(h->sprop_vps_b64->result, return);
        }
        DASSERT(h->sprop_sps_b64->result, return);
        DASSERT(h->sprop_sps_b16->result, return);
        DASSERT(h->sprop_pps_b64->result, return);

        if(h->video_type[p->dwtype] == RTSP_PAYLOAD_TYPE_H265) {
            DBG("VPS BASE64:%s\n",h->sprop_vps_b64->result);
        }
        DBG("SPS BASE64:%s\n",h->sprop_sps_b64->result);
        DBG("SPS BASE16:%s\n",h->sprop_sps_b16->result);
        DBG("PPS BASE64:%s\n",h->sprop_pps_b64->result);

		if (!h->video_type[p->dwtype]) {
			snprintf(sdp, __RTSP_TCP_BUF_SIZE- 1,
					"v=0\r\n"
					"o=- 0 0 IN IP4 127.0.0.1\r\n"
					"s=librtsp\r\n"
					"c=IN IP4 0.0.0.0\r\n"
					"t=0 0\r\n"
					"a=tool:libavformat 52.73.0\r\n"
					"m=video 0 RTP/AVP 96\r\n"
					"a=rtpmap:96 H264/90000\r\n"
					"a=control:streamid=0\r\n"
					"a=fmtp:96 packetization-mode=1;"
					" profile-level-id=%s;"
					" sprop-parameter-sets=%s,%s;\r\n"
					"a=control:trackID=0\r\n"
					"m=audio 0 RTP/AVP 8\r\n"
					"a=rtpmap:8 pcma/8000/1\r\n"
					"a=framerate:50\r\n"
					"a=control:trackID=1\r\n",
					h->sprop_sps_b16->result,
					h->sprop_sps_b64->result,
					h->sprop_pps_b64->result);

					p->video_type[p->dwtype] = RTSP_PAYLOAD_TYPE_H264;
					p->video_fps[p->dwtype] = 25;

					p->audio_type = RTSP_PAYLOAD_TYPE_G711_PCMA;
					p->audio_sample_rate = 8000;
					p->audio_poinum = 160;
					p->trans[0].rtp_timeoffset = 90000/p->video_fps[p->dwtype];
					p->trans[1].rtp_timeoffset = p->audio_poinum;
		} else {
			snprintf(sdp, __RTSP_TCP_BUF_SIZE- 1,
				    "v=0\r\n"
				    "o=- 0 0 IN IP4 127.0.0.1\r\n"
				    "s=librtsp\r\n"
				    "c=IN IP4 0.0.0.0\r\n"
				    "t=0 0\r\n"
				    "a=tool:libavformat 52.73.0\r\n"
				    "m=video 0 RTP/AVP %d\r\n"
				    "a=rtpmap:%d %s/90000\r\n"
				    "a=fmtp:%d packetization-mode=1;"
				    " profile-level-id=%s;"
				    " sprop-parameter-sets=%s,%s;\r\n"
				    "a=control:trackID=0\r\n"
				    "m=audio 0 RTP/AVP %d\r\n"
				    "a=rtpmap:%d %s/%d/1\r\n"
				    "a=framerate:%d\r\n"
				    "a=control:trackID=1\r\n",
				    h->video_type[p->dwtype], h->video_type[p->dwtype], 
				    (h->video_type[p->dwtype]==RTSP_PAYLOAD_TYPE_H265)?"H265":"H264",
				    h->video_type[p->dwtype], 
				    h->sprop_sps_b16->result,
				    h->sprop_sps_b64->result,
				    h->sprop_pps_b64->result,
				    h->audio_type, h->audio_type,
				    (h->audio_type==RTSP_PAYLOAD_TYPE_G711_PCMA)?"pcma":"pcmu",
				    h->audio_sample_rate, h->audio_sample_rate/h->audio_poinum);

			p->video_type[p->dwtype] = h->video_type[p->dwtype];
			p->video_fps[p->dwtype] = h->video_fps[p->dwtype];
			p->audio_type = h->audio_type;
			p->audio_sample_rate = h->audio_sample_rate;
			p->audio_poinum = h->audio_poinum;
			p->trans[0].rtp_timeoffset = 90000/p->video_fps[p->dwtype];
			p->trans[1].rtp_timeoffset = p->audio_poinum;
		}
    } else {
        snprintf(sdp, __RTSP_TCP_BUF_SIZE- 1,
                "v=0\r\n"
                "o=- 0 0 IN IP4 127.0.0.1\r\n"
                "s=librtsp\r\n"
                "c=IN IP4 0.0.0.0\r\n"
                "t=0 0\r\n"
                "a=tool:libavformat 52.73.0\r\n"
                "m=video 0 RTP/AVP %d\r\n"
                "a=rtpmap:%d %s/90000\r\n"
                "a=fmtp:%d packetization-mode=1\r\n"
                "a=control:streamid=0\r\n"
				"a=control:trackID=0\r\n"
				"m=audio 0 RTP/AVP 8\r\n"
				"a=control:trackID=1\r\n",
				h->video_type[p->dwtype], h->video_type[p->dwtype], 
				(h->video_type[p->dwtype]==RTSP_PAYLOAD_TYPE_H265)?"H265":"H264",
				h->video_type[p->dwtype]);
    }

    fprintf(p->fp_tcp_write, "RTSP/1.0 200 OK\r\n"
            "CSeq: %d\r\n"
            "Content-Type: application/sdp\r\n"
            "Content-Length: %d\r\n"
            "\r\n"
            "%s"
            , p->cseq,strlen(sdp),sdp);
}

static void __method_setup(struct connection_item_t *p, rtsp_handle h)
{
    /* make randomized session id */
	if (!p->session_id) {
    	p->session_id = __get_random_llu(&h->ctx);
	}

	if (!p->ssrc[p->track_id]) {
        p->ssrc[p->track_id] = (unsigned int)(__get_random_llu(&h->ctx));
    }

    DBG("created session id %llx\n", p->session_id);
    p->trans[p->track_id].server_port_rtp = SERVER_RTP_PORT + 3*p->ch + p->dwtype + p->track_id;
    p->trans[p->track_id].server_port_rtcp = SERVER_RTCP_PORT + 3*p->ch + p->dwtype + p->track_id;


    fprintf(p->fp_tcp_write, "RTSP/1.0 200 OK\r\n"
            "CSeq: %d\r\n"
            "Session: %llx\r\n"
            "Transport: RTP/AVP/UDP;unicast;client_port=%u-%u;server_port=%u-%u\r\n"
            "\r\n" , p->cseq, p->session_id,
            p->trans[p->track_id].client_port_rtp, p->trans[p->track_id].client_port_rtcp,
            p->trans[p->track_id].server_port_rtp, p->trans[p->track_id].server_port_rtcp);

    p->con_state = __CON_S_READY;
}

static void __method_pause(struct connection_item_t *p, rtsp_handle h)
{
    fprintf(p->fp_tcp_write, "RTSP/1.0 "__RESPONCE_STR_METHODNOTALLOWED "\r\n");

}
static void __method_record(struct connection_item_t *p, rtsp_handle h)
{
    fprintf(p->fp_tcp_write, "RTSP/1.0 " __RESPONCE_STR_METHODNOTALLOWED "\r\n");

}
static void __method_error(struct connection_item_t *p, rtsp_handle h)
{
    fprintf(p->fp_tcp_write, "RTSP/1.0 " __RESPONCE_STR_SERVERERROR "\r\n");

}

static void __method_play(struct connection_item_t *p, rtsp_handle h)
{
	int i;
    fprintf(p->fp_tcp_write, "RTSP/1.0 200 OK\r\n"
            "CSeq: %d\r\n"
            "Session: %llx\r\n"
            "\r\n" , p->cseq, p->session_id);

	for (i=0; i<2; i++) {
		if (!p->trans[i].server_port_rtp) {
			continue;
		}
		p->track_id = i;
		ASSERT(__bind_rtcp(p) == SUCCESS, return );
		ASSERT(__bind_rtp(p) == SUCCESS, return );
		p->trans[p->track_id].rtp_timestamp = 0;
		p->trans[p->track_id].rtp_seq = 1;
		p->trans[p->track_id].rtcp_octet = 0; 
		p->trans[p->track_id].rtcp_packet_cnt= 0; 
		p->trans[p->track_id].rtcp_tick_org = 150; // TODO: must be variant
		p->trans[p->track_id].rtcp_tick = p->trans[p->track_id].rtcp_tick_org;
	}

    p->con_state = __CON_S_PLAYING;

    ASSERT(__rtcp_send_sr(p) == SUCCESS, return );

}

static int __method_teardown(struct connection_item_t *p, rtsp_handle h)
{
    fprintf(p->fp_tcp_write, "RTSP/1.0 200 OK\r\n"
            "CSeq: %d\r\n"
            "Session: %llx\r\n"
            "\r\n" , p->cseq, p->session_id);

    p->con_state = __CON_S_INIT;


    return SUCCESS;
}


/******************************************************************************
 *              METHOD IMPLEMENTATIONS
 ******************************************************************************/

static int __message_proc_sock(struct list_t *e, void *p)
{
    struct connection_item_t *con;
    void (*next_fxn)(struct connection_item_t *p, char *buf) = __parse_head;
    struct sock_select_t *socks = p;
    char buf[__RTSP_TCP_BUF_SIZE];
    rtsp_handle h = NULL;

    DASSERT(socks, return FAILURE);
    MUST(h = socks->h_rtsp, return FAILURE);

    list_upcast(con,e);

    if (con->con_state == __CON_S_DISCONNECTED) {
        ERR("zombie connection detected: report to author\n");
        return SUCCESS;
    }

    if (FD_ISSET(con->client_fd, &(socks->rfds))) {

        con->parser_state = __PARSER_S_INIT;
        con->method = __METHOD_NONE;

        next_fxn = __parse_head;

        /* parse line by line. hereafter parser is switched according to the finite state machine */
        while(__read_line(con, buf)) {
            if (next_fxn) {
                next_fxn(con, buf);
                next_fxn = __state_table[con->method][con->parser_state];
            }
        }

        if (con->parser_state == __PARSER_S_ERROR) {

            __method_error(con,h);

        } else {

            switch(con->method){
                case __METHOD_OPTIONS: __method_options(con, h);break;
                case __METHOD_DESCRIBE: __method_describe(con, h);break;
                case __METHOD_SETUP: __method_setup(con, h);break;
                case __METHOD_PLAY: __method_play(con, h);break;
                case __METHOD_PAUSE: __method_pause(con, h);break;
                case __METHOD_RECORDING: __method_record(con, h);break;
                case __METHOD_TEARDOWN: __method_teardown(con, h);break;
                case __METHOD_NONE: 
                    /* state DISCONNECTED connections should be gabage collected immediately.
                       but sending thread might watches the connection right now.
                       so the connection might live at here */
                    ASSERT(con->con_state == __CON_S_DISCONNECTED, return FAILURE); 
                    break;
                default: ERR("unexpected method state\n"); return FAILURE;
            }

        }

        fflush(con->fp_tcp_write);
    } 
    return SUCCESS;

}


/******************************************************************************
 *              NETWORK FUNCTIONS
 ******************************************************************************/

static int __connection_reset(void *v)
{
    struct connection_item_t *p = v;
    unsigned ctx;
	int i;

    if(p->con_state != __CON_S_DISCONNECTED) {
        DBG("force connection to close\n");
    }

    FCLOSE(p->fp_tcp_read);
    FCLOSE(p->fp_tcp_write);
    CLOSE(p->client_fd);

    p->client_fd = 0;
    p->con_state = __CON_S_DISCONNECTED;

	for (i=0; i<2; i++) {
		if (p->trans[i].server_rtcp_fd != 0) {
			CLOSE(p->trans[i].server_rtcp_fd);
			p->trans[i].server_rtcp_fd = 0;
		}

		if (p->trans[i].server_rtp_fd != 0) {
			CLOSE(p->trans[i].server_rtp_fd);
			p->trans[i].server_rtp_fd = 0;
		}

		p->trans[i].rtp_timestamp = 0;
	}

    p->given_session_id = 0;
    p->cseq = 0;

    ctx = p->trans[0].rtp_timestamp;
    /* randomize session id to avoid conflict */
    p->session_id = __get_random_llu(&ctx);
    /*p->rtp_timestamp = __get_random_llu(&ctx);*/

    return SUCCESS;
}

    static inline int
__connection_list_add(bufpool_handle con_pool, struct list_head_t *head,int fd, struct sockaddr_in addr)
{
    DASSERT(head,return FAILURE);
    DASSERT(fd > 0, return FAILURE);

    struct connection_item_t *p = NULL;

    ASSERT(bufpool_get_free(con_pool, &p) == SUCCESS,return FAILURE);

    DASSERT(p, return FAILURE);

    DBG("previous fd=%d\n", p->client_fd);

    p->addr=addr;
    p->client_fd=fd;

    ASSERT((p->fp_tcp_read = fdopen(fd,"r")), goto error);
    ASSERT((p->fp_tcp_write = fdopen(fd,"w")), goto error);

    p->con_state = __CON_S_INIT;

    return list_add(head,&(p->list_entry));
error:
    __connection_reset(&p->list_entry);
    return FAILURE;
}

static inline int __find_fd_max(struct list_head_t *head)
{
    struct list_t *p;
    struct connection_item_t *c;
    int m = -1;
    p = head->list;
    while(p) {
        list_upcast(c,p);
        if (c->con_state != __CON_S_DISCONNECTED) {
            m = max(c->client_fd,m);
        }
        p = p->next;
    }
    return m;
}

static inline int __set_select_sock(struct list_t *p, void *param)
{
    struct connection_item_t *c;
    struct sock_select_t *socks = param;

    list_upcast(c,p);

    FD_SET(c->client_fd, &(socks->rfds));

    return SUCCESS;
}

static inline int __bind_tcp(unsigned short port)
{
    int server_fd = 0;
    struct sockaddr_in addr;
    int tmp = 1;

    /* setup serve rsocket */
    ASSERT((server_fd = socket(AF_INET,SOCK_STREAM,0)) > 0, ({
                ERR("socket:%s\n",strerror(errno));
                goto error;}));

    setsockopt(server_fd,SOL_SOCKET,SO_REUSEADDR,&tmp,sizeof(tmp));

    addr.sin_port=htons(port);
    addr.sin_addr.s_addr=htonl(INADDR_ANY);
    addr.sin_family=AF_INET;

    ASSERT(bind(server_fd,(struct sockaddr *)&addr,sizeof(addr)) == 0, ({
                ERR("bind:%s\n",strerror(errno));
                goto error;}));

    ASSERT(listen(server_fd,5) >= 0, ({
                ERR("listen:%s\n",strerror(errno));
                goto error;}));

    /* set the socket to non-blocking */
    fcntl(server_fd,F_SETFL,fcntl(server_fd,F_GETFL) | O_NONBLOCK);

    return server_fd;
error:
    if (server_fd > 0) close(server_fd);
    return FAILURE;
}

static inline int __bind_rtp(struct connection_item_t *con )
{
    int server_fd = -1;
    struct sockaddr_in addr = {};
    int tmp;

    /* reset socket */
    if (con->trans[con->track_id].server_rtp_fd != 0) {
        CLOSE(con->trans[con->track_id].server_rtp_fd);
        //FCLOSE(con->fp_rtp_write);
        con->trans[con->track_id].server_rtp_fd = 0;
    }
    /* setup serve rsocket */
    ASSERT((server_fd = socket(AF_INET,SOCK_DGRAM,0)) > 0, ({
                ERR("socket:%s\n",strerror(errno));
                goto error;}));

    addr.sin_port=htons(con->trans[con->track_id].server_port_rtp);
    addr.sin_addr.s_addr=htonl(INADDR_ANY);
    addr.sin_family=AF_INET;
    
    tmp = 1;
    setsockopt(server_fd,SOL_SOCKET,SO_REUSEADDR,&tmp,sizeof(tmp));

    ASSERT(bind(server_fd,(struct sockaddr *)&addr,sizeof(addr)) == 0, ({
                ERR("bind:%s\n",strerror(errno));
                goto error;}));

    addr = con->addr;
    addr.sin_port=htons(con->trans[con->track_id].client_port_rtp);

    ASSERT(connect(server_fd,(struct sockaddr *)&addr,sizeof(addr)) == 0, ({
                ERR("connect:%s\n",strerror(errno));
                goto error;}));

    /* set the socket to non-blocking */
    tmp = 1;
    ASSERT(ioctl(server_fd,FIONBIO, &tmp) != -1, ({
                ERR("ioctl:%s\n",strerror(errno));
                goto error;}));

    con->trans[con->track_id].server_rtp_fd = server_fd;

    return SUCCESS;
error:
    if (server_fd > 0) close(server_fd);
    return FAILURE;
}

static inline int __bind_rtcp(struct connection_item_t *con )
{
    int server_fd = -1;
    struct sockaddr_in addr = {};
    int tmp;

    /* reset socket */
    if (con->trans[con->track_id].server_rtcp_fd != 0) {
        CLOSE(con->trans[con->track_id].server_rtcp_fd);
        con->trans[con->track_id].server_rtcp_fd = 0;
    }

    /* setup serve rsocket */
    ASSERT((server_fd = socket(AF_INET,SOCK_DGRAM,0)) > 0, ({
                ERR("socket:%s\n",strerror(errno));
                goto error;}));

    addr.sin_port=htons(con->trans[con->track_id].server_rtcp_fd);
    addr.sin_addr.s_addr=htonl(INADDR_ANY);
    addr.sin_family=AF_INET;

    tmp = 1;
    setsockopt(server_fd,SOL_SOCKET,SO_REUSEADDR,&tmp,sizeof(tmp));

    ASSERT(bind(server_fd,(struct sockaddr *)&addr,sizeof(addr)) == 0, ({
                ERR("bind:%s\n",strerror(errno));
                goto error;}));

    addr = con->addr;
    addr.sin_port=htons(con->trans[con->track_id].client_port_rtcp);

    ASSERT(connect(server_fd,(struct sockaddr *)&addr,sizeof(addr)) == 0, ({
                ERR("connect:%s\n",strerror(errno));
                goto error;}));

    con->trans[con->track_id].server_rtcp_fd = server_fd;

    return SUCCESS;
error:
    if (server_fd > 0) close(server_fd);
    return FAILURE;
}

static inline int __accept_proc_sock(rtsp_handle h, int server_fd, struct sock_select_t *p_socks)
{
    unsigned int len;
    int fd;
    //int tmp;
    struct sockaddr_in from_addr;

    if (FD_ISSET(server_fd, &p_socks->rfds) != 0) {

        /* accept new connection */
        len = sizeof(from_addr);

        fd = accept(server_fd,(struct sockaddr *) &from_addr,
                &len);

        /* we have selected this fd, but still EAGAIN may occur */
        if (fd < 0){
            ASSERT(errno == EAGAIN, ({
                        ERR("accept:%s\n",strerror(errno));
                        return FAILURE;}));
            return SUCCESS;
        }

        /* set server fd to non-blocking */
        fcntl(fd,F_SETFL,fcntl(fd,F_GETFL) | O_NONBLOCK);

        /* update connection-list exclusively */
        ASSERT(__connection_list_add(h->con_pool,&h->con_list,fd, from_addr) == SUCCESS,
                return FAILURE);

    }
    return SUCCESS;
}

static int __connection_is_dead(struct list_t *l)
{
    struct connection_item_t *c;

    list_upcast(c,l);

    return c->con_state == __CON_S_DISCONNECTED;
}

/******************************************************************************
 *                  THREAD CALLBACKS
 ******************************************************************************/
static void *rtspThrFxn(void *v)
{
    thread_handle           h = v;
    rtsp_handle             rh = h->sharedp->param_shared;
    void                    *status = THREAD_FAILURE;
    struct sock_select_t    socks = {};

    int     ret_select;
    int     server_fd = -1;

    DASSERT(thread_check_isoleted_job(h) == SUCCESS, goto error);

    /* open tcp connection */
    ASSERT((server_fd = __bind_tcp(SERVER_RTSP_PORT)) > 0, goto error);

    socks.nfds = server_fd + 1;
    socks.h_rtsp = rh;

    thread_sync_init(h);

    while (!gbl_get_quit(h->sharedp->gbl)) {

        FD_ZERO(&(socks.rfds));
        FD_SET(server_fd, &(socks.rfds));
        socks.timeout.tv_sec = 1;
        socks.timeout.tv_usec = 0;

        ASSERT(list_map_inline(&rh->con_list, (__set_select_sock), &socks) == SUCCESS, goto error);

        ASSERT((ret_select = select(socks.nfds,&(socks.rfds),NULL,NULL,&(socks.timeout))) >= 0, ({
                    ERR("select:%s\n",  strerror(errno));
                    goto error;}));

        if (ret_select > 0){
            /* lock while tcp layer is done */
            rtsp_lock(rh);

            ASSERT(__accept_proc_sock(rh, server_fd, &socks) == SUCCESS, 
                    ({ rtsp_unlock(rh); goto error;}));

            ASSERT(list_map_inline(&rh->con_list,__message_proc_sock, &socks) == SUCCESS, 
                    ({ rtsp_unlock(rh); goto error;}));

            MUST(list_sweep(&rh->con_list,__connection_is_dead) == SUCCESS, 
                    ({ rtsp_unlock(rh); goto error;}));

            socks.nfds = max(server_fd, __find_fd_max(&rh->con_list)) + 1;

            rtsp_unlock(rh);
        } 
        //bufpool_statistics(rh->con_pool);
    }

    status = THREAD_SUCCESS;
error:
    /* Make sure the other threads aren't waiting for us */
    thread_sync_cleanup(h);

    if (server_fd > 0) close(server_fd);

    return status;
}


/******************************************************************************
 *              PUBLIC FUNCTIONS
 ******************************************************************************/
void rtsp_finish(rtsp_handle h)
{
    /* close every connections in the handle */
    if (h) {
        
        list_destroy(&h->con_list);

        if (h->pool) {

            gbl_set_quit(h->pool->sharedp->gbl);

            ASSERT(threadpool_join(h->pool) == SUCCESS, ERR("thread join with error\n"));

            bufpool_delete(h->con_pool);
            bufpool_delete(h->transfer_pool);

            mime_encoded_delete(h->sprop_vps_b64);
            mime_encoded_delete(h->sprop_sps_b64);
            mime_encoded_delete(h->sprop_sps_b16);
            mime_encoded_delete(h->sprop_pps_b64);

            threadpool_delete(h->pool);
        }

        pthread_mutex_destroy(&h->mutex);

        FREE(h);
    }
    return;
}

rtsp_handle rtsp_create(unsigned char max_con, int priority, int total_ch)
{
    rtsp_handle       nh = NULL;

    ASSERT(max_con <= RTSP_MAXIMUM_CONNECTIONS,
            ({ERR("maximum number of connections should be within %d\n", RTSP_MAXIMUM_CONNECTIONS);
             return NULL;}));

    ASSERT(total_ch <= RTSP_MAXIMUM_CONNECTIONS && total_ch > 0,
            ({ERR("total_ch = %d, total_ch>0 && total_ch<=%d\n", total_ch, RTSP_MAXIMUM_CONNECTIONS);
             return NULL;}));

    TALLOC(nh,return NULL);

    nh->max_con = max_con;
    nh->priority = priority;
	nh->total_ch = total_ch;

    pthread_mutex_init(&nh->mutex,NULL);

    ASSERT(nh->pool = threadpool_create(nh), goto error);
    ASSERT(nh->con_pool =  __connectionpool_create(max_con), goto error);
    ASSERT(nh->transfer_pool =  __transpool_create(max_con), goto error);

    /* create tcp thread */
    ASSERT(CREATE_THREAD(nh->pool, rtspThrFxn, priority--, NULL),
            goto error);

    ASSERT(threadpool_start(nh->pool) == SUCCESS,
            goto error);

    srand((unsigned) time(NULL));

    return nh;

error: 
    rtsp_finish(nh);
    return NULL;
}

void rtsp_set_media_attr(rtsp_handle h, rtsp_media_attr_t *pattr)
{
	int i;

	for (i=0; i<2; i++) {
		h->video_type[i] = pattr->video_type[i];	
		h->video_fps[i] = pattr->video_fps[i];
	}

	h->audio_type = pattr->audio_type;
	h->audio_sample_rate = pattr->audio_sample_rate;
	h->audio_poinum = pattr->audio_poinum;

	return;
}

int rtsp_tick(rtsp_handle h)
{
    ASSERT(h, return FAILURE);
    struct timeval tv;

    ASSERT(gettimeofday(&tv,NULL) == 0, ({
        ERR("gettimeofday failed\n");
        return FAILURE;}));

    return __get_timestamp_offset(&h->stat,&tv);
}
