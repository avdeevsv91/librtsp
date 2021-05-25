#ifndef __RTSP_SERVER_H
#define __RTSP_SERVER_H

#if defined (__cplusplus)
extern "C" {
#endif
#include <unistd.h>
#include <time.h>

/******************************************************************************
 *              DEFINITIONS
 ******************************************************************************/
#define SERVER_RTSP_PORT 554
#define SERVER_RTP_PORT 50000
#define SERVER_RTCP_PORT 60000
#define RTSP_MAXIMUM_FRAMERATE 60
#define RTSP_MAXIMUM_CONNECTIONS 16

#define STR_RTSP_VERSION "RTSP/1.0"

#define RTSP_PAYLOAD_TYPE_H264      96
#define RTSP_PAYLOAD_TYPE_H265      98
#define RTSP_PAYLOAD_TYPE_G711_PCMA 8
#define RTSP_PAYLOAD_TYPE_G711_PCMU 0

/* __rtsp_obj_t is private. you will not see it */
typedef struct __rtsp_obj_t *rtsp_handle;

typedef struct {
	int video_type[2];
	int video_fps[2];
	int audio_type;
	int audio_sample_rate; 	
	int audio_poinum;
} rtsp_media_attr_t;

typedef enum {
	RTSP_MEDIA_DWTYPE_VIDEO_MAIN,
	RTSP_MEDIA_DWTYPE_VIDEO_EXTRA,
	RTSP_MEDIA_DWTYPE_AUDIO	
} rtsp_media_dwtype_e;

/******************************************************************************
 *              LIBRARY FUNCTIONS
 ******************************************************************************/

extern int rtp_send_media(rtsp_handle h, int ch,  int type, signed char *buf, size_t len, struct timeval *p_tv);

extern void rtsp_finish(rtsp_handle h);

extern rtsp_handle rtsp_create(unsigned char max_con, int priority, int total_ch);

extern  void rtsp_set_media_attr(rtsp_handle h, rtsp_media_attr_t *pattr);

#if defined (__cplusplus)
}
#endif

#endif
