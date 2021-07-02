/*!
 *=================================================================\n
 *
 *  COPYRIGHT (c) Ubinetsys Co., Ltd. 2003
 *
 *  The copyright to the document(s) herein is the property of
 *  Ubinetsys Co., Ltd.
 *
 *  The document(s) may be used  and/or copied only with the
 *  written permission from Ubinetysys or in accordance with
 *  the terms and conditions stipulated in the agreement/contract
 *  under which the document(s) have been supplied.
 *
 *=================================================================\n
 */

/*!
 \n******************************************************************
 @file    pmu_r1_06.c
 @brief   PMU spi/tcp/udp routine for OPMS
 @author  NiLL TERU (www.ubinetsys.com)
 @date    2021-07-02 20:16:49
 @version 1.06
 @todo
 @bug
 @warning
 @remark
 \n******************************************************************
 */

/*!
 \n==================================================================
 @brief Includes
 \n==================================================================
 */
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <netdb.h>
#include <sys/types.h>
#include <linux/types.h>
#include <linux/spi/spidev.h>

#include <netinet/in.h>
#include <sys/socket.h>
#include <unistd.h>

#include <stdarg.h> /* for va_list */

#include <stdint.h>
#include <syslog.h>

#include <getopt.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <arpa/inet.h> //ness
#include <net/if.h>

#include <sys/stat.h>

#include <time.h>

#include "swif_pmu.h"

/*!
 \n==================================================================
 @brief Definitions
 \n==================================================================
 */
//125.130.148.80
//#define OPMS_STRX  ("14.63.237.89")     //KT OPMS SERVER
#define OPMS_STRX  ("14.63.159.29")
#define TCPM_STRX  ("218.155.74.14")    //UBN SERVER

#define DEBUG_PMU (1)

#define FIW_ALM_FLAG    (10)

#define PMU_CONF_PORT      (9999)
#define PMU_RSYS_PORT      (5141)
#define PMU_RPRT_PORT      (8001)
#define TCP_SRV_PORT       (8010)

#define MAX_CONF_RECV_SIZE (500)
#define MAX_RSYS_RX_SIZE   (1000)
#define MAX_RSYS_TX_SIZE   (500)
    
#define MAX_OPMS_RX_SIZE   (1000)
#define MAX_OPMS_TX_SIZE   (500)
#define MAX_RPRT_TX_SIZE   (500)

#define MAX_NUMOF_ACL      (20)

#define PS_NORMAL           (0x0)
#define PS_AI_LO_ALARM      (0x1)
#define PS_AI_HI_ALARM      (0x2)
#define PS_DI_ALARM         (0x3)

#define PEC_NOT_USED        (0x0)
#define PEC_AI_ALM_MASK     (0x1)
#define PEC_AI_ALM_USE      (0x2)
#define PEC_DI_A_ALM_MASK   (0x3)
#define PEC_DI_B_ALM_MASK   (0x4)
#define PEC_DI_A_ALM_USE    (0x5)
#define PEC_DI_B_ALM_USE    (0x6)

static uint8_t pmuVer[4]  = {'1','.','0','6'};
static uint8_t pmuAddr[6] = {0,};

static uint8_t pmuOpms[6]={14,63,159,29,0,0}; // @2019-05-28 17:36:15
static uint8_t pmuAddx[6]={192,168,0,229,0,0};
static uint8_t pmuGate[6]={192,168,0,1,0,0};
static uint8_t pmuMask[6]={255,255,255,0,0,0};

#define MAX_STR_AUTH  (30)
char strRID[MAX_STR_AUTH] = "opmssw";
char strRPW[MAX_STR_AUTH] = "sw!@#$";
char strDPW[MAX_STR_AUTH] = "power2018!@";
                          //ACV1,ACV2,DCV1,DCV2,DCV3,TEMP
static float AI_Hyst[8] = { 3.0F, 3.0F, 1.0F, 1.0F, 1.0F, 2.0F, 0.0F, 0.0F };

static uint32_t u32AlarmCnt = 0uL;

static uint8_t bIptableFlag = 0;
static CLOCK_T sysrtc;
static uint32_t pPMU_SID = 55555555uL; //default


static uint32_t p32ACL[MAX_NUMOF_ACL+1]={0uL};

uint8_t bRcvdAlarmAck = 0;
uint8_t bUpgradeRequest = 0;
uint8_t bUpgradeReport = 0;

F32_T f32AnalogVal [7+1];
F32_T f32DigitalVal[7+1];

AI_ETC_ConfigType AI_Conf[6+1];
DI_ETC_ConfigType DI_Conf[6+1];

static uint8_t u8AnalogSTS[8]  = {0}; 
static uint8_t u8AnalogPRV[8]  = {0}; 
static uint8_t u8DigitalSTS[8] = {0};
static uint8_t u8DigitalPRV[8] = {0};

#define ARRAY_SIZE(a) (sizeof(a) / sizeof((a)[0]))
static const char *device = "/dev/spidev0.0";
static uint8_t mode;
static uint8_t debug = 0;
static uint8_t bits = 8;
static uint32_t speed = 500000;
static uint16_t delay = 0;

static uint8_t bLedFlag = 0;

/*
    00 77 19 30 30 70 00 00 00 00 00 00 00 00 D8 F0 00 00 00 00 00 00 00 00 00 00 00 00 00 :Rcvd[29]
    77 FF FE FF FE FF FE FF FE FF FE FF FE FF FE 00 00 00 00 00 00 00 01 01 01 01 01 01 88 :Send[29]
*/

uint8_t spi_tx[] = {    //  rx  tx    
            0x77,       // [ 1][ 0]             CMD Code
            0xFF,       // [ 2][ 1] ACV1         HI       
            0xFE,       // [ 3][ 2]              LO       
            0xFF,       // [ 4][ 3] ACV2         HI       
            0xFE,       // [ 5][ 4]              LO       
            0xFF,       // [ 6][ 5] DCV0         HI       
            0xFE,       // [ 7][ 6]              LO       
            0xFF,       // [ 8][ 7] DCV1         HI       
            0xFE,       // [ 9][ 8]              LO       
            0xFF,       // [10][ 9] DCV2         HI       
            0xFE,       // [11][10]              LO       
            0xFF,       // [12][11] DCV3         HI       
            0xFE,       // [13][12]              LO       
            0xFF,       // [14][13] TEMP1        HI       
            0xFE,       // [15][14]              LO       
            0x00,       // [16][15] ACV1 ST      ACV1 LED 
            0x00,       // [17][16] ACV2 ST      ACV2 LED 
            0x00,       // [18][17] DCV1 ST      DCV1 LED 
            0x00,       // [19][18] DCV2 ST      DCV2 LED 
            0x00,       // [20][19] DCV3 ST      DCV3 LED 
            0x00,       // [21][20] DCV4 ST      DCV4 LED 
            0x00,       // [22][21] TMP1 ST      TEMP1 LED
            0x00,       // [23][22] DI1 ST       DI1 LED  
            0x00,       // [24][23] DI2 ST       DI2 LED  
            0x00,       // [25][24] DI3 ST       DI3 LED  
            0x00,       // [26][25] DI4 ST       DI4 LED  
            0x00,       // [27][26] DI5 ST       DI5 LED  
            0x00,       // [28][27] DI6 ST       DI6 LED  
            0x88,       // [29][28] END CODE
};

uint8_t spi_rx[ARRAY_SIZE(spi_tx)] = {0, };

/*!
 \n==================================================================
 @brief function calls
 \n==================================================================
 */
void checkAnalogAlarm(void);
void checkDigitalAlarm(uint8_t* raw_di);
int setRealTimeReportToFile(void);

int setACLtoFile(void);
int setCNFtoFile(void);
int setNETtoFile(void);
int setDEVtoFile(void);
int setSYStoFile(void);
int rstSYStoFile(void);
int setSFTPtoFile(void);
int setPWDtoFile(void);
void setUserPwd(void);
int getUpgradeStat(void);

int fetchCNFfrFile(void);
int fetchACLfrFile(void);
int fetchNETfrFile(void);
int fetchDEVfrFile(void);

void setTest(void)
{
	unsigned char command[100];
    sprintf((char*)command,"/home/seopms/pmu/sftpclt.r > upgrade.seq"); system(command);
    if (getUpgradeStat()==99) printf("upgrade_success\n");
    else printf("upgrade_fail\n");
}   

int filterInit(void)
{
    unsigned char command[100];
    sprintf((char*)command,"/home/seopms/pmu/iptables.sh"); system(command);
    return 1;
} 

/*!
 \n==================================================================
 @brief Includes
 \n==================================================================
 */
int OPMS_Rprt_Send(uint8_t* tPacket, uint16_t field_no, uint8_t debug); 
uint16_t set_MSG_REALTIME_RSP(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_TIME_CONFIG_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_CONFIG_SEND_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_CONFIG_ALL_SEND_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_CONFIG_LIST_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_NETWORK_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_VERSION_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_RESET_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t set_MSG_UPGRADE_ACK(uint8_t* tPacket, uint8_t* rPacket);
uint16_t send_MSG_RESTART(void);
uint16_t send_MSG_ALARM(void);
uint8_t  get_MSG_ALARM_SEND_ACK(void);
uint8_t  get_MSG_RESTART_ACK(void);

void initRealtimeData(void);
void stopRealtimeReport(void);
void getSystemRTC2(CLOCK_T* rtc);

#define MAX_SEC   (500)
static uint32_t p32SEC900[MAX_SEC+1]={0uL};//900_TCP_SYN_FLOOD
static uint32_t p32SEC901[MAX_SEC+1]={0uL};//901_ARP_SPOOFING
static uint32_t p32SEC902[MAX_SEC+1]={0uL};//902_ICMP_SMURF_ATTACK
static uint32_t p32SEC903[MAX_SEC+1]={0uL};//903_FRAGGLE_ATTACK
static uint32_t p32SEC904[MAX_SEC+1]={0uL};//904_LAND_ATTACK
static uint32_t p32SEC905[MAX_SEC+1]={0uL};//905_PING_OF_DEATH
static uint32_t p32SEC906[MAX_SEC+1]={0uL};//906_ILLEGAL_ARP
static uint32_t p32SEC907[MAX_SEC+1]={0uL};//907_ILLEGAL_MAC_SRC
static uint32_t p32SEC908[MAX_SEC+1]={0uL};//908_UDP_ECHO_LOOP
static uint32_t p32SEC909[MAX_SEC+1]={0uL};//909_ILLEGAL_SRC_IP
static uint16_t u16SameIpCnt[11] = {0};

void clearSBUF(void)
{
    int i;
    
    for (i=0; i<=MAX_SEC; i++) p32SEC900[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC901[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC902[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC903[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC904[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC905[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC906[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC907[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC908[i] = 0uL;
    for (i=0; i<=MAX_SEC; i++) p32SEC909[i] = 0uL;
    for (i=0; i<11; i++) u16SameIpCnt[i] =0;
}

void getP8Addr(struct in_addr u32addr, uint8_t* pADDR)
{
    pADDR[0] = (uint8_t)(u32addr.s_addr);
    pADDR[1] = (uint8_t)(u32addr.s_addr>> 8);
    pADDR[2] = (uint8_t)(u32addr.s_addr>>16);
    pADDR[3] = (uint8_t)(u32addr.s_addr>>24);
}

uint32_t setP8Addr(uint8_t* pADDR)
{
    return (pADDR[3]<<24 | pADDR[2]<<16 | pADDR[1]<<8 | pADDR[0]<<0);
}

void getACLaddr(uint32_t u32addr, uint8_t* pADDR)
{
    pADDR[0] = (uint8_t)(u32addr);
    pADDR[1] = (uint8_t)(u32addr>> 8);
    pADDR[2] = (uint8_t)(u32addr>>16);
    pADDR[3] = (uint8_t)(u32addr>>24);
}

uint32_t setACLaddr(uint8_t* pADDR)
{
    return (pADDR[3]<<24 | pADDR[2]<<16 | pADDR[1]<<8 | pADDR[0]<<0);
}

uint8_t checkSameAttackerIP(uint8_t* bIP, uint32_t* p32IP, uint16_t* cnt)
{
    uint16_t i;
    uint32_t u32IP;
    
    u32IP = setP8Addr(bIP);
    
    for (i=0; i<(*cnt); i++){
        if (p32IP[i]==u32IP){ return 0; }
    }
    p32IP[i] = u32IP; if ((*cnt)<MAX_SEC) (*cnt)++; return 1; 
}

char D2C(uint8_t c)
{
    uint8_t t = (c&0x0F);
    if (t <= 9) //if (t >= 0 && t <= 9)
        return ('0' + t);
    if (t >= 10 && t <= 15)
        return ('A' + t - 10);

    return c;
}

int parse_reset(char* tPacket, char* rPacket, uint8_t set_rcv)
{
	unsigned char command[100];
	sprintf((char*)command,"reboot"); system(command);		
}





/*!
 \n==================================================================
 @brief Variable Definitions
 \n==================================================================
 */
void checkAnalogAlarm(void)
{
    uint8_t i;

    for (i=0; i<6; i++){
        if (AI_Conf[i].AIEtcConf.u16 == PEC_AI_ALM_USE){
            switch(u8AnalogSTS[i]){
                case PS_NORMAL:
                    if      (f32AnalogVal[i].f32 < AI_Conf[i].AILoValue.f32){ u8AnalogSTS[i] = PS_AI_LO_ALARM; }
                    else if (f32AnalogVal[i].f32 > AI_Conf[i].AIHiValue.f32){ u8AnalogSTS[i] = PS_AI_HI_ALARM; }
                    break;

                case PS_AI_LO_ALARM:
                    if (f32AnalogVal[i].f32 > (AI_Conf[i].AILoValue.f32 + AI_Hyst[i])){ u8AnalogSTS[i] = PS_NORMAL; }
                    break;

                case PS_AI_HI_ALARM:
                    if (f32AnalogVal[i].f32 < (AI_Conf[i].AIHiValue.f32 - AI_Hyst[i])){ u8AnalogSTS[i] = PS_NORMAL; }
                    break;

                default: u8AnalogSTS[i] = PS_NORMAL; break;
            }
        }
        else { u8AnalogSTS[i] = PS_NORMAL; }
    }
    ///if (f32AnalogVal[5].f32 < -40.0F){
    ///    u8AnalogSTS[5] = PS_NORMAL;
    ///}
}

void checkDigitalAlarm(uint8_t* raw_di)
{
    int i;
    /* AC in high -> normal */
    for (i=0; i<6; i++){
        if (DI_Conf[i].DIEtcConf.u16 == PEC_DI_A_ALM_USE){
            if (raw_di[i]) u8DigitalSTS[i] = PS_DI_ALARM;
            else           u8DigitalSTS[i] = PS_NORMAL; 
        } 
        else if (DI_Conf[i].DIEtcConf.u16 == PEC_DI_B_ALM_USE){
            if (raw_di[i]) u8DigitalSTS[i] = PS_NORMAL;
            else           u8DigitalSTS[i] = PS_DI_ALARM; 
        }
        else{ // (DI_Conf[i].DIEtcConf.u16 == PEC_NOT_USED) 
            u8DigitalSTS[i] = PS_NORMAL;
        }
    }
}

/*!
 \n==================================================================
 @brief PMU_HEADER_T getOPMSheader(uint8_t * rPacket)
 \n==================================================================
 */
PMU_HEADER_T getOPMSheader(uint8_t* rPacket)
{
    uint16_t i;

    PMU_HEADER_T pHEAD;

    pHEAD.ServiceCode = (uint16_t)rPacket[0]*256 + (uint16_t)rPacket[1];

    pHEAD.SID = rPacket[2];
    for (i=3; i<6; i++){
        pHEAD.SID *= 256UL;
        pHEAD.SID += (uint32_t)rPacket[i];
    }

    pHEAD.MsgLen = (uint16_t)rPacket[6]*256 + (uint16_t)rPacket[7];
    for (i=0; i<4; i++) { pHEAD.IP[i] =  rPacket[i+8]; }

    //12,13
    pHEAD.SeqID = rPacket[14];
    for (i=14; i<18; i++){
        pHEAD.SeqID *= 256UL;
        pHEAD.SeqID += (uint32_t)rPacket[i];
    }
    return pHEAD;
}

uint16_t setOPMSheader(uint8_t* tPacket, uint8_t* rPacket, uint16_t service_code, uint16_t length)
{
    /*
    Rcvd Message[18]
    ::01:31:
    04:4B:DA:B9:
    00:00:
    0E:3F:9F:1D:
    00:
    03:
    08:3F:41:05

    Send[90]to 14.63.159.29[8002 port]
    ::01:32:
    04:4B:DA:B9:
    00:48:
    79:A8:A1:B0:
    00:
    03:
    08:3F:41:05:
    
    43:72:00:00:
    43:40:00:00:
    00:02:
    
    43:72:00:00:
    43:40:00:00:
    00:00:
    
    42:6C:00:00:
    42:4C:00:00:
    00:02:
    
    42:6C:00:00:
    42:4C:00:00:
    00:02:
    
    42:60:00:00:
    42:48:00:00:
    00:00:
    
    42:20:00:00:
    00:00:00:00:
    00:00:
    
    00:05:
    00:05:
    00:05:
    00:05:
    00:05:
    00:05
    */
    
    uint16_t field_no = 0;

    tPacket[field_no++] = service_code/256;       //[0]
    tPacket[field_no++] = service_code%256;       //[1]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>24);//[2] SID
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>16);//[3]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>> 8);//[4]
    tPacket[field_no++] = (uint8_t)(pPMU_SID    );//[5]
    tPacket[field_no++] = length/256;             //[6]
    tPacket[field_no++] = length%256;             //[7]
    tPacket[field_no++] = pmuAddr[0];             //[8]
    tPacket[field_no++] = pmuAddr[1];             //[9]
    tPacket[field_no++] = pmuAddr[2];             //[10]
    tPacket[field_no++] = pmuAddr[3];             //[11]
    tPacket[field_no++] = 0;                      //[12]
    tPacket[field_no++] = PV_TF;                  //[13] pmu vendor
    tPacket[field_no++] = rPacket[14];            //[14] sequence no. 
    tPacket[field_no++] = rPacket[15];            //[15]
    tPacket[field_no++] = rPacket[16];            //[16]
    tPacket[field_no++] = rPacket[17];            //[17]

    return field_no;
}

uint16_t setAlarmHeader(uint8_t* tPacket, uint16_t service_code, uint16_t length)
{
    uint16_t field_no = 0;

    tPacket[field_no++] = service_code/256;       //[0]
    tPacket[field_no++] = service_code%256;       //[1]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>24);//[2] SID
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>16);//[3]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>> 8);//[4]
    tPacket[field_no++] = (uint8_t)(pPMU_SID    );//[5]
    tPacket[field_no++] = length/256;             //[6]
    tPacket[field_no++] = length%256;             //[7]
    tPacket[field_no++] = pmuAddr[0];             //[8]
    tPacket[field_no++] = pmuAddr[1];             //[9]
    tPacket[field_no++] = pmuAddr[2];             //[10]
    tPacket[field_no++] = pmuAddr[3];             //[11]
    tPacket[field_no++] = 0;                      //[12]
    tPacket[field_no++] = PV_TF;                  //[13] pmu vendor
    tPacket[field_no++] = (uint8_t)(u32AlarmCnt>>24); //[14] sequence no. 
    tPacket[field_no++] = (uint8_t)(u32AlarmCnt>>16); //[15]
    tPacket[field_no++] = (uint8_t)(u32AlarmCnt>> 8); //[16]
    tPacket[field_no++] = (uint8_t)(u32AlarmCnt    ); //[17]

    return field_no;
}

void makeAlarmCnt(void)
{
    if (bRcvdAlarmAck==0){
        bRcvdAlarmAck = 1;
        if (++u32AlarmCnt > 99999uL) u32AlarmCnt = 0;
    }
}

/*!
 \n==================================================================
 @brief Real-Time Request Proc
 \n==================================================================
 */
void initRealtimeData(void)
{
    int i;
    
    for (i=0; i<7; i++){
        f32AnalogVal[i].f32 = 0.0F;
    }

    for (i=0; i<6; i++){
        f32DigitalVal[i].f32 = 0.0F;
    }
}

void initConfigData(void)
{
    int i;
    
    AI_Conf[0].AIHiValue.f32 = 242.0F; AI_Conf[0].AILoValue.f32 = 176.0F;
    AI_Conf[1].AIHiValue.f32 = 242.0F; AI_Conf[1].AILoValue.f32 = 176.0F;
    AI_Conf[2].AIHiValue.f32 = 56.00F; AI_Conf[2].AILoValue.f32 = 41.00F;
    AI_Conf[3].AIHiValue.f32 = 56.00F; AI_Conf[3].AILoValue.f32 = 41.00F;
    AI_Conf[4].AIHiValue.f32 = 56.00F; AI_Conf[4].AILoValue.f32 = 41.00F;
    AI_Conf[5].AIHiValue.f32 = 50.0F;  AI_Conf[5].AILoValue.f32 = -10.0F;

    for (i=0; i<6; i++){
        AI_Conf[i].AIEtcConf.u16 = PEC_NOT_USED;
    }

    for (i=0; i<6; i++){
        DI_Conf[i].DIEtcConf.u16 = PEC_NOT_USED;
    }
}

uint16_t set_MSG_REALTIME_RSP(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t i;
    uint16_t field_no = 0;
    
    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_REALTIME_RSP,60);
    
    /*=== PMU DATA ==================================*/
    for (i=0; i<6; i++){
        tPacket[field_no++] = f32AnalogVal[i].u8[3];
        tPacket[field_no++] = f32AnalogVal[i].u8[2];
        tPacket[field_no++] = f32AnalogVal[i].u8[1];
        tPacket[field_no++] = f32AnalogVal[i].u8[0];
        tPacket[field_no++] = u8AnalogSTS[i];
    }

    for (i=0; i<6; i++){
        //if (raw_di[i]) f32DigitalVal[i].f32 = 1.0F; else f32DigitalVal[i].f32 = 0.0F;
        tPacket[field_no++] = f32DigitalVal[i].u8[3];
        tPacket[field_no++] = f32DigitalVal[i].u8[2];
        tPacket[field_no++] = f32DigitalVal[i].u8[1];
        tPacket[field_no++] = f32DigitalVal[i].u8[0];
        tPacket[field_no++] = u8DigitalSTS[i];
    }
    return field_no;
}

/*!
 \n==================================================================
 @brief uint16_t set_MSG_TIME_CONFIG_ACK(void)
 \n==================================================================
 */
void getSystemRTC(void)
{
    time_t t = time(NULL);
    struct tm tm = *localtime(&t);
    printf("RTC: %02d-%02d-%02d %02d:%02d:%02d\n", tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec);
}

void getSystemRTC2(CLOCK_T* rtc)
{
    time_t t = time(NULL);
    struct tm tm = *localtime(&t);
    //printf("RTC: %d-%d-%d %d:%d:%d\n", tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec);

    //rtc->centry   = 20;
    //rtc->year     = 19;//tm.tm_year + 1900
    uint16_t  u16_tmp = (uint16_t)(tm.tm_year + 1900);
    
    rtc->centry   = u16_tmp/100;
    rtc->year     = u16_tmp%100;
    rtc->month    = (uint8_t)(tm.tm_mon + 1);
    rtc->date     = (uint8_t)tm.tm_mday;
    rtc->hours    = (uint8_t)tm.tm_hour;
    rtc->minutes  = (uint8_t)tm.tm_min;
    rtc->seconds  = (uint8_t)tm.tm_sec;
}

int checkSystemRTC(CLOCK_T* sys)
{
    CLOCK_T rtc;
    int changed_date = 0;
    
    getSystemRTC2(&rtc);
    
    if (sys->date != rtc.date){ changed_date = 1; }
    
    sys->centry   = rtc.centry ;
    sys->year     = rtc.year   ;
    sys->month    = rtc.month  ;
    sys->date     = rtc.date   ;
    sys->hours    = rtc.hours  ;
    sys->minutes  = rtc.minutes;
    sys->seconds  = rtc.seconds;

    return changed_date;
}

uint16_t set_MSG_TIME_CONFIG_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t field_no = 0;
    CLOCK_T rtc;
    uint16_t  u16_tmp;
    
    u16_tmp = (uint16_t)rPacket[18]*256 + (uint16_t)rPacket[19];
    rtc.centry  = u16_tmp/100;
    rtc.year    = u16_tmp%100;
    rtc.month   = rPacket[20];
    rtc.date    = rPacket[21];
    rtc.hours   = rPacket[22];
    rtc.minutes = rPacket[23];
    rtc.seconds = rPacket[24];

    getSystemRTC();
    
    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_TIME_CONFIG_ACK,1);
    
    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = AS_NORMAL;              //[18]

    return field_no;
}

uint16_t set_MSG_CONFIG_SEND_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t field_no = 0;

    //get config data from OPMS
    //by point code

    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_CONFIG_SEND_ACK,1);
    
    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = AS_NORMAL; //[18]

    return field_no;
}
/*
:01:2F:03:4F:B5:E3:00:48:0E:3F:ED:59:00:03:00:00:1C:7E:43:72:00:00:43:40:00:00:00:02:43:72:00:00:43:40:00:00:00:02:42:60:00:00:42:48:00:00:00:02:42:60:00:00:42:48:00:00:00:02:42:60:00:00:42:48:00:00:00:02:42:20:00:00:00:00:00:00:00:02:00:00:00:00:00:00:00:00:00:00:00:00
send[19]to 8002 port
*/
uint16_t set_MSG_CONFIG_ALL_SEND_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t i;
    uint16_t field_no = 0;
    uint16_t config_cnt = 0;

    //get config data from OPMS uRXD[18]~uRXD[18+71]

    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_CONFIG_ALL_SEND_ACK,1); //MSG_NETWORK_ACK
    
    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = AS_NORMAL;              //[18]

    config_cnt = 18;
    for (i=0; i<6; i++){
        AI_Conf[i].AIHiValue.u8[3] = rPacket[config_cnt++];
        AI_Conf[i].AIHiValue.u8[2] = rPacket[config_cnt++];
        AI_Conf[i].AIHiValue.u8[1] = rPacket[config_cnt++];
        AI_Conf[i].AIHiValue.u8[0] = rPacket[config_cnt++];

        AI_Conf[i].AILoValue.u8[3] = rPacket[config_cnt++];
        AI_Conf[i].AILoValue.u8[2] = rPacket[config_cnt++];
        AI_Conf[i].AILoValue.u8[1] = rPacket[config_cnt++];
        AI_Conf[i].AILoValue.u8[0] = rPacket[config_cnt++];

        AI_Conf[i].AIEtcConf.u8[1] = rPacket[config_cnt++];
        AI_Conf[i].AIEtcConf.u8[0] = rPacket[config_cnt++];
    }

    for (i=0; i<6; i++){
        DI_Conf[i].DIEtcConf.u8[1] = rPacket[config_cnt++];
        DI_Conf[i].DIEtcConf.u8[0] = rPacket[config_cnt++];
    }
    
    setCNFtoFile();

    return field_no;
}

uint16_t set_MSG_CONFIG_LIST_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t i,j;
    uint16_t field_no = 0;

    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_CONFIG_LIST_ACK,72);
    
    /*=== PMU DATA ==================================*/
    for (i=0; i<6; i++){ /* 6 * 10 = 72 */
        tPacket[field_no++] = AI_Conf[i].AIHiValue.u8[3];
        tPacket[field_no++] = AI_Conf[i].AIHiValue.u8[2];
        tPacket[field_no++] = AI_Conf[i].AIHiValue.u8[1];
        tPacket[field_no++] = AI_Conf[i].AIHiValue.u8[0];
        tPacket[field_no++] = AI_Conf[i].AILoValue.u8[3];
        tPacket[field_no++] = AI_Conf[i].AILoValue.u8[2];
        tPacket[field_no++] = AI_Conf[i].AILoValue.u8[1];
        tPacket[field_no++] = AI_Conf[i].AILoValue.u8[0];
        tPacket[field_no++] = AI_Conf[i].AIEtcConf.u8[1];
        tPacket[field_no++] = AI_Conf[i].AIEtcConf.u8[0];
    }

    for (i=0; i<6; i++){ /* 6 * 2 = 12 */
        tPacket[field_no++] = DI_Conf[i].DIEtcConf.u8[1];
        tPacket[field_no++] = DI_Conf[i].DIEtcConf.u8[0];
    }
    
    /*
    Rcvd Message[18]
    ::01:31:
    04:4B:DA:B9:00:00:0E:3F:9F:1D:00:03:08:3F:41:05

    Send[90]to 14.63.159.29[8002 port]
    ::01:32:04:4B:DA:B9:00:48:79:A8:A1:B0:00:03:08:3F:41:05:43:72:00:00:43:40:00:00:00:02:43:72:00:00:43:40:00:00:00:00:42:6C:00:00:42:4C:00:00:00:02:42:6C:00:00:42:4C:00:00:00:02:42:60:00:00:42:48:00:00:00:00:42:20:00:00:00:00:00:00:00:00:00:05:00:05:00:05:00:05:00:05:00:05
    */

    
    
    
    
    
    
    
    
    
    return field_no;
}

uint16_t set_MSG_NETWORK_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t field_no = 0;

    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_NETWORK_ACK,1);
    
    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = AS_NORMAL; //[18]

    return field_no;
}

uint16_t set_MSG_VERSION_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t field_no = 0;

    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_VERSION_ACK,4);

    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = pmuVer[0]; //[18] 0
    tPacket[field_no++] = pmuVer[1]; //[19] 1
    tPacket[field_no++] = pmuVer[2]; //[20] 2
    tPacket[field_no++] = pmuVer[3]; //[21] 3

    return field_no;
}

uint16_t set_MSG_UPGRADE_RESULT(uint8_t* tPacket)
{
    uint16_t field_no = 0;

    /*=== PMU HEADER ==============================*/
    tPacket[field_no++] = MSG_UPGRADE_RESULT/256; //[0]
    tPacket[field_no++] = MSG_UPGRADE_RESULT%256; //[1]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>24);//[2] SID
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>16);//[3]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>> 8);//[4]
    tPacket[field_no++] = (uint8_t)(pPMU_SID    );//[5]
    tPacket[field_no++] = 0;                      //[6]
    tPacket[field_no++] = 5;                      //[7]
    tPacket[field_no++] = pmuAddr[0];             //[8]
    tPacket[field_no++] = pmuAddr[1];             //[9]
    tPacket[field_no++] = pmuAddr[2];             //[10]
    tPacket[field_no++] = pmuAddr[3];             //[11]
    tPacket[field_no++] = 0;                      //[12]
    tPacket[field_no++] = PV_TF;                  //[13] pmu vendor
    tPacket[field_no++] = 0;                      //[14] sequence no. 
    tPacket[field_no++] = 0;                      //[15]
    tPacket[field_no++] = 0;                      //[16]
    tPacket[field_no++] = 0;                      //[17]
    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = AS_NORMAL;              //[18] 0
    tPacket[field_no++] = pmuVer[0];              //[19] 1
    tPacket[field_no++] = pmuVer[1];              //[20] 2
    tPacket[field_no++] = pmuVer[2];              //[21] 3
    tPacket[field_no++] = pmuVer[3];              //[22] 4

    return field_no;
}

void send_MSG_UPGRADE_RESULT(void)
{
    char tPacket[MAX_OPMS_TX_SIZE];
    uint16_t field_no = 0;
    
    if (bUpgradeReport){
        bUpgradeReport = 0;
        
        field_no = set_MSG_UPGRADE_RESULT(tPacket);
        OPMS_Rprt_Send(tPacket, field_no, 1);
        syslog(LOG_NOTICE, "KT-PMU# Image Updated to ver%c%c%c%c",pmuVer[0],pmuVer[1],pmuVer[2],pmuVer[3]);
    }
}

uint16_t set_MSG_RESET_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t field_no = 0;

    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_RESET_ACK,1);
    
    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = AS_NORMAL; //[18]

    //SoftwareReset(); <==

    return field_no;
}

int getUpgradeStat(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    int ncnt = 0;
    
    fp = fopen("/home/seopms/pmu/upgrade.seq", "r");
    if (fp == NULL){ 
        return 0; 
    }

    while ((read = getline(&line, &len, fp)) != -1) {
       // if (strstr(line,"No such file or directory")!=NULL){  failcnt = 1; break; }
       if (strstr(line,"100%")!=NULL){  ncnt = 1; break; }
    }
    
    fclose(fp);
    
    if (ncnt) return 99;
    
    return 0;
}

int getGUIconfig(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    int ncnt=0;
    
    fp = fopen("/home/seopms/pmu/config.gui", "r");
    if (fp == NULL){ 
        return 0; 
    }
    while ((read = getline(&line, &len, fp)) != -1) {
       if (strstr(line,"config.pmu=1" )!=NULL){  ncnt = 1; break; }
    }
    
    fclose(fp);
    
    return ncnt;
}

int setGUIconfig(void)
{
	FILE * fp;
    
    fp = fopen("/home/seopms/pmu/config.gui", "w");
    if (fp == NULL)
    {
        return 0;
    }
    fprintf(fp, "config.pmu=0\n");
	
	fclose(fp);
		
	return 1;
}
int getGUInetwork(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    int ncnt=0;
    
    fp = fopen("/home/seopms/pmu/network.gui", "r");
    if (fp == NULL){ 
        return 0; 
    }
    while ((read = getline(&line, &len, fp)) != -1) {
       if (strstr(line,"network.pmu=1" )!=NULL){  ncnt = 1; break; }
    }
    
    fclose(fp);
    
    return ncnt;
}

int setGUInetwork(void)
{
	FILE * fp;
    
    fp = fopen("/home/seopms/pmu/network.gui", "w");
    if (fp == NULL)
    {
        return 0;
    }
    fprintf(fp, "network.pmu=0\n");
	
	fclose(fp);
		
	return 1;
}

int getGUIacllist(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    int ncnt=0;
    
    fp = fopen("/home/seopms/pmu/acllist.gui", "r");
    if (fp == NULL){ 
        return 0; 
    }
    while ((read = getline(&line, &len, fp)) != -1) {
       if (strstr(line,"acllist.pmu=1" )!=NULL){  ncnt = 1; break; }
    }
    
    fclose(fp);
    
    return ncnt;
}

int setGUIacllist(void)
{
	FILE * fp;
    
    fp = fopen("/home/seopms/pmu/acllist.gui", "w");
    if (fp == NULL)
    {
        return 0;
    }
    fprintf(fp, "acllist.pmu=0\n");
	
	fclose(fp);
		
	return 1;
}

int getGUIdevinfo(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    int ncnt=0;
    
    fp = fopen("/home/seopms/pmu/devinfo.gui", "r");
    if (fp == NULL){ 
        return 0; 
    }
    while ((read = getline(&line, &len, fp)) != -1) {
       if (strstr(line,"devinfo.pmu=1" )!=NULL){  ncnt = 1; break; }
    }
    
    fclose(fp);
    
    return ncnt;
}

int setGUIdevinfo(void)
{
	FILE * fp;
    
    fp = fopen("/home/seopms/pmu/devinfo.gui", "w");
    if (fp == NULL)
    {
        return 0;
    }
    fprintf(fp, "devinfo.pmu=0\n");
	
	fclose(fp);
		
	return 1;
}

int chkSFTPcommand(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    
    unsigned char command[100];
    
    fp = fopen("/home/seopms/pmu/sftpclt.r", "r");
    if (fp == NULL){ 
        setSFTPtoFile();
        sprintf((char*)command,"chmod 700 /home/seopms/pmu/sftpclt.r"); system(command);
        return 0; 
    }
	
	fclose(fp);
		
	return 1;
}

uint16_t set_MSG_UPGRADE_ACK(uint8_t* tPacket, uint8_t* rPacket)
{
    uint16_t field_no = 0;
    unsigned char command[100];
	  int fflag = 0;
    /*=== PMU HEADER ==============================*/
    field_no = setOPMSheader(tPacket,rPacket,MSG_UPGRADE_ACK,1);
    
    /*=== PMU DATA ==================================*/
    sprintf((char*)command,"/home/seopms/pmu/sftpclt.r > upgrade.seq"); system(command); /* @2019-11-20 14:03:39 */
    
    //sleep(3);
    
    fflag = getUpgradeStat();
    if (fflag==99){
    	tPacket[field_no++] = AS_NORMAL;              //[18] 0
    
    	syslog(LOG_NOTICE, "KT-PMU# Image Updated (from ver%c%c%c%c)",pmuVer[0],pmuVer[1],pmuVer[2],pmuVer[3]);
    	//sprintf((char*)command,"reboot"); system(command);

    	// UPGRADE()....
    	//setSYStoFile();
    	bUpgradeRequest = 1;
    }
    else tPacket[field_no++] = AS_NONSTORED_DATA ;              //[18] 2

    return field_no;
}

uint16_t set_MSG_ALARM_FIW(uint8_t* tPacket, uint16_t PointCode, uint8_t * bIP)
{
    CLOCK_T rtc;
    uint16_t field_no = 0;

    getSystemRTC2(&rtc);

    makeAlarmCnt();

    /*=== PMU HEADER ==============================*/
    field_no = setAlarmHeader(tPacket, MSG_ALARM_SEND, 19);

    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = PointCode/256;       //[18] 0
    tPacket[field_no++] = PointCode%256;       //[19] 1
    tPacket[field_no++] = 0;                   //[21] 3
    tPacket[field_no++] = D2C(rtc.year/10);    //[22] 4
    tPacket[field_no++] = D2C(rtc.year%10);    //[23] 5
    tPacket[field_no++] = D2C(rtc.month/10);   //[24] 6
    tPacket[field_no++] = D2C(rtc.month%10);   //[25] 7
    tPacket[field_no++] = D2C(rtc.date/10);    //[26] 8
    tPacket[field_no++] = D2C(rtc.date%10);    //[27] 9
    tPacket[field_no++] = D2C(rtc.hours/10);   //[28] 10
    tPacket[field_no++] = D2C(rtc.hours%10);   //[29] 11
    tPacket[field_no++] = D2C(rtc.minutes/10); //[30] 12
    tPacket[field_no++] = D2C(rtc.minutes%10); //[31] 13
    tPacket[field_no++] = D2C(rtc.seconds/10); //[32] 14
    tPacket[field_no++] = D2C(rtc.seconds%10); //[33] 15
    tPacket[field_no++] = bIP[0];              //[34] 16
    tPacket[field_no++] = bIP[1];              //[35] 17
    tPacket[field_no++] = bIP[2];              //[36] 18
    tPacket[field_no++] = bIP[3];              //[37] 19

    return field_no;
}

uint16_t set_MSG_ALARM_STD(uint8_t* tPacket, uint16_t u16PointCode, float fval, uint8_t stat)
{
    CLOCK_T rtc;
    F32_T f32AlarmValue;
    uint16_t field_no = 0;

    getSystemRTC2(&rtc);
    makeAlarmCnt();
    
    f32AlarmValue.f32 = fval;
    
    /*=== PMU HEADER ==============================*/
    field_no = setAlarmHeader(tPacket, MSG_ALARM_SEND, 19);
    
    /*=== PMU DATA ==================================*/
    tPacket[field_no++] = u16PointCode/256;    //[18] 0
    tPacket[field_no++] = u16PointCode%256;    //[19] 1
    tPacket[field_no++] = stat;                //[21] 3
    tPacket[field_no++] = D2C(rtc.year/10);    //[22] 4
    tPacket[field_no++] = D2C(rtc.year%10);    //[23] 5
    tPacket[field_no++] = D2C(rtc.month/10);   //[24] 6
    tPacket[field_no++] = D2C(rtc.month%10);   //[25] 7
    tPacket[field_no++] = D2C(rtc.date/10);    //[26] 8
    tPacket[field_no++] = D2C(rtc.date%10);    //[27] 9
    tPacket[field_no++] = D2C(rtc.hours/10);   //[28] 10
    tPacket[field_no++] = D2C(rtc.hours%10);   //[29] 11
    tPacket[field_no++] = D2C(rtc.minutes/10); //[30] 12
    tPacket[field_no++] = D2C(rtc.minutes%10); //[31] 13
    tPacket[field_no++] = D2C(rtc.seconds/10); //[32] 14
    tPacket[field_no++] = D2C(rtc.seconds%10); //[33] 15
    tPacket[field_no++] = f32AlarmValue.u8[3]; //[34] 16
    tPacket[field_no++] = f32AlarmValue.u8[2]; //[35] 17
    tPacket[field_no++] = f32AlarmValue.u8[1]; //[36] 18
    tPacket[field_no++] = f32AlarmValue.u8[0]; //[37] 19

    return field_no;
}

uint8_t get_MSG_ALARM_SEND_ACK(void)
{
    bRcvdAlarmAck = 0;

    return 1;
}

uint16_t send_MSG_RESTART(void)
{
    uint16_t field_no = 0;

    #if 0
    /*=== PMU HEADER ==============================*/
    tPacket[field_no++] = MSG_RESTART_SEND/256;   //[0]
    tPacket[field_no++] = MSG_RESTART_SEND%256;   //[1]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>24);//[2] 
    tPacket[field_no++] = (uint8_t)(pPMU_SID>>16);//[3]
    tPacket[field_no++] = (uint8_t)(pPMU_SID>> 8);//[4]
    tPacket[field_no++] = (uint8_t)(pPMU_SID    );//[5]
    tPacket[field_no++] = 0;                      //[6]
    tPacket[field_no++] = 0;                      //[7]
    tPacket[field_no++] = pmuAddr[0];             //[8]
    tPacket[field_no++] = pmuAddr[1];             //[9]
    tPacket[field_no++] = pmuAddr[2];             //[10]
    tPacket[field_no++] = pmuAddr[3];             //[11]
    tPacket[field_no++] = 0;                      //[12]
    tPacket[field_no++] = PV_TF;                  //[13] pmu vendor
    tPacket[field_no++] = 0;                      //[14]
    tPacket[field_no++] = 0;                      //[15]
    tPacket[field_no++] = 0;                      //[16]
    tPacket[field_no++] = 1;                      //[17]
    /*=== PMU DATA ==================================*/
    #endif
    return field_no;
}

uint8_t get_MSG_RESTART_ACK(void)
{
    return 1;
}

uint8_t get_MSG_UPGRADE_RESULT_ACK(void)
{
    bUpgradeReport = 0;
    //rstSYStoFile();
    return 1;
}


/* ####################################################################### */

/*
PMU장비에 새로 추가된 보안 경보 메시지(10가지)관련 포인트코드 자료 작성하여 보내드립니다.
그리고 OPMS 수신 포트(8001, 8002, 8003, 8004) 정보 부분도 간략하게 작성하였습니다. 참고하시기 바랍니다.
~ ps
SID부분은 문서상으로 작성 규칙이 저희 쪽 문서에도 없습니다. 그래서 테스트시에는 임시로 8자리(PMC번호(4자리) + 사업장번호(4자리))로 정해서 진행해야 할 것 같습니다.
*/

/*!
 \n==================================================================
 @brief uint16_t parseOpmsReqFrame(uint8_t * rPacket)
 \n==================================================================
 */
#if 0
uint16_t send_WRONG_MSG(void)
{
    uint16_t field_no = 0;
    
    tPacket[field_no++] = 'W';
    tPacket[field_no++] = 'R';
    tPacket[field_no++] = 'O';
    tPacket[field_no++] = 'N';
    tPacket[field_no++] = 'G';

    return field_no;
}
#endif

uint16_t parseOpmsReqFrame(uint8_t* tPacket, uint8_t* rPacket)
{
    PMU_HEADER_T pPMU_HEAD;
    uint16_t field_no = 0;

    pPMU_HEAD  = getOPMSheader(rPacket);

    #ifdef UDP_DEBUG
    printf("Service_Code:%u\r",pPMU_HEAD.ServiceCode);
    #endif

    switch(pPMU_HEAD.ServiceCode)
    {
        case MSG_REALTIME_REQ      : field_no = set_MSG_REALTIME_RSP(tPacket, rPacket);        break;
        case MSG_TIME_CONFIG_SEND  : field_no = set_MSG_TIME_CONFIG_ACK(tPacket, rPacket);     break;
        case MSG_CONFIG_SEND       : field_no = set_MSG_CONFIG_SEND_ACK(tPacket, rPacket);     break;
        case MSG_CONFIG_ALL_SEND   : field_no = set_MSG_CONFIG_ALL_SEND_ACK(tPacket, rPacket); break;
        case MSG_CONFIG_LIST_REQ   : field_no = set_MSG_CONFIG_LIST_ACK(tPacket, rPacket);     break;
        case MSG_NETWORK_CHECK_SEND: field_no = set_MSG_NETWORK_ACK(tPacket, rPacket);         break;
        case MSG_VERSION_REQ       : field_no = set_MSG_VERSION_ACK(tPacket, rPacket);         break;
        case MSG_RESET_REQ         : field_no = set_MSG_RESET_ACK(tPacket, rPacket);           break;
        case MSG_UPGRADE_SEND      : field_no = set_MSG_UPGRADE_ACK(tPacket, rPacket);         break;
        case MSG_ALARM_SEND_ACK    : get_MSG_ALARM_SEND_ACK();                                 break;
        case MSG_RESTART_ACK       : get_MSG_RESTART_ACK();                                    break;
        case MSG_UPGRADE_RESULT_ACK: get_MSG_UPGRADE_RESULT_ACK(); break;
        //default: field_no = send_WRONG_MSG(); break;
    }

    return field_no;
}

/* ####################################################################### */
int getIpAddr(char* address)
{
    int field_no = 0;

    int fd;
    struct ifreq ifr;
    struct sockaddr_in *aptr;

    fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        perror("sock failed\n");//printf("#sock failed#\n");
        return -1;
    }
    strncpy(ifr.ifr_name, "eth0", IFNAMSIZ);
    if (ioctl(fd, SIOCGIFADDR, &ifr) < 0) {
        perror("ioctl(2) failed\n");
        return -2;
    }

    aptr = (struct sockaddr_in *)&ifr.ifr_addr;
    inet_ntop(AF_INET, &aptr->sin_addr, address, ADDR_MAX);

    close(fd);

    return 1;
}

/*!
 \n******************************************************************
 @brief   main procedure
 \n******************************************************************
 */
static uint16_t dPRINTF(char* tPacket, const char *fmt, ...)
{
    va_list ap;
    char *str;
    char pSTR[500];
    uint16_t field_no = 0;

    va_start(ap, fmt);          /* make ap point to 1st unnamed arg */
    vsprintf(pSTR, fmt, ap );
    va_end(ap);                 /* clean up when done */

    str = &pSTR[0];

    while( *str != 0 )          /* Reached zero byte ? */
    {
        *tPacket = *str;        /* string copy */
        tPacket++;
        str++;                  /* Increment ptr */
        field_no++;             /* Increment byte counter */
    }

    return field_no;
}


/*
    ### send_MSG_ALARMS(900, bIP);KT-PMU#S_TCP_SYN_FLOOD      //TCP Syn Flooding
    ### send_MSG_ALARMS(901, bIP);KT-PMU#S_ARP_SPOOFING       //ARP Spoofing
    ### send_MSG_ALARMS(902, bIP);KT-PMU#S_ICMP_SMURF_ATTACK  //Smurf Attack
    ### send_MSG_ALARMS(903, bIP);KT-PMU#S_FRAGGLE_ATTACK     //Fraggle Attack
    ### send_MSG_ALARMS(904, bIP);KT-PMU#S_LAND_ATTACK        //Land Attack
    ### send_MSG_ALARMS(905, bIP);KT-PMU#S_PING_OF_DEATH      //Ping of Death
    ### send_MSG_ALARMS(906, bIP);KT-PMU#S_ILLEGAL_ARP        //Illegal ARP
    ### send_MSG_ALARMS(907, bIP);KT-PMU#S_ILLEGAL_MAC_SRC    //Illegal Source MAC
    ### send_MSG_ALARMS(908, bIP);KT-PMU#S_UDP_ECHO_LOOP      //UDP Echo Loop Attack
    ### send_MSG_ALARMS(909, bIP);KT_PMU#S_ILLEGAL_SRC_IP     //Illegal Source IP Attack  KT-PMU#S_IP SPOOFING
*/

int getValidAddr(char* ipstr, uint8_t* tIP)
{
    struct hostent *be;
    struct in_addr u32addr;
    
    if ((be=gethostbyname(ipstr)) == NULL) {  /* get the host info */
        tIP[0] = 0;
        tIP[1] = 0;
        tIP[2] = 0;
        tIP[3] = 0;
        return -1;
    }

    u32addr = *((struct in_addr *)be->h_addr);
    tIP[0] = (uint8_t)(u32addr.s_addr);
    tIP[1] = (uint8_t)(u32addr.s_addr>> 8);
    tIP[2] = (uint8_t)(u32addr.s_addr>>16);
    tIP[3] = (uint8_t)(u32addr.s_addr>>24);

    return 1;
}
                
uint16_t parseRsysFrame(char* rPacket, uint16_t* sec_nos, uint8_t * bIP)
{
    char *token;
    char *str = rPacket;
    char ipstr [ADDR_MAX]={0,};
    uint8_t sIP[6] = {0};
    uint16_t flag = 0;
    //uint16_t j = 0;

    if (str[0]=='\0'){ return 0; } // Is key buffer empty?
    //printf("#Rcvd# %s\n",str);

    token = strtok(str, " ");
    do
    {
        if      (strstr(token,"KT-PMU#S_TCP_SYN_FLOOD"      ) != NULL)    { *sec_nos = 900; flag = 1; }
      //else if (strstr(token,"KT-PMU#S_ARP_SPOOFING"       ) != NULL)    { *sec_nos = 901; flag = 1; }
        else if (strstr(token,"KT-PMU#S_ICMP_SMURF_ATTACK"  ) != NULL)    { *sec_nos = 902; flag = 1; }
        else if (strstr(token,"KT-PMU#S_FRAGGLE_ATTACK"     ) != NULL)    { *sec_nos = 903; flag = 1; }
      //else if (strstr(token,"KT-PMU#S_LAND_ATTACK"        ) != NULL)    { *sec_nos = 904; flag = 1; }
        else if (strstr(token,"KT-PMU#S_PING_OF_DEATH"      ) != NULL)    { *sec_nos = 905; flag = 1; }
        else if (strstr(token,"KT-PMU#S_ILLEGAL_ARP"        ) != NULL)    { *sec_nos = 906; flag = 1; }
        else if (strstr(token,"KT-PMU#S_ILLEGAL_MAC_SRC"    ) != NULL)    { *sec_nos = 907; flag = 1; }
        else if (strstr(token,"KT-PMU#S_UDP_ECHO_LOOP"      ) != NULL)    { *sec_nos = 908; flag = 1; }
        else if (strstr(token,"KT-PMU#S_ILLEGAL_SRC_IP"     ) != NULL)    { *sec_nos = 909; flag = 1; }
        else if (strstr(token,"martian"                     ) != NULL)    { *sec_nos = 904; flag = 2; }
        else if (strstr(token,"arpwatch"                    ) != NULL)    { flag = 3; }

        if (flag==1){
            if (strstr(token,"SRC=")!=NULL){
                strcpy(ipstr,&token[4]);
                if (getValidAddr(ipstr,bIP)>0) return FIW_ALM_FLAG;
                return 0;
            }
        }
        else if (flag==2){
            if (strstr(token,"from")!= NULL){
                token = strtok(NULL, ", ");
                if (token){
                    strcpy(ipstr,token);
                    if (getValidAddr(ipstr,bIP)>0){ 
                        if (sIP[0]==bIP[0] && sIP[1]==bIP[1] && sIP[2]==bIP[2] && sIP[3]==bIP[3]){
                            if ( *sec_nos==904 && bIP[0]!=127){
                                syslog(LOG_NOTICE, "KT-PMU#S_LAND_ATTACK from %u.%u.%u.%u", bIP[0], bIP[1], bIP[2], bIP[3]);
                                return FIW_ALM_FLAG;
                            }
                        }
                        else return 0;
                    }
                    else return 0;
                }
            }
            else if (strstr(token,"source")!= NULL){
                token = strtok(NULL, " ");
                if (token){
                    strcpy(ipstr,token);
                    if (getValidAddr(ipstr,sIP)< 1) return 0; 
                }
            }
        }
        else if (flag==3){
            if (strstr(token,"mismatch")!= NULL){
                //printf("#token: %s[%d]\n", token,strlen(token));
                token = strtok(NULL, ", ");
                if (token){
                    strcpy(ipstr,token);
                    if (getValidAddr(ipstr,bIP)>0){ 
                        *sec_nos = 901;
                        syslog(LOG_NOTICE, "KT-PMU#S_ARP_SPOOFING from %u.%u.%u.%u", bIP[0], bIP[1], bIP[2], bIP[3]);
                        return FIW_ALM_FLAG;
                    }
                    //else if (sec_code==906) syslog(LOG_NOTICE, "KT-PMU#S_ILLEGAL_ARP of %u.%u.%u.%u", bIP[0], bIP[1], bIP[2], bIP[3]);
                    //else if (sec_code==901) 
                }
            }
            //else if (strstr(token,"bogon")!= NULL){}
        }
    }
    while (token = strtok(NULL, " "));

    return flag;
}

uint32_t getValidACL(char* ipstr, uint8_t* tIP)
{
    struct hostent *be;
    struct in_addr u32addr;
    
    va_list ap;
    char *str;
    int fcnt = 0;
    str = ipstr;

    while( *str != 0 )          /* Reached zero byte ? */
    {
        if ( (*str != '.') && ( (*str < 0x30) || (*str > 0x39) ) ){ fcnt++; }          /* string copy */
        str++;                  /* Increment ptr */
    }
    
    if (fcnt) return 0;
    
    //printf("#ip#=%s\n",ipstr);
    #if 0
    if (strstr(ipstr,"none")){
    	tIP[0] = 0;
    	tIP[1] = 0;
    	tIP[2] = 0;
    	tIP[3] = 0;
    	return 0;
    }
    #endif
    
    {
    	if ((be=gethostbyname(ipstr)) == NULL) {  /* get the host info */
    	    tIP[0] = 0;
    	    tIP[1] = 0;
    	    tIP[2] = 0;
    	    tIP[3] = 0;
    	    return 0;
    	}
    	
    	u32addr = *((struct in_addr *)be->h_addr);
    	tIP[0] = (uint8_t)(u32addr.s_addr);
    	tIP[1] = (uint8_t)(u32addr.s_addr>> 8);
    	tIP[2] = (uint8_t)(u32addr.s_addr>>16);
    	tIP[3] = (uint8_t)(u32addr.s_addr>>24);
    }
    //printf("ip=%u.%u.%u.%u",tIP[0],tIP[1],tIP[2],tIP[3]);

    return u32addr.s_addr;
}

int parse_aclinfo(char* tPacket, char* rPacket, uint8_t set_rcv)
{
    char *token;
    char *str = rPacket;
    int field_no = 0;
    int flag = 0;
    int cnt = 0;
    int i;
    uint8_t tIP[6]={0};

    if (set_rcv){
        if (str[0]=='\0'){ return 0; } // Is key buffer empty?
        token = strtok(str, ",");
        
        if (strstr(token,"ACL=1")!=NULL){
        	//printf("niltest aclset 1 \n");
            token = strtok(NULL, "=");
            do
            {
                //if (strstr(token,"IP01")!=NULL){ token = strtok(NULL, ","); printf("%s\n",token); }
                if (strstr(token,"IP01")!=NULL){ token = strtok(NULL, ",");      p32ACL[0]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP02")!=NULL){ token = strtok(NULL, ","); p32ACL[1]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP03")!=NULL){ token = strtok(NULL, ","); p32ACL[2]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP04")!=NULL){ token = strtok(NULL, ","); p32ACL[3]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP05")!=NULL){ token = strtok(NULL, ","); p32ACL[4]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP06")!=NULL){ token = strtok(NULL, ","); p32ACL[5]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP07")!=NULL){ token = strtok(NULL, ","); p32ACL[6]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP08")!=NULL){ token = strtok(NULL, ","); p32ACL[7]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP09")!=NULL){ token = strtok(NULL, ","); p32ACL[8]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP10")!=NULL){ token = strtok(NULL, ","); p32ACL[9]  = getValidACL(token,tIP); }
                else if (strstr(token,"IP11")!=NULL){ token = strtok(NULL, ","); p32ACL[10] = getValidACL(token,tIP); }
                else if (strstr(token,"IP12")!=NULL){ token = strtok(NULL, ","); p32ACL[11] = getValidACL(token,tIP); }
                else if (strstr(token,"IP13")!=NULL){ token = strtok(NULL, ","); p32ACL[12] = getValidACL(token,tIP); }
                else if (strstr(token,"IP14")!=NULL){ token = strtok(NULL, ","); p32ACL[13] = getValidACL(token,tIP); }
                else if (strstr(token,"IP15")!=NULL){ token = strtok(NULL, ","); p32ACL[14] = getValidACL(token,tIP); }
                else if (strstr(token,"IP16")!=NULL){ token = strtok(NULL, ","); p32ACL[15] = getValidACL(token,tIP); }
                else if (strstr(token,"IP17")!=NULL){ token = strtok(NULL, ","); p32ACL[16] = getValidACL(token,tIP); }
                else if (strstr(token,"IP18")!=NULL){ token = strtok(NULL, ","); p32ACL[17] = getValidACL(token,tIP); }
                else if (strstr(token,"IP19")!=NULL){ token = strtok(NULL, ","); p32ACL[18] = getValidACL(token,tIP); }
                else if (strstr(token,"IP20")!=NULL){ token = strtok(NULL, ","); p32ACL[19] = getValidACL(token,tIP); }
            }
            while (token = strtok(NULL, "="));
            
            //printf("niltest aclset 2 \n");
            setACLtoFile();
            
        }
    }
    else{
        fetchACLfrFile();
        cnt = dPRINTF(&tPacket[field_no],"ACL=0");field_no += cnt;
        for (i=0; i<20; i++){
            if (p32ACL[i]==0uL){
                cnt = dPRINTF(&tPacket[field_no],",IP%02d=none",i+1); 
            }
            else{
                getACLaddr(p32ACL[i],tIP);
                cnt = dPRINTF(&tPacket[field_no],",IP%02d=%u.%u.%u.%u", i+1, tIP[0],tIP[1],tIP[2],tIP[3]);    
            }
            field_no += cnt;
        }
        cnt = dPRINTF(&tPacket[field_no],",END"); field_no += cnt;
    }   
    return field_no;
}

int parse_netinfo(char* tPacket, char* rPacket, uint8_t set_rcv)
{
    char *token;
    char *str = rPacket;
    int field_no = 0;
    int flag = 0;
    int cnt = 0;
    uint8_t isDPWchk = 0;
    uint8_t isSFTPchk = 0;
    char tmpDPW[MAX_STR_AUTH] = "power2018!@";

    if (set_rcv==1){
        if (str[0]=='\0'){ return 0; } // Is key buffer empty?
        token = strtok(str, ",");
        
        if (strstr(token,"NET=1")!=NULL){
            token = strtok(NULL, "=");
            do
            {
                if (strstr(token,"SID")!=NULL){ token = strtok(NULL, ",") ; pPMU_SID = atol(token); }
                if (strstr(token,"RID")!=NULL){ token = strtok(NULL, ",") ; strcpy(strRID,token); isSFTPchk = 1; }
                if (strstr(token,"RPW")!=NULL){ token = strtok(NULL, ",") ; strcpy(strRPW,token); isSFTPchk = 1; }
                if (strstr(token,"DPW")!=NULL){ token = strtok(NULL, ",") ; strcpy(tmpDPW,token); isDPWchk = 1; }
                if (strstr(token,"DIP")!=NULL){ token = strtok(NULL, ",") ; getValidACL(token,pmuAddx); }
                if (strstr(token,"DGW")!=NULL){ token = strtok(NULL, ",") ; getValidACL(token,pmuGate); }
                if (strstr(token,"DMK")!=NULL){ token = strtok(NULL, ",") ; getValidACL(token,pmuMask); }
            }
            while (token = strtok(NULL, "="));
            
            setNETtoFile();
            if (isSFTPchk) setSFTPtoFile();
            if (isDPWchk){
                if (strcmp(strDPW,tmpDPW)){
                    strcpy(strDPW,tmpDPW);
                    //printf("DPW=%s",strDPW);
                    setPWDtoFile();
                }
            }
            if (isSFTPchk || isDPWchk) setDEVtoFile();
        }
    }
    else if (set_rcv==2){
        if (str[0]=='\0'){ return 0; } // Is key buffer empty?
        token = strtok(str, ",");
        
        if (strstr(token,"NET=2")!=NULL){
            token = strtok(NULL, "=");
            do
            {
                if (strstr(token,"RID")!=NULL){ token = strtok(NULL, ",") ; strcpy(strRID,token); isSFTPchk = 1; }
                if (strstr(token,"RPW")!=NULL){ token = strtok(NULL, ",") ; strcpy(strRPW,token); isSFTPchk = 1; }
                if (strstr(token,"DPW")!=NULL){ token = strtok(NULL, ",") ; strcpy(strDPW,token); isDPWchk = 1; }
            }
            while (token = strtok(NULL, "="));
            
            if (isSFTPchk) setSFTPtoFile();
            if (isDPWchk){
                if (strcmp(strDPW,tmpDPW)){
                    strcpy(strDPW,tmpDPW);
                    //printf("DPW=%s",strDPW);
                    setPWDtoFile();
                }
            }
            if (isSFTPchk || isDPWchk) setDEVtoFile();
        }
    }
    else{
        fetchNETfrFile();
        fetchDEVfrFile();
        
        cnt = dPRINTF(&tPacket[field_no],"NET=0");field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",SID=%u",pPMU_SID); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",RID=%s",strRID); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",RPW=%s",strRPW); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DPW=%s",strDPW); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DIP=%u.%u.%u.%u",pmuAddx[0],pmuAddx[1],pmuAddx[2],pmuAddx[3]); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DGW=%u.%u.%u.%u",pmuGate[0],pmuGate[1],pmuGate[2],pmuGate[3]); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DMK=%u.%u.%u.%u",pmuMask[0],pmuMask[1],pmuMask[2],pmuMask[3]); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",END"); field_no += cnt;
    }
    
    return field_no;
}

uint16_t parse_setinfo(char* tPacket, char* rPacket, uint8_t set_rcv)
{
    char *token;
    char *str = rPacket;
    uint16_t field_no = 0;
    uint16_t cnt = 0;
    int flag = 0;
    
    if (set_rcv){
        if (str[0]=='\0'){ return 0; } // Is key buffer empty?
        token = strtok(str, ",");

        if (strstr(token,"SET=1")!=NULL){
            #if 1
            token = strtok(NULL, "=");
            do
            {
                //printf("Rcvd## %s\n",token);
                if (strstr(token,"ACV1H")!=NULL){ token = strtok(NULL, ","); AI_Conf[0].AIHiValue.f32 = atof(token); u8AnalogSTS[0] = PS_NORMAL; }
                if (strstr(token,"ACV1L")!=NULL){ token = strtok(NULL, ","); AI_Conf[0].AILoValue.f32 = atof(token); u8AnalogSTS[0] = PS_NORMAL; }
                if (strstr(token,"ACV1C")!=NULL){ token = strtok(NULL, ","); AI_Conf[0].AIEtcConf.u16 = atoi(token); u8AnalogSTS[0] = PS_NORMAL; }
                if (strstr(token,"ACV2H")!=NULL){ token = strtok(NULL, ","); AI_Conf[1].AIHiValue.f32 = atof(token); u8AnalogSTS[1] = PS_NORMAL; }
                if (strstr(token,"ACV2L")!=NULL){ token = strtok(NULL, ","); AI_Conf[1].AILoValue.f32 = atof(token); u8AnalogSTS[1] = PS_NORMAL; }
                if (strstr(token,"ACV2C")!=NULL){ token = strtok(NULL, ","); AI_Conf[1].AIEtcConf.u16 = atoi(token); u8AnalogSTS[1] = PS_NORMAL; }
                if (strstr(token,"DCV1H")!=NULL){ token = strtok(NULL, ","); AI_Conf[2].AIHiValue.f32 = atof(token); u8AnalogSTS[2] = PS_NORMAL; }
                if (strstr(token,"DCV1L")!=NULL){ token = strtok(NULL, ","); AI_Conf[2].AILoValue.f32 = atof(token); u8AnalogSTS[2] = PS_NORMAL; }
                if (strstr(token,"DCV1C")!=NULL){ token = strtok(NULL, ","); AI_Conf[2].AIEtcConf.u16 = atoi(token); u8AnalogSTS[2] = PS_NORMAL; }
                if (strstr(token,"DCV2H")!=NULL){ token = strtok(NULL, ","); AI_Conf[3].AIHiValue.f32 = atof(token); u8AnalogSTS[3] = PS_NORMAL; }
                if (strstr(token,"DCV2L")!=NULL){ token = strtok(NULL, ","); AI_Conf[3].AILoValue.f32 = atof(token); u8AnalogSTS[3] = PS_NORMAL; }
                if (strstr(token,"DCV2C")!=NULL){ token = strtok(NULL, ","); AI_Conf[3].AIEtcConf.u16 = atoi(token); u8AnalogSTS[3] = PS_NORMAL; }
                if (strstr(token,"DCV3H")!=NULL){ token = strtok(NULL, ","); AI_Conf[4].AIHiValue.f32 = atof(token); u8AnalogSTS[4] = PS_NORMAL; }
                if (strstr(token,"DCV3L")!=NULL){ token = strtok(NULL, ","); AI_Conf[4].AILoValue.f32 = atof(token); u8AnalogSTS[4] = PS_NORMAL; }
                if (strstr(token,"DCV3C")!=NULL){ token = strtok(NULL, ","); AI_Conf[4].AIEtcConf.u16 = atoi(token); u8AnalogSTS[4] = PS_NORMAL; }
                if (strstr(token,"TEMPH")!=NULL){ token = strtok(NULL, ","); AI_Conf[5].AIHiValue.f32 = atof(token); u8AnalogSTS[5] = PS_NORMAL; }
                if (strstr(token,"TEMPL")!=NULL){ token = strtok(NULL, ","); AI_Conf[5].AILoValue.f32 = atof(token); u8AnalogSTS[5] = PS_NORMAL; }
                if (strstr(token,"TEMPC")!=NULL){ token = strtok(NULL, ","); AI_Conf[5].AIEtcConf.u16 = atoi(token); u8AnalogSTS[5] = PS_NORMAL; }
                if (strstr(token,"DI1C") !=NULL){ token = strtok(NULL, ","); DI_Conf[0].DIEtcConf.u16 = atoi(token); }
                if (strstr(token,"DI2C") !=NULL){ token = strtok(NULL, ","); DI_Conf[1].DIEtcConf.u16 = atoi(token); }
                if (strstr(token,"DI3C") !=NULL){ token = strtok(NULL, ","); DI_Conf[2].DIEtcConf.u16 = atoi(token); }
                if (strstr(token,"DI4C") !=NULL){ token = strtok(NULL, ","); DI_Conf[3].DIEtcConf.u16 = atoi(token); }
                if (strstr(token,"DI5C") !=NULL){ token = strtok(NULL, ","); DI_Conf[4].DIEtcConf.u16 = atoi(token); }
                if (strstr(token,"DI6C") !=NULL){ token = strtok(NULL, ","); DI_Conf[5].DIEtcConf.u16 = atoi(token); }
                if (strstr(token,"END")  !=NULL){ break; }
            }
            while (token = strtok(NULL, "="));
            
            setCNFtoFile();
            
            //setTest();
            #endif
        }
    }
    else{
        fetchCNFfrFile();
        
        cnt = dPRINTF(&tPacket[field_no],"SET=0");field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",ACV1H=%.1f",AI_Conf[0].AIHiValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",ACV1L=%.1f",AI_Conf[0].AILoValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",ACV1C=%u",AI_Conf[0].AIEtcConf.u16); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",ACV2H=%.1f",AI_Conf[1].AIHiValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",ACV2L=%.1f",AI_Conf[1].AILoValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",ACV2C=%u",AI_Conf[1].AIEtcConf.u16); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",DCV1H=%.1f",AI_Conf[2].AIHiValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DCV1L=%.1f",AI_Conf[2].AILoValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DCV1C=%u",AI_Conf[2].AIEtcConf.u16); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",DCV2H=%.1f",AI_Conf[3].AIHiValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DCV2L=%.1f",AI_Conf[3].AILoValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DCV2C=%u",AI_Conf[3].AIEtcConf.u16); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",DCV3H=%.1f",AI_Conf[4].AIHiValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DCV3L=%.1f",AI_Conf[4].AILoValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DCV3C=%u",AI_Conf[4].AIEtcConf.u16); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",TEMPH=%.1f",AI_Conf[5].AIHiValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",TEMPL=%.1f",AI_Conf[5].AILoValue.f32); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",TEMPC=%u",AI_Conf[5].AIEtcConf.u16); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",DI1C=%u",DI_Conf[0].DIEtcConf.u16); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DI2C=%u",DI_Conf[1].DIEtcConf.u16); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DI3C=%u",DI_Conf[2].DIEtcConf.u16); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DI4C=%u",DI_Conf[3].DIEtcConf.u16); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DI5C=%u",DI_Conf[4].DIEtcConf.u16); field_no += cnt;
        cnt = dPRINTF(&tPacket[field_no],",DI6C=%u",DI_Conf[5].DIEtcConf.u16); field_no += cnt;
        
        cnt = dPRINTF(&tPacket[field_no],",END"); field_no += cnt;
    }

    return field_no;
}

uint16_t parse_cmdinfo(char* tPacket, char* rPacket)
{
    uint16_t field_no = 0;
    uint16_t cnt = 0;

    cnt = dPRINTF(&tPacket[field_no],"CMD=0");field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",ACV1=%.1f",f32AnalogVal[0].f32); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",AI1=%u",u8AnalogSTS[0]); field_no += cnt;
    
    cnt = dPRINTF(&tPacket[field_no],",ACV2=%.1f",f32AnalogVal[1].f32); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",AI2=%u",u8AnalogSTS[1]); field_no += cnt;
    
    cnt = dPRINTF(&tPacket[field_no],",DCV0=%.1f",f32AnalogVal[6].f32); field_no += cnt;
    
    cnt = dPRINTF(&tPacket[field_no],",DCV1=%.1f",f32AnalogVal[2].f32); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",AI3=%u",u8AnalogSTS[2]); field_no += cnt;
    
    cnt = dPRINTF(&tPacket[field_no],",DCV2=%.1f",f32AnalogVal[3].f32); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",AI4=%u",u8AnalogSTS[3]); field_no += cnt;
    
    cnt = dPRINTF(&tPacket[field_no],",DCV3=%.1f",f32AnalogVal[4].f32); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",AI5=%u",u8AnalogSTS[4]); field_no += cnt;
    
    cnt = dPRINTF(&tPacket[field_no],",TEMP=%.1f",f32AnalogVal[5].f32); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",AI6=%u",u8AnalogSTS[5]); field_no += cnt;
    
    cnt = dPRINTF(&tPacket[field_no],",DI1=%u",u8DigitalSTS[0]); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",DI2=%u",u8DigitalSTS[1]); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",DI3=%u",u8DigitalSTS[2]); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",DI4=%u",u8DigitalSTS[3]); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",DI5=%u",u8DigitalSTS[4]); field_no += cnt;
    cnt = dPRINTF(&tPacket[field_no],",DI6=%u",u8DigitalSTS[5]); field_no += cnt;

    cnt = dPRINTF(&tPacket[field_no],",END"); field_no += cnt;
    
    return field_no;
}

uint16_t parseConfMsg(uint8_t* tPacket, uint8_t* rPacket)
{
    int i;
    char *token;
    char *str = rPacket;
    uint16_t field_no = 0;
    
    if (str[0]=='\0'){ return 0; } // Is key buffer empty?
        
    token = strtok(str, " ");
    if      (strstr(token,"SET=0")!=NULL){ field_no = parse_setinfo(tPacket,rPacket,0); }
    else if (strstr(token,"SET=1")!=NULL){ field_no = parse_setinfo(tPacket,rPacket,1); }
    else if (strstr(token,"NET=0")!=NULL){ field_no = parse_netinfo(tPacket,rPacket,0); }
    else if (strstr(token,"NET=1")!=NULL){ field_no = parse_netinfo(tPacket,rPacket,1); }
    else if (strstr(token,"NET=2")!=NULL){ field_no = parse_netinfo(tPacket,rPacket,2); }
    else if (strstr(token,"CMD=0")!=NULL){ field_no = parse_cmdinfo(tPacket,rPacket); }
    else if (strstr(token,"ACL=0")!=NULL){ field_no = parse_aclinfo(tPacket,rPacket,0); }
    else if (strstr(token,"ACL=1")!=NULL){ field_no = parse_aclinfo(tPacket,rPacket,1); }
    else if (strstr(token,"NIL=18309")!=NULL){ field_no = parse_reset(tPacket,rPacket,1); }
    	
    //if (strstr(token,"CMD=0")!=NULL){ for (i=0; i<153; i++) tPacket[i] = cTXD[i]; field_no = 153; }
    return field_no;
}

/*!
 \n==================================================================
 @brief OPMS UDP Server Start
 \n==================================================================
 */
int OPMS_Rprt_Send(uint8_t* tPacket, uint16_t field_no, uint8_t debug)
{
    int sockf;
    struct hostent *oe;
    struct sockaddr_in opmsAddr;
    int i;
    int send_cnt = 0;

    char opms_strx[] = OPMS_STRX;
    //uint32_t u32IP; u32IP = setP8Addr(pmuOpms);
        
    if ((oe=gethostbyname(opms_strx)) == NULL) {  /* get the host info */
        if (debug) printf("gethostbyname\n");
        return -1;
    }
    
    if ((sockf = socket(AF_INET, SOCK_DGRAM, 0)) == -1)
    {
        if (debug) printf("Socket Creation Failed\n");
        return 0;
    }
    
    memset(&opmsAddr,0,sizeof(opmsAddr));
    opmsAddr.sin_family = AF_INET;
    opmsAddr.sin_port = htons(PMU_RPRT_PORT);
    //opmsAddr.sin_addr = *((struct in_addr *)oe->h_addr);
    opmsAddr.sin_addr.s_addr = setP8Addr(pmuOpms);

    send_cnt = sendto(sockf, tPacket, field_no, 0, (struct sockaddr*)&opmsAddr, sizeof(opmsAddr));
    
    if (debug){
        uint8_t tIP[6]={0}; getP8Addr(opmsAddr.sin_addr, tIP);
        printf("#RPT send[%d]to %u.%u.%u.%u[%d port]:", send_cnt, tIP[0],tIP[1],tIP[2],tIP[3], htons(opmsAddr.sin_port));
        for (i=0; i<send_cnt;i++){ printf(":%.2X",tPacket[i]); }
        printf("\n");    
    }
    return 1; 
}

int RSYS_Recv_Init(int* sockf, uint8_t debug)
{
    struct hostent *se;
    struct sockaddr_in servAddr;
    
    char host_strx[] = "127.0.0.1";
    
    if ((se=gethostbyname(host_strx)) == NULL) {  /* get the host info */
        if (debug) printf("gethostbyname\n");
        return -1;
    }
    
    if (((*sockf) = socket(AF_INET, SOCK_DGRAM, 0)) == -1){
        if (debug) printf("Socket Creation Failed\n");
        return 0;
    } 
    memset(&servAddr, 0, sizeof(servAddr));
    servAddr.sin_family = AF_INET;
    servAddr.sin_port = htons(PMU_RSYS_PORT);
    servAddr.sin_addr = *((struct in_addr *)se->h_addr);
    //servAddr.sin_addr.s_addr = 0x0100007F;
    //uint8_t tIP[6]={0}; getP8Addr(servAddr.sin_addr, tIP); printf("addr=%u.%u.%u.%u",tIP[0],tIP[1],tIP[2],tIP[3]);
    if (bind((*sockf),(struct sockaddr *)&servAddr, sizeof(struct sockaddr)) == -1)
    {
        if (debug) printf("Bind Error\n");
        return 0;
    }
    return 1;
}
    
int CONF_Recv_Init(int* sockf, uint8_t debug)
{    
    struct hostent *se;
    struct sockaddr_in servAddr;
    
    char host_strx[ADDR_MAX] = { 0, };
            
    if (getIpAddr(host_strx)<0){
        return -1;
    }
    if ((se=gethostbyname(host_strx)) == NULL) {  /* get the host info */
        if (debug) printf("gethostbyname\n");
        return -1;
    }
    if (((*sockf) = socket(AF_INET, SOCK_DGRAM, 0)) == -1)
    {
        if (debug) printf("Socket Creation Failed\n");
        return 0;
    }
    memset(&servAddr, 0, sizeof(servAddr));
    servAddr.sin_family = AF_INET;
    servAddr.sin_port = htons(PMU_CONF_PORT);
    servAddr.sin_addr = *((struct in_addr *)se->h_addr);

    if (bind((*sockf),(struct sockaddr *)&servAddr, sizeof(struct sockaddr)) == -1)
    {
        if (debug) printf("Bind Error\n");
        return 0;
    }
    
    return 1;
}

int OPMS_Recv_Init(int* sockf, uint8_t debug)
{
    struct hostent *se;
    struct sockaddr_in servAddr;
    
    char host_strx[ADDR_MAX] = { 0, };
            
    if (getIpAddr(host_strx)<0){
        return -1;
    }
    if ((se=gethostbyname(host_strx)) == NULL) {  /* get the host info */
        if (debug) printf("gethostbyname\n");
        return -1;
    }
    if (((*sockf) = socket(AF_INET, SOCK_DGRAM, 0)) == -1)
    {
        if (debug) printf("Socket Creation Failed\n");
        return 0;
    }
    memset(&servAddr, 0, sizeof(servAddr));
    servAddr.sin_family = AF_INET;
    servAddr.sin_port = htons(PMU_RECV_PORT);
    servAddr.sin_addr = *((struct in_addr *)se->h_addr);
    getP8Addr(servAddr.sin_addr, pmuAddr);
    
    if (bind((*sockf),(struct sockaddr *)&servAddr, sizeof(struct sockaddr)) == -1)
    {
        if (debug) printf("Bind Error\n");
        return 0;
    }

    return 1;
}
    
int OPMS_Recv_Proc(int* sockf, uint8_t debug)
{
    struct sockaddr_in clntAddr;
    int i;
    char rPacket[MAX_OPMS_RX_SIZE];
    char tPacket[MAX_OPMS_TX_SIZE];
    
    int clnt_len = 0;
    int recv_len = 0;
    int send_cnt = 0;
    uint16_t field_no = 0;
    unsigned char command[100];
    
    clnt_len = sizeof(clntAddr);
    if ((recv_len = recvfrom((*sockf), rPacket, MAX_OPMS_RX_SIZE, MSG_DONTWAIT, (struct sockaddr *)&clntAddr, &clnt_len))==-1){
        return 0;
    }
    
    if (recv_len > 0) {

        //getRawData();
        
        rPacket[recv_len] = '\0';
        field_no = parseOpmsReqFrame(tPacket,rPacket);
        if (debug){
            printf("Rcvd Message[%d]:",recv_len);
            for (i=0; i<recv_len;i++){
                printf(":%.2X", rPacket[i]);
            }
            printf("\n");
        }
        clntAddr.sin_port = htons(OPMS_RSP_PORT);
    
        if (field_no) {
            send_cnt = sendto((*sockf), tPacket, field_no, 0,(struct sockaddr*)&clntAddr, sizeof(clntAddr));
            if (debug){
                uint8_t tIP[6]={0}; getP8Addr(clntAddr.sin_addr, tIP);
                printf("Send[%d]to %u.%u.%u.%u[%d port]:", send_cnt, tIP[0],tIP[1],tIP[2],tIP[3], htons(clntAddr.sin_port));//
                for (i=0; i<field_no;i++){
                    printf(":%.2X", tPacket[i]);
                }
                printf("\n");
                
            }
            //return 1;
        }
        //recv_len = 0;
    }
    
    if (bUpgradeRequest==1){
    	 bUpgradeRequest = 0;
    	 setSYStoFile();
    	 sprintf((char*)command,"reboot"); system(command);
    }
    
    	// UPGRADE()....

    return 1;
} 

int CONF_Recv_Proc(int * sockf, uint8_t debug)
{
    struct sockaddr_in clntAddr;
    char rPacket[MAX_CONF_RECV_SIZE];
    char tPacket[MAX_CONF_RECV_SIZE];
    
    uint16_t i;
    uint16_t field_no = 0;
    
    int clnt_len = 0;
    int recv_len = 0;
    int send_cnt = 0;

    clnt_len = sizeof(clntAddr);
    if ((recv_len = recvfrom((*sockf), rPacket, MAX_CONF_RECV_SIZE, MSG_DONTWAIT, (struct sockaddr *)&clntAddr, &clnt_len))==-1){
        return 0;
    }

    if (recv_len > 0) {
        rPacket[recv_len] = '\0';
        if (debug){
            printf("Rcvd Message[%d]:",recv_len);
            for (i=0; i<recv_len;i++){
                printf("%c", rPacket[i]);
                //printf(":%.2X", rPacket[i]);
            }
            printf("\n");
        }

        field_no = parseConfMsg(tPacket, rPacket);
        if (field_no) {
            send_cnt = sendto((*sockf), (uint8_t*)tPacket, field_no, 0, (struct sockaddr*)&clntAddr, sizeof(clntAddr));
            if (debug){
                printf("Send[%d]to %d port:", send_cnt, htons(clntAddr.sin_port));
                for (i=0; i<send_cnt;i++){
                //for (i=0; i<field_no;i++){
                    printf("%c", tPacket[i]);
                }
                printf("\n");
            }
            return 1;
        }
        //recv_len = 0;
    }
    
    return 0;
}

int RSYS_Recv_Proc(int * sockf, uint8_t debug)
{
    struct sockaddr_in clntAddr;
    int i;
    char rPacket[MAX_RSYS_RX_SIZE];
    char tPacket[MAX_RSYS_TX_SIZE];
    uint8_t bIP[6]={0};
    uint16_t sec_code = 0;
    uint8_t sameFlag = 0;
    
    int clnt_len = 0;
    int recv_len = 0;
    uint16_t field_no = 0;

    clnt_len = sizeof(clntAddr);
    if ((recv_len = recvfrom((*sockf), rPacket, MAX_RSYS_RX_SIZE, MSG_DONTWAIT, (struct sockaddr *)&clntAddr, &clnt_len))==-1){
        return 0;
    }

    if (recv_len > 0) {
        rPacket[recv_len] = '\0';
        if (debug){
            printf("Rcvd Message[%d]:%s\n",recv_len,rPacket);
        }

        if (parseRsysFrame(rPacket, &sec_code, bIP) == FIW_ALM_FLAG){
            field_no = set_MSG_ALARM_FIW(tPacket, sec_code, bIP);
            sameFlag = 0;
            if (field_no){
                #if 1
                switch(sec_code){
                    case 900: sameFlag = checkSameAttackerIP(bIP,p32SEC900,&u16SameIpCnt[0]); break;
                    case 901: sameFlag = checkSameAttackerIP(bIP,p32SEC901,&u16SameIpCnt[1]); break;
                    case 902: sameFlag = checkSameAttackerIP(bIP,p32SEC902,&u16SameIpCnt[2]); break;
                    case 903: sameFlag = checkSameAttackerIP(bIP,p32SEC903,&u16SameIpCnt[3]); break;
                    case 904: sameFlag = checkSameAttackerIP(bIP,p32SEC904,&u16SameIpCnt[4]); break;
                    case 905: sameFlag = checkSameAttackerIP(bIP,p32SEC905,&u16SameIpCnt[5]); break;
                    case 906: sameFlag = checkSameAttackerIP(bIP,p32SEC906,&u16SameIpCnt[6]); break;
                    case 907: sameFlag = checkSameAttackerIP(bIP,p32SEC907,&u16SameIpCnt[7]); break;
                    case 908: sameFlag = checkSameAttackerIP(bIP,p32SEC908,&u16SameIpCnt[8]); break;
                    case 909: sameFlag = checkSameAttackerIP(bIP,p32SEC909,&u16SameIpCnt[9]); break;
                }
                #else
                sameFlag = 1;
                #endif
                if (sameFlag){
                	if (debug) OPMS_Rprt_Send(tPacket, field_no, 1);
                    else OPMS_Rprt_Send(tPacket, field_no, 0);
                    //sendTcpSecuEventPacket(sec_code, bIP);
                    //if (debug){ printf("#SEC: %u.%u.%u.%u\n", bIP[0], bIP[1], bIP[2], bIP[3]); }
                }
            }
        }
    }
    return 0;
}

int STD_ALM_AI_Proc(uint8_t debug)
{
    uint8_t ecnt;
    uint16_t i;
    uint16_t point_code;
    uint16_t field_no = 0;
    char tPacket[MAX_RPRT_TX_SIZE];
    
    for (i=0; i<6; i++){
        point_code = 101+i;
        ecnt = 0;

        if ((u8AnalogPRV[i]==PS_NORMAL) && (u8AnalogSTS[i]!=PS_NORMAL)){
            switch(point_code){
                case 101: syslog(LOG_NOTICE, "KT-PMU#R_AC1 Volt Alarm Occured"); ecnt = 1; break;
                case 102: syslog(LOG_NOTICE, "KT-PMU#R_AC2 Volt Alarm Occured"); ecnt = 1; break;
                case 103: syslog(LOG_NOTICE, "KT-PMU#R_DC1 Volt Alarm Occured"); ecnt = 1; break;
                case 104: syslog(LOG_NOTICE, "KT-PMU#R_DC2 Volt Alarm Occured"); ecnt = 1; break;
                case 105: syslog(LOG_NOTICE, "KT-PMU#R_DC3 Volt Alarm Occured"); ecnt = 1; break;
                case 106: syslog(LOG_NOTICE, "KT-PMU#R_TEMP Alarm Occured"    ); ecnt = 1; break;
                default: break;
            }
        }
        else if ((u8AnalogPRV[i]!=PS_NORMAL) && (u8AnalogSTS[i]==PS_NORMAL)){
            switch(point_code){
                case 101: syslog(LOG_NOTICE, "KT-PMU#R_AC1 Volt Alarm Released"); ecnt = 1; break;
                case 102: syslog(LOG_NOTICE, "KT-PMU#R_AC2 Volt Alarm Released"); ecnt = 1; break;
                case 103: syslog(LOG_NOTICE, "KT-PMU#R_DC1 Volt Alarm Released"); ecnt = 1; break;
                case 104: syslog(LOG_NOTICE, "KT-PMU#R_DC2 Volt Alarm Released"); ecnt = 1; break;
                case 105: syslog(LOG_NOTICE, "KT-PMU#R_DC3 Volt Alarm Released"); ecnt = 1; break;
                case 106: syslog(LOG_NOTICE, "KT-PMU#R_TEMP Alarm Released"    ); ecnt = 1; break;
                default: break;
            }
        }
        u8AnalogPRV[i] = u8AnalogSTS[i];
        
        if (ecnt){
            field_no = set_MSG_ALARM_STD(tPacket, point_code, f32AnalogVal[i].f32, u8AnalogSTS[i]);
            if (field_no){
                OPMS_Rprt_Send(tPacket, field_no, debug);
                //sendTcpAnalogEventPacket(point_code, f32AnalogVal[i], u8AnalogSTS[i]);
            }
        }
    }
    
    return 1;
}

int STD_ALM_DI_Proc(uint8_t debug)
{
    uint8_t ecnt;
    uint16_t i;
    uint16_t point_code;
    uint16_t field_no = 0;
    char tPacket[MAX_RPRT_TX_SIZE];
    
    for (i=0; i<6; i++){
        point_code = 201+i;
        ecnt = 0;
        if ((u8DigitalPRV[i]==PS_NORMAL) && (u8DigitalSTS[i]!=PS_NORMAL)){
            syslog(LOG_NOTICE, "KT-PMU#R_DI%d Alarm Occured",i+1); ecnt = 1;
        }
        else if ((u8DigitalPRV[i]!=PS_NORMAL) && (u8DigitalSTS[i]==PS_NORMAL)){
            syslog(LOG_NOTICE, "KT-PMU#R_DI%d Alarm Realsed",i+1); ecnt = 1;
        }
        
        if (ecnt){
            field_no = set_MSG_ALARM_STD(tPacket, point_code, (float)u8DigitalSTS[i], u8DigitalSTS[i]);
            if (field_no){
                OPMS_Rprt_Send(tPacket, field_no, debug);
                //sendTcpDigitalEventPacket(point_code, u8DigitalSTS[i]);
            }
        }
        u8DigitalPRV[i] = u8DigitalSTS[i];
    }
    return 1;
}

/*!
 \n==================================================================
 @brief main()
 \n==================================================================
 */
int setIPtables(void)
{
	FILE * fp;
    int i;
    uint8_t tIP[6]={0};
    
    //int test_cnt = 0;
    //printf("niltest iptables %d\n",test_cnt++);
    
    fp = fopen("/home/seopms/pmu/iptables.sh", "w");
    if (fp == NULL)
    {
    	//printf("niltest iptables ###\n");
        return 0;
    }
    
	//printf("niltest iptables %d\n",test_cnt++);
	fprintf(fp, "#!/bin/bash\n");
	fprintf(fp, "EXTERNAL_IF=%ceth0%c\n",0x22,0x22);
	fprintf(fp, "NOG_LEVEL=%c4%c\n",0x22,0x22);
	fprintf(fp, "LOG_TARGET=%cLOG%c\n",0x22,0x22);
	fprintf(fp, "LEXT=%c--log-tcp-options --log-ip-options%c\n",0x22,0x22);
	fprintf(fp, "LOCALNET_MASK=`ifconfig ${EXTERNAL_IF} | grep 'inet ' | awk '{print $6}'`\n");
	fprintf(fp, "LOCALNET_ADDR=`ifconfig ${EXTERNAL_IF} | grep 'inet ' | awk '{print $2}'`\n");
	fprintf(fp, "LOCALNET_HW=`ifconfig ${EXTERNAL_IF} | grep 'ether ' | awk '{print $2}'`\n");
	fprintf(fp, "LOCALNET_GW=`ip route | grep 'via ' | awk '{print $3}'`\n");
	fprintf(fp, "LOCALNET_MTU=`ifconfig ${EXTERNAL_IF} | grep 'mtu ' | awk '{print $4}'`\n");
	//printf("niltest iptables %d\n",test_cnt++);
	fprintf(fp, "sysctl -w net.ipv4.tcp_syncookies=1\n");
	fprintf(fp, "sysctl -w net.ipv4.conf.all.log_martians=1\n");
	fprintf(fp, "sysctl -w net.ipv4.conf.eth0.log_martians=1\n");

	fprintf(fp, "arptables -F\n");
	fprintf(fp, "arptables -X\n");
	fprintf(fp, "arptables -Z\n");

	fprintf(fp, "iptables -F\n");
	fprintf(fp, "iptables -X\n");
	fprintf(fp, "iptables -Z\n");

	for (i=0; i<20; i++){
		if (p32ACL[i]!=0uL){
			getACLaddr(p32ACL[i],tIP);
            fprintf(fp, "iptables -A INPUT -p tcp --dport 22 -s %u.%u.%u.%u -j ACCEPT\n", tIP[0],tIP[1],tIP[2],tIP[3]);
            fprintf(fp, "iptables -A INPUT -p tcp --dport 23 -s %u.%u.%u.%u -j ACCEPT\n", tIP[0],tIP[1],tIP[2],tIP[3]);
            //usleep(10);
        }
    }
    //printf("niltest iptables %d\n",test_cnt++);
    fprintf(fp, "iptables -A INPUT -p tcp --dport 22 -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --dport 23 -j DROP\n");

	fprintf(fp, "arptables -N ILLEGAL_ARP\n");
	fprintf(fp, "arptables -A INPUT -i ${EXTERNAL_IF} --dst-mac ff:ff:ff:ff:ff:ff -j ILLEGAL_ARP\n");
	fprintf(fp, "arptables -A ILLEGAL_ARP -j DROP\n");

	fprintf(fp, "iptables -N IPTABLES_224_0_0_251\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -d 224.0.0.251 -j IPTABLES_224_0_0_251\n");
	fprintf(fp, "iptables -A IPTABLES_224_0_0_251 -j DROP\n");

	fprintf(fp, "iptables -N ILLEGAL_SRC_IP\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -s 10.0.0.0/8 -j ILLEGAL_SRC_IP\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -s 127.0.0.0/8 -j ILLEGAL_SRC_IP\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -s 192.168.0.0/16 -j ILLEGAL_SRC_IP\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -s 172.16.0.0/12 -j ILLEGAL_SRC_IP\n");
	fprintf(fp, "iptables -A ILLEGAL_SRC_IP -j LOG --log-level ${NOG_LEVEL} --log-prefix 'KT-PMU#S_ILLEGAL_SRC_IP '\n");
	fprintf(fp, "iptables -A ILLEGAL_SRC_IP -j DROP\n");

	fprintf(fp, "iptables -N ICMP_SMURF_ATTACK\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -p icmp -d ${LOCALNET_MASK} -j ICMP_SMURF_ATTACK\n");
	fprintf(fp, "iptables -A ICMP_SMURF_ATTACK -j LOG --log-level ${NOG_LEVEL} --log-prefix 'KT-PMU#S_ICMP_SMURF_ATTACK '\n");
	fprintf(fp, "iptables -A ICMP_SMURF_ATTACK -j DROP\n");

	fprintf(fp, "iptables -N ILLEGAL_MAC_SRC\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -m mac --mac-source 00:00:00:00:00:00 -j ILLEGAL_MAC_SRC\n");
	fprintf(fp, "iptables -A ILLEGAL_MAC_SRC -j LOG --log-level ${NOG_LEVEL} --log-prefix 'KT-PMU#S_ILLEGAL_MAC_SRC '\n");
	fprintf(fp, "iptables -A ILLEGAL_MAC_SRC -j DROP\n");

	fprintf(fp, "iptables -N PING_OF_DEATH\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -p icmp -j PING_OF_DEATH\n");
	fprintf(fp, "iptables -A PING_OF_DEATH -m length --length 1:${LOCALNET_MTU} -j ACCEPT\n");
	fprintf(fp, "iptables -A PING_OF_DEATH -j LOG --log-level ${NOG_LEVEL} --log-prefix 'KT-PMU#S_PING_OF_DEATH '\n");
	fprintf(fp, "iptables -A PING_OF_DEATH -m length --length ${LOCALNET_MTU}:65535 -j DROP\n");

	fprintf(fp, "iptables -N PING_FRAGMENTATION\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -p icmp --fragment -j PING_FRAGMENTATION\n");
	fprintf(fp, "iptables -A PING_FRAGMENTATION -j LOG --log-level ${NOG_LEVEL} --log-ip-options --log-prefix 'KT-PMU#S_PING_OF_DEATH '\n");
	fprintf(fp, "iptables -A PING_FRAGMENTATION -j DROP\n");

	fprintf(fp, "iptables -N UDP_ECHO_LOOP\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF}  -p udp --dport 7 --sport 7 -j UDP_ECHO_LOOP\n");
	fprintf(fp, "iptables -A UDP_ECHO_LOOP -j LOG --log-level ${NOG_LEVEL} --log-prefix 'KT-PMU#S_UDP_ECHO_LOOP '\n");
	fprintf(fp, "iptables -A UDP_ECHO_LOOP -j DROP\n");

	fprintf(fp, "iptables -N FRAGGLE_ATTACK\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -p udp -d ${LOCALNET_MASK} -m multiport --dport 7,19 -j FRAGGLE_ATTACK\n");
	fprintf(fp, "iptables -A FRAGGLE_ATTACK -j LOG --log-level ${NOG_LEVEL} --log-prefix 'KT-PMU#S_FRAGGLE_ATTACK '\n");
	fprintf(fp, "iptables -A FRAGGLE_ATTACK -j DROP\n");

	fprintf(fp, "iptables -N SYN_FLOOD\n");
	fprintf(fp, "iptables -A INPUT -i ${EXTERNAL_IF} -p tcp --syn -j SYN_FLOOD\n");
	fprintf(fp, "iptables -A SYN_FLOOD -m limit --limit 1/s --limit-burst 3 -j RETURN\n");
	fprintf(fp, "iptables -A SYN_FLOOD -m limit --limit 1/s --limit-burst 500 -j LOG --log-level ${NOG_LEVEL} --log-ip-options --log-prefix 'KT-PMU#S_TCP_SYN_FLOOD '\n");
	fprintf(fp, "iptables -A SYN_FLOOD -j DROP\n");

	fprintf(fp, "iptables -A INPUT -m state --state ESTABLISHED,RELATED -j ACCEPT\n");
	fprintf(fp, "iptables -A INPUT -p tcp ! --syn -m state --state NEW -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ACK,FIN FIN -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL NONE -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL PSH,FIN -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL URG,PSH,FIN -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL SYN,ACK,FIN -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL SYN,FIN,PSH -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL SYN,FIN,RST -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL SYN,FIN,RST,PSH -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL SYN,FIN,ACK,RST -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ALL SYN,ACK,FIN,RST,PSH -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags FIN,RST FIN,RST -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags SYN,FIN SYN,FIN -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ACK,PSH PSH -j DROP\n");
	fprintf(fp, "iptables -A INPUT -p tcp --tcp-flags ACK,URG URG -j DROP\n");
	
	fprintf(fp, "\n");
	
	fclose(fp);
		
    //printf("niltest iptables.sh\n");
		
	return 1;
	
}

int setACLtoFile(void)
{
    FILE * fp;
    int i;
    uint8_t tIP[6]={0};
    
    //printf("niltest acllist 1\n");
    fp = fopen("/home/seopms/pmu/acllist.pmu", "w");
    if (fp == NULL)
    {
        //printf("Error opening file!\n");
        return 0;//exit(1);
    }
    
    //printf("niltest acllist 2\n");
    
    /* print some text */
    //const char *text = "Write this to the file";
    fprintf(fp, "#acllist.pmu\r\n");
    
    #if 1
    for (i=0; i<20; i++){
        getACLaddr(p32ACL[i],tIP);
        fprintf(fp,"IP%02d=%u.%u.%u.%u\r\n",i+1,tIP[0],tIP[1],tIP[2],tIP[3]);
    }
    #endif
    
    fprintf(fp, "\r\n");
        
    fclose(fp);
    
    #if 0
    bIptableFlag  = 1;
    #else
    if (setIPtables()) filterInit();
    #endif
    
    return 1;
    
}

int fetchACLfrFile(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    uint8_t tIP[6]={0};
    
    char ipstr [ADDR_MAX]={0,};
    
    fp = fopen("/home/seopms/pmu/acllist.pmu", "r");
    if (fp == NULL){ 
        for (i=0; i<20; i++){
            p32ACL[i] = 0; 
        }
        setACLtoFile();
        return 0; 
    }

    while ((read = getline(&line, &len, fp)) != -1) {
        for (i=0; i<read; i++){
            if (line[i]=='\r' || line[i]=='\n') line[i] = '\0';
        }
        if      (strstr(line,"IP01=")!=NULL){  p32ACL[0]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP02=")!=NULL){  p32ACL[1]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP03=")!=NULL){  p32ACL[2]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP04=")!=NULL){  p32ACL[3]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP05=")!=NULL){  p32ACL[4]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP06=")!=NULL){  p32ACL[5]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP07=")!=NULL){  p32ACL[6]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP08=")!=NULL){  p32ACL[7]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP09=")!=NULL){  p32ACL[8]  = getValidACL(&line[5],tIP); }            
        else if (strstr(line,"IP10=")!=NULL){  p32ACL[9]  = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP11=")!=NULL){  p32ACL[10] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP12=")!=NULL){  p32ACL[11] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP13=")!=NULL){  p32ACL[12] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP14=")!=NULL){  p32ACL[13] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP15=")!=NULL){  p32ACL[14] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP16=")!=NULL){  p32ACL[15] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP17=")!=NULL){  p32ACL[16] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP18=")!=NULL){  p32ACL[17] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP19=")!=NULL){  p32ACL[18] = getValidACL(&line[5],tIP); }
        else if (strstr(line,"IP20=")!=NULL){  p32ACL[19] = getValidACL(&line[5],tIP); }
    }
        
    #if 0
    for (i=0; i<20; i++){
        getACLaddr(p32ACL[i],tIP);
        printf("IP%02d=%u.%u.%u.%u\n",i+1,tIP[0],tIP[1],tIP[2],tIP[3]);
    }
    #endif

    fclose(fp);
    
    return 1;
}

int setCNFtoFile(void)
{
    FILE * fp;
    int i;
    
    fp = fopen("/home/seopms/pmu/config.pmu", "w");
    if (fp == NULL)
    {
        return 0;//exit(1);
    }

    fprintf(fp, "#config.pmu\r\n");
    fprintf(fp,"ACV1H=%.1f\r\n", AI_Conf[0].AIHiValue.f32);
    fprintf(fp,"ACV1L=%.1f\r\n", AI_Conf[0].AILoValue.f32);
    fprintf(fp,"ACV1C=%u\r\n"  , AI_Conf[0].AIEtcConf.u16);
    fprintf(fp,"ACV2H=%.1f\r\n", AI_Conf[1].AIHiValue.f32);
    fprintf(fp,"ACV2L=%.1f\r\n", AI_Conf[1].AILoValue.f32);
    fprintf(fp,"ACV2C=%u\r\n"  , AI_Conf[1].AIEtcConf.u16);
    fprintf(fp,"DCV1H=%.1f\r\n", AI_Conf[2].AIHiValue.f32);
    fprintf(fp,"DCV1L=%.1f\r\n", AI_Conf[2].AILoValue.f32);
    fprintf(fp,"DCV1C=%u\r\n"  , AI_Conf[2].AIEtcConf.u16);
    fprintf(fp,"DCV2H=%.1f\r\n", AI_Conf[3].AIHiValue.f32);                    
    fprintf(fp,"DCV2L=%.1f\r\n", AI_Conf[3].AILoValue.f32);
    fprintf(fp,"DCV2C=%u\r\n"  , AI_Conf[3].AIEtcConf.u16);
    fprintf(fp,"DCV3H=%.1f\r\n", AI_Conf[4].AIHiValue.f32);
    fprintf(fp,"DCV3L=%.1f\r\n", AI_Conf[4].AILoValue.f32);
    fprintf(fp,"DCV3C=%u\r\n"  , AI_Conf[4].AIEtcConf.u16);
    fprintf(fp,"TEMPH=%.1f\r\n", AI_Conf[5].AIHiValue.f32);
    fprintf(fp,"TEMPL=%.1f\r\n", AI_Conf[5].AILoValue.f32);
    fprintf(fp,"TEMPC=%u\r\n"  , AI_Conf[5].AIEtcConf.u16);
    fprintf(fp,"DI1C=%u\r\n"   , DI_Conf[0].DIEtcConf.u16);
    fprintf(fp,"DI2C=%u\r\n"   , DI_Conf[1].DIEtcConf.u16);
    fprintf(fp,"DI3C=%u\r\n"   , DI_Conf[2].DIEtcConf.u16);
    fprintf(fp,"DI4C=%u\r\n"   , DI_Conf[3].DIEtcConf.u16);
    fprintf(fp,"DI5C=%u\r\n"   , DI_Conf[4].DIEtcConf.u16);
    fprintf(fp,"DI6C=%u\r\n"   , DI_Conf[5].DIEtcConf.u16);
    fprintf(fp, "\r\n");
    fclose (fp);
    
    return 1;
}

int fetchCNFfrFile(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    
    //char ipstr [ADDR_MAX]={0,};
    
    fp = fopen("/home/seopms/pmu/config.pmu", "r");
    if (fp == NULL){ 
        initConfigData();
        setCNFtoFile();
        return 0; 
    }
        
    while ((read = getline(&line, &len, fp)) != -1) {
        for (i=0; i<read; i++){
            if (line[i]=='\r' || line[i]=='\n') line[i] = '\0';
        }
        if (strstr(line,"ACV1H=")!=NULL){ AI_Conf[0].AIHiValue.f32 = atof(&line[6]); }
        if (strstr(line,"ACV1L=")!=NULL){ AI_Conf[0].AILoValue.f32 = atof(&line[6]); }
        if (strstr(line,"ACV1C=")!=NULL){ AI_Conf[0].AIEtcConf.u16 = atoi(&line[6]); }
        if (strstr(line,"ACV2H=")!=NULL){ AI_Conf[1].AIHiValue.f32 = atof(&line[6]); }
        if (strstr(line,"ACV2L=")!=NULL){ AI_Conf[1].AILoValue.f32 = atof(&line[6]); }
        if (strstr(line,"ACV2C=")!=NULL){ AI_Conf[1].AIEtcConf.u16 = atoi(&line[6]); }
        if (strstr(line,"DCV1H=")!=NULL){ AI_Conf[2].AIHiValue.f32 = atof(&line[6]); }
        if (strstr(line,"DCV1L=")!=NULL){ AI_Conf[2].AILoValue.f32 = atof(&line[6]); }
        if (strstr(line,"DCV1C=")!=NULL){ AI_Conf[2].AIEtcConf.u16 = atoi(&line[6]); }
        if (strstr(line,"DCV2H=")!=NULL){ AI_Conf[3].AIHiValue.f32 = atof(&line[6]); }                    
        if (strstr(line,"DCV2L=")!=NULL){ AI_Conf[3].AILoValue.f32 = atof(&line[6]); }
        if (strstr(line,"DCV2C=")!=NULL){ AI_Conf[3].AIEtcConf.u16 = atoi(&line[6]); }
        if (strstr(line,"DCV3H=")!=NULL){ AI_Conf[4].AIHiValue.f32 = atof(&line[6]); }
        if (strstr(line,"DCV3L=")!=NULL){ AI_Conf[4].AILoValue.f32 = atof(&line[6]); }
        if (strstr(line,"DCV3C=")!=NULL){ AI_Conf[4].AIEtcConf.u16 = atoi(&line[6]); }
        if (strstr(line,"TEMPH=")!=NULL){ AI_Conf[5].AIHiValue.f32 = atof(&line[6]); }
        if (strstr(line,"TEMPL=")!=NULL){ AI_Conf[5].AILoValue.f32 = atof(&line[6]); }
        if (strstr(line,"TEMPC=")!=NULL){ AI_Conf[5].AIEtcConf.u16 = atoi(&line[6]); }
        if (strstr(line,"DI1C=") !=NULL){ DI_Conf[0].DIEtcConf.u16 = atoi(&line[5]); }
        if (strstr(line,"DI2C=") !=NULL){ DI_Conf[1].DIEtcConf.u16 = atoi(&line[5]); }
        if (strstr(line,"DI3C=") !=NULL){ DI_Conf[2].DIEtcConf.u16 = atoi(&line[5]); }
        if (strstr(line,"DI4C=") !=NULL){ DI_Conf[3].DIEtcConf.u16 = atoi(&line[5]); }
        if (strstr(line,"DI5C=") !=NULL){ DI_Conf[4].DIEtcConf.u16 = atoi(&line[5]); }
        if (strstr(line,"DI6C=") !=NULL){ DI_Conf[5].DIEtcConf.u16 = atoi(&line[5]); }
    }

    fclose(fp);
    
    return 1;
}

int setNETtoFile(void)
{
    FILE * fp;
    int i;
    uint8_t tIP[6]={0};
    
    fp = fopen("/etc/network/interfaces", "w");
    if (fp == NULL)
    {
        return 0;//exit(1);
    }
    
    /*
    #/etc/network/interfaces
    #OPMS1=
    auto lo
    iface lo inet loopback
    auto eth0
    allow-hotplug eth0
    iface eth0 inet static
    address 192.135.174.10
    netmask 255.255.255.0
    gateway 192.135.174.97
    dns-nameservers 168.126.63.1
    */
    fprintf(fp, "#/etc/network/interfaces\n");
    fprintf(fp, "#OPMS1=%u.%u.%u.%u\n",pmuOpms[0],pmuOpms[1],pmuOpms[2],pmuOpms[3]);
    fprintf(fp, "auto lo\n");
    fprintf(fp, "iface lo inet loopback\n");
    fprintf(fp, "auto eth0\n");
    fprintf(fp, "allow-hotplug eth0\n");
    fprintf(fp, "iface eth0 inet static\n");
    fprintf(fp, "address %u.%u.%u.%u\n",pmuAddx[0],pmuAddx[1],pmuAddx[2],pmuAddx[3]);
    fprintf(fp, "netmask %u.%u.%u.%u\n",pmuMask[0],pmuMask[1],pmuMask[2],pmuMask[3]);
    fprintf(fp, "gateway %u.%u.%u.%u\n",pmuGate[0],pmuGate[1],pmuGate[2],pmuGate[3]);
    fprintf(fp, "dns-nameservers 168.126.63.1\n");
    fprintf(fp, "\n");
        
    fclose(fp);

    return 1;
}

int fetchNETfrFile(void)
{
    FILE* fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    
    uint8_t isOpmsInvalid = 1;
    
    //char ipstr [ADDR_MAX]={0,};
    
    fp = fopen("/etc/network/interfaces", "r");
    if (fp == NULL){ 
        setNETtoFile();
        return 0; 
    }

    while ((read = getline(&line, &len, fp)) != -1) {
        for (i=0; i<read; i++){
            if (line[i]=='\r' || line[i]=='\n') line[i] = '\0';
        }
        if (strstr(line,"#OPMS1=") !=NULL){ getValidACL(&line[7],pmuOpms); isOpmsInvalid = 0; }
        if (strstr(line,"address ")!=NULL){ getValidACL(&line[8],pmuAddx); }
        if (strstr(line,"netmask ")!=NULL){ getValidACL(&line[8],pmuMask); }
        if (strstr(line,"gateway ")!=NULL){ getValidACL(&line[8],pmuGate); }//printf("???=%s\r\n",&line[8]); }
    }
    
    if (isOpmsInvalid){
        setNETtoFile();
    }
    
    fclose(fp);
    
    return 1;
}

/* 
    0x21: !  --> 0x21 + 0x02 ==> 
    0x7E: ~  --> 0x7E + 0x02 ==> 
*/

#define AUTH_SEED   (0x02)

int encodeSTR(char* target, char* src)
{
    char *str;
    int field_no = 0;
   
    str = &src[0];

    while( *str != 0 )                  /* Reached zero byte ? */
    {
        *target = *str + AUTH_SEED;     /* string copy */
        target++;
        str++;                          /* Increment ptr */
        field_no++;                     /* Increment byte counter */
    }

    return field_no;
}

int decodeSTR(char* target, char* src)
{
    char *str;
    int field_no = 0;

    str = &src[0];

    while( *str != 0 )                /* Reached zero byte ? */
    {
        *target = (*str) - AUTH_SEED; /* string copy */
        target++;
        str++;                        /* Increment ptr */
        field_no++;                   /* Increment byte counter */
    }
    
    return field_no;
}

int setSFTPtoFile(void)
{
    FILE * fp;
    
    fp = fopen("/home/seopms/pmu/sftpclt.r", "w+");
    if (fp == NULL)
    {
        return 0;//exit(1);
    }
    
    /*
    #devinfo.pmu
    RID=opmssw
    RPW=sw!@#$
    DPW=power2018!@
    
    expect <<EOF
    set timeout 1
    spawn sftp -oPort=2222 -oStrictHostKeyChecking=no opmssw@14.63.237.89
    set timeout 2
    expect "opmssw@14.63.237.89's password:  "
    send "sw!@#$\r"
    set timeout 2
    expect "Connected to 14.63.237.89. "
    set timeout 2
    send "get ./down/03/pmu_image_03 /home/seopms/pmu/pmu_update\r"
    send "exit/r"
    expect eof
    EOF
    */

    fprintf(fp, "expect <<EOF\r\n");
    fprintf(fp, "set timeout 1\r\n");
    fprintf(fp, "spawn sftp -oPort=2222 -oStrictHostKeyChecking=no %s@%u.%u.%u.%u\r\n",strRID,pmuOpms[0],pmuOpms[1],pmuOpms[2],pmuOpms[3]);
    fprintf(fp, "set timeout 2\r\n");
    fprintf(fp, "expect %c%s@%u.%u.%u.%u's password:  %c\r\n",0x22,strRID,pmuOpms[0],pmuOpms[1],pmuOpms[2],pmuOpms[3],0x22);
    fprintf(fp, "send %c%s%c%c%c\r\n",0x22,strRPW,0x5C,0x72,0x22);
    fprintf(fp, "set timeout 2\r\n");
    fprintf(fp, "expect %cConnected to @%u.%u.%u.%u. %c\r\n",0x22,pmuOpms[0],pmuOpms[1],pmuOpms[2],pmuOpms[3],0x22);
    fprintf(fp, "set timeout 2\r\n");
    fprintf(fp, "send %cget ./down/03/pmu_image_03 /home/seopms/pmu/pmu_update%c%c%c\r\n",0x22,0x5C,0x72,0x22);
    //:/add/opms_sw/down/03/pmu_image_03 /home/seopms/pmu/pmu_update
    fprintf(fp, "send %cexit%c%c%c\r\n",0x22,0x5C,0x72,0x22);
    fprintf(fp, "expect eof\r\n");
    fprintf(fp, "EOF\r\n");
    //fprintf(fp, "\n");

    fclose(fp);
    
    return 1;
}

void setUserPwd(void)
{
	unsigned char command[100];
    sprintf((char*)command,"/home/seopms/pmu/pmupwd"); system(command);
}   

int setPWDtoFile(void)
{
    FILE * fp;
    
    fp = fopen("/home/seopms/pmu/pmupwd", "w+");
    if (fp == NULL)
    {
        return 0;//exit(1);
    }
    
    /*
    #devinfo.pmu
    RID=opmssw
    RPW=sw!@#$
    DPW=power2018!@
    */
    fprintf(fp, "expect <<EOF\r\n");
    fprintf(fp, "set timeout 1\r\n");
    fprintf(fp, "spawn passwd seopms\r\n");
    fprintf(fp, "expect %cEnter new UNIX password:%c\r\n",0x22,0x22); 
    fprintf(fp, "send %c%s%c%c%c\r\n",0x22,strDPW,0x5C,0x72,0x22);
    fprintf(fp, "expect %cRetype new UNIX password:%c\r\n",0x22,0x22); 
    fprintf(fp, "send %c%s%c%c%c\r\n",0x22,strDPW,0x5C,0x72,0x22);
    fprintf(fp, "expect eof\r\n");
    fprintf(fp, "EOF\r\n");
   //fprintf(fp, "\r\n");
   
    fclose(fp);
    
    setUserPwd();
    
    return 1;
}

int setDEVtoFile(void)
{
    FILE * fp;
    char str_RID[MAX_STR_AUTH+1]={0};
    char str_RPW[MAX_STR_AUTH+1]={0};
    char str_DPW[MAX_STR_AUTH+1]={0};
    
    fp = fopen("/home/seopms/pmu/devinfo.pmu", "w");
    if (fp == NULL)
    {
        return 0;//exit(1);
    }
    /*
    #devinfo.pmu
    RID=opmssw
    RPW=sw!@#$
    DPW=power2018!@
    */
    fprintf(fp, "#devinfo.pmu\r\n");
    encodeSTR(str_RID,strRID);
    encodeSTR(str_RPW,strRPW);
    encodeSTR(str_DPW,strDPW);
    fprintf(fp, "SID=%u\r\n",pPMU_SID);
    fprintf(fp, "RID=%s\r\n",str_RID);
    fprintf(fp, "RPW=%s\r\n",str_RPW);
    fprintf(fp, "DPW=%s\r\n",str_DPW);
    fprintf(fp, "\r\n");

    fclose(fp);
    return 1;
}

int fetchDEVfrFile(void)
{
    FILE * fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    
    char str_RID[MAX_STR_AUTH+1]={0};
    char str_RPW[MAX_STR_AUTH+1]={0};
    char str_DPW[MAX_STR_AUTH+1]={0};

    fp = fopen("/home/seopms/pmu/devinfo.pmu", "r");
    if (fp == NULL){ 
        setDEVtoFile();
        setSFTPtoFile();
        return 0; 
    }

    while ((read = getline(&line, &len, fp)) != -1) {
        for (i=0; i<read; i++){
            if (line[i]=='\r' || line[i]=='\n') line[i] = '\0';
        }
        if (strstr(line,"SID=")!=NULL){ pPMU_SID = atol(&line[4]); }       
        if (strstr(line,"RID=")!=NULL){ decodeSTR(str_RID,&line[4]); strcpy(strRID,str_RID); } 
        if (strstr(line,"RPW=")!=NULL){ decodeSTR(str_RPW,&line[4]); strcpy(strRPW,str_RPW); }
        if (strstr(line,"DPW=")!=NULL){ decodeSTR(str_DPW,&line[4]); strcpy(strDPW,str_DPW); }
    }
    
    fclose(fp);
    
    return 1;
}

int rstSYStoFile(void)
{
    FILE * fp;
    
    fp = fopen("/home/seopms/pmu/sysinfo.pmu", "w");
    if (fp == NULL)
    {
        return 0;//exit(1);
    }

    fprintf(fp, "#sysinfo.pmu\r\n");
    fprintf(fp, "UPGRADE_REPORT=0\r\n");
    fprintf(fp, "\r\n");

    fclose(fp);
    
    return 1;

}

int setSYStoFile(void)
{
    FILE * fp;
    
    fp = fopen("/home/seopms/pmu/sysinfo.pmu", "w");
    if (fp == NULL)
    {
        return 0;//exit(1);
    }

    fprintf(fp, "#sysinfo.pmu\r\n");
    fprintf(fp, "UPGRADE_REPORT=1\r\n");
    fprintf(fp, "\r\n");

    fclose(fp);
    return 1;
}

int fetchSYSfrFile(void)
{
    FILE* fp;
    int i;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    
    fp = fopen("/home/seopms/pmu/sysinfo.pmu", "r");
    if (fp == NULL){ 
        rstSYStoFile();
        return 0; 
    }

    while ((read = getline(&line, &len, fp)) != -1) {
        for (i=0; i<read; i++){
            if (line[i]=='\r' || line[i]=='\n') line[i] = '\0';
        }
        if (strstr(line,"UPGRADE_REPORT=")!=NULL){ if (line[15]=='1') bUpgradeReport = 1; }
    }

    if (bUpgradeReport == 1) rstSYStoFile();

    fclose(fp);
    
    return 1;
}


int CheckLink(char *ifname)
{
    #if 1
    //int state = -1;
    int socId = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP);

    if (socId < 0) return -1; //syslog(LOG_NOTICE, "KT-PMU# Socket failed. Errno = %d\n", errno);

    struct ifreq if_req;
    (void) strncpy(if_req.ifr_name, ifname, sizeof(if_req.ifr_name));
    int rv = ioctl(socId, SIOCGIFFLAGS, &if_req);
    close(socId);

    if ( rv == -1) return -1; //syslog(LOG_NOTICE, "KT-PMU# Ioctl failed. Errno = %d\n", errno);

    printf("ethernet link-up\n");
    return ( (if_req.ifr_flags & IFF_UP) && (if_req.ifr_flags & IFF_RUNNING) );
    #else

    #endif
    
    return 1;
}

int SPI_Oper_Init(int* fd, uint8_t debug)
{
    //int fd;
    int ret = 0;

    *fd = open(device, O_RDWR);
    if (fd < 0){
        if (debug) printf("can't open spi device\n");
        return 0;
    }
    
    mode = 0;
    mode |= SPI_LOOP;
    mode |= SPI_CPHA;
    mode |= SPI_CPOL;
    mode |= SPI_LSB_FIRST;
    mode |= SPI_CS_HIGH;
    //mode |= SPI_3WIRE;
    //mode |= SPI_NO_CS;
    mode |= SPI_READY;
    
    /*
     * spi mode
     */
    ret = ioctl(*fd, SPI_IOC_WR_MODE, &mode);
    if (ret == -1){
        //if (debug) printf("can't set spi mode\n");
        //return 0;
    }

    ret = ioctl(*fd, SPI_IOC_RD_MODE, &mode);
    if (ret == -1){
        if (debug) printf("can't get spi mode\n");
        return 0;
    }
    
    /*
     * bits per word
     */
    ret = ioctl(*fd, SPI_IOC_WR_BITS_PER_WORD, &bits);
    if (ret == -1){
        if (debug) printf("can't set bits per word\n");
        return 0;
    }
    
    ret = ioctl(*fd, SPI_IOC_RD_BITS_PER_WORD, &bits);
    if (ret == -1){
        if (debug) printf("can't get bits per word\n");
        return 0;
    }
    
    /*
     * max speed hz
     */
    ret = ioctl(*fd, SPI_IOC_WR_MAX_SPEED_HZ, &speed);
    if (ret == -1){
        if (debug) printf("can't set max speed hz\n");
        return 0;
    }
    
    ret = ioctl(*fd, SPI_IOC_RD_MAX_SPEED_HZ, &speed);
    if (ret == -1){
        if (debug) printf("can't get max speed hz\n");
        return 0;
    }

    if (debug){
        printf("spi mode: %d\n", mode);
        printf("bits per word: %d\n", bits);
        printf("max speed: %d Hz (%d KHz)\n", speed, speed/1000);
    }
    
    //close(fd);
    
    return 1;
}

int SPI_Oper_Proc(int fd, uint8_t debug)
{
    int field_no = 1;
    int16_t tmp_ai[8];
    int16_t raw_ai[8];
    uint8_t tmp_di[8];
    uint8_t raw_di[8];
    
    int i;
    int ret;
    int offset;

    struct spi_ioc_transfer spi_tr = {
        .tx_buf = (unsigned long)spi_tx,
        .rx_buf = (unsigned long)spi_rx,
        .len = ARRAY_SIZE(spi_tx),
        .delay_usecs = delay,
        .speed_hz = speed,
        .bits_per_word = bits,
    };
 
    ret = ioctl(fd, SPI_IOC_MESSAGE(1), &spi_tr);
    if (ret < 1){
        if (debug) printf("can't send spi message\n");
        return 0;
    }
    
    if (debug){
        for (ret = 0; ret < ARRAY_SIZE(spi_tx); ret++) {
            printf("%.2X ", spi_rx[ret]);
        }
        printf(":Rcvd[%d]\r\n",ret);
        
        for (ret = 0; ret < ARRAY_SIZE(spi_tx); ret++) {
            printf("%.2X ", spi_tx[ret]);
        }
        printf(":Send[%d]\r\n",ret);
    }
    
    /*--- read raw data from afe-mcu ---*/
    offset = 2;
    for (i=0; i<7; i++){
        tmp_ai[i] = (int16_t)(spi_rx[offset]*256 + spi_rx[offset+1]);
        //if (tmp_ai[i] >= 0) raw_ai[i] = temp_ai[i];
        offset += 2;
    }
    for (i=0; i<6; i++){
        if (tmp_ai[i] >= 0) raw_ai[i] = tmp_ai[i];
    }
    
    if (raw_ai[3]<10) raw_ai[3] = raw_ai[2];
    
    if (tmp_ai[6] < -400) raw_ai[6] = 0;
    else                  raw_ai[6] = tmp_ai[6];
    
    offset = 23; /* if di_value == 0, di_signal is in alarm stat */
    for (i=0; i<6; i++){
        tmp_di[i] = spi_rx[offset];
        if (tmp_di[i]==1) raw_di[i] = 1;
        else              raw_di[i] = 0;
        offset += 1;
    }

    /*--- conversion routine ---*/
    f32AnalogVal[0].f32 = ((float)(raw_ai[0]))*(0.1F);//221.3F;//
    f32AnalogVal[1].f32 = ((float)(raw_ai[1]))*(0.1F);//221.0F;//
    f32AnalogVal[2].f32 = ((float)(raw_ai[3]))*(0.01F);
    f32AnalogVal[3].f32 = ((float)(raw_ai[4]))*(0.01F);
    f32AnalogVal[4].f32 = ((float)(raw_ai[5]))*(0.01F);
    f32AnalogVal[5].f32 = ((float)(raw_ai[6]))*(0.1F);
    f32AnalogVal[6].f32 = ((float)(raw_ai[2]))*(0.01F);
    
    checkAnalogAlarm();
    checkDigitalAlarm(raw_di);

    /*--- set led on/off ---*/
    if (u8AnalogSTS[0]==PS_NORMAL) spi_tx[15] = 0; else spi_tx[15] = 1;
    if (u8AnalogSTS[1]==PS_NORMAL) spi_tx[16] = 0; else spi_tx[16] = 1;
    if (u8AnalogSTS[2]==PS_NORMAL) spi_tx[17] = 0; else spi_tx[17] = 1;
    if (u8AnalogSTS[3]==PS_NORMAL) spi_tx[18] = 0; else spi_tx[18] = 1;
    if (u8AnalogSTS[4]==PS_NORMAL) spi_tx[19] = 0; else spi_tx[19] = 1;
    if (u8AnalogSTS[5]==PS_NORMAL) spi_tx[21] = 0; else spi_tx[21] = 1;

    if (u8DigitalSTS[0]==PS_NORMAL) spi_tx[22] = 0; else spi_tx[22] = 1;
    if (u8DigitalSTS[1]==PS_NORMAL) spi_tx[23] = 0; else spi_tx[23] = 1;
    if (u8DigitalSTS[2]==PS_NORMAL) spi_tx[24] = 0; else spi_tx[24] = 1;
    if (u8DigitalSTS[3]==PS_NORMAL) spi_tx[25] = 0; else spi_tx[25] = 1;
    if (u8DigitalSTS[4]==PS_NORMAL) spi_tx[26] = 0; else spi_tx[26] = 1;
    if (u8DigitalSTS[5]==PS_NORMAL) spi_tx[27] = 0; else spi_tx[27] = 1;

    return field_no;
}

int SPI_Oper_Prev(int fd, uint8_t debug)
{
    int field_no = 1;
    int16_t tmp_ai[8];
    int16_t raw_ai[8];
    uint8_t tmp_di[8];
    uint8_t raw_di[8];
    
    int i;
    int ret;
    int offset;

    struct spi_ioc_transfer spi_tr = {
        .tx_buf = (unsigned long)spi_tx,
        .rx_buf = (unsigned long)spi_rx,
        .len = ARRAY_SIZE(spi_tx),
        .delay_usecs = delay,
        .speed_hz = speed,
        .bits_per_word = bits,
    };
 
    ret = ioctl(fd, SPI_IOC_MESSAGE(1), &spi_tr);
    if (ret < 1){
        if (debug) printf("can't send spi message\n");
        return 0;
    }
    
    if (debug){
        for (ret = 0; ret < ARRAY_SIZE(spi_tx); ret++) {
            printf("%.2X ", spi_rx[ret]);
        }
        printf(":Rcvd[%d]\r\n",ret);
        
        for (ret = 0; ret < ARRAY_SIZE(spi_tx); ret++) {
            printf("%.2X ", spi_tx[ret]);
        }
        printf(":Send[%d]\r\n",ret);
    }
    
    /*--- read raw data from afe-mcu ---*/
    offset = 2;
    for (i=0; i<7; i++){
        tmp_ai[i] = (int16_t)(spi_rx[offset]*256 + spi_rx[offset+1]);
        //if (tmp_ai[i] >= 0) raw_ai[i] = temp_ai[i];
        offset += 2;
    }
    for (i=0; i<6; i++){
        if (tmp_ai[i] >= 0) raw_ai[i] = tmp_ai[i];
    }
    
    if (raw_ai[3]<10) raw_ai[3] = raw_ai[2];
    
    if (tmp_ai[6] < -400) raw_ai[6] = 0;
    else                  raw_ai[6] = tmp_ai[6];
    
    offset = 23; /* if di_value == 0, di_signal is in alarm stat */
    for (i=0; i<6; i++){
        tmp_di[i] = spi_rx[offset];
        if (tmp_di[i]==1) raw_di[i] = 1;
        else              raw_di[i] = 0;
        offset += 1;
    }

    /*--- conversion routine ---*/
    f32AnalogVal[0].f32 = ((float)(raw_ai[0]))*(0.1F);//221.3F;//
    f32AnalogVal[1].f32 = ((float)(raw_ai[1]))*(0.1F);//221.0F;//
    f32AnalogVal[2].f32 = ((float)(raw_ai[3]))*(0.01F);
    f32AnalogVal[3].f32 = ((float)(raw_ai[4]))*(0.01F);
    f32AnalogVal[4].f32 = ((float)(raw_ai[5]))*(0.01F);
    f32AnalogVal[5].f32 = ((float)(raw_ai[6]))*(0.1F);
    f32AnalogVal[6].f32 = ((float)(raw_ai[2]))*(0.01F);
    
    //checkAnalogAlarm();
    //checkDigitalAlarm(raw_di);

    /*--- set led on/off ---*/
    if (bLedFlag){
        spi_tx[15] = 1; 
        spi_tx[16] = 1;
        spi_tx[17] = 1;
        spi_tx[18] = 1;
        spi_tx[19] = 1;
        spi_tx[21] = 1;
                                                                
        spi_tx[22] = 1;
        spi_tx[23] = 1;
        spi_tx[24] = 1;
        spi_tx[25] = 1;
        spi_tx[26] = 1;
        spi_tx[27] = 1;
    }
    else{
        spi_tx[15] = 0; 
        spi_tx[16] = 0;
        spi_tx[17] = 0;
        spi_tx[18] = 0;
        spi_tx[19] = 0;
        spi_tx[21] = 0;
                                                                
        spi_tx[22] = 0;
        spi_tx[23] = 0;
        spi_tx[24] = 0;
        spi_tx[25] = 0;
        spi_tx[26] = 0;
        spi_tx[27] = 0;    
    }
    
    bLedFlag ^= 1;
    
    return field_no;
}

int setRealTimeReportToFile(void)
{
    FILE * fp;
    int i;
        
    fp = fopen("/home/seopms/pmu/realtime.pmu", "w");
    if (fp == NULL)
    {
        return 0;
    }

    fprintf(fp, "#realtime.pmu\n");
    for (i=0; i<6; i++){
        fprintf(fp,"AI%dV=%.1f\r\n", i+1, f32AnalogVal[i].f32);
    }
    for (i=0; i<6; i++){
        fprintf(fp,"AI%dS=%u\r\n",i+1, u8AnalogSTS[i]);
    }
    
    for (i=0; i<6; i++){
        fprintf(fp,"DI%dS=%u\r\n",i+1, u8DigitalSTS[i]);
    }
    fprintf(fp, "\r\n");

    fclose(fp);
    
    return 1;
}

/*!
 \n==================================================================
 @brief main()
 \n==================================================================
 */

void auto_reboot(void)
{
	unsigned char command[100];
	sprintf((char*)command,"reboot"); system(command);		
}

static int iAFE_InitCnt = 1;
int main(int argc, char *argv[])
{
    int fd_spi;   /* SPI Device for AFE-MCU */  
    int sockRecv; /* UDP Server Socket for OPMS Request */
    int sockConf; /* UDP Server Socket for CONF Request */
    int sockRsys; /* UDP Server Socket for rsyslog report */

    uint8_t init_debug = 0;
    uint8_t oper_debug = 0;
    uint8_t opms_debug = 0;
    uint8_t spi_debug = 0;
    uint32_t rpt_cnt = 1;
    uint32_t tcp_cnt = 1;
    uint32_t rcv_cnt = 1;
    uint32_t u32auto_reboot_cnt = 0;  //604800, 86400

    
    int i;
    for (i=0; i<argc; i++){
        //printf("option%d=%s\n",i,argv[i]);
        if (strstr(argv[i],"-d") != NULL) { oper_debug = 1; init_debug = 1; }
        if (strstr(argv[i],"-o") != NULL) opms_debug = 1;
        if (strstr(argv[i],"-s") != NULL) spi_debug = 1;
    }

    fetchACLfrFile();
    fetchCNFfrFile();
    fetchNETfrFile();
    fetchDEVfrFile();
    fetchSYSfrFile();
    
    chkSFTPcommand();
    
    //while(CheckLink("eth0")==0){}
    //initConfigData();
    initRealtimeData();
    getSystemRTC();

    syslog(LOG_NOTICE, "KT-PMU# Report Start v%c.%c%c",pmuVer[0],pmuVer[2],pmuVer[3]);
    
    //filterInit();
    
    SPI_Oper_Init (&fd_spi,init_debug);
    OPMS_Recv_Init(&sockRecv,init_debug);
    CONF_Recv_Init(&sockConf,init_debug);
    RSYS_Recv_Init(&sockRsys,init_debug);
    
    send_MSG_UPGRADE_RESULT();

    #if 1
    while (1)
    {
        if (rcv_cnt){
            //if (++rcv_cnt > 2uL)
            {
                rcv_cnt = 1;
                OPMS_Recv_Proc(&sockRecv,opms_debug);
                CONF_Recv_Proc(&sockConf,oper_debug);
                RSYS_Recv_Proc(&sockRsys,oper_debug);
            }
        }
        
        if (rpt_cnt){
            
            if (++rpt_cnt > 1000uL){//1sec
                rpt_cnt = 1uL;
                if (checkSystemRTC(&sysrtc)) clearSBUF();
                //if (getGUIconfig()){ fetchCNFfrFile(); setGUIconfig(); }
                //if (getGUIacllist()){ fetchACLfrFile(); if (setIPtables()) filterInit(); setGUIacllist(); }
                //if (getGUIdevinfo()){ fetchDEVfrFile(); setSFTPtoFile(); setPWDtoFile(); setGUIdevinfo(); }
                //if (getGUInetwork()){ fetchNETfrFile(); setSFTPtoFile(); setNETtoFile(); setGUInetwork(); }
                if (iAFE_InitCnt==0){       
                    SPI_Oper_Proc(fd_spi, spi_debug);
                    STD_ALM_AI_Proc(opms_debug);
                    STD_ALM_DI_Proc(opms_debug);
                }
                else{
                    SPI_Oper_Prev(fd_spi, spi_debug);
                    if (++iAFE_InitCnt > 4){
                        iAFE_InitCnt = 0;
                    }
                }
                
                if (++u32auto_reboot_cnt > 86400uL){ //  604800, 86400)
                    auto_reboot();
                }
            }
        }
        
        if (tcp_cnt){
            if (++tcp_cnt > 3000uL){ //10sec
                tcp_cnt = 1uL;
                setRealTimeReportToFile();
                //getSystemRTC();
                //sendTcpRealtimePacket();
            }
        }
        
        #if 0
        if (bIptableFlag){
        	bIptableFlag = 0;
        	if (setIPtables()) filterInit();
        }
        #endif
    
        

        usleep(1000);/* important !!! do not remove */
        
        fflush(stdout);
    }
    return 0;
    
    #else
    while(1){
        sleep(1);
    }
    return 0;
    #endif
}

//*******************************pmu_udp_rxx.c*******************************//
#if 0

#endif
