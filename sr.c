#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"

/* ******************************************************************
   Selective Repeat protocol.
   Adapted GBN Protocol provided which was sadpted from J.F.Kurose
   Selective Repeat Protocol Emulator: VERSION 0.1 

   Network properties:


   Modifications: 
   - 
**********************************************************************/

#define RTT  16.0                   /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6                /* the maximum number of buffered unacked packet */
#define SEQSPACE   (2*WINDOWSIZE)   /* the min sequence space for SR must be at least windowsize * 2 */
#define NOTINUSE (-1)               /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver  
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your 
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ ) 
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}

/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE];  /* array for storing packets waiting for ACK */
static bool acked[WINDOWSIZE];    /* which buffered packets have been ACK’d */
static int windowfirst, windowlast;    /* array indexes of the first/last packet awaiting ACK */
static int windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if not blocked waiting on ACK */
  if ( windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for ( i=0; i<20 ; i++ )
        sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    /* buffer this packet by its sequence number */
    windowlast = (windowlast + 1) % WINDOWSIZE;
    buffer[windowlast] = sendpkt;
    acked[windowlast]  = false;
    windowcount++;

    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3(A, sendpkt);

     /* start to track per-packet timeouts */
    if (windowcount == 1)
      starttimer(A, RTT);

    /* get next sequence number, wrap back to 0 */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;  
  }
  /* if blocked,  window is full */
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4 
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{

  int dist;
  int idx;

  /* if received ACK is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
        printf("----A: uncorrupted ACK %d is received\n", packet.acknum);
    total_ACKs_received++;

    /* check if new ACK or duplicate */
    if (windowcount != 0) {
      int seqfirst = buffer[windowfirst].seqnum;
      int seqlast = buffer[windowlast].seqnum;
      /* check if ACK within current window */
      if (((seqfirst <= seqlast) && (packet.acknum >= seqfirst && packet.acknum <= seqlast)) ||
          ((seqfirst > seqlast) && (packet.acknum >= seqfirst || packet.acknum <= seqlast))) {

          if (TRACE > 0)
              printf("----A: ACK %d is not a duplicate\n", packet.acknum);
          new_ACKs++;

          /* locate buffer index */
          dist = (packet.acknum - seqfirst + SEQSPACE) % SEQSPACE;
          idx = (windowfirst + dist) % WINDOWSIZE;
          if (!acked[idx]) {
              acked[idx] = true;
              windowcount--;
          }

          /* slide window over all leading ACKed */
          while (acked[windowfirst]) {
              acked[windowfirst] = false;
              windowfirst = (windowfirst + 1) % WINDOWSIZE;
          }

          /* restart timer if still unacked */
          stoptimer(A);
          if (windowcount > 0)
              starttimer(A, RTT);
      } 
      else {
          if (TRACE > 0)
              printf("----A: duplicate ACK received, do nothing!\n");
      }
  }
} else {
  if (TRACE > 0)
      printf("----A: corrupted ACK is received, do nothing!\n");
}
}

/* called when A's timer goes off */
void A_timerinterrupt(void) 
{

  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");

  if (TRACE > 0)
    printf("---A: resending packet %d\n", buffer[windowfirst].seqnum);
  
  tolayer3(A,buffer[windowfirst]);
  packets_resent++;
  starttimer(A,RTT);

}         

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{

  int i;

  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;   /* windowlast is where the last packet sent is stored.  
		     new packets are placed in winlast + 1 
		     so initially this is set to -1
		   */
  windowcount = 0;

  for (i = 0; i < WINDOWSIZE; i++) 
    acked[i] = false;

}


/********* Receiver (B)  variables and procedures ************/

/********* Receiver (B)  variables and procedures ************/

static struct pkt recvbuf[WINDOWSIZE];
static bool recvOK[WINDOWSIZE];
static int recvbase;
static int B_nextseqnum;


/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;
  int last;

  bool corrupt = IsCorrupted(packet);
  int dist = (packet.seqnum - recvbase + SEQSPACE) % SEQSPACE;
  bool inWindow = (!corrupt && dist < WINDOWSIZE);

  /* if not corrupted and received packet is in order */
  if (inWindow) {
    if (!recvOK[dist]) {
        /* buffer new in-window packet */
        recvbuf[dist] = packet;
        recvOK[dist]  = true;
    }
    /* original trace for correct receipt */
    if (TRACE > 0)
        printf("----B: packet %d is correctly received, send ACK!\n", packet.seqnum);
    packets_received++;
    sendpkt.acknum = packet.seqnum;
  } else {
      /* corrupted or out-of-window */
      if (TRACE > 0)
          printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");
      /* ACK last in-order */
      last = (recvbase == 0 ? SEQSPACE - 1 : recvbase - 1);
      sendpkt.acknum = last;
  }

  /* deliver any in-order packets */
  while (recvOK[0]) {
      tolayer5(B, recvbuf[0].payload);
      /* shift buffer */
      for (i = 0; i < WINDOWSIZE - 1; i++) {
          recvbuf[i] = recvbuf[i + 1];
          recvOK[i]  = recvOK[i + 1];
      }
      recvOK[WINDOWSIZE - 1] = false;
      recvbase = (recvbase + 1) % SEQSPACE;
  }

  /* finish ACK packet and send */
  sendpkt.seqnum = B_nextseqnum;
  B_nextseqnum   = (B_nextseqnum + 1) % 2;
  for (i = 0; i < 20; i++)
      sendpkt.payload[i] = '0';
  sendpkt.checksum = ComputeChecksum(sendpkt);
  tolayer3(B, sendpkt);

}


/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void) {

  int i;

  recvbase = 0;
  B_nextseqnum = 1;

  for (i = 0; i < WINDOWSIZE; i++)
      recvOK[i] = false;

}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)  
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}

