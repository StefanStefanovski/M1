#include "stdlib.h"
#include "stdio.h"
#include "unistd.h"
#include "sys/types.h"
#include "sys/ipc.h"
#include "sys/msg.h"
#include "calc.h"
int calc_plus(calc_msg *msg, int queue_id){
  eval_msg eval;
  eval.mtype=msg->mtype;
  eval.res=msg->x+msg->y;
  if(msgsnd(queue_id, &eval, sizeof(eval),0)==-1){
    printf("err dans calc.c msg snd calc_plus\n");
  }
  return eval.res;
}

int calc_moins(calc_msg *msg, int queue_id){
  eval_msg eval;
  eval.mtype = msg->mtype;
  eval.res = msg->x - msg->y;
    if(msgsnd(queue_id, &eval, sizeof(eval),0)==-1){
    printf("err dans calc.c msg snd calc_moins\n");
  }
  return eval.res;
}
int calc_div(calc_msg *msg, int queue_id){
  eval_msg  eval;
  eval.mtype = msg->mtype;
  eval.res = msg->x / msg->y;
    if(msgsnd(queue_id, &eval, sizeof(eval),0)==-1){
    printf("err dans calc.c msg snd calc_div\n");
  }
  return eval.res;
}
int calc_mult(calc_msg *msg, int queue_id){
  eval_msg  eval;
  eval.mtype = msg->mtype;
  eval.res = msg->x * msg->y;
    if(msgsnd(queue_id, &eval, sizeof(eval),0)==-1){
    printf("err dans calc.c msg snd calc_mult\n");
  }
  return eval.res;
}
int eval_calc_msg (calc_msg *msg, int queue_id){
  switch(msg->s){
  case '+':
    return calc_plus(msg, queue_id);
    break;
  case '-':
    return calc_moins(msg, queue_id);
    break;
  case '/':
    return calc_div(msg, queue_id);
    break;
  case '*':
    return calc_mult(msg,queue_id);
    break;
  default:
    printf("operateur inconnue\n");
    return 1;
  }
}

		    
int main(){
  printf("Creation de file de messsages\n");

  int queue_id=msgget(IPC_PRIVATE, 0666);

  printf("id File = %d\n", queue_id);

  calc_msg calc;
  
  if(msgrcv(queue_id, &calc, sizeof(calc),0,0)==-1){
    printf("err dans calc.c  msgrcv\n");
    return 1;
    }
  int res=eval_calc_msg(&calc, queue_id);
  
  msgctl(queue_id, IPC_RMID,NULL);
  return 0;
}
