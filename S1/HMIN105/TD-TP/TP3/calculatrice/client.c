#include "stdio.h"
#include "stdlib.h"
#include "unistd.h"
#include "sys/ipc.h"
#include "sys/types.h"
#include "sys/msg.h"
#include "calc.h"



int main(int argc, char** argv){
  if(argc<2){
    printf("2 argument SVP\n");
    return 1;
  }
  int idFile=atoi(argv[1]);

  printf("inserer les valaues\n");
  calc_msg calc;
  eval_msg eval;
  scanf("%d %c %d",&calc.x,&calc.s,&calc.y);
  
  if(msgsnd(idFile,&calc,sizeof(calc),0)==-1){
    printf("erreur d'envoi de message\n");
    return 1;
  }
  if(msgrcv(idFile, &eval, sizeof(eval),0,0)==-1){
    printf("erreur de rcv\n");
    return 1;
  }
  printf("resultat = %d \n",eval.res);
  return 0;

}
       
