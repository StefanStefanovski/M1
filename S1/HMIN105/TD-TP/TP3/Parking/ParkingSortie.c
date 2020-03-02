#include "stdio.h"
#include "stdlib.h"
#include "unistd.h"
#include "sys/types.h"
#include "sys/ipc.h"
#include "sys/shm.h"
#include "sys/sem.h"

struct sembuf op[] = {
  {(u_short)0, (short)-1, SEM_UNDO},
    {(u_short)0, (short)1, SEM_UNDO}
};
typedef union semun {
  int val;
  struct semid_ds *buf;
  unsigned short *array;
  struct seminfo *__buf;
}semun;

int main(){
  const char* path = "file.txt";
  
  int key = ftok(path, 1);
  int key_sem = ftok(path, 2);
  if(key_sem==-1){
     printf("err ftok\n");
     return -1;
   }
 if(key==-1){
    printf("err ftok\n");
    return -1;
  }
  printf("creation de memoire partage\n");
  
  int sh_id = shmget(key, sizeof(int), SHM_RDONLY);
  if(sh_id==-1){
    printf("err de shmget\n");
    return -1;
  }

  int sem_id = semget(key_sem, 1, IPC_CREAT|0666);

  if(sem_id==-1){
    printf("err de creation de semaphore\n");
    return -1;
  }

  int* nb_places = shmat(sh_id, NULL, 0);
  if(*nb_places == -1){
    printf("err d'attachement\n");
    return -1;
  }
  
 semun egCtrl;
  egCtrl.val=1;
  
  if(semctl(sem_id, 0, SETVAL, egCtrl)==-1){
    perror("probleme avec init de sem\n");
    return -1;
  }
  while(1){
    sleep(3);
    if(semop(sem_id, op, 1)==-1){
      printf("err de semop\n");
      return -1;
    }

    if(*nb_places <5){
      printf("demande acceptée\n");
      (*nb_places)++;
      printf("impression ticket\n");
      printf("nombre de places : %d", *nb_places);
      printf("\n");
    }
    else
      printf("parking vide\n");

    if(semop(sem_id, op+1, 1)==-1){
      printf("err de devrouillagre de semaphore\n");
      return -1;
    }
    
  }
  if(shmdt((void*)nb_places)==-1){
    printf("err de detachement\n");
    return -1;
  }

  if(shmctl(sh_id, IPC_RMID, NULL)==-1){
    printf("err de destruction de memoire partage\n");
    return -1;
  }
}
