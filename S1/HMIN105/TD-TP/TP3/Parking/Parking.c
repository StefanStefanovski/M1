#include "stdio.h"
#include "stdlib.h"
#include "unistd.h"
#include "sys/types.h"
#include "sys/ipc.h"
#include "sys/shm.h"


int main(int argc, char** argv){
  const char* path = "file.txt";
  
  if(argc<2){
    printf("2argumentSVP\n");
    return -1;
  }

  int places=atoi(argv[1]);
  int key = ftok(path, 1);
 if(key==-1){
    printf("err ftok\n");
    return -1;
  }
  printf("creation de memoire partage\n");
  
  int sh_id = shmget(key, sizeof(int), IPC_CREAT|0666);
  if(sh_id==-1){
    printf("err de shmget\n");
    return -1;
  }
  printf("memoire partage cree\n");

  int* nb_places = shmat(sh_id, NULL, 0);
  if(*nb_places == -1){
    printf("err d'attachement\n");
    return -1;
  }
  *nb_places = places;
  printf("nombre de places : %d   nb_places : %d \n", places, *nb_places);
  printf("\n tapez entree pour termine\n");
  getchar();

  if(shmdt((void*)nb_places)==-1){
    printf("err de detachement\n");
    return -1;
  }

  if(shmctl(sh_id, IPC_RMID, NULL)==-1){
    printf("err de destruction de memoire partage\n");
    return -1;
  }
  printf("memoire partage supprime\n");

  return 0;
}
