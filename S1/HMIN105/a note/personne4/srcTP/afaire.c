#include "definitions.h"


// Fonction exécutée par chaque thread de traitement.
// /!\ NE PAS MODIFIER LES LIGNES DE CODE INCLUES
void * travailler(void * p){

  params * param = (params*)p;
  afficheDebutFinThread(1, param->indice); // conserver cet appel à cet emplacement. 

  // Début partie à compléter -----

  // En boucle, prendre une ligne à traiter pour la traiter. Sortir de
  // la boucle quand toutes les lignes ont été prises en compte
  // (traitées ou en cours de traitement). Le traitement d'une ligne
  // est indépendant du traitement d'une autre ligne, donc, les
  // traitements sur différentes lignes, effectués par différents
  // threads, doivent pouvoir s'exécuter en parallèle.

  // Ensuite, attendre la fin des traitements de ligne en cours avant
  // de passer au traitement des colonnes.

  
  // Fin partie à compléter -----

  // printf("%d", param->donnees->compteur);
  
  pthread_mutex_lock(&(param->donnees->mut));
  while(param->donnees->ligneCourante < param->donnees->n){
    pthread_mutex_unlock(&(param->donnees->mut));
    // pthread_mutex_lock(&(param->donnees->mut));
    traiterUneLigne(param->donnees->matrice, param->donnees->ligneCourante, param->donnees->m, param->indice);
    // pthread_mutex_unlock(&(param->donnees->mut));
    pthread_mutex_lock(&(param->donnees->mut));
    param->donnees->ligneCourante++;
    param->donnees->compteur++;
    pthread_mutex_unlock(&(param->donnees->mut));
  }
  
  pthread_mutex_lock(&(param->donnees->mut));

  while(param->donnees->compteur < param->donnees->n){
    pthread_cond_wait(&(param->donnees->condition), &(param->donnees->mut));
  }
  if(param->donnees->ligneCourante == param->donnees->n){
    pthread_cond_broadcast(&(param->donnees->condition));
    param->donnees->ligneCourante = 0;
  }

  pthread_mutex_unlock(&(param->donnees->mut));

  // L'appel suivant doit être conservé avant de passer au traitement
  // des colonnes et ne doit pas apparaitre dans une section critique.
  testEtapeLignes(&(param->donnees->mut));
  
  // Début partie à compléter -----
  
  // En boucle, prendre une colonne à traiter pour la
  // traiter. Sortir de la boucle quand toutes les colonnes ont été
  // prises en compte (traitées ou en cours de traitement). Le
  // traitement d'une colonne est indépendant du traitement d'une
  // autre colonne, donc, les traitements sur différentes colonnes,
  // effectués par différents threads, doivent pouvoir s'exécuter en
  // parallèle.
  
  // Fin partie à compléter -----
  
  pthread_mutex_lock(&(param->donnees->mut));
  while(param->donnees->colonneCourante < param->donnees->m){
    pthread_mutex_unlock(&(param->donnees->mut));
    traiterUneColonne(param->donnees->matrice, param->donnees->colonneCourante, param->donnees->m, param->indice);
    pthread_mutex_lock(&(param->donnees->mut));
    param->donnees->colonneCourante++;
    param->donnees->compteur++;
    pthread_mutex_unlock(&(param->donnees->mut));
  }
  /*
  pthread_mutex_lock(&(param->donnees->mut));
  while(param->donnees->compteur < 99){
    pthread_cond_wait(&(param->donnees->condition), &(param->donnees->mut));
  }
  if(param->donnees->colonneCourante == param->donnees->n){
    param->donnees->compteur = 0;
    pthread_cond_broadcast(&(param->donnees->condition));
  }

  pthread_mutex_unlock(&(param->donnees->mut));*/
  
  // le code suivant (jusqu'à la fin de la fonction), est à conserver.
  afficheDebutFinThread(0, param->indice);
  free(param);
  pthread_exit(NULL);
}
