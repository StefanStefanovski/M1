#include "definitions.h"


// Fonction exécutée par chaque thread de traitement.
// /!\ NE PAS MODIFIER LES LIGNES DE CODE INCLUES
void * travailler(void * p){

  params * param = (params*)p;
  afficheDebutFinThread(1, param->indice); // conserver cet appel à cet emplacement. 
  // Début partie à compléter -----
	

	pthread_mutex_lock(&(param->donnees->mut));
	while(param->donnees->compteur < param->donnees->n){
		if(param->donnees->ligneCourante >= param->donnees->n) break;
	
		pthread_mutex_unlock(&(param->donnees->mut));
		pthread_mutex_lock(&(param->donnees->mut));
		int ligne = param->donnees->ligneCourante;
		traiterUneLigne(param->donnees->matrice, ligne, param->donnees->m, param->indice);	
		param->donnees->ligneCourante = param->donnees->ligneCourante + 1;
		param->donnees->compteur = param->donnees->compteur+1;
		pthread_mutex_unlock(&(param->donnees->mut));
		
	}
	

  // En boucle, prendre une ligne à traiter pour la traiter. Sortir de
  // la boucle quand toutes les lignes ont été prises en compte
  // (traitées ou en cours de traitement). Le traitement d'une ligne
  // est indépendant du traitement d'une autre ligne, donc, les
  // traitements sur différentes lignes, effectués par différents
  // threads, doivent pouvoir s'exécuter en parallèle.

  // Ensuite, attendre la fin des traitements de ligne en cours avant
  // de passer au traitement des colonnes.

  	
  // Fin partie à compléter -----

	while(param->donnees->compteur <= param->donnees->n){
		pthread_cond_wait(&(param->donnees->condition),&(param->donnees->mut));
	}

	if(param->donnees->compteur > param->donnees->n)
		pthread_cond_broadcast(&(param->donnees->condition));
	pthread_mutex_unlock(&(param->donnees->mut));

  // L'appel suivant doit être conservé avant de passer au traitement
  // des colonnes et ne doit pas apparaitre dans une section critique.
  testEtapeLignes(&(param->donnees->mut));

  

  // Début partie à compléter -----
	
	pthread_mutex_lock(&(param->donnees->mut));
	//while(param->donnees->colonneCourante < param->donnees->m){
	traiterUneColonne(param->donnees->matrice, param->donnees->colonneCourante, param->donnees->n, param->indice);
	param->donnees->colonneCourante = param->donnees->colonneCourante + 1;

	//}
	pthread_mutex_unlock(&(param->donnees->mut));




  // En boucle, prendre une colonne à traiter pour la
  // traiter. Sortir de la boucle quand toutes les colonnes ont été
  // prises en compte (traitées ou en cours de traitement). Le
  // traitement d'une colonne est indépendant du traitement d'une
  // autre colonne, donc, les traitements sur différentes colonnes,
  // effectués par différents threads, doivent pouvoir s'exécuter en
  // parallèle.
  
  // Fin partie à compléter -----
  
  // le code suivant (jusqu'à la fin de la fonction), est à conserver.
  afficheDebutFinThread(0, param->indice);
  free(param);
  pthread_exit(NULL);
}
