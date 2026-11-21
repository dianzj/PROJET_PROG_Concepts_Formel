#include "enumeration.h"


/* renvoie tout les objet d extent  qui ont tous les attribue(caracteristique ) d intent
   posons extent=A et intent =B
   la fonction renvoie B' inter A  */
static word *intersection(const FormalContext *ctx,word *extent,const word *intent){
    for(size_t i=0;i<ctx->nb_att;i++){
        if ((intent[i/WORD_BITS] & (UINT64_C(1)<<(i%WORD_BITS)))!=0){ /*test si l attribu i est dans intent */
            for (size_t obj=0;obj<ctx->nb_word_obj;obj++){ /* concerve les mot qui ont l attribue i */
                extent[obj]=extent[obj] & ctx->incidence[i*ctx->nb_word_obj + obj];
            }

        }
    }
    return extent;
}

/*Soit B un un ens d attribut la fonction renvoie l ens de tous les objet qui ont comme attribut tous les 
   les attribut de B  et c est B'*/
static word* derive_intent(const FormalContext *ctx,const word *intent ){
    word *extent=calloc(ctx->nb_word_obj,sizeof(word));
    
    if(extent==NULL){
        fprintf(stderr, "Erreur d allocation d extent dans derive_intent.\n");
        return NULL;
    }
    for (size_t g=0;g<ctx->nb_obj;g++){
        extent[g/WORD_BITS]|=UINT64_C(1)<<g%WORD_BITS;
    }
    return intersection(ctx,extent,intent);


}


/* l extent passer a la fct doit avoir ces bit de remplissage a 0
   et la fct prent A=extent (a verifie) et retourne A'
   */
static word* derive_extent(const FormalContext *ctx,const word *extent ){
    word *intent=calloc(ctx->nb_word_att,sizeof(word));/*aloue de la mem pour stocker les attribue representer par des mots binaire 
    le bit de position i vaut 0 si l attribut i n est pas commun
    */
    if(intent==NULL){
        fprintf(stderr, "Erreur d allocation d intent dans derive_extent.\n");
        return NULL;
    }
    int V=1;

    /* on recupere les mots d attribut i et on regarde si extent inclus dans ces mots 
       si oui i est l un des attribut commun 
    */
    for(size_t i=0;i<ctx->nb_att;i++){
        V=1;
        for (size_t obj=0;obj<ctx->nb_word_obj;obj++){ /*on verifie chaque mot au cas on a plus de 64 objet */
            if (extent[obj] & ~ctx->incidence[i*ctx->nb_word_obj +obj]){ /* si extent[obj] n est pas inclus dans le mots d attibue i */
                V=0;
                break;
            }
        }
        if(V==1){
          intent[i/WORD_BITS]|=UINT64_C(1)<< i%WORD_BITS ; /* si V=1 alors extent est inclu dans le mots d attribut i donc
          i est un attribut commun*/
        }

    }
    return intent;    
}

/* rnevoi 1 si l ens est vide (ne contiet que 0 pour chaque mot) 0 sinon*/
static int test_vide(word *extent,size_t nb_mot){
    
    for(size_t i;i<nb_mot;i++){
        if(extent[i]!=0){
            return 0;
        }
    }
    return 1;
}

/* TODO : pour chaque B de 2^M, calculer B' puis B'' ; B est un intent ssi B'' = B.
   Ne garder que les concepts d'extent non vide. */

size_t enum_naive(const FormalContext *ctx, concept_cb cb, void *user)
{
    if(ctx->nb_att>63){
        fprintf(stderr, "Erreur nb_att trop grand calul trop long.\n");
        return 0;
    }
    word M=(word)1<<ctx->nb_att;
    size_t compt=0;
    for(word intent=0;intent<M;intent++){
        word *extent=derive_intent(ctx,&intent);
        if(extent!=NULL){

            word *extent_sec=derive_extent(ctx,extent);
            if(*extent_sec==intent){
                compt+=1;
                Concept C;
                C.extent=extent;
                C.intent=&intent;
                cb(ctx,&C,user);
            }
            
            free(extent_sec); 
        }
        
           
    }

    return compt;
}
