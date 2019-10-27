/**
 * @file NodeList.c
 * @author Vincent Penelle (vincent.penelle@u-bordeaux.fr)
 * @brief  Structure to store a list of graph nodes that can be dynamically modified. Used as a temporary structure during parsing before translating into a more static structure.
 *         Includes automata features (initial and final nodes).
 * @version 1
 * @date 2019-07-22
 * 
 * @copyright Creative Commons.
 * 
 */


#include "NodeList.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


/**
 * @brief Allocates space for node list
 * @return The expression or NULL if not enough memory
 */
static SNodeList *allocateNodeList()
{
    SNodeList *b = (SNodeList *)malloc(sizeof(SNodeList));

    if (b == NULL)
        return NULL;

    b->node = NULL;

    b->initial = false;
    b->final = false;

    b->next = NULL;

    return b;
}


SNodeList *addNode(char *n1, bool isInit, bool isFinal, SNodeList *list)
{
    SNodeList *b = allocateNodeList();

    if (b == NULL)
        return NULL;

    b->node = (char *)malloc((strlen(n1)+1)*sizeof(char));
    strcpy(b->node,n1);

    b->initial = isInit;
    b->final = isFinal;

    b->next = list;
	
    return b;
}

void addOrUpdateNode(char *n, bool isInit, bool isFinal, SNodeList *list)
{
    if (list == NULL)
    {
        return;
    }

    if (strcmp(list->node,n) != 0) 
    {
        if(list->next == NULL) list->next = addNode(n,isInit,isFinal,NULL);
        else addOrUpdateNode(n,isInit,isFinal,list->next);
        return;
    }

    list->initial = list->initial || isInit;
    list->final = list->final || isFinal;
    return;
}


void printNodeList(SNodeList *e)
{
    if(e == NULL) { printf("\n"); return;}
    printf("%s,%d,%d\n",e->node,e->initial,e->final);
	printNodeList(e->next);
}

void deleteNodeList(SNodeList *b)
{
    if (b == NULL)
        return;

    deleteNodeList(b->next);

    free(b->node);

    free(b);
}

/* Testing main.
int main (void){
    SNodeList *toto = NULL;
    toto = addNode("coucou",true,false,toto);
    toto = addNode("voilà",false,false,toto);
    addOrUpdateNode("coucou",false,true,toto);
    addOrUpdateNode("Hey",false,false,toto);
    SNodeList *arg = toto;
    while(arg!=NULL){
        printf("%s,%d,%d\n",arg->node,arg->initial,arg->final);
        arg=arg->next;
    }
    deleteNodeList(toto);
}
*/
