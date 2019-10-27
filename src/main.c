#include <Graph.h>
#include <Parsing.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "Z3Tools.h"
#include "Solving.h"
void usage(){
    printf("Usage: graphParser file\n");
    printf(" Displays information on the graph discribed by file. It should be provided with a .dot file\n");
}

int main(int argc, char* argv[]){
     if(argc<2) {
        usage();
        return 0;
    }
    /*************************************Init and first test getNodeVariable*****************/
    Z3_context ctx = makeContext();
    printf("Creating the context. Must be destroyed at the end of the program.\n");
	int number = 1;
	int position = 1;
	int k = 1;
	int node = 1;
    //getNodeVariable(ctx, number, position, k, node);
    /*************************************Draw graphs****************************************/
    int numGraphs = argc-1;
    int pathLength = 2;
    Graph graphs[argc-1];
    for (int i = 0; i < argc-1; ++i) // Il faudra penser à prendre en compte les options etc
    {
        graphs[i] = getGraphFromFile(argv[i+1]);
        //printGraph(graphs[i]);
    }
    /***************************Exec graphsToPathFormula**************************************/
    graphsToPathFormula(ctx,graphs,numGraphs,pathLength);
    
    /***************************Clear Memory*************************************/
    printf("Context deleted, memory is now clean.\n");
    Z3_del_context(ctx);
    return 0;
}
