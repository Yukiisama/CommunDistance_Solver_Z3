#include <stdio.h>
#include "Z3Tools.h"
#include "Graph.h"
/**
 * @brief Generates a formula consisting of a variable representing the fact that @p node of graph number @p number is at position @p position of an accepting path.
 * 
 * @param ctx The solver context.
 * @param number The number of the graph.
 * @param position The position in the path.
 * @param k The mysterious k from the subject of this assignment.
 * @param node The node identifier.
 * @return Z3_ast The formula.
 */
Z3_ast getNodeVariable(Z3_context ctx, int number, int position, int k, int node){
	char s[50];
	if(number<0 || position<0 || k<0 || node < 0)
		fprintf(stderr, "getNodeVariable wrong arguments must be positive\n" ); 
		
	sprintf(s,"x%d,%d,%d,%d",number,position,k,node);
	Z3_ast x = mk_bool_var(ctx, s);
	printf("Variable %s created.\n",Z3_ast_to_string(ctx,x));
	return x;
	}

/**
* @param numGraph The indice of the graph .
*/
Z3_ast getIsPathFormula_PHI_1(Z3_context ctx, Graph graph,unsigned int numGraph, int pathLength){
	
	for(int node = 0; node<graph.numNodes;node++){
		for(int position = 0; position<pathLength;position++){ 
			//printf("%d : %s, ",node,graph.nodes[node]);
			//printf("%d : %d : %d : %d \n",numGraph, position, pathLength, node);
			getNodeVariable(ctx, numGraph, position, pathLength, node);
		}
	}
}

/**
 * @brief Generates a SAT formula satisfiable if and only if all graphs of @p graphs contain an accepting path of length @p pathLength.
 * 
 * @param ctx The solver context.
 * @param graphs An array of graphs.
 * @param numGraphs The number of graphs in @p graphs.
 * @param pathLength The length of the path to check.
 * @return Z3_ast The formula.
 */
Z3_ast graphsToPathFormula( Z3_context ctx, Graph *graphs,unsigned int numGraphs, int pathLength){

	/**********************************Get Sub_Formulas***************************************/
	Z3_ast Phi_1[numGraphs];
	//for(int i = 0; i<numGraphs;i++){ 
		Phi_1[0]= getIsPathFormula_PHI_1(ctx,graphs[1],1,pathLength);
	//}
}
