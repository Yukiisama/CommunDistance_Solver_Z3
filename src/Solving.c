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


// Differ a little from the formula of the rapport but is equivalent 
Z3_ast getIsPathFormula_PHI_1(Z3_context ctx, Graph graph,unsigned int numGraph, int pathLength){
	Z3_ast clause[1000];
	int indice_clause = 0;
	Z3_ast Or_clause[1000];
	int indice_Or_clause = 0;
	for(int position = 0; position<pathLength;position++){ 
		for(int u = 0; u<graph.numNodes;u++){
			for(int v = 0; v<graph.numNodes;v++){
				if(u!=v){
						//printf("%d : %s, ",node,graph.nodes[node]);//[DEBUG]
						//printf("%d : %d : %d : %d \n",numGraph, position, pathLength, node); //[DEBUG]
						Z3_ast xj = getNodeVariable(ctx, numGraph, position, pathLength, u);
						Z3_ast xj_1 = getNodeVariable(ctx, numGraph, position+1, pathLength, v);
						Z3_ast anOtherTab[2] = {xj,xj_1};
						clause[indice_clause] = Z3_mk_and(ctx,2,anOtherTab);
						//printf("We have now: %s\n\n",Z3_ast_to_string(ctx,clause[indice_clause])); //[DEBUG]
						indice_clause++;
					}
				}
			} 
		Or_clause[indice_Or_clause] = Z3_mk_or(ctx,indice_clause,clause);
		//printf("OR CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,Or_clause[indice_Or_clause])); //[DEBUG]
		indice_Or_clause++;
		indice_clause = 0;
	}
	Z3_ast And_clause = Z3_mk_and(ctx,indice_Or_clause,Or_clause);
	printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause));
	return And_clause;
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
	for(int i = 0; i<numGraphs;i++){ 
		Phi_1[i]= getIsPathFormula_PHI_1(ctx,graphs[i],i,pathLength);
		if(i!=numGraphs-1) printf("********************Next graph : ********************\n");
		//printf("Phi 1 : %d ", isFormulaSat(ctx,Phi_1[i]));
		switch (isFormulaSat(ctx,Phi_1[i]))
        {
        case Z3_L_FALSE:
            printf("%s is not satisfiable.\n",Z3_ast_to_string(ctx,Phi_1[i]));
            break;

        case Z3_L_UNDEF:
                printf("We don't know if %s is satisfiable.\n",Z3_ast_to_string(ctx,Phi_1[i]));
            break;

        case Z3_L_TRUE:
                printf("%s \nphi1 is satisfiable.\n",Z3_ast_to_string(ctx,Phi_1[i]));
				printf("***********************************************************\n");
                //Z3_model model = getModelFromSatFormula(ctx,Phi_1[i]);
                //printf("Model obtained for %s:\n",Z3_model_to_string(ctx,model));

                break;
        }

	}
}
