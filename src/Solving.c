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
 * @param ctx The solver context.
 * @param graph The graph
 * @param numGraph The number of the graph
 * @param pathLength The length of the path to check.
 * @return Z3_ast The formula phi 1.
*  @brief : Differ a little from the formula phi 1 of the rapport but is equivalent , Check if the solution is a path
*/

Z3_ast getIsPathFormula_PHI_1(Z3_context ctx, Graph graph,unsigned int numGraph, int pathLength){
	printf("BEGIN PHI 1 \n");
	Z3_ast clause[1000];
	int indice_clause = 0;
	Z3_ast And_clause[1000];
	int indice_And_clause = 0;
	for(int position = 0; position<pathLength;position++){ //j
		for(int u = 0; u<graph.numNodes;u++){
			for(int v = 0; v<graph.numNodes;v++){
				if(u!=v && !isEdge(graph,u,v)){
						//printf("%d : %s, ",node,graph.nodes[node]);//[DEBUG]
						//printf("%d : %d : %d : %d \n",numGraph, position, pathLength, node); //[DEBUG]
						Z3_ast xj = getNodeVariable(ctx, numGraph, position, pathLength, u);
						Z3_ast xj_1 = getNodeVariable(ctx, numGraph, position+1, pathLength, v);
						Z3_ast negxj = Z3_mk_not(ctx,xj);
						Z3_ast negxj_1 = Z3_mk_not(ctx,xj_1);
						Z3_ast anOtherTab[2] = {negxj,negxj_1};
						clause[indice_clause] = Z3_mk_or(ctx,2,anOtherTab);
						//printf("We have now: %s\n\n",Z3_ast_to_string(ctx,clause[indice_clause])); //[DEBUG]
						indice_clause++;
					}
				}
			} 
		And_clause[indice_And_clause] = Z3_mk_and(ctx,indice_clause,clause);
		//printf("OR CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,Or_clause[indice_Or_clause])); //[DEBUG]
		indice_And_clause++;
		indice_clause = 0;
	}
	Z3_ast And_final_clause = Z3_mk_and(ctx,indice_And_clause,And_clause);
	printf("AND FINAL CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_final_clause));
	printf("END PHI 1 \n");
	return And_final_clause;
}


/**
 * @param ctx The solver context.
 * @param graph The graph
 * @param numGraph The number of the graph
 * @param pathLength The length of the path to check.
 * @return Z3_ast The formula phi 2.
*  @brief : Differ a little from the formula phi 2 of the rapport but is equivalent , Check if for each j there is 
* at least one vertex which is the j-th vertex of a simple path of pathlenght
*/

Z3_ast getIsPathFormula_PHI_2(Z3_context ctx, Graph graph,unsigned int numGraph, int pathLength){
	printf("BEGIN PHI 2 \n");
	Z3_ast clause[1000];
	int indice_clause = 0;
	Z3_ast Or_clause[1000];
	int indice_Or_clause = 0;

	for(int position = 0; position<=pathLength;position++){ 
		for(int u = 0; u<graph.numNodes;u++){
			clause[indice_clause] = getNodeVariable(ctx, numGraph, position, pathLength, u);
			indice_clause++;

		}
		Or_clause[indice_Or_clause] = Z3_mk_or(ctx,indice_clause,clause);
		//printf("OR CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,Or_clause[indice_Or_clause])); //[DEBUG]
		indice_Or_clause++;
		indice_clause = 0;
	}
	Z3_ast And_clause = Z3_mk_and(ctx,indice_Or_clause,Or_clause);
	printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause));
	printf("END PHI 2 \n");
	return And_clause;
}


/**
 * @param ctx The solver context.
 * @param graph The graph
 * @param numGraph The number of the graph
 * @param pathLength The length of the path to check.
 * @return Z3_ast The formula phi 3.
*  @brief : Differ a little from the formula phi 3 of the rapport but is equivalent , Check if for each j there isn't
* two vertex which is the j-th vertex of a simple path of pathlenght
*/

Z3_ast getIsPathFormula_PHI_3(Z3_context ctx, Graph graph,unsigned int numGraph, int pathLength){
	printf("BEGIN PHI 3 \n");
	Z3_ast clause[1000];
	int indice_clause = 0;
	Z3_ast And_clause[1000];
	int indice_And_clause = 0;
	for(int position = 0; position<=pathLength;position++){ //j
		for(int u = 0; u<graph.numNodes;u++){
			for(int v = 0; v<graph.numNodes;v++){
				if(u!=v){
						Z3_ast xj = getNodeVariable(ctx, numGraph, position, pathLength, u);
						Z3_ast xj_1 = getNodeVariable(ctx, numGraph, position, pathLength, v);
						Z3_ast negxj = Z3_mk_not(ctx,xj);
						Z3_ast negxj_1 = Z3_mk_not(ctx,xj_1);
						Z3_ast anOtherTab[2] = {negxj,negxj_1};
						clause[indice_clause] = Z3_mk_or(ctx,2,anOtherTab);
						indice_clause++;
					}
				}
			} 
		And_clause[indice_And_clause] = Z3_mk_and(ctx,indice_clause,clause);
		//printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause[indice_And_clause])); //[DEBUG]
		indice_And_clause++;
		indice_clause = 0;
	}
	Z3_ast And_final_clause = Z3_mk_and(ctx,indice_And_clause,And_clause);
	printf("AND FINAL CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_final_clause)); //[DEBUG]
	printf("END PHI 3 \n");
	return And_final_clause;

}


void check_satisfiable(Z3_context ctx,Z3_ast f,const char * str){
	switch (isFormulaSat(ctx,f))
        {
        case Z3_L_FALSE:
            printf("%s is not satisfiable.\n",Z3_ast_to_string(ctx,f));
            break;

        case Z3_L_UNDEF:
                printf("We don't know if %s is satisfiable.\n",Z3_ast_to_string(ctx,f));
            break;

        case Z3_L_TRUE:
                printf("%s \n %s is satisfiable.\n",Z3_ast_to_string(ctx,f),str);
				printf("***********************************************************\n");
                //Z3_model model = getModelFromSatFormula(ctx,Phi_1[i]);
                //printf("Model obtained for %s:\n",Z3_model_to_string(ctx,model));

                break;
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
	Z3_ast Phi_2[numGraphs];
	Z3_ast Phi_3[numGraphs];
	for(int i = 0; i<numGraphs;i++){ 
		Phi_1[i]= getIsPathFormula_PHI_1(ctx,graphs[i],i,pathLength);
		Phi_2[i]= getIsPathFormula_PHI_2(ctx,graphs[i],i,pathLength);
		Phi_3[i]= getIsPathFormula_PHI_3(ctx,graphs[i],i,pathLength);
		if(i!=numGraphs-1) printf("********************Next graph : ********************\n");
		check_satisfiable(ctx, Phi_1[i] ,"PHI 1");
		check_satisfiable(ctx, Phi_2[i] ,"PHI 2");
		check_satisfiable(ctx, Phi_3[i] ,"PHI 3");
	}
}
