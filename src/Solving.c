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
	//printf("Variable %s created.\n",Z3_ast_to_string(ctx,x));
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

/**
 * @param ctx The solver context.
 * @param graph The graph
 * @param numGraph The number of the graph
 * @param pathLength The length of the path to check.
 * @return Z3_ast The formula phi 4.
*  @brief : Differ a little from the formula phi 4 of the rapport but is equivalent , Check if for each vertex u
* ,u can't be at j-th and e-th position of a simple path of pathlenght
*/

Z3_ast getIsPathFormula_PHI_4(Z3_context ctx, Graph graph,unsigned int numGraph, int pathLength){
	printf("BEGIN PHI 4 \n");
	Z3_ast clause[1000];
	int indice_clause = 0;
	Z3_ast And_clause[1000];
	int indice_And_clause = 0;

	for(int u = 0; u<graph.numNodes;u++){
		for(int position1 = 0; position1<=pathLength;position1++){
			for(int position2 = 0; position2<=pathLength;position2++){
				if(position1!=position2){
					Z3_ast xj = getNodeVariable(ctx, numGraph, position1, pathLength, u);
					Z3_ast xj_1 = getNodeVariable(ctx, numGraph, position2, pathLength, u);
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
	printf("END PHI 4 \n");
	return And_final_clause;

}


/**
 * @param ctx The solver context.
 * @param graph The graph
 * @param numGraph The number of the graph
 * @param pathLength The length of the path to check.
 * @return Z3_ast The formula phi 4.
*  @brief : Differ a little from the formula phi 4 of the rapport but is equivalent , Check if the source is the first vertex , and the target the last
*/

Z3_ast getIsPathFormula_PHI_5(Z3_context ctx, Graph graph,unsigned int numGraph, int pathLength){
	printf("BEGIN PHI 5 \n");
	int source,target;
	for(int u = 0; u<graph.numNodes;u++){
		if(isSource(graph, u)) source = u;
		if(isTarget(graph, u)) target = u;
	}
	Z3_ast xj_source = getNodeVariable(ctx, numGraph, 0, pathLength, source);
	Z3_ast xj_target = getNodeVariable(ctx, numGraph, graph.numNodes-1, pathLength, target);
	Z3_ast tab[2] = {xj_source,xj_target};
	Z3_ast And_clause = Z3_mk_and(ctx,2,tab);
	printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause)); //[DEBUG]
	printf("END PHI 5 \n");

	return And_clause;
}

Z3_ast Concat_sub_formulas(Z3_context ctx, Graph * graphs,unsigned int i, int pathLength){
		Z3_ast Phi_1= getIsPathFormula_PHI_1(ctx,graphs[i],i,pathLength);
		Z3_ast Phi_2= getIsPathFormula_PHI_2(ctx,graphs[i],i,pathLength);
		Z3_ast Phi_3= getIsPathFormula_PHI_3(ctx,graphs[i],i,pathLength);
		Z3_ast Phi_4= getIsPathFormula_PHI_4(ctx,graphs[i],i,pathLength);
		Z3_ast Phi_5= getIsPathFormula_PHI_5(ctx,graphs[i],i,pathLength);
		Z3_ast tab[5] = {Phi_1,Phi_2,Phi_3,Phi_4,Phi_5};
		Z3_ast And_sub_formulas = Z3_mk_and(ctx,5,tab);
		//printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_sub_formulas)); //[DEBUG]
		return And_sub_formulas;
		
}

void check_satisfiable(Z3_context ctx,Z3_ast f,const char * str, int number){
	if(number!=-1){
		printf("Check Satisfiable for %s \n",str);
		switch (isFormulaSat(ctx,f))
			{
			case Z3_L_FALSE:
				printf("%s number %d is not satisfiable.\n",Z3_ast_to_string(ctx,f),number);
				break;

			case Z3_L_UNDEF:
					printf("We don't know if %s number %d is satisfiable.\n",Z3_ast_to_string(ctx,f),number);
				break;

			case Z3_L_TRUE:
					printf("%s \n %s number %d is satisfiable.\n",Z3_ast_to_string(ctx,f),str,number);
					printf("********************END CHECK SATISFIABLE***************************************\n");
					//Z3_model model = getModelFromSatFormula(ctx,Phi_1[i]);
					//printf("Model obtained for %s:\n",Z3_model_to_string(ctx,model));
					break;
			}
	}
	else{
		switch (isFormulaSat(ctx,f))
			{
			printf("Check Satisfiable for %s number %d \n",str,number);
			case Z3_L_FALSE:
				printf("%s is not satisfiable.\n",Z3_ast_to_string(ctx,f));
				break;

			case Z3_L_UNDEF:
					printf("We don't know if %s is satisfiable.\n",Z3_ast_to_string(ctx,f),str);
				break;

			case Z3_L_TRUE:
					printf("%s \n %s is satisfiable.\n",Z3_ast_to_string(ctx,f),str);
					printf("********************END CHECK SATISFIABLE***************************************\n");
					//Z3_model model = getModelFromSatFormula(ctx,Phi_1[i]);
					//printf("Model obtained for %s:\n",Z3_model_to_string(ctx,model));
					break;
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
	Z3_ast Sub_Formulas_Concat[numGraphs];
	for(int i = 0; i<numGraphs;i++){ 
		Sub_Formulas_Concat[i] = Concat_sub_formulas(ctx,graphs,i,pathLength);
		check_satisfiable(ctx, Sub_Formulas_Concat[i] ,"Sub_formulas_concat",i);
		if(i!=numGraphs-1) printf("*********Graph %d done ***********Next graph : ********************\n",i);
	}
	Z3_ast Allgraph_formula = Z3_mk_and(ctx,numGraphs,Sub_Formulas_Concat); 
	printf("Allgraph_formula : \n  %s created.\n",Z3_ast_to_string(ctx,Allgraph_formula)); //[DEBUG]
	return Allgraph_formula;
	
}


/**
 * @brief Generates a SAT formula satisfiable if and only if all graphs of @p graphs contain an accepting path of common length.
 * 
 * @param ctx The solver context.
 * @param graphs An array of graphs.
 * @param numGraphs The number of graphs in @p graphs.
 * @return Z3_ast The formula.
 */
Z3_ast graphsToFullFormula( Z3_context ctx, Graph *graphs,unsigned int numGraphs){
	int Min_numberNodesAllgraphs = orderG(graphs[0]);
	for(int i = 1;i < numGraphs;i++)
	{
		if(Min_numberNodesAllgraphs > orderG(graphs[i]))
			Min_numberNodesAllgraphs = orderG(graphs[i]);
	}
	Z3_ast Formulas_for_k_lenght_Concat[Min_numberNodesAllgraphs];
	for(int pathLength = 1 ; pathLength < Min_numberNodesAllgraphs; pathLength++){
		//pathLenght-1 Because the case 0 is empty( LenghtPath= 0 impossible) so we fill it 
		Formulas_for_k_lenght_Concat[pathLength-1] = graphsToPathFormula(ctx,graphs,numGraphs,pathLength);
	}
	//Min_numberNodesAllgraphs-1 cause we have started writed to case 0 the formula for LenghtPath = 1
	Z3_ast Full_formula = Z3_mk_and(ctx,Min_numberNodesAllgraphs-1,Formulas_for_k_lenght_Concat); 
	printf("Full_formula : \n  %s created.\n",Z3_ast_to_string(ctx,Full_formula)); //[DEBUG]
	check_satisfiable(ctx, Full_formula ,"FULL FORMULA",-1);
	return Full_formula;
}