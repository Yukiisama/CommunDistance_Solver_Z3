#include <stdio.h>
#include <string.h>
#include "Z3Tools.h"
#include "Graph.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
extern int sflag;
extern int aflag;
static int number_graphs = 0;
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
Z3_ast getNodeVariable(Z3_context ctx, int number, int position, int k, int node)
{
	char s[50];
	if (number < 0 || position < 0 || k < 0 || node < 0)
		fprintf(stderr, "getNodeVariable wrong arguments must be positive\n");
	// This line is intented to give the number of graphs when i will use
	// getSolutionLengthFromModel because numgraphs was not given
	if (number + 1 > number_graphs)
		number_graphs = number + 1;
	sprintf(s, "x%d,%d,%d,%d", number, position, k, node);
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

Z3_ast getIsPathFormula_PHI_1(Z3_context ctx, Graph graph, unsigned int numGraph, int pathLength)
{
	//printf("BEGIN PHI 1 \n");
	Z3_ast clause[100000];
	int indice_clause = 0;
	Z3_ast And_clause[100000];
	int indice_And_clause = 0;
	for (int position = 0; position < pathLength; position++)
	{ //j
		for (int u = 0; u < graph.numNodes; u++)
		{
			for (int v = 0; v < graph.numNodes; v++)
			{
				if (!isEdge(graph, u, v))
				{
					//printf("%d : %s, ", u, graph.nodes[u]); //[DEBUG]
					//printf("%d : %s, ",v,graph.nodes[v]);//[DEBUG]
					//printf("%d : %d : %d : %d : %d \n",numGraph, position, pathLength, u,v); //[DEBUG]
					Z3_ast xj = getNodeVariable(ctx, numGraph, position, pathLength, u);
					Z3_ast xj_1 = getNodeVariable(ctx, numGraph, position + 1, pathLength, v);
					Z3_ast negxj = Z3_mk_not(ctx, xj);
					Z3_ast negxj_1 = Z3_mk_not(ctx, xj_1);
					Z3_ast anOtherTab[2] = {negxj, negxj_1};
					clause[indice_clause] = Z3_mk_or(ctx, 2, anOtherTab);
					//printf("We have now: %s\n\n",Z3_ast_to_string(ctx,clause[indice_clause])); //[DEBUG]
					indice_clause++;
				}
			}
		}
		And_clause[indice_And_clause] = Z3_mk_and(ctx, indice_clause, clause);
		//printf("OR CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,Or_clause[indice_Or_clause])); //[DEBUG]
		indice_And_clause++;
		indice_clause = 0;
	}
	Z3_ast And_final_clause = Z3_mk_and(ctx, indice_And_clause, And_clause);
	//printf("AND FINAL CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_final_clause));
	//printf("END PHI 1 \n");
	return And_final_clause;
}

/**
 * @param ctx The solver context.
 * @param graph The graph.
 * @param numGraph The number of the graph
 * @param pathLength The length of the path to check.
 * @return Z3_ast The formula phi 2.
*  @brief : Differ a little from the formula phi 2 of the rapport but is equivalent , Check if for each j there is 
* at least one vertex which is the j-th vertex of a simple path of pathlenght
*/

Z3_ast getIsPathFormula_PHI_2(Z3_context ctx, Graph graph, unsigned int numGraph, int pathLength)
{
	//printf("BEGIN PHI 2 \n");
	Z3_ast clause[100000];
	int indice_clause = 0;
	Z3_ast Or_clause[100000];
	int indice_Or_clause = 0;

	for (int position = 0; position <= pathLength; position++)
	{
		for (int u = 0; u < graph.numNodes; u++)
		{
			clause[indice_clause] = getNodeVariable(ctx, numGraph, position, pathLength, u);
			indice_clause++;
		}
		Or_clause[indice_Or_clause] = Z3_mk_or(ctx, indice_clause, clause);
		//printf("OR CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,Or_clause[indice_Or_clause])); //[DEBUG]
		indice_Or_clause++;
		indice_clause = 0;
	}
	Z3_ast And_clause = Z3_mk_and(ctx, indice_Or_clause, Or_clause);
	//printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause));
	//printf("END PHI 2 \n");
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

Z3_ast getIsPathFormula_PHI_3(Z3_context ctx, Graph graph, unsigned int numGraph, int pathLength)
{
	//printf("BEGIN PHI 3 \n");
	Z3_ast clause[100000];
	int indice_clause = 0;
	Z3_ast And_clause[100000];
	int indice_And_clause = 0;
	for (int position = 0; position <= pathLength; position++)
	{ //j
		for (int u = 0; u < graph.numNodes; u++)
		{
			for (int v = 0; v < graph.numNodes; v++)
			{
				if (u != v)
				{
					Z3_ast xj = getNodeVariable(ctx, numGraph, position, pathLength, u);
					Z3_ast xj_1 = getNodeVariable(ctx, numGraph, position, pathLength, v);
					Z3_ast negxj = Z3_mk_not(ctx, xj);
					Z3_ast negxj_1 = Z3_mk_not(ctx, xj_1);
					Z3_ast anOtherTab[2] = {negxj, negxj_1};
					clause[indice_clause] = Z3_mk_or(ctx, 2, anOtherTab);
					indice_clause++;
				}
			}
		}
		And_clause[indice_And_clause] = Z3_mk_and(ctx, indice_clause, clause);
		//printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause[indice_And_clause])); //[DEBUG]
		indice_And_clause++;
		indice_clause = 0;
	}
	Z3_ast And_final_clause = Z3_mk_and(ctx, indice_And_clause, And_clause);
	//printf("AND FINAL CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_final_clause)); //[DEBUG]
	//printf("END PHI 3 \n");
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

Z3_ast getIsPathFormula_PHI_4(Z3_context ctx, Graph graph, unsigned int numGraph, int pathLength)
{
	//printf("BEGIN PHI 4 \n");
	Z3_ast clause[100000];
	int indice_clause = 0;
	Z3_ast And_clause[100000];
	int indice_And_clause = 0;

	for (int u = 0; u < graph.numNodes; u++)
	{
		for (int position1 = 0; position1 <= pathLength; position1++)
		{
			for (int position2 = 0; position2 <= pathLength; position2++)
			{
				if (position1 != position2)
				{
					Z3_ast xj = getNodeVariable(ctx, numGraph, position1, pathLength, u);
					Z3_ast xj_1 = getNodeVariable(ctx, numGraph, position2, pathLength, u);
					Z3_ast negxj = Z3_mk_not(ctx, xj);
					Z3_ast negxj_1 = Z3_mk_not(ctx, xj_1);
					Z3_ast anOtherTab[2] = {negxj, negxj_1};
					clause[indice_clause] = Z3_mk_or(ctx, 2, anOtherTab);
					indice_clause++;
				}
			}
		}
		And_clause[indice_And_clause] = Z3_mk_and(ctx, indice_clause, clause);
		//printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause[indice_And_clause])); //[DEBUG]
		indice_And_clause++;
		indice_clause = 0;
	}

	Z3_ast And_final_clause = Z3_mk_and(ctx, indice_And_clause, And_clause);
	//printf("AND FINAL CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_final_clause)); //[DEBUG]
	//printf("END PHI 4 \n");
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

Z3_ast getIsPathFormula_PHI_5(Z3_context ctx, Graph graph, unsigned int numGraph, int pathLength)
{
	//printf("BEGIN PHI 5 \n");
	int source, target;
	for (int u = 0; u < graph.numNodes; u++)
	{
		if (isSource(graph, u))
			source = u;
		if (isTarget(graph, u))
			target = u;
	}
	Z3_ast xj_source = getNodeVariable(ctx, numGraph, 0, pathLength, source);
	Z3_ast xj_target = getNodeVariable(ctx, numGraph, pathLength, pathLength, target);
	Z3_ast tab[2] = {xj_source, xj_target};
	Z3_ast And_clause = Z3_mk_and(ctx, 2, tab);
	//printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_clause)); //[DEBUG]
	//printf("END PHI 5 \n");

	return And_clause;
}



void check_satisfiable(Z3_context ctx, Z3_ast f, const char *str, int number)
{
	if (number != -1)
	{
		printf("Check Satisfiable for %s \n", str);
		switch (isFormulaSat(ctx, f))
		{
		case Z3_L_FALSE:
			printf("%s number %d is not satisfiable.\n", Z3_ast_to_string(ctx, f), number);
			break;

		case Z3_L_UNDEF:
			printf("We don't know if %s number %d is satisfiable.\n", Z3_ast_to_string(ctx, f), number);
			break;

		case Z3_L_TRUE:
			printf("%s \n %s number %d is satisfiable.\n", Z3_ast_to_string(ctx, f), str, number);
			printf("********************END CHECK SATISFIABLE***************************************\n");
			//Z3_model model = getModelFromSatFormula(ctx,Phi_1[i]);
			//printf("Model obtained for %s:\n",Z3_model_to_string(ctx,model));
			break;
		}
	}
	else
	{
		printf("Check Satisfiable for %s number %d \n", str, number);
		switch (isFormulaSat(ctx, f))
		{
			printf("Check Satisfiable for %s number %d \n", str, number);
		case Z3_L_FALSE:
			printf("%s is not satisfiable.\n", Z3_ast_to_string(ctx, f));
			break;

		case Z3_L_UNDEF:
			printf("We don't know if %s is satisfiable.\n", Z3_ast_to_string(ctx, f), str);
			break;

		case Z3_L_TRUE:
			printf("%s \n %s is satisfiable.\n", Z3_ast_to_string(ctx, f), str);
			printf("********************END CHECK SATISFIABLE***************************************\n");
			//Z3_model model = getModelFromSatFormula(ctx,f);
			//printf("Model obtained for %s:\n",Z3_model_to_string(ctx,model));

			break;
		}
	}
}

Z3_ast Concat_sub_formulas(Z3_context ctx, Graph *graphs, unsigned int i, int pathLength)
{
	Z3_ast Phi_1 = getIsPathFormula_PHI_1(ctx, graphs[i], i, pathLength);
	Z3_ast Phi_2 = getIsPathFormula_PHI_2(ctx, graphs[i], i, pathLength);
	Z3_ast Phi_3 = getIsPathFormula_PHI_3(ctx, graphs[i], i, pathLength);
	Z3_ast Phi_4 = getIsPathFormula_PHI_4(ctx, graphs[i], i, pathLength);
	Z3_ast Phi_5 = getIsPathFormula_PHI_5(ctx, graphs[i], i, pathLength);

	/*check_satisfiable(ctx, Phi_1 ,"Check Phi ",1);
		check_satisfiable(ctx, Phi_2 ,"Check Phi ",2);
		check_satisfiable(ctx, Phi_3 ,"Check Phi ",3);
		check_satisfiable(ctx, Phi_4 ,"Check Phi ",4);
		check_satisfiable(ctx, Phi_5 ,"Check Phi ",5);*/
	Z3_ast tab[5] = {Phi_1, Phi_2, Phi_3, Phi_4, Phi_5};
	Z3_ast And_sub_formulas = Z3_mk_and(ctx, 5, tab);
	//check_satisfiable(ctx, And_sub_formulas, "Check all formulas ", -1);
	if (isFormulaSat(ctx, And_sub_formulas) == Z3_L_TRUE)
	{
		Z3_model model = getModelFromSatFormula(ctx, And_sub_formulas);
		//printf("Model obtained for %s:\n", Z3_model_to_string(ctx, model));
		//printf("PHI 1 W MODEL : %d \n", valueOfVarInModel(ctx, model, Phi_1));
		//printf("PHI 2 W MODEL : %d \n", valueOfVarInModel(ctx, model, Phi_2));
		//printf("PHI 3 W MODEL : %d \n", valueOfVarInModel(ctx, model, Phi_3));
		//printf("PHI 4 W MODEL : %d \n", valueOfVarInModel(ctx, model, Phi_4));
		//printf("PHI 5 W MODEL : %d \n", valueOfVarInModel(ctx, model, Phi_5));
	}
	//printf("AND CLAUSE : \n  %s created.\n",Z3_ast_to_string(ctx,And_sub_formulas)); //[DEBUG]
	return And_sub_formulas;
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
Z3_ast graphsToPathFormula(Z3_context ctx, Graph *graphs, unsigned int numGraphs, int pathLength)
{
	/**********************************Get Sub_Formulas***************************************/
	Z3_ast x = getNodeVariable(ctx, 0, 0, 0, 0);
	Z3_ast notx = Z3_mk_not(ctx, x);
	Z3_ast t[2] = {x, notx};
	if (pathLength < 1)
	{
		//printf("pathLength %d : %d  \n", pathLength, -1);
		return Z3_mk_and(ctx, 2, t);
	}

	Z3_ast Sub_Formulas_Concat[numGraphs];
	for (int i = 0; i < numGraphs; i++)
	{
		Sub_Formulas_Concat[i] = Concat_sub_formulas(ctx, graphs, i, pathLength);
		//check_satisfiable(ctx, Sub_Formulas_Concat[i] ,"Sub_formulas_concat",i);
		//if (i != numGraphs - 1)
			//printf("*********Graph %d done ***********Next graph : ********************\n", i);
	}
	Z3_ast Allgraph_formula = Z3_mk_and(ctx, numGraphs, Sub_Formulas_Concat);

	//printf("Allgraph_formula : \n  %s created.\n",Z3_ast_to_string(ctx,Allgraph_formula)); //[DEBUG]
	//check_satisfiable(ctx, Allgraph_formula ,"Check formula graph ",pathLength);
	
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
Z3_ast graphsToFullFormula(Z3_context ctx, Graph *graphs, unsigned int numGraphs)
{
	int Min_numberNodesAllgraphs = orderG(graphs[0]);
	for (int i = 1; i < numGraphs; i++)
	{
		if (Min_numberNodesAllgraphs > orderG(graphs[i]))
			Min_numberNodesAllgraphs = orderG(graphs[i]);
	}
	Z3_ast Formulas_for_k_lenght_Concat[Min_numberNodesAllgraphs];
	for (int pathLength = 1; pathLength < Min_numberNodesAllgraphs; pathLength++)
	{
		//pathLenght-1 Because the case 0 is empty( LenghtPath= 0 impossible) so we fill it
		Formulas_for_k_lenght_Concat[pathLength - 1] = graphsToPathFormula(ctx, graphs, numGraphs, pathLength);
	}
	//Min_numberNodesAllgraphs-1 cause we have started writed to case 0 the formula for LenghtPath = 1
	Z3_ast Full_formula = Z3_mk_or(ctx, Min_numberNodesAllgraphs - 1, Formulas_for_k_lenght_Concat);
	
	/** AMELIORATION STEP : We want only valuation of the found pathLength to be true **/
	//Voir pour améliorer --> trouver une formule qui dit que si y'a un chemin , tous les autres sommets doivent être faux
	
	//printf("Full_formula : \n  %s created.\n",Z3_ast_to_string(ctx,Full_formula)); //[DEBUG]
	//check_satisfiable(ctx, Full_formula, "FULL FORMULA", -1);
	return Full_formula;
}
/**
 * @brief Gets the length of the solution from a given model.
 * 
 * @param ctx The solver context.
 * @param model A variable assignment.
 * @param graphs An array of graphs.
 * @return int The length of a common simple accepting path in all graphs from @p graphs.
 */
int getSolutionLengthFromModel(Z3_context ctx, Z3_model model, Graph *graphs)
{

	int Min_numberNodesAllgraphs = orderG(graphs[0]);
	for (int i = 1; i < number_graphs; i++)
	{
		if (Min_numberNodesAllgraphs > orderG(graphs[i]))
			Min_numberNodesAllgraphs = orderG(graphs[i]);
	}
	for (int j = 0; j <= Min_numberNodesAllgraphs; j++)
	{
		Z3_ast Path_formula = graphsToPathFormula(ctx, graphs, number_graphs, j);
		if (valueOfVarInModel(ctx, model, Path_formula))
		{
			printf("There is a simple valid path of length %d in all graphs  \n", j);
			return j;
		}
	}
	printf("No simple valid path in all graphs  \n");
	return 0;
}

/**
 * @brief Displays the paths of length @p pathLength of each graphs in @p graphs described by @p model.
 * 
 * @param ctx The solver context.
 * @param model A variable assignment.
 * @param graphs An array of graphs.
 * @param numGraph The number of graphs in @p graphs.
 * @param pathLength The length of path.
 */
void printPathsFromModel(Z3_context ctx, Z3_model model, Graph *graphs, int numGraph, int pathLength)
{
	int indice_trueVal = 0;
	int size_model = Z3_model_get_num_consts(ctx, model);
	int nbgraph[size_model], pos[size_model], path[size_model], vertex[size_model];
	for (int counter = 0; counter < size_model; counter++)
	{
		Z3_func_decl f = Z3_model_get_const_decl(ctx, model, counter);
		//printf("TEST 1 : %s", Z3_func_decl_to_string(ctx, f));
		//printf("TEST 1 : %s", Z3_ast_to_string(ctx, Z3_model_get_const_interp(ctx, model, f)));
		//printf(" ICI Model obtained of len %d for %s:\n",i,Z3_model_to_string(ctx,model));
		if (strcmp(Z3_ast_to_string(ctx, Z3_model_get_const_interp(ctx, model, f)), "true") == 0)
		{
			const char *tmp = Z3_func_decl_to_string(ctx, f);
			sscanf(tmp, "(declare-fun |x%d,%d,%d,%d|%*s", &nbgraph[indice_trueVal], &pos[indice_trueVal], &path[indice_trueVal], &vertex[indice_trueVal]);
			//printf("\nICI :|x%d,%d,%d,%d| , value = %s \n", nbgraph[indice_trueVal], pos[indice_trueVal], path[indice_trueVal], vertex[indice_trueVal], Z3_ast_to_string(ctx, Z3_model_get_const_interp(ctx, model, f)));
			indice_trueVal++;
		}
	}
	//end for
	
	for (int i = 0; i < numGraph; i++)
	{
		printf("Path in graph %d \n", i);
		for (int position = 0; position < graphs[i].numNodes; position++)
		{
			for (int x = 0; x < indice_trueVal; x++)
			{
				if (position == pos[x] && i == nbgraph[x])
					printf("%d: pos %d: %s %s", nbgraph[x], pos[x], getNodeName(graphs[nbgraph[x]], vertex[x]), (position != pathLength) ? "->" : "");
			}
		}
		printf("\n");
	}
}
/**
 * @brief Creates the file ("%s-l%d.dot",name,pathLength) representing the solution to the problem described by @p model, or ("result-l%d.dot,pathLength") if name is NULL.
 * 
 * @param ctx The solver context.
 * @param model A variable assignment.
 * @param graphs An array of graphs.
 * @param numGraph The number of graphs in @p graphs.
 * @param pathLength The length of path.
 * @param name The name of the output file.
 */
void createDotFromModel(Z3_context ctx, Z3_model model, Graph *graphs, int numGraph, int pathLength, char *name)
{
	char title[1000];
	char title_diagraph[1000];
	if (name)
	{
		sprintf(title, "sol/%s-l%d.dot", name, pathLength);
		sprintf(title_diagraph, "%s_l%d", name, pathLength);
	}
	else
	{
		sprintf(title, "sol/result-l%d.dot", pathLength);
		sprintf(title_diagraph, "result_l%d", pathLength);
	}
	FILE *file;
	struct stat st = {0};

	if (stat("sol", &st) == -1) {
		mkdir("sol", 0777);
	}

	file = fopen(title, "w");
	if (file == NULL)
	{
		printf("Unable to create file.\n");
		//exit(EXIT_FAILURE);
	}
	int source, target;
	//PENSER A ITERAL SUR CHAQUE GRAPH
	int numgraph_actual = 0;
	fprintf(file, "digraph %s{\n", title_diagraph);
	for (numgraph_actual = 0; numgraph_actual < numGraph; numgraph_actual++)
	{
		for (int u = 0; u < graphs[numgraph_actual].numNodes; u++)
		{
			if (isSource(graphs[numgraph_actual], u)) // deplacer fprintf source ici
			{
				source = u;
				char *source_str = getNodeName(graphs[numgraph_actual], source);
				fprintf(file, "_%d_%s [initial=1,color=green][style=filled,fillcolor=lightblue];\n", numgraph_actual, source_str);
				continue;
			}

			if (isTarget(graphs[numgraph_actual], u)) // deplacer fprintf target ici
			{
				target = u;
				char *target_str = getNodeName(graphs[numgraph_actual], target);
				fprintf(file, "_%d_%s [final=1,color=red][style=filled,fillcolor=lightblue];\n", numgraph_actual, target_str);
				continue;
			}

			for (int position = 0; position <= pathLength; position++)
			{
				Z3_ast variable = getNodeVariable(ctx, numgraph_actual, position, pathLength, u);

				char *u_str = getNodeName(graphs[numgraph_actual], u);

				if (valueOfVarInModel(ctx, model, variable) == true)
				{
					fprintf(file, "_%d_%s [style=filled,fillcolor=lightblue];\n", numgraph_actual, u_str);
					break;
				}

				else if (position == pathLength - 1)
				{
					fprintf(file, "_%d_%s ;\n", numgraph_actual, u_str);
				}
			}
		}
		int written = 0;
		//Faire les arêtes + arêtes chemins
		for (int u = 0; u < graphs[numgraph_actual].numNodes; u++)
		{
			for (int v = 0; v < graphs[numgraph_actual].numNodes; v++)
			{
				for (int position = 0; position < graphs[numgraph_actual].numNodes; position++)
				{
					for (int position2 = 0; position2 < graphs[numgraph_actual].numNodes; position2++)
					{
						Z3_ast variable = getNodeVariable(ctx, numgraph_actual, position, pathLength, u);
						Z3_ast variable2 = getNodeVariable(ctx, numgraph_actual, position2, pathLength, v);
						if (isEdge(graphs[numgraph_actual], u, v) && valueOfVarInModel(ctx, model, variable) == true && valueOfVarInModel(ctx, model, variable2) == true && position2 == position + 1)
						{
							char *u_str = getNodeName(graphs[numgraph_actual], u);
							char *v_str = getNodeName(graphs[numgraph_actual], v);
							fprintf(file, "_%d_%s -> _%d_%s [color=blue];\n", numgraph_actual, u_str, numgraph_actual, v_str);
							written = 1;
						}
						else if (isEdge(graphs[numgraph_actual], u, v) && written == 0 && position2 == graphs[numgraph_actual].numNodes - 1 && position == graphs[numgraph_actual].numNodes - 1)
						{
							char *u_str = getNodeName(graphs[numgraph_actual], u);
							char *v_str = getNodeName(graphs[numgraph_actual], v);
							fprintf(file, "_%d_%s -> _%d_%s ;\n", numgraph_actual, u_str, numgraph_actual, v_str);
							written = 1;
						}
					}
				}
				written = 0;
			}
		}
	}
	fprintf(file, "}\n");

	fclose(file);
}
