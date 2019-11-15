#include <Graph.h>
#include <Parsing.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "Z3Tools.h"
#include "Solving.h"
#include <ctype.h>

#include <unistd.h>
int hflag = 0;
int vflag = 0;
int Fflag = 0;
int sflag = 0;
int dflag = 0;
int aflag = 0;
int tflag = 0;
int fflag = 0;
int oflag = 0;
char * ovalue = NULL;
void usage()
{
printf("Use: equalPath [options] files...\n");
printf("Each file should contain a graph in dot format.\n");
printf("The program decides if there exists a length n such that each input graph has a valid simple path of length n.\n");
printf("Can display the result both on the command line or in dot format.\n");
printf("Options: \n");
printf(" -h         Displays this help\n");
printf(" -v         Activate verbose mode (displays parsed graphs)\n");
printf(" -F         Displays the formula computed (obviously not in this version, but you should really display it in your code)\n");
printf(" -s         Tests separately all formula by depth [if not present: uses the global formula]\n");
printf(" -d         Only if -s is present. Explore the length in decreasing order. [if not present: in increasing order]\n");
printf(" -a         Only if -s is present. Computes a result for every length instead of stopping at the first positive result (default behaviour)\n");
printf(" -t         Displays the paths found on the terminal [if not present, only displays the existence of the path].\n");
printf(" -f         Writes the result with colors in a .dot file. See next option for the name. These files will be produced in the folder 'sol'.\n");
printf(" -o NAME    Writes the output in \"NAME-lLENGTH.dot\" where LENGTH is the length of the solution. Writes several files in this format if both -s and -a are present. [if not present: \"result-lLENGTH.dot\"]\n");

}

int main(int argc, char *argv[])
{
	opterr = 0;
	int option;
	
	if (argc < 2)
	{
		usage();
		return 0;
	}
	while((option = getopt (argc,argv,"hvFsdatfo:"))!=-1)
		switch(option)
		{
		case 'h':
			hflag=1;
			usage();
			return 0;
		case 'v':
			vflag=1;
			break;
		case 'F':
			Fflag=1;
			break;	
		case 's':
			sflag=1;
			break;
		case 'd':
			dflag=1;
			break;
		case 'a':
			aflag=1;
			break;
		case 't':
			tflag=1;
			break;
		case 'f':
			fflag=1;
			break;
		case 'o':
			oflag=1;
			ovalue = optarg;
			break;
		case '?':
			if (optopt == 'o')
			  fprintf (stderr, "Option -%c requires an argument.\n", optopt);
			else if (isprint (optopt))
			  fprintf (stderr, "Unknown option `-%c'.\n", optopt);
			else
			  fprintf (stderr,
					   "Unknown option character `\\x%x'.\n",
					   optopt);
			return 1;
		  default:
			abort ();
			
		  }
	/***********************************Init and Verbose Mode**********************************/
	Z3_context ctx = makeContext();
	int numGraphs = argc-optind;
	Graph graphs[numGraphs];
	for (int i = 0; i < numGraphs; ++i) // Il faudra penser à prendre en compte les options etc
	{
		graphs[i] = getGraphFromFile(argv[optind+i]);
		if(vflag) printGraph(graphs[i]);
	}
	//
	int Min_numberNodesAllgraphs = orderG(graphs[0]);
	for (int i = 1; i < numGraphs; i++)
	{
		if (Min_numberNodesAllgraphs > orderG(graphs[i]))
			Min_numberNodesAllgraphs = orderG(graphs[i]);
	}
	/**************Calculate Length Solution (-s not present so full formula, if -F display the FULL formula)*****************/
	if(sflag==0)
	{
		Z3_ast Full_formula = graphsToFullFormula(ctx, graphs, numGraphs);
		if(Fflag==1) printf("Full_formula : \n  %s \n",Z3_ast_to_string(ctx,Full_formula));
		if (isFormulaSat(ctx, Full_formula)== Z3_L_TRUE)
		{
			Z3_model model = getModelFromSatFormula(ctx, Full_formula);
			int x = getSolutionLengthFromModel(ctx,model,graphs);
			printf("There is a simple valid path of length %d in all graphs  \n", x);
			//if(tflag==1)printf("%s",Z3_model_to_string(ctx,model));
			if(tflag==1)printPathsFromModel(ctx,model,graphs,numGraphs, x);
			if(fflag==1)createDotFromModel(ctx,model, graphs,numGraphs, x, NULL);
			if(oflag==1)createDotFromModel(ctx,model, graphs,numGraphs, x, ovalue);
		}
		else
			printf("No simple valid path in all graphs  \n");
		
	}
	/***Calculate Length Solution (-s present so path formula ,stop when find one , don't stop if -a present)*****************/
	if(sflag==1)
	{
		if(dflag==0)
		{
			
			for (int i = 0; i <=Min_numberNodesAllgraphs; i++)
			{	
				
				Z3_ast Path_formula = graphsToPathFormula(ctx, graphs, numGraphs, i);
				if(Fflag==1) printf("Path_formula of len %d : \n  %s \n",i,Z3_ast_to_string(ctx,Path_formula));
				if (isFormulaSat(ctx, Path_formula)== Z3_L_TRUE)
				{
					Z3_model model = getModelFromSatFormula(ctx, Path_formula);
					int x=getSolutionLengthFromModel(ctx,model,graphs);
					printf("There is a simple valid path of length %d in all graphs  \n", x);
					if(tflag==1)printPathsFromModel(ctx,model,graphs,numGraphs, i);
					if(fflag==1)createDotFromModel(ctx,model, graphs,numGraphs, x, NULL);
					if(oflag==1)createDotFromModel(ctx,model, graphs,numGraphs, x, ovalue);
					if(aflag==0)break;
					
				}
				else
				{
					printf("No simple valid path of length %d in all graphs  \n", i);
				}
			}
			
		}
		if(dflag==1)
		{
			for (int i = Min_numberNodesAllgraphs; i >0; i--)
			{	
				
				Z3_ast Path_formula = graphsToPathFormula(ctx, graphs, numGraphs, i);
				if(Fflag==1) printf("Path_formula of len %d : \n  %s \n",i,Z3_ast_to_string(ctx,Path_formula));
				if (isFormulaSat(ctx, Path_formula)== Z3_L_TRUE)
				{
					Z3_model model = getModelFromSatFormula(ctx, Path_formula);
					int x=getSolutionLengthFromModel(ctx,model,graphs);
					printf("There is a simple valid path of length %d in all graphs  \n", x);
					if(tflag==1)printPathsFromModel(ctx,model,graphs,numGraphs, i);
					if(fflag==1)createDotFromModel(ctx,model, graphs,numGraphs, x, NULL);
					if(oflag==1)createDotFromModel(ctx,model, graphs,numGraphs, x, ovalue);
					if(aflag==0)break;
					
				}
				else
				{
					printf("No simple valid path of length %d in all graphs  \n", i);
				}
			}
		}
	}

	///***************************Clear Memory*************************************/
	Z3_del_context(ctx);

	return 0;
}
