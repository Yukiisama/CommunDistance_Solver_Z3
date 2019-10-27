#include <stdio.h>
#include "Z3Tools.h"
#include "Solving.h"

int main(int argc, char* argv[]){
    
    Z3_context ctx = makeContext();
    printf("Creating the context. Must be destroyed at the end of the program.\n");
	int number = 1;
	int position = 1;
	int k = 1;
	int node = 1;
    getNodeVariable(ctx, number, position, k, node);
    Z3_del_context(ctx);
    printf("Context deleted, memory is now clean.\n");
    
    return 0;
}
