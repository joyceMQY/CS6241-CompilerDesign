#include <stdio.h>
#include <stdlib.h>

int main() {
	int a = 10;
	int array[17];



// Case 5: subsumed subscript expression
  

    array[a+1] = 1;
    array[a-1] = 1;
    array[a+2] = 1;
    array[a+0] = 1;


	return 10;
}


/*
 * 
 * ~/llvm/llvm3.4/llvm/Release+Asserts/bin/clang -O0 -emit-llvm test1.c -c -o test1.bc
 * llvm-dis < test1.bc >test1.print
 * opt -dot-cfg-only < test1.bc
 * dot -Tpng cfg.main.dot -o test1.png
 * opt -load ../../../Release+Asserts/lib/HW2.dylib -project <test1.bc >test1.out.bc
 *
 */
