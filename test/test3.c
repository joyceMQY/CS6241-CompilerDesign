#include <stdio.h>
#include <stdlib.h>

int main() {
	int a = 10;
	int array[17];

 

// Case 3: subsume range check with identical subscript expression
	 int array2[15];
     array[a] = 1;
     array2[a] = 2;



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
