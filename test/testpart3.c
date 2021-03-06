#include <stdio.h>
#include <stdlib.h>

void part3test(int n) {
	int a[20];
	int b[20];
	int i = n, j = n;

	if(i > 0) {
		a[i+1] = 0;
		b[j+1] = 0;
	} else {
		i = 3;
		j = 3;
		a[i+5] = 1;
		b[j+5] = 1;
	}
}

int main() {
	part3test(16);
}

// with baseline, we add 4 checks
// after running part3, there are only 2 checks... (no check for j)
/*
 * clang testpart3.c -o testpart3
 * clang -O0 -emit-llvm testpart3.c -c -o testpart3.bc
 * llvm-dis < testpart3 | less
 *
 * opt -load ../../../Release+Asserts/lib/project2.so -stat < project/testpart3
 *
 * opt -dot-cfg-only < src/project-test.bc
 * dot -Tpng cfg.test2.dot -o test2.png
 */
