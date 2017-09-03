/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-19 12:19:12 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-19 12:40:49
 */

#define T int
#define ture 1
#define false 0
#include <assert.h>

			
T* swap (T array[], int i,int j)
	// // elements in positions i,j are swapped
	// ensures ( b[i] == a[j]  &&  b[j] == a[i] );
	// // all other elements are unchanged
	// ensures ( forall k: int :: k != i && k != j  ==>  b[k] == a[k] );
	// // the output is a permutation of the input (not proved)
	// free ensures ( perm (a, b) );
{
    T temp;
	tmp = array[i];
	array[i] = array[j];
	array[j] = tmp;
    return array;
}

int max(int a,int b){
    if(a>b)return a;
    else return b;
}

int genc(){
    return 2;
}

T* comb_sort (T array[], int n)
{
	int i, gap;
	int swapped;
		
	a =array;
	swapped = true;
	gap = n-1;
	
	while ( swapped || gap != 0 )
	{
        gap = max (1, gap / genc());
		assert (0 <= gap && gap <= n-1);
		swapped = false;
		i = 1;
		while ( i + gap != n )
		{
			if ( !(a[i] < a[i + gap]) ) {
				a = swap (a, i, i + gap);
				swapped = true;
			}
			i = i + 1;
		}
	}
    return array;
}
