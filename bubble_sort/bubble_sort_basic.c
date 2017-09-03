/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-17 22:13:05 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-18 20:27:24
 */

#define true 1
#define false 0

int swap(int* array,int num1,int num2);
void bubble_sort_basic (int* old_a, int n);

int swap(int* array,int num1,int num2){
    if (array==0)return -1;
    int temp;
    temp= array[num1];
    array[num1]=array[num2];
	array[num2]=temp;
}


void bubble_sort_basic (int* a, int n)
	// returns(a: array T)
	// requires n >= 1;
	// ensures perm (a, old_a);
	// ensures sorted (a, 1, n);
{
	if (n<1)return;
	int i;
	int swapped=true;
	// a = old_a;
	
	while ( swapped )
	// invariant ( perm (a, old_a) );
	// invariant ( !swapped ==> sorted (a, 1, n) ); 
    {
		swapped =0;
		i = 1;
		while ( i != n )
		// invariant (1 <= i && i <= n);
		// invariant ( perm (a, old_a) );
		// invariant ( !swapped ==> sorted (a, 1, i) );
		{
			if ( !(a[i] <= a[i + 1]) ) {
				swap (a, i, i + 1);
				swapped = true;
			}
			i = i + 1;
		}
	}
}

// driver
int main(){
	int test[]={2,7,58,0,2,6,0,567,3,45,2};
	bubble_sort_basic(test,(sizeof(test)/sizeof(int)));
	return 0;
}