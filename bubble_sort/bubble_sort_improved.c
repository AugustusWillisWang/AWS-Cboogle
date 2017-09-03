/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-17 22:53:10 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-17 22:59:59
 */

#define true 1
#define false 0

void swap(int* array,int num1,int num2);
void bubble_sort_improved (int* old_a, int n);
void swap(int* array,int num1,int num2){
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
	int i=1;
	
	while ( i<n )
	{
		j = 1;
		while ( j != i )
		{
			if ( !(a[j] <= a[j + 1]) ) {
				swap (a, j, j + 1);
			}
		}
		i = i + 1;
	}
}

// driver
int main(){
	int test[]={2,7,58,0,2,6,0,567,3,45,2};
	bubble_sort_improved(test,(sizeof(test)/sizeof(int)));
	return 0;
}