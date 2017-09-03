/*
 * @Author Augustus.Wang 
 * @Date 2017-07-19 132121 
 * @Last Modified by   Augustus.Wang 
 * @Last Modified time 2017-07-19 132121 
 */


#define T int



T* insertion_sort (T* a, int n)
{
int i,j;
T v;
	
	i = 0;
	
	while ( i != n-1 )
	{
		i = i + 1;
		v = a[i];
		j = i - 1;
		while ( j != -1 && !(a[j] < v) )
		{
			a[j + 1] = a[j];
			j = j - 1;
		}
		a[j + 1] = v;
	}
}
