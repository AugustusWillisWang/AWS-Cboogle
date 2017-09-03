/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-19 12:44:23 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-19 12:57:35
 */


#define bool int

enum COLOR {Blue ,White,Red};
enum COLOR col;

bool is_flag_color ( enum COLOR col ){
    return( col == Blue  ||  col == White  ||  col == Red);
}

#define tt enum COLOR
tt* swap(tt* A, int i, int j)
{
	tt tmp;
	tmp = A[i];
	A[i] = A[j];
	A[j] = tmp;
    return A;
}

#define ARRAY_COLOR tt*
void make_flag (ARRAY_COLOR A, int n,ARRAY_COLOR B,int* bp,int* rp)
{
	int r,b,i,
	B = A;
	b, i, r = 1, 1, n+1;
	
	while ( i < r )
	{
		if (B[i] == Blue)
		{
			B = swap(B, b, i);
			i = i + 1;
			b = b + 1;
		}
		else
		{
			if (B[i] == White)
			{
				i = i + 1;
			}
			else
			{
				r= r - 1;
			    B = swap(B, r, i);
			}
		}
	}
    *bp=b;
    *rp=r;
}

