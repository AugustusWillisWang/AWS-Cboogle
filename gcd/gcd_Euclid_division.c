/*
 * @Author Augustus.Wang 
 * @Date 2017-07-19 130658 
 * @Last Modified by Augustus.Wang
 * @Last Modified time 2017-07-19 131326
 */

#include<assert.h>

procedure gcd_Euclid_division(int a,int b)
{
    assert(a>=0);
    assert(b>=0);
int t,x,y;

x=a;
y=b;
   while (y > 0)

   {
	  t = y;
	  y = x % y;
	  x = t;
     // With parallel assignment x, y  =  y, x % y;
   }
	Result = x;
}
