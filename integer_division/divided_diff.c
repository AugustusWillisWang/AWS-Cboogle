/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-19 14:35:45 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-19 14:48:48
 */

#include<stdlib.h>
#include<assert.h>
//Integer division by successive differences
int* divided_diff(int n,int m) 
{
    assert(n >= 0  &&  m > 0);
   int q = 0;  
   int r = n;
   while (r >= m)
    //   invariant  0 <= r;
    //   invariant  n == m * q + r;
   {
      r = r - m;
      q = q + 1;
   }
   int * result=(int*)malloc(2*sizeof(int));
   result[0]=q; //商
   result[1]=r;//余数
   return result;
}
