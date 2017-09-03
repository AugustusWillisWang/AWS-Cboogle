/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-19 14:22:32 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-19 14:49:37
 */

#include <assert.h>
#include <stdlib.h>
// x + y + c with properties
int get_sum(int x,int y,int c,int base)
{
    assert(0 <= c && 0 <= x && 0 <= y && c < base && x < base && y < base);
      int t = x + y + c;
      return t;
}


// The carry "c" in base "base" of a value "sum", with properties
int get_carry(int sum,int base) 
{
    assert(0 <= sum && 0 <= base && sum / base < base);
   c = sum / base;
   return c;
}

// has_base (v, b) with v.count = n
int has_base(int* v[], int b, int n) 
{
    for (int i=0;i<n;i++){
         if(!(0 <= v[i] && v[i] < b))return 0;
    }
}

int* addition(int* a[],int* b[], int* base[], int n)

{
    int* Result =(int*)(malloc(n*sizeof(int)));
    Result={0};
int i,d,carry;
   assert(  n >= 1  &&  base > 0);
   assert(  has_base (a, base, n));
   assert(  has_base (b, base, n));

  carry = 0;
   i = 0;
   while (i != n)

   {
     d = get_sum(a[i], b[i], carry, base);
      Result[i] = d % base;
	  call carry = get_carry(d, base);
      i = i + 1;
   }
   Result[n] = carry;
   return Result;
}
