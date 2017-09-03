/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-19 12:58:13 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-19 13:05:00
 */

// Greatest common divisor of a and b

#include <assert.h>
int gcd_subtraction(a, b: int)
{
   int x;

   result = a; 
    x = b;
   while (result != x)
   {
      if (result > x)
      {
         result = result - x;
      }
      else
      {
         x = x - result;
      }
   }
   return result;
}
