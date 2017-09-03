/*
 * @Author Augustus.Wang 
 * @Date 2017-07-19 144944 
 * @Last Modified by   Augustus.Wang 
 * @Last Modified time 2017-07-19 144944 
 */


procedure check_even_power(x, y int)
   requires  y % 2 == 0;
   ensures   pow(x, y / 2) * pow(x, y / 2) == pow(x, y);
{}


procedure check_power(x, y int)
   ensures  pow(x, y) == pow(x, 1) * pow(x, y - 1);
{}


int power_binary(int m,int n) 
   requires  n >= 0;
   ensures   Result == pow(m, n);
{
   int x;
   int y;

   int Result = 1;
   x = m;
   y = n;  
   while (y != 0)
   {
      assert(y>=0);
      if (y % 2 == 0)
      {
         x = x * x;
         y = y / 2;
      }
      else
      {
         Result = Result * x;
         y = y - 1;
      }
   }
   return Result;
}
