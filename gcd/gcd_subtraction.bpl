// Program: Greatest common divisor (with subtraction)
// Author: Sergey Velder


// Greatest common divisor of a and b
function gcd(a, b: int) returns (int);
// Fundamental properties of "gcd"
axiom (forall x   : int  ::  gcd(x, x) == x);
axiom (forall x, y: int  ::  gcd(x, y) == gcd(y, x));
// Fundamental property of "gcd" w.r.t. subtraction
axiom (forall x, y: int  ::  x > y  ==>  gcd(x, y) == gcd(x - y, y));


procedure gcd_subtraction(a, b: int) returns (Result: int)
   requires  a > 0  &&  b > 0;
   ensures   Result == gcd(a, b);
{
   var x: int;

   Result := a;  x := b;
   while (Result != x)
      invariant  Result > 0  &&  x > 0;
      invariant  gcd(Result, x) == gcd(a, b);
   {
      if (Result > x)
      {
         Result := Result - x;
      }
      else
      {
         x := x - Result;
      }
   }
}
