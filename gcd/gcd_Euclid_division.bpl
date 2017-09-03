// Program: Greatest common divisor (with division)
// Author: Sergey Velder


// Property of "%" ("\\" in Eiffel, i.e. remainder)
axiom (forall x, y: int  ::  x >= 0  &&  y > 0  ==>  x % y >= 0);

// Greatest common divisor
function gcd(a, b: int) returns (int);
// Fundamental property of "gcd"
axiom (forall x   : int  ::  gcd(x, 0) == x);
// Fundamental property of "gcd" w.r.t. modulo
axiom (forall x, y: int  ::  y > 0  ==>  gcd(x, y) == gcd(y, x % y));


procedure gcd_Euclid_division(a, b: int) returns (Result: int)
   requires  a > 0  &&  b >= 0;
   ensures   Result == gcd(a, b);
{
   var t, x, y: int;

   x := a;  y := b;
   while (y > 0)
      invariant  x >= 0  &&  y >= 0;
      invariant  gcd(a, b) == gcd(x, y);
   {
	  t := y;
	  y := x % y;
	  x := t;
     // With parallel assignment: x, y  :=  y, x % y;
   }
	Result := x;
}
