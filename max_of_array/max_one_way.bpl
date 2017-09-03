// Program: Maximum (one-variable loop)
// Author: Sergey Velder


// Generic type totally ordered
type T;
axiom (forall x, y: T  ::  x <: y || x == y || y <: x);

type array G = [int] G;

function max(a: array T,  n: int) returns (T);
axiom (forall a: array T           ::  a[1] == max(a, 1));
axiom (forall a: array T,  n: int  ::    max(a, n) <: a[n + 1]   ==> max(a, n + 1) == a[n + 1]);
axiom (forall a: array T,  n: int  ::  !(max(a, n) <: a[n + 1])  ==> max(a, n + 1) == max(a, n));

procedure max_one_way(a: array T,  n: int) returns (Result: T)
   requires  n > 0;
   ensures   Result == max(a, n);
{
   var i: int;

   i := 1;
   Result := a[1];
   while (i < n)
      invariant  i <= n;
      invariant  Result == max(a, i);
   {
      i := i + 1;
      if (Result <: a[i])
      {
         Result := a[i];
      }
   }
}
