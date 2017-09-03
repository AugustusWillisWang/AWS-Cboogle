// Program: Maximum (two-variable loop)
// Author: Sergey Velder


// Generic type totally ordered
type T;
axiom (forall x, y: T  ::  x <: y || x == y || y <: x);

type array G = [int] G;

function max(a: array T,  left, right: int) returns (T);
axiom (forall a: array T,  i          : int  ::  max(a, i, i) == a[i]);
axiom (forall a: array T,  left, right: int  ::  (exists i: int  ::  left <  i && i <= right && a[left] <: a[i])   ==>  max(a, left, right) == max(a, left + 1, right));
axiom (forall a: array T,  left, right: int  ::  (exists i: int  ::  left <= i && i <  right && a[right] <: a[i])  ==>  max(a, left, right) == max(a, left, right - 1));

procedure max_two_way (a: array T,  n: int) returns (Result: T)
   requires  n > 0;
   ensures   Result == max(a, 1, n);
{
   var i, j: int;

   i := 1;  j := n;
   while (i < j)
      invariant  1 <= i && i <= j && j <= n;
      invariant  max(a, 1, n) == max(a, i, j);
   {
      if (!(a[i] <: a[j]))
      {
         j := j - 1;
      }
      else
      {
         i := i + 1;
      }
   }
   Result := a[i];
}
