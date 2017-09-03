// Program: Binary search
// Author: Sergey Velder


// Generic type totally ordered
type T;
axiom (forall x, y: T  ::  x <: y || x == y || y <: x);

type array G = [int] G;

// contains(a, n, key) iff key in elements(a[1..n]), under the assumption that "a" is sorted
function contains(a: array T,  left, right: int,  key: T) returns (bool);
axiom (forall a: array T,  left, right,  i  : int,  key: T  ::  contains(a, left, right, key) && left <= i && i <= right && a[i] <: key  ==>  contains(a, i + 1, right, key));
axiom (forall a: array T,  left, right,  i  : int,  key: T  ::  contains(a, left, right, key) && left <= i && i <= right && key <: a[i]  ==>  contains(a, left, i - 1, key));
axiom (forall a: array T,                i  : int,  key: T  ::  a[i] == key  <==> contains(a, i, i, key));
axiom (forall a: array T,  left, right, l, r: int,  key: T  ::  contains(a, left, right, key) && l <= left && r >= right  ==>  contains(a, l, r, key));


procedure choose(a: array T,  left, right: int,  key: T) returns (mid: int)
   requires left <= right;
   ensures  contains(a, left, right, key) && a[mid] == key  ==>  contains(a, mid, mid, key);
   ensures  left <= mid && mid < right;
{
   havoc mid;   //  mid := (left + right) / 2;
   assume  left <= mid && mid < right;
}


procedure collapse(a: array T,  n: int,  key: T) returns (Result: int)
   requires  n > 0;
   ensures   a[Result] == key  ==>  contains(a, Result, Result, key);
   ensures   contains(a, 1, n, key)  ==>  a[Result] == key;
   ensures   Result > 0;
{
   var i, j, mid: int;

   i := 1;  j := n;
   while (i < j)
      invariant  1 <= i && i <= j && j <= n;
      invariant  contains(a, 1, n, key)  ==>  contains(a, i, j, key);
   {
      call mid := choose(a, i, j, key);
      if (a[mid] <: key)
      {
         i  := mid + 1;
      }
      else
      {
         j := mid;
      }
   }
   Result := i;
}


procedure has_binary(a: array T,  n: int,  key: T) returns (Result: int)
   requires  n > 0;
   ensures   Result == 0 ==>  !contains(a, 1, n, key);
   ensures   Result > 0  ==>  a[Result] == key;
{         	
   call Result := collapse(a, n, key);
   if (a[Result] != key)
   {
      Result := 0;
   }
}
