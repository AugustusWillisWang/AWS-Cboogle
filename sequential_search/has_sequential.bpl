// Program: Sequential search
// Author: Sergey Velder


// Generic type
type T;

type array G = [int] G;

// contains(a, n, key) iff key in elements(a[1..n])
function contains(a: array T,  n: int,  key: T) returns (bool);
axiom (forall a: array T,           key: T  ::  !contains(a, 0, key));
axiom (forall a: array T,  n: int,  key: T  ::   contains(a, n, key) && a[n] != key  ==> contains(a, n - 1, key));


procedure has_sequential (a: array T,  n: int,  key: T) returns (Result: int)
   requires  n >= 0;
   ensures   0 <= Result && Result <= n;
   ensures   Result == 0  ==>  !contains(a, n, key);
   ensures   Result != 0  ==>  a[Result] == key;
{
   var i: int;

   i := 0;
   Result := 0;
   while (i < n)
      invariant  0 <= i && i <= n;
	  invariant  0 <= Result && Result <= i;
      invariant  Result == 0  ==>  !contains(a, i, key);
      invariant  Result  > 0  ==>  a[Result] == key;
   {
      i := i + 1;
      if (a[i] == key)
      {
         Result := i;
      }
   }
}
