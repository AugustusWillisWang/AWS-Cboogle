// Program: Long integer addition
// Author: Sergey Velder


// Fundamental properties of 
// "/" (integer division, "//" in Eiffel) and "%" (reminder, "\\" in Eiffel)
axiom (forall a, b   : int  ::  0 <= a  ==>  (a < b  ==>  a % b == a && a / b == 0) &&
                                             (0 < b  ==>  a / b >= 0));
axiom (forall a, b, c: int  ::  a < b * c && b > 0  ==>  a / b < c);
axiom (forall a, b: int  ::  a >= 0 && b > 0  ==>  a % b < b && a % b >= 0);

// The sum of "x" and "y" with carry "c" equals the sum of "z" for digits from 0 to n - 1, 
// assuming "x", "y", and "z" are encoded in base "base"
function sum(x, y, z: [int]int,  base, c, n: int) returns (bool);
axiom (forall x, y, z    : [int]int,  base      : int  ::  sum(x, y, z, base, 0, 0));
axiom (forall x, y, z, z_: [int]int,  base, c, n: int  ::  sum(x, y, z, base, c, n)  &&  (forall i: int  ::  0 <= i && i < n  ==>  z[i] == z_[i])  &&
                                 
								 z_[n] == (x[n] + y	[n] + c) % base  ==>  sum(x, y, z_, base, (x[n] + y[n] + c) / base, n + 1));

// has_base (v, b) with v.count = n
function has_base(v: [int]int, b: int, n: int) returns(bool)
{ ( (forall i: int :: 0 <= i && i < n ==> 0 <= v[i] && v[i] < b) && (forall i: int :: i >= n ==> v[i] == 0) ) }
// This is actually a lemma
axiom (forall v: [int]int, b: int, n: int, d: int :: has_base(v, b, n - 1) && 0 <= d && d < b ==> has_base(v[n := d], b, n));


// x + y + c with properties
procedure get_sum(x, y, c, base: int) returns (t: int)
   requires  0 <= c && 0 <= x && 0 <= y && c < base && x < base && y < base;
   ensures   3 * base - 3 < base * base;
   ensures   t == x + y + c;
{
   t := x + y + c;
}


// The carry "c" in base "base" of a value "sum", with properties
procedure get_carry(sum, base: int) returns (c: int)
  requires  0 <= sum && 0 <= base && sum / base < base;
  ensures   c < base;
  ensures   c == sum / base;
{
   c := sum / base;
}


procedure addition(a, b: [int]int,  base, n: int) returns (Result: [int]int)
   requires  n >= 1  &&  base > 0;
   requires  has_base (a, base, n);
   requires  has_base (b, base, n);
   ensures   sum (a, b, Result, base, 0, n + 1);
   ensures   has_base (Result, base, n + 1);
{
   var i, d, carry: int;

   assume (forall k : int :: Result[k] == 0);
   carry := 0;
   i := 0;
   while (i != n)
	  invariant  0 <= carry && carry < base;
      invariant  sum (a, b, Result, base, carry, i);
	  invariant  has_base (Result, base, i - 1);
   {
      call d := get_sum(a[i], b[i], carry, base);
      Result[i] := d % base;
	  call carry := get_carry(d, base);
      i := i + 1;
   }
   Result[n] := carry;
}
