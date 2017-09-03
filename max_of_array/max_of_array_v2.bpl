// Program: Maximum of an array
// Author: Carlo A. Furia


type array t = [int] t;

// sum of content of A from position to position
function is_max <t> (m: t, A: array t, low: int, high: int) returns(bool)
{ ( forall j: int :: low <= j  && j <= high  ==>  A[j] <: m ) }
// this postulates that there is a total order on any type t
axiom ( forall <t> el1, el2: t ::  (el1 <: el2)  ||  (el2 <: el1) );

				
				
procedure max <t> (A: array t, n: int) returns(m: t)
	requires n >= 0;
	ensures is_max(m, A, 1, n);
{
	var i: int;
	i := 0;  m := A[1];
	while ( i < n )
	invariant ( 0 <= i  &&  i <= n );
	invariant ( is_max(m, A, 1, i) );
	{
		i := i + 1;
		if ( m <: A[i] )
		{ m := A[i]; }
	}
	return;
}
