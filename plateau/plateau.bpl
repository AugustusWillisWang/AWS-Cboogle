// Program: Find a plateau in an array
// Author: Carlo A. Furia


type array t = [int] t;

// this postulates that there is a total order on any type t
axiom ( forall <t> el1, el2: t ::  (el1 <: el2)  ||  (el2 <: el1) );

function is_ordered <tt> (A: array tt) returns (bool)
{ ( forall k: int :: A[k] <: A[k+1] ) }
			
function has_plateau <tt> (A: array tt, low: int, high: int, len: int) returns (bool);
axiom ( forall <tt> A: array tt, low: int, high: int ::  high >= low  ==>  has_plateau(A, low, high, 1) );
axiom ( forall <tt> A: array tt, low: int, high: int, len: int ::
						is_ordered(A)  &&  has_plateau(A, low, high, len)  ==>  has_plateau(A, low, high+1, len) );
axiom ( forall <tt> A: array tt, low: int, high: int, len: int ::
						is_ordered(A)  &&  has_plateau(A, low, high, len)  &&  A[high+1] == A[high+1-len+1]  ==>  has_plateau(A, low, high+1, len+1) );

						
function no_longer_plateau <tt> (A: array tt, low: int, high: int, len: int) returns (bool);
axiom ( forall <tt> A: array tt, low: int, high: int, len: int ::  high >= low  &&  len >= high - low + 1  ==>  no_longer_plateau(A, low, high, len) );
axiom ( forall <tt> A: array tt, low: int, high: int, len: int ::
						is_ordered(A)  &&  no_longer_plateau(A, low, high, len)  &&  A[high+1] != A[high+1-len+1]  ==>  no_longer_plateau(A, low, high+1, len) );
axiom ( forall <tt> A: array tt, low: int, high: int, len: int ::
						is_ordered(A)  &&  no_longer_plateau(A, low, high, len)  &&  A[high+1] == A[high+1-len+1]  ==>  no_longer_plateau(A, low, high+1, len+1) );

			
procedure longest_plateau <t> (A: array t, n: int)
	returns (p: int)
	requires n > 0;
	requires is_ordered (A);
	ensures p >= 1;
	ensures has_plateau (A, 1, n, p);
	ensures no_longer_plateau (A, 1, n, p);
{
	var i: int;
	
	i, p := 2, 1;

	while ( i <= n )
	invariant 1 <= i && i <= n + 1;
	invariant has_plateau (A, 1, i-1, p);
	invariant no_longer_plateau (A, 1, i-1, p);
	{
		if ( A[i] != A[i-p+1] )
		{
			i := i + 1;
		}
		else
		{
			assert (A[i] == A[i-p+1]);
			i := i + 1;
			p := p + 1;
		}
	}
}
