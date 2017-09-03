// Program: Sequential search in an array
// Author: Carlo A. Furia


type array t = [int] t;

// there is no element v in A over range low..high
function not_exists <t> (v: t, A: array t, low: int, high: int) returns(bool)
{ ( forall j: int :: low <= j  && j <= high  ==>  A[j] != v ) }
				
				
procedure seq_search <t> (A: array t, n: int, v: t) returns(found: bool, p: int)
	requires n >= 0;
	ensures found  ==> A[p] == v;
	ensures found ==> 1 <= p && p <= n;
	ensures !found ==> not_exists(v, A, 1, n);
{
	var i: int;
	
	i := 1;  found := false;
	while ( i <= n  &&  !found )
	invariant ( found  ==>  A[p] == v );
	invariant (found ==> 1 <= p && p <= n);
	invariant ( !found ==>  not_exists(v, A, 1, i-1) );
	{
		if (A[i] == v)
		{
			p := i;
			found := true;
		}
		else
		{
			i := i + 1;
		}
	}
	return;
}
