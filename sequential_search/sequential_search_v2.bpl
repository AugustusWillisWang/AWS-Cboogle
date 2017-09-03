// Program: Sequential search in an array
// Author: Carlo A. Furia


type array t = [int] t;

// there is one element equal to v in A over range low..high
function exists_one <t> (v: t, A: array t, low: int, high: int) returns(bool)
{ ( exists j: int :: low <= j  && j <= high  &&  A[j] == v ) }
				
				
procedure seq_search <t> (A: array t, n: int, v: t) returns(found: bool, p: int)
	requires n >= 0;
	ensures exists_one(v, A, 1, n)   ==>  found && A[p] == v;
	ensures !exists_one(v, A, 1, n)  ==>  !found;
{
	var i: int;
	
	i := 1;  found := false;
	while ( i <= n  &&  A[i] != v )
	invariant ( exists_one(v, A, 1, i-1)   ==>  found && A[p] == v );
	invariant ( !exists_one(v, A, 1, i-1)  ==>  !found );	
	{
		i := i + 1;
	}
	if ( i <= n )
	{
		p := i;
		found := true;
	}
	return;
}

