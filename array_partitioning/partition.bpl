// Program: Partitioning (used in Quick sort)
// Author: Carlo A. Furia


type array T = [int] T;

// this postulates that there is a total order on any generic type T
axiom ( forall <T> el1, el2: T ::  (el1 <: el2)  ||  (el2 <: el1) );

// a[lower..upper] <= pivot
function less_equal_pivot <T> (pivot: T, a: array T, lower, upper: int) returns(bool)
{ ( forall k: int  ::  lower <= k  &&  k <= upper  ==>  a[k] <: pivot ) }
// a[lower..upper] >= pivot
function greater_equal_pivot <T> (pivot: T, a: array T, lower, upper: int) returns(bool)
{ ( forall k: int  ::  lower <= k  &&  k <= upper  ==>  pivot <: a[k] ) }

// perm (a, b)
function perm <T> (a: array T, b: array T) returns(bool);
// rather than providing a complete axiomatization, we just state minimal properties and add as a "free ensures" of "swap"
   // reflexive
axiom ( forall <T> a: array T :: perm (a, a) );
   // symmetric
axiom ( forall <T> a, b: array T :: perm (a, b) <==> perm (b, a) );
   // transitive
axiom ( forall <T> a, b, c: array T :: perm (a, b) && perm (b, c) ==> perm (a, c) );

					
procedure swap <t> (a: array t, i : int, j: int) returns(b: array t)
	// elements in positions i,j are swapped
	ensures ( b[i] == a[j]  &&  b[j] == a[i] );
	// all other elements are unchanged
	ensures ( forall k: int :: k != i && k != j  ==>  b[k] == a[k] );
	free ensures ( perm (a, b) );
{
	var tmp: t;
	
	b := a;
	tmp := b[i];
	b[i] := b[j];
	b[j] := tmp;
}


procedure partition <T> (old_a: array T, n: int, pivot: T)
	returns(Result: int, a: array T)
	requires n >= 1;
	ensures 0 <= Result && Result <= n;
	ensures perm (a, old_a);
	ensures less_equal_pivot (pivot, a, 1, Result);
	ensures greater_equal_pivot (pivot, a, Result + 1, n);
{
	var low, high: int;
	
	low, high := 1, n;
	a := old_a;
	
	while ( low != high )
	invariant ( 1 <= low && low <= high && high <= n );
	invariant ( perm (a, old_a) );
	invariant ( less_equal_pivot (pivot, a, 1, low - 1) );
	invariant ( greater_equal_pivot (pivot, a, high + 1, n) );	
	{
		while ( low != high  &&  a[low] <: pivot )
		invariant ( 1 <= low && low <= high && high <= n );
		invariant ( perm (a, old_a) );
		invariant ( less_equal_pivot (pivot, a, 1, low - 1) );
		invariant ( greater_equal_pivot (pivot, a, high + 1, n) );			
		{
			low := low + 1;
		}
		while ( low != high  &&  pivot <: a[high] )
		invariant ( 1 <= low && low <= high && high <= n );
		invariant ( perm (a, old_a) );
		invariant ( less_equal_pivot (pivot, a, 1, low - 1) );
		invariant ( greater_equal_pivot (pivot, a, high + 1, n) );			
		{
			high := high - 1;
		}
		
		call a := swap(a, low, high);
	}
	
	if ( pivot <: a[low] )
	{
		low := low - 1;
		high := low;
	}
	Result := low;
}
