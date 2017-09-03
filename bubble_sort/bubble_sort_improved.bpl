// Program: Bubble sort (improved)
// Author: Carlo A. Furia


type T;
type array G = [int] G;

// this postulates that T is a total order
axiom ( forall el1, el2: T ::  (el1 <: el2)  ||  (el2 <: el1) );

// a[lower..upper] <= pivot
function less_equal_pivot (pivot: T, a: array T, lower, upper: int) returns(bool)
{ ( forall k: int  ::  lower <= k  &&  k <= upper  ==>  a[k] <: pivot ) }

// perm (a, b)
function perm (a: array T, b: array T) returns(bool);
// rather than providing a complete axiomatization, we just state minimal properties and add as a "free ensures" of "swap"
   // reflexive
axiom ( forall a: array T :: perm (a, a) );
   // symmetric
axiom ( forall a, b: array T :: perm (a, b) <==> perm (b, a) );
   // transitive
axiom ( forall a, b, c: array T :: perm (a, b) && perm (b, c) ==> perm (a, c) );

// sorted (a [lower, upper])
function sorted (a: array T, lower, upper: int) returns (bool)
{ ( forall k: int :: lower <= k && k < upper ==> a[k] <: a[k+1] ) }
// equivalent formulation of sortedness
// { ( forall i, j: int :: lower <= i && i <= j && j <= upper ==> a[i] <: a[j] ) }

	// property of sortedness: not needed for proofs
// axiom ( forall a: array T, lower, upper: int  ::  sorted(a, lower, upper) ==> less_equal_pivot (a[upper], a, lower, upper) );

			
procedure swap (a: array T, i, j: int) returns(b: array T)
	// elements in positions i,j are swapped
	ensures ( b[i] == a[j]  &&  b[j] == a[i] );
	// all other elements are unchanged
	ensures ( forall k: int :: k != i && k != j  ==>  b[k] == a[k] );
	// the output is a permutation of the input (not proved)
	free ensures ( perm (a, b) );
{
	var tmp: T;
	
	b := a;
	tmp := b[i];
	b[i] := b[j];
	b[j] := tmp;
}


procedure bubble_sort_improved (old_a: array T, n: int)
	returns(a: array T)
	requires n >= 1;
	ensures perm (a, old_a);
	ensures sorted (a, 1, n);
{
	var i, j: int;
			
	a := old_a;
	i := n;
	
	while ( i != 1 )
	invariant ( 1 <= i && i <= n );
	invariant ( perm (a, old_a) );
	invariant ( sorted (a, i, n) );
	invariant ( i < n ==> less_equal_pivot (a[i + 1], a, 1, i) );
	{
		j := 1;
		while ( j != i )
		invariant ( 1 <= i && i <= n );
		invariant ( 1 <= j && j <= i );
		invariant ( perm (a, old_a) );
		invariant ( sorted (a, i, n) );
		invariant ( i < n ==> less_equal_pivot (a[i + 1], a, 1, i) );
		invariant ( less_equal_pivot (a[j], a, 1, j) );
		{
			if ( !(a[j] <: a[j + 1]) ) {
				call a := swap (a, j, j + 1);
			}
			j := j + 1;
		}
	}
}
