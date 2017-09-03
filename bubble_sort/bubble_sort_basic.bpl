// Program: Bubble sort (basic)
// Author: Carlo A. Furia


type T;
type array G = [int] G;

// this postulates that T is a total order
axiom ( forall el1, el2: T ::  (el1 <: el2)  ||  (el2 <: el1) );

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


procedure bubble_sort_basic (old_a: array T, n: int)
	returns(a: array T)
	requires n >= 1;
	ensures perm (a, old_a);
	ensures sorted (a, 1, n);
{
	var i: int;
	var swapped: bool;
		
	a := old_a;
	swapped := true;
	
	while ( swapped )
	invariant ( perm (a, old_a) );
	invariant ( !swapped ==> sorted (a, 1, n) );
	{
		swapped := false;
		i := 1;
		while ( i != n )
		invariant (1 <= i && i <= n);
		invariant ( perm (a, old_a) );
		invariant ( !swapped ==> sorted (a, 1, i) );
		{
			if ( !(a[i] <: a[i + 1]) ) {
				call a := swap (a, i, i + 1);
				swapped := true;
			}
			i := i + 1;
		}
	}
}
