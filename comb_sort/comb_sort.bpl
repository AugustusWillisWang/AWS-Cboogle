// Program: Comb sort
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

// gap_sorted (a [lower, upper], d)
function gap_sorted (a: array T, lower, upper, d: int) returns (bool)
{ ( forall k: int :: lower <= k && k <= upper - d ==> a[k] <: a[k+d] ) }

			
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


procedure comb_sort (old_a: array T, n: int)
	returns(a: array T)
	requires n >= 1;
	ensures perm (a, old_a);
	ensures sorted (a, 1, n);
{
	var i, gap: int;
	var swapped: bool;
		
	a := old_a;
	swapped := true;
	gap := n;
	
	while ( swapped || gap != 1 )
	invariant ( 1 <= gap && gap <= n );
	invariant ( perm (a, old_a) );
	invariant ( !swapped ==> gap_sorted (a, 1, n, gap) );
	{
		// gap := max (1, gap // c) for some c > 1
		havoc gap;
		assume (1 <= gap && gap <= n);
		swapped := false;
		i := 1;
		while ( i + gap != n + 1 )
		invariant ( 1 <= gap && gap <= n );
		invariant ( 1 <= i && i < i + gap && i + gap <= n + 1 );
		invariant ( perm (a, old_a) );
		invariant ( !swapped ==> gap_sorted (a, 1, i - 1 + gap, gap) );
		{
			if ( !(a[i] <: a[i + gap]) ) {
				call a := swap (a, i, i + gap);
				swapped := true;
			}
			i := i + 1;
		}
	}
}
