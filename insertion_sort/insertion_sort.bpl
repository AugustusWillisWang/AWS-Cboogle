// Program: Insertion sort
// Author: Carlo A. Furia


type T;
type array G = [int] G;

// this postulates that T is a total order
axiom ( forall el1, el2: T ::  (el1 <: el2)  ||  (el2 <: el1) );

// a[lower..upper] > pivot
function greater_equal_pivot (pivot: T, a: array T, lower, upper: int) returns(bool)
{ ( forall k: int  ::  lower <= k  &&  k <= upper  ==>  pivot <: a[k] ) }

// perm (a, b)
function perm (a: array T, b: array T) returns(bool);
// rather than providing a complete axiomatization, we just state minimal properties required in the proof of "insertion_sort"
   // reflexive
axiom ( forall a: array T :: perm (a, a) );

// sorted (a [lower, upper])
function sorted (a: array T, lower, upper: int) returns (bool)
{ ( forall k: int :: lower <= k && k < upper ==> a[k] <: a[k+1] ) }

// a[lower..mid] * v * a[mid + 2..upper]
function cat (a: array T, lower, mid, upper: int, v: T) returns (array T);
axiom ( forall a: array T, lower, mid, upper: int, v: T, k: int :: lower <= k && k <= mid ==> cat(a, lower, mid, upper, v)[k] == a[k] );
axiom ( forall a: array T, lower, mid, upper: int, v: T, k: int :: lower <= mid && mid + 2 <= k && k <= upper ==> cat(a, lower, mid, upper, v)[k] == a[k] );
axiom ( forall a: array T, lower, mid, upper: int, v: T, k: int :: lower <= mid && mid <= upper && k == mid + 1 ==> cat(a, lower, mid, upper, v)[k] == v );
axiom ( forall a: array T, lower, mid, upper: int, k: int :: lower - 1 <= mid && mid <= upper ==> cat(a, lower, mid, upper, a[mid + 1]) == a );

	// Domain property that relates "perm" and "cat" (used to prove inductiveness of the main loop's invariant perm(a, old_a)
axiom ( forall a, b: array T, lower, mid, upper: int, v: T :: lower - 1 <= mid && mid <= upper ==>
			(perm(cat(a, lower, mid, upper, v), b) ==> perm(cat(a[mid + 1 := v], lower, mid, upper, v), b)) );


procedure insertion_sort (old_a: array T, n: int)
	returns(a: array T)
	requires n >= 1;
	ensures perm (a, old_a);
	ensures sorted (a, 1, n);
{
	var i, j: int;
	var v: T;
	
	i := 1;
	a := old_a;
	
	while ( i != n )
	invariant ( 1 <= i && i <= n );
	invariant ( perm (a, old_a) );
	invariant ( sorted (a, 1, i) );
	{
		i := i + 1;
		v := a[i];
		j := i - 1;
		while ( j != 0 && !(a[j] <: v) )
		invariant ( 0 <= j && j < i && i <= n );
		// proving the following invariant inductive amount to proving that the two sequences:
		// S1: a[1..j] * v * a[j + 2..n]     S2: a[1..j - 1] * v * a[j] * a[j+2..n]
		// contain the same elements; S2 expresses what you get after backward substitution through the loop's body
		// For simplicity, we just assume inductiveness
		free invariant ( perm (cat(a, 1, j, n, v), old_a) );
		invariant ( sorted (a, 1, i - 1) );
		invariant ( greater_equal_pivot (v, a, j + 1, i) );
		invariant ( sorted (a, j + 1, i) );
		{
			a[j + 1] := a[j];
			j := j - 1;
		}
		a[j + 1] := v;
	}
}
