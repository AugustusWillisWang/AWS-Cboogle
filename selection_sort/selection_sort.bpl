// Program: Selection sort
// Author: Carlo A. Furia


type T;
type array G = [int] G;

// this postulates that T is a total order
axiom ( forall el1, el2: T ::  (el1 <: el2)  ||  (el2 <: el1) );

// a[lower..upper] <= pivot
function less_equal_pivot (pivot: T, a: array T, lower, upper: int) returns(bool)
{ ( forall k: int  ::  lower <= k  &&  k <= upper  ==>  a[k] <: pivot ) }
// a[lower..upper] >= pivot
function greater_equal_pivot (pivot: T, a: array T, lower, upper: int) returns(bool)
{ ( forall k: int  ::  lower <= k  &&  k <= upper  ==>  pivot <: a[k] ) }

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


// This is a lemma of the domain theory about "swap"
procedure swap$sorted_progress (a: array T, n, i, m: int) returns (b: array T)
		// P1. a[1..i] is sorted
	requires ( sorted (a, 1, i) );
		// P2. m is a position in [i..n]
	requires ( i <= m );
		// P3. a[1..i - 1] <= a[m], that is: a[m] is an upper bound of a[1..i - 1]
	requires ( less_equal_pivot (a[m], a, 1, i - 1) );
		// P4. a[m] <= a[i]
	requires ( a[m] <: a[i] );
		// P5. a[m] <= a[i + 1]
	requires ( a[m] <: a[i + 1] );
		// P6. a[i..n] >= a[m], that is: a[m] is the minimum of a[i..n]
	requires ( greater_equal_pivot (a[m], a, i, n) );
		// swap preserves permutations
	ensures ( perm (b, a) );
		// b[1..i + 1] is sorted (extends P1 from P2, P3, P4, P5, P6)
	ensures ( sorted (b, 1, i + 1) );
		// b[i + 1..n] >= b[i], that is: b[i] is the minimum of b[i..n] (extends P6)
	ensures ( greater_equal_pivot (b[i], b, i + 1, n) );
		// forall k in [i + 1..n]: b[1..i] <= b[k]
	ensures ( forall k: int :: i < k && k <= n ==> less_equal_pivot (b[k], b, 1, i) );
{
	call b := swap (a, i, m);
}

			
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


procedure selection_sort (old_a: array T, n: int)
	returns(a: array T)
	requires n >= 1;
	ensures perm (a, old_a);
	ensures sorted (a, 1, n);
{
	var i, j, m: int;
	
	i := 1;
	a := old_a;
	
	while ( i != n )
	invariant ( 1 <= i && i <= n );
	invariant ( perm (a, old_a) );
	invariant ( sorted (a, 1, i) );
	invariant ( forall k: int :: i <= k && k <= n ==> less_equal_pivot (a[k], a, 1, i - 1) );
	{
		j := i + 1;
		m := i;
		while ( j != n + 1 )
		invariant ( 1 <= i && i < j && j <= n + 1 );
		invariant ( i <= m && m < j );
		invariant ( perm (a, old_a) );
		invariant ( sorted (a, 1, i) );
		invariant ( greater_equal_pivot (a[m], a, i, j - 1) );
		invariant ( less_equal_pivot (a[m], a, 1, i - 1) );
		{
			if ( !(a[m] <: a[j]) ) {
				m := j;
			}
			j := j + 1;
		}
		call a := swap$sorted_progress(a, n, i, m);
		i := i + 1;
	}
}
