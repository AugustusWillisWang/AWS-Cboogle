// Program: Partitioning of an array (used in Quick sort)
// Author: Carlo A. Furia


type array t = [int] t;

// this postulates that there is a total order on any type t
axiom ( forall <t> el1, el2: t ::  (el1 <: el2)  ||  (el2 <: el1) );

// elements in A[left..right] are partitioned at index according to value pivot
function is_LT_pivot <t> (pivot: t, A: array t, left: int, right: int, index: int) returns(bool)
{ ( forall k: int  ::  left <= right  &&  left <= k  &&  k < index  ==>  A[k] <: pivot ) }

function is_GT_pivot <t> (pivot: t, A: array t, left: int, right: int, index: int) returns(bool)
{ ( forall k: int  ::  left <= right  &&  index <= k  &&  k <= right  ==>  pivot <: A[k] ) }
// this should be derivable from the definition but it is needed nonetheless
axiom ( forall <t> pivot: t, A: array t, left: int, right: int, index: int ::
		left <= right && is_GT_pivot(pivot, A, left, right-1, index) && pivot <: A[right]
			==> is_GT_pivot(pivot, A, left, right, index) );
// this should be derivable from the definition but it is needed nonetheless
axiom ( forall <t> pivot: t, A: array t, left: int, right: int, index: int ::
		is_GT_pivot(pivot, A, left, right, index)	==> pivot <: A[index] );
			

					
procedure swap <tt> (A: array tt, i : int, j: int) returns(B: array tt)
	// elements in positions i,j are swapped
	ensures (B[i] == A[j]  &&  B[j] == A[i]);
	// all other elements are unchanged
	ensures (forall k: int :: k != i && k != j  ==>  B[k] == A[k]);
{
	var tmp: tt;
	
	B := A;
	tmp := B[i];
	B[i] := B[j];
	B[j] := tmp;
}


procedure partition <t> (A: array t, left, right: int, pivot: t) returns(index: int, B: array t)
	requires left <= right;
	ensures is_LT_pivot(pivot, B, left, right, index);
	ensures is_GT_pivot(pivot, B, left, right, index);	
{
	var i: int;

	B := A;	
	i := left; index := left;
	while ( i <= right )
	invariant ( is_LT_pivot(pivot, B, left, i-1, index) );
	invariant ( is_GT_pivot(pivot, B, left, i-1, index) );
	invariant ( index <= i );	
	{
		if ( B[i] <: pivot )
		{
			call B := swap(B, i, index);
			index := index + 1;
		}
		i := i + 1;
	}
}
