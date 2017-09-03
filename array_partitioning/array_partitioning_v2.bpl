// Program: Partitioning of an array (used in Quick sort)
// Author: Carlo A. Furia


type array t = [int] t;

// this postulates that there is a total order on any type t
axiom ( forall <t> el1, el2: t ::  (el1 <: el2)  ||  (el2 <: el1) );

// elements in A[left..right] are partitioned at index according to value pivot
function is_LT_pivot <t> (pivot: t, A: array t, left: int, right: int, low: int, high: int) returns(bool)
{ ( forall k: int  ::  left <= right  &&  left <= k  &&  k < low  ==>  A[k] <: pivot ) }
function is_GT_pivot <t> (pivot: t, A: array t, left: int, right: int, low: int, high: int) returns(bool)
{ ( forall k: int  ::  left <= right  &&  high < k  &&  k <= right  ==>  pivot <: A[k] ) }

					
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



procedure partition <t> (A: array t, left, right: int, pivot: t)
	returns(low_index, high_index: int, B: array t)
	requires left <= right;
	ensures low_index == high_index;	
	ensures is_LT_pivot(pivot, B, left, right, low_index+1, high_index);
	ensures is_GT_pivot(pivot, B, left, right, low_index, high_index);
{
	var i: int;
	
	low_index, high_index := left, right;
	B := A;
	
	while ( low_index != high_index )
	invariant ( low_index <= high_index );
	invariant ( is_LT_pivot(pivot, B, left, right, low_index, high_index) );
	invariant ( is_GT_pivot(pivot, B, left, right, low_index, high_index) );	
	{
		while ( low_index != high_index  &&  B[low_index] <: pivot )
		invariant ( low_index <= high_index );			
		invariant ( is_LT_pivot(pivot, B, left, right, low_index, high_index) );
		invariant ( is_GT_pivot(pivot, B, left, right, low_index, high_index) );	
		{
			low_index := low_index + 1;
		}
		while ( low_index != high_index  &&  pivot <: B[high_index] )
		invariant ( low_index <= high_index );		
		invariant ( is_LT_pivot(pivot, B, left, right, low_index, high_index) );
		invariant ( is_GT_pivot(pivot, B, left, right, low_index, high_index) );	
		{
			high_index := high_index - 1;
		}
		call B := swap(B, low_index, high_index);
	}
	
	if ( pivot <: B[low_index] )
	{
		low_index := low_index - 1;
		high_index := low_index;
	}
}
