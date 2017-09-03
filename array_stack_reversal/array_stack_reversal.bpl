// Program: Reversal of an array using a stack
// Author: Carlo A. Furia


type array t = [int] t;

type q;

var A: array q;

var top: int;
var bottom: int;
var s: array q;

procedure s.make ()
	modifies top, bottom;
	ensures bottom == top;
{
	bottom := 0;
	top := 0;
}

function empty(low: int, high: int) returns(bool)
{ high <= low }

procedure s.empty () returns (is_empty: bool)
	ensures is_empty <==> empty(bottom, top);
{
	is_empty := top <= bottom;
}

procedure s.sequence () returns(a_sequence: array q)
	ensures a_sequence == s;
{
	a_sequence := s;
}

procedure s.top() returns(top_element: q)
	requires !empty(bottom, top);
	ensures top_element == s[top - 1];
{
	top_element := s[top - 1];
}

procedure s.pop() returns(top_element: q)
	modifies top;
	requires !empty(bottom, top);
	ensures top + 1 == old(top);
	ensures s[top] == top_element;
{
	call top_element := s.top();
	top := top - 1;
}

procedure s.push(new_element: q)
	modifies top, s;
	ensures top == old(top) + 1;
	ensures s[top - 1] == new_element;
	ensures s == old(s)[old(top) := new_element];
{
	s[top] := new_element;
	top := top + 1;
}

// A[low_A..low_A+length-1] == B[low_B..low_B+length-1]
function seq_equal_from_to(A: array q, B: array q, low_A: int, low_B: int, length: int)
	returns(bool);
axiom ( forall A: array q, B: array q, low_A: int, low_B: int, length: int ::
		length < 1  ==>  seq_equal_from_to(A, B, low_A, low_B, length) );
axiom ( forall A: array q, B: array q, low_A: int, low_B: int, length: int ::
		length >= 1  &&
			A[low_A + length - 1] == B[low_B + length - 1] &&
			seq_equal_from_to(A, B, low_A, low_B, length - 1)
			==>  seq_equal_from_to(A, B, low_A, low_B, length) );
axiom ( forall A: array q, B: array q, low_A: int, low_B: int, length: int ::
		length >= 1  &&
			A[low_A + length - 1] != B[low_B + length - 1]
			==>  !seq_equal_from_to(A, B, low_A, low_B, length) );
axiom ( forall A_old: array q, A: array q, B: array q, low_A: int, low_B: int, length: int ::
		seq_equal_from_to(A_old, B, low_A, low_B, length)
		&& ( forall i: int :: low_A <= i && i < low_A + length ==> A[i] == A_old[i] )
			==> seq_equal_from_to(A, B, low_A, low_B, length) );
			

// A[low_A, high_A] + reverse(B[low_B, high_B]) == C[low_C, high_C]
function seq_cat_reverse_equals(A: array q, low_A: int, high_A: int,
								B: array q, low_B: int, high_B: int,
								C: array q, low_C: int, high_C: int)
	returns(bool);
axiom ( forall 	A: array q, low_A: int, high_A: int,
				B: array q, low_B: int, high_B: int,
				C: array q, low_C: int, high_C: int ::
		high_C - low_C != high_A - low_A + high_B - low_B + 1
			==>  !seq_cat_reverse_equals(A, low_A, high_A, B, low_B, high_B, C, low_C, high_C) );
axiom ( forall 	A: array q, low_A: int, high_A: int,
				B: array q, low_B: int, high_B: int,
				C: array q, low_C: int, high_C: int ::
		high_C - low_C == high_A - low_A + high_B - low_B + 1
		&& high_B < low_B  && seq_equal_from_to(A, C, low_A, low_C, high_C - low_C + 1)
			==>  seq_cat_reverse_equals(A, low_A, high_A, B, low_B, high_B, C, low_C, high_C) );
axiom ( forall 	A: array q, low_A: int, high_A: int,
				B: array q, low_B: int, high_B: int,
				C: array q, low_C: int, high_C: int ::
		high_C - low_C == high_A - low_A + high_B - low_B + 1
		&& seq_cat_reverse_equals(A, low_A, high_A, B, low_B, high_B, C, low_C, high_C)
		&& high_A >= low_A  &&  high_B >= low_B-1  &&  A[high_A] == B[high_B+1]
			==>  seq_cat_reverse_equals(A, low_A, high_A-1, B, low_B, high_B+1, C, low_C, high_C) );
axiom ( forall 	A: array q, low_A: int, high_A: int,
				B_old: array q, low_B: int, high_B: int, B: array q,
				C: array q, low_C: int, high_C: int ::
		seq_cat_reverse_equals(A, low_A, high_A, B_old, low_B, high_B, C, low_C, high_C)
		&& ( forall i: int :: low_B <= i && i <= high_B ==> B[i] == B_old[i] )
		==>  seq_cat_reverse_equals(A, low_A, high_A, B, low_B, high_B, C, low_C, high_C) );


			
			
procedure stack_reverse (n: int)
	modifies A, s, top, bottom;
	requires n > 0;
	// s[bottom, top-1] + reverse(A[1, n]) == old(A)[1, n]
	ensures seq_cat_reverse_equals (s, bottom, top-1, A, 1, n, old(A), 1, n);
	ensures top - bottom == 0;
{
	var val: q;
	var i: int;
		
	i := 1;
	call s.make();
	while ( i <= n )
	invariant i <= n + 1;
	invariant A == old(A);
	invariant top - bottom == i - 1;
	invariant seq_equal_from_to(s, A, bottom, 1, i - 1); 
	{
		call s.push(A[i]);
		i := i + 1;
	}
	i := 1;
	while ( i <= n )
	invariant i <= n + 1;
	invariant top - bottom + i - 1 == n;
	invariant seq_cat_reverse_equals(s, bottom, top-1, A, 1, i-1, old(A), 1, n);
	{
		call val := s.pop();
		A[i] := val;
		// this is needed to make it go trough
		assert ( seq_cat_reverse_equals(s, bottom, top, A, 1, i-1, old(A), 1, n) );		
		i := i + 1;
	}
}

