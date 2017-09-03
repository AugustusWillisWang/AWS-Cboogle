// Program: Sum of the elements in an array
// Author: Carlo A. Furia


type array t = [int] t;

// sum of content of A from position to position
function sum_from_to(array int, int, int) returns(int);
axiom ( forall A: array int, low, high: int ::
				high < low   ==>  sum_from_to(A,low,high) == 0 );
axiom ( forall A: array int, low, high: int ::
				high >= low  ==>  sum_from_to(A,low,high-1) + A[high] == sum_from_to(A,low,high) );

				
// Boogie cannot check this without user-provided invariant
procedure sum (A: array int, n: int) returns(s: int)
	requires n >= 0;
	ensures s == sum_from_to(A, 1, n);
{
	var i: int;
	i := 1;  s := 0;
	while ( i <= n )
	invariant ( 1 <= i  &&  i <=  n + 1);
	invariant ( s == sum_from_to(A, 1, i - 1) );
	{
		s := s + A[i];
		i := i + 1;
	}
	return;
}
