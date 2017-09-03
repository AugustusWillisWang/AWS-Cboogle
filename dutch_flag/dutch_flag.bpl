// Program: Dutch flag problem
// Author: Carlo A. Furia


type array t = [int] t;

type COLOR;
const unique Blue: COLOR;
const unique White: COLOR;
const unique Red: COLOR;

function is_flag_color ( col: COLOR ) returns (bool)
{ col == Blue  ||  col == White  ||  col == Red }

type ARRAY_COLOR = array COLOR;

function is_flag_color_array ( A: ARRAY_COLOR, low: int, high: int) returns (bool)
{ ( forall i: int :: low <= i && i <= high  ==>  is_flag_color(A[i]) ) }

function monochrome ( A: ARRAY_COLOR, low: int, high: int, col: COLOR) returns (bool)
{ ( forall i: int :: low <= i && i <= high  ==>  A[i] == col ) }


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


procedure make_flag (A: ARRAY_COLOR, n: int)
	returns (B: ARRAY_COLOR, b: int, r: int)
	requires n >= 1;
	requires is_flag_color_array(A, 1, n);
	ensures 1 <= b;
	ensures b <= r;
	ensures r <= n+1;
	ensures monochrome(B, 1, b-1, Blue);
	ensures monochrome(B, b, r-1, White);	
	ensures monochrome(B, r, n, Red);
{
	var i: int;

	B := A;
	b, i, r := 1, 1, n+1;
	
	while ( i < r )
	invariant is_flag_color_array(B, 1, n);	
	invariant ( 1 <= b  &&  b <= i  &&  i <= r && r <= n+1 );
	invariant ( monochrome(B, 1, b-1, Blue) );
	invariant ( monochrome(B, b, i-1, White) );	
	invariant ( monochrome(B, r, n, Red) );
	{
		if (B[i] == Blue)
		{
			call B := swap(B, b, i);
			i := i + 1;
			b := b + 1;
		}
		else
		{
			if (B[i] == White)
			{
				i := i + 1;
			}
			else
			{
				r := r - 1;
				call B := swap(B, r, i);
			}
		}
	}
}

