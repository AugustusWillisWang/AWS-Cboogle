// Program: Welfare crook (detection) problem
// Author: Carlo A. Furia


type array t = [int] t;

// integer arrays are assumed for simplicity
// also, arrays are assumed ordered implicitly
var F: array int;
var G: array int;
var H: array int;

function is_crook (left: int, i: int, j: int, k: int, A: array int, B: array int, C: array int) returns (bool)
{  i >= left  &&  j >= left  && k >= left  && A[i] == B[j]  &&  B[j] == C[k]  }

function has_crook (left: int, n1: int, n2: int, n3: int, A: array int, B: array int, C: array int) returns (bool)
{ ( exists i, j, k: int :: i <= n1 && j <= n2 && k <= n3 && is_crook(left, i, j, k, A, B, C) ) }
axiom ( forall left: int, n1: int, n2: int, n3: int, A: array int, B: array int, C: array int ::
		!has_crook (left, n1, n2, n3, A, B, C) && A[n1+1] != B[n2+1]  ==>  !has_crook (left, n1+1, n2, n3, A, B, C) );
axiom ( forall left: int, n1: int, n2: int, n3: int, A: array int, B: array int, C: array int ::
		!has_crook (left, n1, n2, n3, A, B, C) && B[n2+1] != C[n3+1]  ==>  !has_crook (left, n1, n2+1, n3, A, B, C) );
axiom ( forall left: int, n1: int, n2: int, n3: int, A: array int, B: array int, C: array int ::
		!has_crook (left, n1, n2, n3, A, B, C) && C[n3+1] != A[n1+1]  ==>  !has_crook (left, n1, n2, n3+1, A, B, C) );

function earliest_crook (left: int, i: int, j: int, k: int, A: array int, B: array int, C: array int) returns (bool);
axiom ( forall left: int, i: int, j: int, k: int, A: array int, B: array int, C: array int ::
			earliest_crook(left, i, j, k, A, B, C)  ==>  is_crook(left, i, j, k ,A, B, C) );
axiom ( forall left: int, i: int, j: int, k: int, A: array int, B: array int, C: array int, i2: int, j2: int, k2: int ::
			earliest_crook(left, i, j, k, A, B, C) && A[i+1] < B[j+1]  ==>  earliest_crook(left, i+1, j, k, A, B, C) );
axiom ( forall left: int, i: int, j: int, k: int, A: array int, B: array int, C: array int, i2: int, j2: int, k2: int ::
			earliest_crook(left, i, j, k, A, B, C) && B[j+1] < C[k+1]  ==>  earliest_crook(left, i, j+1, k, A, B, C) );
axiom ( forall left: int, i: int, j: int, k: int, A: array int, B: array int, C: array int, i2: int, j2: int, k2: int ::
			earliest_crook(left, i, j, k, A, B, C) && C[k+1] < A[i+1]  ==>  earliest_crook(left, i, j, k+1, A, B, C) );

					

procedure find_crook (left: int)
	returns (p_f, p_g, p_h: int)
	ensures p_f+1 >= left && p_g+1 >= left && p_h+1 >= left;
	ensures has_crook(left, p_f, p_g, p_h, F, G, H)  ==>  earliest_crook(left, p_f, p_g, p_h, F, G, H);
{
	p_f, p_g, p_h := left-1, left-1, left-1;
	
	while ( F[p_f+1] != G[p_g+1]  ||  G[p_g+1] != H[p_h+1] )
	invariant p_f+1 >= left && p_g+1 >= left && p_h+1 >= left;
	invariant has_crook(left, p_f, p_g, p_h, F, G, H)  ==>  earliest_crook(left, p_f, p_g, p_h, F, G, H);
	{
		if ( F[p_f+1] < G[p_g+1] ) {
			p_f := p_f + 1;
		} else {
			if ( G[p_g+1] < H[p_h+1] ) {
				p_g := p_g + 1;
			} else { 
					 // assert ( H[p_h+1] < F[p_f+1] );
					 p_h := p_h + 1;
			}
		}
	}
}

