// Program: Unbounded knapsack with integer weights
// Author: Carlo A. Furia


type array G = [int] G;

// a[1..n] > 0
function is_positive_array (a: array int, n: int) returns (bool)
{ ( forall k: int :: 1 <= k && k <= n ==> a[k] > 0 ) }

// max_knapsack (b, v, w, n) = K(b): uninterpreted
function max_knapsack (b: int, v: array int, w: array int, n: int) returns (int);
// K(0) = 0
axiom ( forall v: array int, w: array int, n: int :: n > 0 && is_positive_array(w, n) ==> max_knapsack(0, v, w, n) == 0 );

// best_value (b, v, w, j, n)
function best_value (b: int, v: array int, w: array int, j, n: int) returns (int);
// base case: b = 0, j = 0
axiom ( forall b: int, v: array int, w: array int, n: int :: b > 0 && n > 0 ==> best_value(0, v, w, 0, n) == 0 );
// base case: b > 0, j = 0
axiom ( forall b: int, v: array int, w: array int, n: int :: b > 0 && n > 0 ==> best_value(b, v, w, 0, n) == max_knapsack(b - 1, v, w, n) );
// inductive case (preservation): w[j] > b
axiom ( forall b: int, v: array int, w: array int, j, n: int :: 0 < j && j <= n && is_positive_array(w, n) && b > 0 && w[j] > b 
				==> best_value(b, v, w, j, n) == best_value(b, v, w, j - 1, n) );
// inductive case (preservation): m[b] >= v[j] + m[b - w[j]]
axiom ( forall b: int, v: array int, w: array int, j, n: int :: 0 < j && j <= n && is_positive_array(w, n) && b > 0 && 
		best_value(b, v, w, j - 1, n) >= v[j] + max_knapsack(b - w[j], v, w, n)
				==> best_value(b, v, w, j, n) == best_value(b, v, w, j - 1, n) );
// inductive case (progress): w[n] <= b && m[b] < v[n] + m[b - w[n]]
axiom ( forall b: int, v: array int, w: array int, j, n: int :: 0 < j && j <= n && is_positive_array(w, n) && b > 0 && 
		w[j] <= b && best_value(b, v, w, j - 1, n) < v[j] + max_knapsack(b - w[j], v, w, n)
				==> best_value(b, v, w, j, n) == v[j] + max_knapsack(b - w[j], v, w, n) );
			
// Domain property (introduced as axiom, used to prove inductiveness of the main loop invariant):
//	best_value(b, v, w, n, n) = max_knapsack(b, v, w, n)
axiom ( forall b: int, v: array int, w: array int, n: int :: 
			n > 0 && is_positive_array(w, n) && b > 0 ==> best_value(b, v, w, n, n) == max_knapsack(b, v, w, n) );

			
procedure knapsack (v, w: array int, n, weight: int)
	returns(Result: int)
	requires weight >= 0;
	requires n >= 1;
	requires is_positive_array(w, n);
	ensures Result == max_knapsack (weight, v, w, n);
{
	var b, j: int;
	var m: array int;
		
	b := 0;
	m[0] := 0;

	while ( b != weight )
	invariant ( 0 <= b && b <= weight );
	invariant ( forall k: int :: 0 <= k && k <= b ==> m[k] == max_knapsack(k, v, w, n) );
	{
		b := b + 1;
		j := 0;
		m[b] := m[b - 1];
		while ( j != n )
		invariant ( 0 <= b && b <= weight );
		invariant ( 0 <= j && j <= n );
		invariant ( forall k: int :: 0 <= k && k <= b - 1 ==> m[k] == max_knapsack(k, v, w, n) );
		invariant ( m [b] == best_value(b, v, w, j, n) );
		{
			j := j + 1;
			if ( w[j] <= b && m[b] < v[j] + m[b - w[j]] ) {
				m[b] := v[j] + m[b - w[j]];
			}
		}
	} 
	Result := m[weight];
}
