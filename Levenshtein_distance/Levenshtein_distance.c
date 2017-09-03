// Program: Levenshtein distance 求两个字符串之间的最小距离

// Generic type
#typedef T char

// Ternary minimum (uninterpreted)
// function min (a, b, c: int) returns (int);

// // Levenshtein distance: recursive definition
// function distance (s, t: array T, m, n: int) returns(int);
// axiom ( forall s, t: array T :: distance(s, t, 0, 0) == 0 );
// axiom ( forall s, t: array T, m: int :: m > 0 ==> distance(s, t, m, 0) == m );
// axiom ( forall s, t: array T, n: int :: n > 0 ==> distance(s, t, 0, n) == n );
// axiom ( forall s, t: array T, m, n: int :: m > 0 && n > 0 && s[m] == t[n] ==> 
// 				distance(s, t, m, n) == distance(s, t, m-1, n-1) );
// axiom ( forall s, t: array T, m, n: int :: m > 0 && n > 0 && s[m] != t[n] ==> 
// 				distance(s, t, m, n) == 1 + min( distance(s, t, m-1, n), distance(s, t, m-1, n), distance(s, t, m-1, n-1) ) );

			
int Levenshtein_distance (T* s,T* t,int m,int n)
	// returns(Result: int)
	// requires m >= 0;
	// requires n >= 0;
	// ensures Result == distance (s, t, m, n);
{
    assert(m>=0);
    assert(n>=0);
	int i,j;
	int* d[m+1][n+1]={0};
	for (int i=0;i<=m;i++){
        d[0][i]=i;
    }
    for(int i=0;i<=n;i++){
        d[i][0]=i;
        }
	// Initialization of matrix "d" for base values
	// // havoc d;
	// assume ( ( d[0, 0] == 0 )  &&
	// 		 ( forall x: int :: 1 <= x && x <= m ==> d[x, 0] == x ) &&
	// 		 ( forall y: int :: 1 <= y && y <= n ==> d[0, y] == y ) );
	
	i = 1;
	while ( i <= m )
	// invariant 0 <= i && i <= m;
	// invariant ( forall h, k: int :: 0 <= h && h <= i-1 && 0 <= k && k <= n ==> d[h, k] == distance(s, t, h, k) );
	{
		j = 1;
		while ( j <= n )
		// invariant 0 <= i && i <= m ;
		// invariant 0 <= j && j <= n ;
		// invariant ( forall h, k: int :: 0 <= h && h <= i-1 && 0 <= k && k <= j-1 ==> d[h, k] == distance(s, t, h, k) );
		{
			if ( s[i] == t[j] ) {
				d[i, j] = d[i - 1, j - 1];
			} else {
				d[i, j] = 1 + min(d[i - 1, j - 1], d[i, j - 1], d[i - 1, j]);
			}
		}
	}
	Result = d[m, n];

