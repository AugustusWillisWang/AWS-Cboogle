// Program: Binary Search Trees
// Author: Carlo A. Furia


// Node type
type ref;
const Void: ref;
// Value (key) type
type G = int;
// Node --> Node
type LINK = [ref] ref;
// Node --> Value
type VAL = [ref] G;


// Left child
var left: LINK;
// Right child
var right: LINK;
// Parent
var parent: LINK;
// Values
var value: VAL;
// Root
var root: ref;


// binary tree invariant
function is_tree(l, r, p: LINK, v: VAL) returns(bool);
axiom (forall l, r, p: LINK, v: VAL, n: ref :: is_tree(l, r, p, v) && n != Void && p[n] != Void  ==>  n == r[p[n]] || n == l[p[n]] );
axiom (forall l, r, p: LINK, v: VAL, n: ref :: is_tree(l, r, p, v) && n != Void && l[n] != Void  ==>  p[l[n]] == n );
axiom (forall l, r, p: LINK, v: VAL, n: ref :: is_tree(l, r, p, v) && n != Void && r[n] != Void  ==>  p[r[n]] == n );

// binary search tree is a special kind of binary tree
function is_bst(l, r, p: LINK, v: VAL) returns(bool);
axiom (forall l, r, p: LINK, v: VAL :: is_bst(l, r, p, v) ==> is_tree(l, r, p, v));
// Invariant property of bst (not actually used)
// axiom (forall l, r, p: LINK, v: VAL, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, l[x], y) ==> v[y] <= v[x]);
// axiom (forall l, r, p: LINK, v: VAL, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, r[x], y) ==> v[y] >= v[x]);

// Add `node' to the tree
procedure put_bst (node: ref) returns (Result: ref)
	requires is_bst(left, right, parent, value);
	requires node != Void;
	requires !in(left, right, parent, value, root, node);
	requires parent[root] == Void;  // This is an invariant of bst, which we encode as precondition for simplicity
	requires left[node] == Void && right[node] == Void;
	modifies left, right, parent, root;
	ensures parent[root] == Void;
	ensures in(left, right, parent, value, root, node);		// Cannot prove this post if switched with the next one!
	ensures is_bst(left, right, parent, value);
{
	var x, y: ref;
	y := Void;
	x := root;
	while (x != Void)
		invariant is_bst(left, right, parent, value);
		invariant in(left, right, parent, value, root, x);
		invariant y != Void ==> left[y] == x || right[y] == x;
		invariant y != Void ==> in(left, right, parent, value, root, y);
		invariant root != Void && x == Void ==> y != Void;
		invariant x == Void ==> inode(left, right, parent, value, root, value[node]) == y;
		invariant x != Void ==> inode(left, right, parent, value, root, value[node]) == inode(left, right, parent, value, x, value[node]);
	{
		y := x;
		if (value[node] < value[x]) {
			x := left[x];
		} else {
			x := right[x];
		}
	}
	parent[node] := y;
	if (y == Void) {
		root := node;
	} else {
		if (value[node] < value[y]) {
			left[y] := node;
		} else {
			right[y] := node;
		}
	}
}


// Node with the successor value in the tree
procedure successor_bst (node: ref) returns (Result: ref)
	requires is_bst(left, right, parent, value);
	requires node != Void;
	ensures Result == succ(left, right, parent, value, node);
{
	var x, y: ref;
	x := node;
	if ( right[x] != Void ) {
		call Result := minimum_bst (right[x]);
	} else {
		y := parent[x];
		while ( y != Void && x == right[y] )
			invariant is_bst(left, right, parent, value);
			invariant y == parent[x];  // not necessary for the proof
			invariant x != Void;
			invariant lowest_ancestor_leftchild(left, right, parent, value, x) == lowest_ancestor_leftchild(left, right, parent, value, node);
		{
			x := y;
			y := parent[y];
		}
		Result := y;
	}
}


// Node with the minimum value in the tree rooted in `node'
procedure minimum_bst (node: ref) returns (Result: ref)
	requires is_bst(left, right, parent, value);
	requires node != Void;
	ensures Result == leftmost(left, right, parent, value, node);
	ensures min(left, right, parent, value, node) == value[Result];
{
	var x: ref;
	x := node;
	while ( left[x] != Void )
		invariant is_bst(left, right, parent, value);
		invariant in(left, right, parent, value, node, x);
		invariant x != Void;
		invariant leftmost(left, right, parent, value, x) == leftmost(left, right, parent, value, node);
	{
		x := left[x];
	}
	Result := x;
}


 // Node with value `key' if one exists, otherwise Void
 procedure has_bst (key: G) returns (Result: ref)
	requires is_bst(left, right, parent, value);
	requires root != Void;
	ensures has(left, right, parent, value, root, key) ==> in(left, right, parent, value, root, Result) && value[Result] == key;
	ensures !has(left, right, parent, value, root, key) ==> Result == Void;
{
	Result := root;
	while ( Result != Void && value[Result] != key ) 
		invariant is_bst(left, right, parent, value);
		invariant Result != Void ==> in(left, right, parent, value, root, Result);
		invariant has(left, right, parent, value, root, key) ==> Result != Void && has(left, right, parent, value, Result, key);
	{
		if ( key < value[Result] ) {
			Result := left[Result];
		} else {
			Result := right[Result];
		}
	}
}
// Invariance when adding node:
	// To an empty tree
axiom (forall l, r, p: LINK, v: VAL, n, x: ref :: is_bst(l, r, p, v) && in(l, r, p, v, n, n) && inode(l, r, p, v, n, v[x]) == n && l[x] == Void && r[x] == Void && 
															n == Void  ==>  is_bst(l, r, p[x := n], v));
	// As left child
axiom (forall l, r, p: LINK, v: VAL, n, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, n, y) && inode(l, r, p, v, n, v[x]) == y && l[x] == Void && r[x] == Void && 
															n != Void && v[x] <= v[y]  ==>  is_bst(l[y := x], r, p[x := y], v) && in(l[y := x], r, p[x := y], v, n, x));
	// As right child
axiom (forall l, r, p: LINK, v: VAL, n, x, y: ref :: is_bst(l, r, p, v) && in(l, r, p, v, n, y) && inode(l, r, p, v, n, v[x]) == y && l[x] == Void && r[x] == Void && 
															n != Void && v[x] >= v[y]  ==>  is_bst(l, r[y := x], p[x := y], v) && in(l, r[y := x], p[x := y], v, n, x));

// node y is in the tree rooted in x
function in(l, r, p: LINK, v: VAL, x, y: ref) returns(bool);
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_tree(l, r, p, v) ==> in(l, r, p, v, n, n));
axiom (forall l, r, p: LINK, v: VAL, n, x: ref  ::  is_tree(l, r, p, v) && in(l, r, p, v, n, x) ==> in(l, r, p, v, n, l[x]) && in(l, r, p, v, n, r[x]));

// value k is in the tree rooted in n
function has(l, r, p: LINK, v: VAL, n: ref, k: G) returns(bool)
{ (exists x: ref :: x != Void && in(l, r, p, v, n, x) && v[x] == k) }
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && has(l, r, p, v, n, k) && k < v[n] ==> l[n] != Void && has(l, r, p, v, l[n], k));
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && has(l, r, p, v, n, k) && k > v[n] ==> r[n] != Void && has(l, r, p, v, r[n], k));
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && has(l, r, p, v, n, k) && l[n] == Void ==> k >= v[n]);
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && has(l, r, p, v, n, k) && r[n] == Void ==> k <= v[n]);

// leftmost node in the tree rooted in `n'
function leftmost(l, r, p: LINK, v: VAL, n: ref) returns(ref);
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_bst(l, r, p, v) && n != Void && l[n] == Void ==> leftmost(l, r, p, v, n) == n);
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_bst(l, r, p, v) && n != Void && l[n] != Void ==> leftmost(l, r, p, v, l[n]) == leftmost(l, r, p, v, n));

// minimum value in the tree rooted in `n'
function min(l, r, p: LINK, v: VAL, n: ref) returns(int)
{ v[leftmost(l, r, p, v, n)] }

// lowest ancestor of node `n' whose left child is also an ancestor
function lowest_ancestor_leftchild(l, r, p: LINK, v: VAL, n: ref) returns(ref);
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_bst(l, r, p, v) && n != Void && p[n] == Void ==> 
																	lowest_ancestor_leftchild(l, r, p, v, n) == Void);
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_bst(l, r, p, v) && n != Void && p[n] != Void && l[p[n]] == n ==> 
																	lowest_ancestor_leftchild(l, r, p, v, n) == p[n]);
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_bst(l, r, p, v) && n != Void && p[n] != Void && r[p[n]] == n ==> 
																	lowest_ancestor_leftchild(l, r, p, v, n) == lowest_ancestor_leftchild(l, r, p, v, p[n]));

// successor node of node `n'
function succ(l, r, p: LINK, v: VAL, n: ref) returns(ref);
// the successor of a node with right subtree is the subtree's leftmost node
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_bst(l, r, p, v) && n != Void && r[p[n]] == n ==> succ(l, r, p, v, p[n]) == leftmost(l, r, p, v, n));
// the successor of a node n with no right subtree is n's lowest ancestor whose left child is also an ancestor
axiom (forall l, r, p: LINK, v: VAL, n: ref  ::  is_bst(l, r, p, v) && n != Void && r[n] == Void ==> succ(l, r, p, v, n) == lowest_ancestor_leftchild(l, r, p, v, n));

// insertion node for a new node with value `k' in tree rooted in `n'
function inode(l, r, p: LINK, v: VAL, n: ref, k: G) returns (ref);
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n == Void ==> inode(l, r, p, v, n, k) == n);
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && l[n] == Void && k <= v[n] ==> inode(l, r, p, v, n, k) == n);
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && r[n] == Void && k >= v[n] ==> inode(l, r, p, v, n, k) == n);
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && l[n] != Void && k <= v[n] ==> inode(l, r, p, v, n, k) == inode(l, r, p, v, l[n], k));
axiom (forall l, r, p: LINK, v: VAL, n: ref, k: G  ::  is_bst(l, r, p, v) && n != Void && r[n] != Void && k >= v[n] ==> inode(l, r, p, v, n, k) == inode(l, r, p, v, r[n], k));

