/*
 * @Author: Augustus.Wang 
 * @Date: 2017-07-18 20:54:50 
 * @Last Modified by: Augustus.Wang
 * @Last Modified time: 2017-07-18 22:24:33
 */
//bst

#define valuetype int
#include <stdlib.h>
#include <stdio.h>

void error(){
    printf("error!");
}

struct Node{
    valuetype value;
    struct Node* left;
    struct Node *right;
    struct Node* parent;
}

struct Node Node={
    0,
    Null,
    Null,
    Null
}

struct Bst{
    struct Node* root;
}


// //setupabst
// struct Bst newtree={0,Null,Null,Null};


// Add `node' to the tree
struct Bst put_bst (struct Bst bst,valuetype value)
	// requires is_bst(left, right, parent, value);
	// requires node != Void;
	// requires !in(left, right, parent, value, root, node);
	// requires parent[root] == Void;  // This is an invariant of bst, which we encode as precondition for simplicity
	// requires left[node] == Void && right[node] == Void;
	// modifies left, right, parent, root;
	// ensures parent[root] == Void;
	// ensures in(left, right, parent, value, root, node);		// Cannot prove this post if switched with the next one!
	// ensures is_bst(left, right, parent, value);
{
	struct Node* root=bst.root;
    struct Node* now=root;
    struct Node* last=root;


    if (root=Null){
        struct Node new =(struct Node)malloc(sizeof(Node));
        new={value,Null,Null,Null};
        bsr.root=&new;
        return bsr;
    }

	while (now != Null)
	{
        last=now;
		if (value < now->value) {
			now = now->left;
		} else if(value>now->value) {
			now = now->right;
		} else error();
	}
	now=(struct Node)malloc(sizeof(Node));
    now*={
        value,
        Null,
        Null,
        last
    };
	if (value < last->value) {
		last->left= now;
	} else {
		last->right = now;
	}
	
}


// Node with the successor value in the tree

struct Node* successor(struct Node* inputnodepoint){
    if(inputnodepoint==Null)error;
    struct Node* x,y,result;
    x= inputnodepoint;
    if(x->right!=Null){
        result=minimum_bst(struct Bst temp ={x->right});
    }else{
        y=x->parent;
        while(y!=Null&&x==y->right){
            x=y;
            y=y->parent;
        }
        result=y;
    }
}
// procedure successor_bst (node: ref) returns (Result: ref)
// 	requires is_bst(left, right, parent, value);
// 	requires node != Void;
// 	ensures Result == succ(left, right, parent, value, node);
// {
// 	var x, y: ref;
// 	x := node;
// 	if ( right[x] != Void ) {
// 		call Result := minimum_bst (right[x]);
// 	} else {
// 		y := parent[x];
// 		while ( y != Void && x == right[y] )
// 			invariant is_bst(left, right, parent, value);
// 			invariant y == parent[x];  // not necessary for the proof
// 			invariant x != Void;
// 			invariant lowest_ancestor_leftchild(left, right, parent, value, x) == lowest_ancestor_leftchild(left, right, parent, value, node);
// 		{
// 			x := y;
// 			y := parent[y];
// 		}
// 		Result := y;
// 	}
// }


// Node with the minimum value in the tree rooted in `node'

struct Node minimum_bst(struct Bst bst){
    struct Node* root=bst.root;
    struct Node* x;
    x=root;
    while(x->left!=Null){
        x=x->left;
    }
    return x;
}
// procedure minimum_bst (node: ref) returns (Result: ref)
// 	requires is_bst(left, right, parent, value);
// 	requires node != Void;
// 	ensures Result == leftmost(left, right, parent, value, node);
// 	ensures min(left, right, parent, value, node) == value[Result];
// {
// 	var x: ref;
// 	x := node;
// 	while ( left[x] != Void )
// 		invariant is_bst(left, right, parent, value);
// 		invariant in(left, right, parent, value, node, x);
// 		invariant x != Void;
// 		invariant leftmost(left, right, parent, value, x) == leftmost(left, right, parent, value, node);
// 	{
// 		x := left[x];
// 	}
// 	Result := x;
// }
struct Node maximum_bst(struct Bst bst){
    struct Node* root=bst.root;
    struct Node* x;
    x=root;
    while(x->right!=Null){
        x=x->right;
    }
    return x;
}


// Node with value `key' if one exists, otherwise Void
struct Node has_bst(struct Bst bst,valuetype key){
    struct Node* result = bst.root;
    while(result!=Null&&result->value!=key){
      		if ( key < result->value ) {
			result =result->left;
		} else {
			result =result->right;
		}  
    }
    return result;
}
//  procedure has_bst (key: G) returns (Result: ref)
// 	requires is_bst(left, right, parent, value);
// 	requires root != Void;
// 	ensures has(left, right, parent, value, root, key) ==> in(left, right, parent, value, root, Result) && value[Result] == key;
// 	ensures !has(left, right, parent, value, root, key) ==> Result == Void;
// {
// 	Result := root;
// 	while ( Result != Void && value[Result] != key ) 
// 		invariant is_bst(left, right, parent, value);
// 		invariant Result != Void ==> in(left, right, parent, value, root, Result);
// 		invariant has(left, right, parent, value, root, key) ==> Result != Void && has(left, right, parent, value, Result, key);
// 	{
// 		if ( key < value[Result] ) {
// 			Result := left[Result];
// 		} else {
// 			Result := right[Result];
// 		}
// 	}
// }

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


int main(){
    //setupabst
    struct Bst newtree;
    newtree.root=Null;
}