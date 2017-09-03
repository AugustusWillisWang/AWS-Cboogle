// Program: List reversal
// Author: Carlo A. Furia


type ref;
const Void: ref;
type G;
type LIST _ = ref;
type NEXT _ = [ref] ref;
type VALS _ = [ref] _;
type SEQ _ = [int] _;


	// The sequence "s" from "ls" to "us" is a consistent representation of list "h" with references "n" to the next cells and values "v"
function consistent (h: LIST G, n: NEXT G, v: VALS G, s: SEQ G, ls, us: int) returns (bool);
	// The representation of an empty list is an empty sequence
axiom ( forall n: NEXT G, v: VALS G, s: SEQ G, ls, us: int  ::  consistent(Void, n, v, s, ls, us) <==> us < ls );
	// The representation of a non-empty consistent list is a non-empty sequence
axiom ( forall h: LIST G, n: NEXT G, v: VALS G, s: SEQ G, ls, us: int  ::  h != Void && us < ls ==> !consistent(h, n, v, s, ls, us) );
	// The representation of the rest of a consistent non-empty list "h" is the rest of "h"'s representation
axiom ( forall h: LIST G, n: NEXT G, v: VALS G, s: SEQ G, ls, us: int  ::  
			h != Void && consistent(h, n, v, s, ls, us) ==> consistent(n[h], n, v, s, ls + 1, us) && s[ls] == v[h] );
	// Changing "next" in the first cell of a consistent list does not affect the consistency of the list's rest
axiom ( forall h: LIST G, n: NEXT G, v: VALS G, s: SEQ G, ls, us: int, x: LIST G  ::  
			h != Void && consistent(n[h], n, v, s, ls + 1, us) ==> consistent(n[h], n[h := x], v, s, ls + 1, us) );


	// Reversal of sequence "s" from "ls" to "us"
function rev (s: SEQ G, ls, us: int) returns (r: SEQ G);
	// The reversal of an empty sequence is the sequence itself
axiom ( forall s: SEQ G, ls, us: int :: us < ls ==> rev(s, ls, us) == s );
	// Inductive property of "rev" w.r.t. "cat" for sequences "s" from "ls" to "us" and "t" from "lt" to "ut"
axiom ( forall s: SEQ G, ls, us: int, t: SEQ G, lt, ut: int  ::
			us >= ls   ==>   cat(rev(s, ls, us), ls, us, t, lt, ut) ==
							 cat(rev(s, ls + 1, us), ls + 1, us, t[lt - 1 := s[ls]], lt - 1, ut) );

							 
	// Concatenation of sequence "s" from "ls" to "us" and sequence "t" from "lt" to "ut"
function cat (s: SEQ G, ls, us: int, t: SEQ G, lt, ut: int) returns (ct: SEQ G);
	// If "s" is empty, the concatenation is just "t"
axiom ( forall s: SEQ G, ls, us: int, t: SEQ G, lt, ut: int  ::  us < ls ==> cat(s, ls, us, t, lt, ut) == t );
	// If "t" is empty, the concatenation is just "s"
axiom ( forall s: SEQ G, ls, us: int, t: SEQ G, lt, ut: int  ::  ut < lt ==> cat(s, ls, us, t, lt, ut) == s );


// Uninterpreted
function acyclic (h: LIST G, n: NEXT G) returns (bool);


// LIST TO BE REVERSED: reference to first cell
var list: LIST G;
// LIST TO BE REVERSED: reference to next cells
var list.next: NEXT G;
// LIST TO BE REVERSED: values stored in cells
var list.values: VALS G;
// LIST TO BE REVERSED: sequence of values
var list.seq: SEQ G;
// LIST TO BE REVERSED: sequence beginning at index
var list.lower: int;
// LIST TO BE REVERSED: sequence ending at index
var list.upper: int;


procedure reverse ()
	modifies list, list.next, list.values, list.seq, list.lower, list.upper;
	requires consistent (list, list.next, list.values, list.seq, list.lower, list.upper);
	requires acyclic (list, list.next);
	ensures list.seq == rev(old(list.seq), old(list.lower), old(list.upper));
{
	var temp: LIST G;

	// "reversed" list
	var reversed: LIST G;
	var reversed.next: NEXT G;
	var reversed.values: VALS G;
	var reversed.seq: SEQ G;
	var reversed.lower: int;
	var reversed.upper: int;
	
	reversed := Void;
	havoc reversed.next, reversed.values, reversed.seq, reversed.lower, reversed.upper;
	assume consistent (reversed, reversed.next, reversed.values, reversed.seq, reversed.lower, reversed.upper);
	while ( list != Void )
	invariant consistent (list, list.next, list.values, list.seq, list.lower, list.upper);
	invariant consistent (reversed, reversed.next, reversed.values, reversed.seq, reversed.lower, reversed.upper);
	invariant cat (rev (list.seq, list.lower, list.upper), list.lower, list.upper, reversed.seq, reversed.lower, reversed.upper) == rev (old(list.seq), old(list.lower), old(list.upper));
	{		// Indented code updates list representations to preserve consistency
		temp := list.next[list];
		list.next[list] := reversed;
			reversed.next [list] := reversed;
			reversed.values [list] := list.values[list];
		reversed := list;
			reversed.lower := reversed.lower - 1;
			reversed.seq [reversed.lower] := list.values[list];
		list := temp;
			list.lower := list.lower + 1;
			// This property is assumed for simplicity: proving it would require reasoning about non sharing,
			// to guarantee that the element moved from "list" to the front of "reversed" is not already a member of "reversed"
			assume consistent (reversed, reversed.next, reversed.values, reversed.seq, reversed.lower, reversed.upper);
	}
	list := reversed;
		list.next := reversed.next;
		list.values := reversed.values;
		list.seq := reversed.seq;
		list.lower := reversed.lower;
		list.upper := reversed.upper;
}
