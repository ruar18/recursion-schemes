/*
We want to sort the leaves of a tree. First we use a modified 
in-order recursion scheme, and then a modified BFTH scheme.  
A lot of work goes into proving the associativity of \otimes. 
*/
datatype tree = leaf(int) | node(tree, tree) 

/**** Defining helpers for the definition of F ****/

// Sorted(s) iff s is sorted in nondecreasing order
predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// SortedPlacement(s, a, i) ==> s[..i] + [a] + s[i..] is sorted
predicate SortedPlacement(s: seq<int>, a: int, i: int)
  requires 0 <= i <= |s|
  requires Sorted(s)
{
  (forall j :: 0 <= j < i ==> s[j] <= a) && 
  (forall j :: i <= j < |s| ==> s[j] >= a) 
}

// Finds 0 <= i <= |x| s.t. SortedPlacement(x, a, i)
function FindSortedPlacement(x: seq<int>, a: int): int 
  requires Sorted(x) 
  ensures 0 <= FindSortedPlacement(x, a) <= |x|
  ensures SortedPlacement(x, a, FindSortedPlacement(x, a))
{
  if x == [] then 0 
  else if x[0] < a then 1 + FindSortedPlacement(x[1..], a)
  else 0
}

// Inserting a new element in a sequence changes the multiset
// of the sequence as expected
lemma MultisetInsertion(x: seq<int>, a: int, i: int)
  requires 0 <= i <= |x| 
  ensures multiset(x[..i] + [a] + x[i..]) == multiset(x) + multiset([a])
  decreases i 
{
  if i == 0 {
    assert x[i..] == x;
  }
  else {
    // Just a bit of moving around elements in sequences
    calc == {
      multiset(x[..i-1]) + multiset([a]) + multiset(x[i-1..]);
        {assert x[i-1..] == [x[i-1]] + x[i..];}
      multiset(x[..i-1]) + multiset([a]) + multiset([x[i-1]]) + multiset(x[i..]);
      multiset(x[..i-1]) + multiset([x[i-1]]) + multiset([a]) + multiset(x[i..]);
        {assert x[..i] == x[..i-1] + [x[i-1]];}
      multiset(x[..i]) + multiset([a]) + multiset(x[i..]);
    }
    MultisetInsertion(x, a, i-1);
  }
}

/**** Defining the components of F  ****/

// This is the base case 
function f_0(x: seq<int>, a: int): seq<int>
  requires Sorted(x)
  ensures Sorted(f_0(x, a))
  ensures a in f_0(x, a) && |f_0(x,a)| == |x| + 1 
  ensures multiset(f_0(x,a)) == multiset(x) + multiset([a])
{
  var i := FindSortedPlacement(x, a);
  assert (0 <= i <= |x| && SortedPlacement(x, a, i));
  var s := x[..i] + [a] + x[i..];
  MultisetInsertion(x, a, i);
  s
}

function F(x: seq<int>, t: tree): seq<int> 
  decreases t
  requires Sorted(x)
  ensures Sorted(F(x,t))
{
  match t 
  case leaf(a) => f_0(x, a) // insert a into x while keeping it sorted
  case node(l, r) => F(F(x, l), r)
}

// The starting accumulator
const x_f: seq<int> := [];

function MainF(t: tree): seq<int> 
  ensures Sorted(MainF(t))
{
  F(x_f, t)
}

/**** Declaring helpers for the definition of G ****/

// Some desirable properties that we would like <combine> to have 
predicate IsMerge(r1: seq<int>, r2: seq<int>, s: seq<int>)
{
  (Sorted(s) && |s| == |r1| + |r2|) && 
  (forall a :: (a in r1 || a in r2) ==> a in s) 
}

// An inefficient merge function
function combine(r1: seq<int>, r2: seq<int>): seq<int> 
  requires Sorted(r1) && Sorted(r2) 
  ensures IsMerge(r1, r2, combine(r1, r2))
  decreases r2 
{
  var s:= if r2 == [] then r1 
  else if |r2| == 1 then f_0(r1, r2[0])
  else combine(f_0(r1, r2[|r2|-1]), r2[..|r2|-1]);
  s
} 

// Lemma that combine(r1, r2) contains the same element as the (multiset)
// union of r1 and r2 
lemma CombineIsUnion(r1: seq<int>, r2: seq<int>)
  requires Sorted(r1) && Sorted(r2) 
  ensures multiset(combine(r1, r2)) == multiset(r1) + multiset(r2)
  decreases r2
{
  var s := combine(r1, r2);
  if r2 == [] {}
  else if |r2| == 1 {}
  else {
    var n := |r2|;
    assert r2 == r2[..n-1] + [r2[n-1]]; // hint for the induction
  }
}

/**** Declaring components of G ****/

// This is the base case
function g_0(a: int): seq<int> 
  ensures Sorted(g_0(a))
{
  [a]
}

// "Mergesort" of the leaves 
function G(t: tree): seq<int> 
  ensures Sorted(G(t))
{ 
  match t 
  case leaf(a) => g_0(a) 
  case node(l, r) => combine(G(l), G(r))
}

function MainG(t: tree): seq<int> 
  ensures Sorted(G(t))
{
  G(t)
}

/**** The main components of the proof of equivalence */

// Declaring the \otimes operator 
function accJoin(x: seq<int>, res: seq<int>): seq<int> 
  requires Sorted(x) && Sorted(res)
{
  combine(x, res)
}

// Property (1) of \otimes
lemma AccJoinBehaviour(x: seq<int>, t: tree)
  requires Sorted(x)
  ensures F(x, t) == accJoin(x, MainF(t))
  decreases t
{
  match t 
  case leaf(a) => {}
  case node(l, r) => {
    // Since we don't have "node labels" with this definition of <tree>, 
    // we need a different property here, namely associativity of \otimes
    AccJoinAssoc(x, MainF(l), MainF(r));
  }
}

// The desired result. 
lemma EquivalentSchemes(t: tree)
  ensures MainF(t) == MainG(t)
{
  match t 
  case leaf(a) => {} 
  case node(l, r) => {
    // Follow the structure of the proof on Overleaf. 
    // The "AccJoinCombine" step is trivial here by definition of accJoin.
    var s := MainF(l);
    AccJoinBehaviour(s, r);
    EquivalentSchemes(l); EquivalentSchemes(r);
  }
}


/**** Declaring helpers for proving AccJoinBehaviour ****/

// Associativity of \otimes
lemma AccJoinAssoc(x: seq<int>, y: seq<int>, z: seq<int>)
  requires Sorted(x) && Sorted(y) && Sorted(z)
  ensures accJoin(accJoin(x, y), z) == accJoin(x, accJoin(y, z))
{
  if z == [] {}
  else {
    calc == {
      multiset(accJoin(accJoin(x, y), z));
        {CombineIsUnion(accJoin(x, y), z);}
      multiset(accJoin(x, y)) + multiset(z);
        {CombineIsUnion(x, y);}
      multiset(x) + multiset(y) + multiset(z);
        {CombineIsUnion(y, z);}
      multiset(x) + multiset(accJoin(y, z));
        {CombineIsUnion(x, accJoin(y, z));}
      multiset(accJoin(x, accJoin(y, z)));
    }
    UniqueSorted(accJoin(accJoin(x, y), z), accJoin(x, accJoin(y, z)));
  }
}

// If x and y are two sorted sequences containing the same elements 
// (with multiplicity), then they are equal
lemma UniqueSorted(x: seq<int>, y: seq<int>)
  requires Sorted(x) && Sorted(y) && multiset(x) == multiset(y)
  ensures x == y 
  decreases x, y
{
  if x == [] {
    UniqueSortedBase(x, y);
  }
  else {
    // Show that the last element in x and y is the same, 
    // and then use induction
    var last := x[|x|-1];
    assert last in multiset(y);
    assert |x| == |y|;
    UniqueSortedInduction(x, y);
    RemovingMultiset(x); RemovingMultiset(y);
    UniqueSorted(x[..|x|-1], y[..|y|-1]);
  }
}

// Removing an element of a seq changes the multiset as expected
lemma RemovingMultiset(x: seq<int>)
  requires |x| > 0 
  ensures multiset(x[..|x|-1]) == multiset(x) - multiset{x[|x|-1]}
{
  assert x[..|x|-1] + [x[|x|-1]] == x; 
}

// Base case for UniqueSorted, proof by contradiction
lemma UniqueSortedBase(x: seq<int>, y: seq<int>)
  requires multiset(x) == multiset(y) 
  requires x == [] // what we'll contradict
  ensures y == [] 
{
  if y != [] {
    var a :| a in multiset(y); 
    assert a in x;
    assert false; // contradiction
  }
}

// Enables the induction for UniqueSorted, proof by contradiction
lemma UniqueSortedInduction(x: seq<int>, y: seq<int>)
  requires Sorted(x) && Sorted(y) && multiset(x) == multiset(y)
  requires |x| > 0 && |x| == |y|
  ensures x[|x|-1] == y[|y|-1]
{
  var last_x, last_y := x[|x|-1], y[|y|-1];
  if last_x != last_y {
    // last_x must be in y 
    assert last_x in multiset(y) ==> last_x in y;
    // But it's not last_y, by assumption
    assert exists i :: (0 <= i < |y|-1) && (y[i] == last_x); 
    // Get an index of last_x in y 
    var i :| (0 <= i < |y|-1) && (y[i] == last_x);
    // So last_y is in fact greater than last_x
    assert last_y > last_x; 
    // But last_y must be in x
    assert last_y in multiset(x) ==> last_y in x;
    // Contradiction, since last_x is already the greatest element in x
    assert false; 
  }
}