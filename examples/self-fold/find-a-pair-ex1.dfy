/*
Example for proving equivalence of a self-fold and an iterative solution for 
the "finding a pair satisfying a predicate" problem. 
Here we use a simple predicate on integers that checks for divisibility, 
but it is commutative. 
*/

include "../lists/list-utils.dfy"
module FindAPair1 {
  import opened Lists 

  // The type of the fold state
  type D = (List, int, bool)

  // Note that p is commutative
  predicate method p(a: int, b: int)
  {
    a != b && (a != 0 && b != 0) && 
    ((a % b == 0) || (b % a == 0))
  }

  /**** Naive iterative approach ****/
  // Note that we lift this function from the original implementation.
  function method Main1(l: List): D 
  {
    // The integer doesn't really matter
    (l, 0, F1(l))
  }

  // Outer loop 
  function method F1(l: List): bool
  {
    match l 
    case Nil => false 
    case Cons(hd, tl) => G1(hd, l) || F1(tl) // recursing on entire l 
  }

  // Inner loop. Checks if there exists b in l s.t. p(a, b)
  function method G1(a: int, l: List): bool 
  {
    match l 
    case Nil => false 
    // We modified this a bit since p isn't commutative. 
    case Cons(hd, tl) => p(a, hd) || G1(a, tl)
  }


  /**** Self-fold approach ****/
  
  // Starting value for the outer fold
  const s_0 := (Nil, 0, false);

  // Starting value for the inner fold 
  function method init(s: D, a: int): D 
  {
    (s.0, a, s.2)
  }

  // Postprocessing after the inner fold
  function method post(t: D, a: int): D 
  {
    // The only things that matter now are the .0 and .2 fields.
    // Hence I set the .1 field to 0 for convenience.
    (ListConc(t.0, Cons(a, Nil)), 0, t.2 || p(a, a))
  }

  // Inner fold operation 
  function method CheckPredicate(t: D, e: int): D 
  {
    // p is commutative so we only check once
    if t.2 then t else (t.0, t.1, p(t.1, e))
  }

  function method Main2(l: List): D 
  {
    F2(s_0, l)
  }

  // The outer fold
  function method F2(s: D, l: List): D 
    decreases l
  {
    match l 
    case Nil => s 
    case Cons(a, tl) => F2(CheckAll(s, a), tl)
  }

  // Outer fold operation: checks a against all elems in s 
  function method CheckAll(s: D, a: int): D 
  {
    post(G2(init(s, a), s.0), a)
  }

  // The inner fold over the state
  function method G2(t: D, l: List): D 
    decreases l 
  {
    match l 
    case Nil => t 
    case Cons(e, tl) => G2(CheckPredicate(t, e), tl)
  }


  /**** Proving Equivalence ****/
  // Attempt 1: using the approach for trees. 
  function method AccJoin(s: D, res: D): D 
  {
    F2(s, res.0)
  }

  lemma AccJoinBehaviour(s: D, l: List) 
    ensures F2(s, l) == AccJoin(s, Main2(l))
  {
    assume F2(s, l) == AccJoin(s, Main2(l));
  }

  // We generated this automatically
  lemma InductiveFact(a: int, tl: List)
    ensures Main1(Cons(a, tl)) == AccJoin(CheckAll(s_0, a), Main1(tl))
  {
    assume Main1(Cons(a, tl)) == AccJoin(CheckAll(s_0, a), Main1(tl));
  }

  lemma EquivalentSchemes(l: List)
    ensures Main1(l).2 == Main2(l).2
  {
    match l 
    case Nil => {}
    case Cons(a, tl) => {
      // Same template as that discussed in the Overleaf document
      var s := CheckAll(s_0, a);
      AccJoinBehaviour(s, tl);
      InductiveFact(a, tl);
    }
  }

  method Main() {
    var l := Cons(14, Cons(7, Cons(21, Nil)));
    print Main1(l);
    print "\n";
    print Main2(l);
  }
}
