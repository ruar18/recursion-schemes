/*
Here we try the maximum tail sum example of recsynt Section A.1.3.
We use a coding function that changes up the recursive structure of the list. 
*/

include "./list-utils.dfy"
module MaxTailSum {
  import opened Lists
  function method Max(x: int, y: int): int 
  {
    if x < y then y else x
  }

  // Sequential (leftwards). 
  // Note that the function is already lifted.
  function method F(l: List): (int, int) 
  {
    match l 
    case Nil => (0, 0)
    case Cons(a, x) => FoldOp(a, F(x))
  }

  // Operator given as input to the fold
  function method FoldOp(a: int, res: (int, int)): (int, int)
  {
    var (s, m) := res; // (sum, max)
    (s + a, Max(m, s + a))
  }

  function method MainF(l: List): (int, int)
  {
    F(l)
  }

  // Homomorphism. 
  function method G(l: ListC): (int, int) 
  {
    match l 
    case NilC => (0, 0)
    case El(a) => (a, Max(a, 0)) 
    case Conc(x, y) => Join(G(x), G(y))
  }

  function method Join(res1: (int, int), res2: (int, int)): (int, int)
  {
    var (s1, m1), (s2, m2) := res1, res2;
    (s1 + s2, Max(s2 + m1, m2))
  }

  function method MainG(l: ListC): (int, int)
  {
    G(l)
  }


  /**** Proving the equivalence ****/
  lemma InterestingLemma(hd: int, res1: (int, int), res2: (int, int))
    // requires res1.1 >= res1.0 && res2.1 >= res2.0
    ensures FoldOp(hd, Join(res1, res2)) == Join(FoldOp(hd, res1), res2)
  {

  }

  lemma SecondLemma(a: ListC, a': ListC, b: ListC, b': ListC)
    requires Rep(a) == Rep(a') && Rep(b) == Rep(b')
    ensures Rep(Conc(a, b)) == Rep(Conc(a', b'))
  {

  }

  lemma FHom(x: List, y: List) 
    ensures MainF(ListConc(x, y)) == Join(MainF(x), MainF(y))
  {

  }


  lemma FRepBehaviour(x: ListC) 
    ensures MainG(x) == MainF(Rep(x))
  {
    match x 
    case NilC => {}
    case El(a) => {
      assert F(Nil) == (0, 0);
    }
    case Conc(a, b) => {
      FHom(Rep(a), Rep(b));
    }
  }

  lemma EquivalentSchemes(l: List, x: ListC)
    requires x in Coding(l)
    ensures MainF(l) == MainG(x) 
  {
    if x == NilC {} 
    else {
      RepInverse(x, l);
      FRepBehaviour(x);
    }
  }

  // Trying the original direction directly doesn't work well 
}




