/*
Here we try the maximum tail sum example of recsynt Section A.1.3.
We use a coding function that changes up the recursive structure of the list. 
We try to explicitly produce a set of lists with the coding function.
WARNING: messy and does not verify. 
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
    ensures G(l).1 >= G(l).0
  {
    match l 
    case NilC => (0, 0)
    case El(a) => (a, Max(a, 0)) 
    case Conc(x, y) => Join(G(x), G(y))
  }

  function method Join(res1: (int, int), res2: (int, int)): (int, int)
    // ensures Join(res1, res2).1 == res1.1
  {
    var (s1, m1), (s2, m2) := res1, res2;
    (s1 + s2, Max(s2 + m1, m2))
  }

  function method MainG(l: ListC): (int, int)
    ensures MainG(l).1 >= MainG(l).0
  {
    G(l)
  }


  /**** Some experiments with the Rep function ****/
  lemma RepInverse(l: List, x: ListC) 
    requires x in NewComplex(l)
    ensures Rep(x) == l
  {
    // match l 
    // case Nil => {} 
    // case Cons(head, tail) => {

    // }
    assume Rep(x) == l;
  }

  

  lemma FHom(x: List, y: List) 
    ensures MainF(ListConc(x, y)) == Join(MainF(x), MainF(y))
  {
    assume MainF(ListConc(x, y)) == Join(MainF(x), MainF(y));
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
    requires x in NewComplex(l)
    ensures MainF(l) == MainG(x) 
  {
    RepInverse(l, x);
    FRepBehaviour(x);
  }
}




