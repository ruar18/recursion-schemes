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

  // Simple coding function
  // function method SimpleCoding(l: List): ListC 
  //   decreases l
  //   ensures l != Nil ==> HeadDecomposableC(SimpleCoding(l))
  //   ensures l != Nil ==> (DecomposableC(DecomposeHeadC(SimpleCoding(l)).1) ==> HeadDecomposableC(DecomposeHeadC(SimpleCoding(l)).1))
  //   ensures DecomposableC(SimpleCoding(l)) ==> l != Nil 
  //   ensures HeadDecomposableC(SimpleCoding(l)) ==> DecomposeHeadC(SimpleCoding(l)) == (Decompose(l).0, SimpleCoding(Decompose(l).1))
  // {
  //   match l 
  //   case Nil => NilC 
  //   case Cons(a, x) => Conc(El(a), SimpleCoding(x))
  // }

  // Produces a set of ListC's associated in different ways corresponding 
  // to Conc(x, y). l is the current list corresponding to y. 
  // function method Aux(orig: List, l: List, x: ListC, y: ListC): set<ListC>
  //   decreases y
  //   requires SimpleCoding(l) == y // specifies what l is 
  //   requires y != NilC ==> HeadDecomposableC(y) // specifies the structure of y
  //   requires x != NilC ==> InitDecomposableC(x) // specifies the structure of x 
  //   ensures forall t: ListC :: (t in Aux(orig, l, x, y)) ==> DecomposableC(t)
  // {
  //   match y 
  //   case NilC => {Conc(x, y)}
  //   case El(a) => {Conc(x, y)}
  //   case Conc(El(a), z) => Aux(orig, Decompose(l).1, Conc(x, El(a)), z) + {Conc(x, y)}
  // }

  // The more interesting coding function
  // function method ComplexCoding(l: List): set<ListC> 
  // {
  //   Aux(l, l, NilC, SimpleCoding(l))
  // }

  lemma CanMove(x: ListC, a: int, y: ListC)
    ensures G(AssociateLeft(x, a, y)) == G(AssociateRight(x, a, y))
  {
    // nice
  }


  // x is of the form ((init, a), rest)
  lemma MovedInCoding(l: List, x: ListC, a: int, y: ListC)
    requires AssociateLeft(x, a, y) in ComplexCoding(l)
    ensures AssociateRight(x, a, y) in ComplexCoding(l)
  {
    assume AssociateRight(x, a, y) in ComplexCoding(l) ;
  }

  // Idea: write x = ((init, a), rest) and associate a to the right, 
  // until you get to the "normal form" SimpleCoding(l)
  lemma EquivToNormal(l: List, x: ListC)
    requires l != Nil
    requires x in ComplexCoding(l)
    decreases x.left
    ensures G(SimpleCoding(l)) == G(x)
  {
    // assert exists w: ListC, z: ListC :: x == Conc(w, z);
    // var w :|
    if x == SimpleCoding(l) {}
    else {
      assert x.Conc?;
      assert x.left != NilC;
      match x.left 
      case El(a) => {
        assume G(SimpleCoding(l)) == G(x);
      }
      // We know x.left is head-decomposable
      case Conc(init, El(a)) => {
        assume init != NilC;
        MovedInCoding(l, init, a, x.right);
        CanMove(init, a, x.right);
      }
    } 
  }

  lemma AllEquivalent(l: List, x: ListC, y: ListC)
    requires l != Nil
    requires x in ComplexCoding(l) && y in ComplexCoding(l)
    ensures G(x) == G(y)
  {
    EquivToNormal(l, x); EquivToNormal(l, y);
  }

  lemma EquivalentSimple(l: List)
    ensures MainF(l) == MainG(SimpleCoding(l)) 
  {
    match l 
    case Nil => {} 
    case Cons(a, x) => {
      assert MainF(l) == Join(G(El(a)), G(SimpleCoding(x)));
    }
  }

  // The ListC that preserves the recursive structure of l 
  // is present in ComplexCoding(l)
  lemma NormalFormInCoding(l: List)
    requires l != Nil
    ensures SimpleCoding(l) in ComplexCoding(l)
  {
  }

  lemma JoinIdentity(res: (int, int))
    requires res.1 >= res.0
    ensures Join(MainG(NilC), res) == res
  {
  }

  lemma FormsEquivalent(l: List)
    requires l != Nil 
    ensures MainG(Conc(NilC, SimpleCoding(l))) == MainG(SimpleCoding(l))
  {
    JoinIdentity(MainG(SimpleCoding(l)));
  }

  lemma EquivalentSchemes(l: List, x: ListC)
    requires x in ComplexCoding(l)
    ensures MainF(l) == MainG(x) 
  {
    match l 
    case Nil => {} 
    case Cons(a, z) => {
      EquivalentSimple(l); // ComplexCoding is defined using SimpleCoding
      assert MainF(l) == Join(G(El(a)), G(SimpleCoding(z)));
      assert SimpleCoding(l) in ComplexCoding(l); // TODO: can we remove the NilC somehow?
      AllEquivalent(l, SimpleCoding(l), x);
    }
  }

  /**** Some experiments with the Rep function ****/
  lemma RepInverse(l: List, x: ListC) 
    requires x in ComplexCoding(l)
    ensures Rep(x) == l
  {
  }

  lemma FRepBehaviour(x: ListC) 
    ensures MainG(x) == MainF(Rep(x))
  {
    assume MainG(x) == MainF(Rep(x));
  }

  lemma EquivalentSchemes2(l: List, x: ListC)
    requires x in ComplexCoding(l)
    ensures MainF(l) == MainG(x) 
  {
    RepInverse(l, x);
    FRepBehaviour(x);
  }
}




