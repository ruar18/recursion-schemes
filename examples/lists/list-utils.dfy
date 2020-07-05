/*
Some useful list-related definitions, including: 
  - Datatype definitions 
  - Common functions on lists
  - Definitions for decomposing cons-lists and concatenation lists.
  - Coding functions between list types 
  - Representation function
*/

module Lists {
  /**** Datatype definitions ****/
  datatype List = Nil | Cons(head: int, tail: List) 
  datatype ListC = NilC | El(val: int) | Conc(left: ListC, right: ListC)

  /**** Useful list functions ****/
  function method Length(l: List): int
    ensures Length(l) >= 0
  {
    match l 
    case Nil => 0 
    case Cons(a, tail) => 1 + Length(tail)
  }

  function method LengthC(x: ListC): int 
  {
    match x 
    case NilC => 0 
    case El(a) => 1 
    case Conc(a, b) => LengthC(a) + LengthC(b)
  }

  function method PrintListC(l: ListC): string 
  {
    match l
    case NilC => "?"
    case El(a) => "." 
    case Conc(x, y) => "(" + PrintListC(x) + ", " + PrintListC(y) + ")" 
  }

  function method PrintList(l: List): string 
  {
    match l 
    case Nil => "?"
    case Cons(hd, tl) => "(., " + PrintList(tl) + ")"
  }


  function method ListConc(a: List, b: List): List 
  {
    match a 
    case Nil => b 
    case Cons(head, tail) => Cons(head, ListConc(tail, b))
  }

  // Note the special case for x == NilC 
  function method AssociateLeft(x: ListC, a: int, y: ListC): ListC
  {
    if x == NilC then Conc(El(a), y) else Conc(Conc(x, El(a)), y)
  }

  function method AssociateRight(x: ListC, a: int, y: ListC): ListC 
    // ensures Rep(AssociateRight(x, a, y)) == 
  {
    if x == NilC then Conc(El(a), y) else Conc(x, Conc(El(a), y))
  }

  /**** Decomposing cons-lists ****/
  function method Decompose(l: List): (int, List) 
    requires l != Nil 
    ensures Length(Decompose(l).1) < Length(l)
    ensures l == Cons(Decompose(l).0, Decompose(l).1)
  {
    match l 
    case Cons(a, tail) => (a, tail)
  }

  /**** Decomposing concatenation lists */
  predicate DecomposableC(x: ListC)
  {
    exists w: ListC, z: ListC :: x == Conc(w, z)
  }

  predicate InitDecomposableC(x: ListC) 
    requires x.Conc?
  {
    x.right.El?
  }

  predicate HeadDecomposableC(x: ListC) 
    requires x.Conc?
  {
    // exists a: int, tail: ListC :: x == Conc(El(a), tail)
    x.left.El? 
  }

  /**** List -> ListC coding functions  ****/
  function method SimpleCoding(l: List): ListC 
    decreases l
    ensures l != Nil ==> SimpleCoding(l).Conc?
    // If not trivial, then head-decomposable
    ensures l != Nil ==> SimpleCoding(l).left.El?
    // If the tail is decomposable, then it is also head-decomposable
    ensures l != Nil ==> SimpleCoding(l).right.Conc? ==> SimpleCoding(l).right.left.El?
    // If decomposable, the original list is not Nil 
    ensures SimpleCoding(l).Conc? ==> l != Nil
    // Head-decomposing after coding is the same as first decomposing and then coding  
    ensures (l != Nil && SimpleCoding(l).left.El?) ==> SimpleCoding(l).left.val == l.head && SimpleCoding(l).right == SimpleCoding(l.tail)
  {
    match l 
    case Nil => NilC 
    case Cons(a, x) => Conc(El(a), SimpleCoding(x))
  }


  function method NewAux(orig: List, x: ListC, y: List): seq<ListC> 
    decreases y
    requires x.El? || x.Conc?
    requires !x.Conc? ==> orig == Cons(x.val, y) // Special case
    requires SnocStructure(x) // Structure of x 
    requires !x.Conc? ==> ListConc(Rep(NilC), Cons(x.val, y)) == orig
    requires x.Conc? ==> ListConc(Rep(x.left), Cons(x.right.val, y)) == orig 
    ensures forall t: ListC :: t in NewAux(orig, x, y) ==> t.Conc? // Results are always decomposable
    // ensures !x.Conc? ==> Conc(x, SimpleCoding(y)) == SimpleCoding(orig) // Special case
    ensures forall t: ListC :: (t in NewAux(orig, x, y) && !t.left.Conc?) ==> t == SimpleCoding(orig) // Special case of the results
    ensures forall t: ListC :: (t in NewAux(orig, x, y) && t.left.Conc?) ==> InitDecomposableC(t.left) // Structure of the left sublist
    ensures Conc(x, SimpleCoding(y)) in NewAux(orig, x, y)  // Info about which lists are included 
    ensures ListConc(Rep(x), y) == orig 
    ensures y == Nil ==> (forall t: ListC :: t in NewAux(orig, x, y) ==> ListConc(Rep(t.left), Rep(t.right)) == orig) 
    // ensures y != Nil ==> (NewAux(orig, x, y) - NewAux(orig, Conc(x, El(y.head)), y.tail)) == {Conc(x, SimpleCoding(y))} // maybe using a seq will be better? 
    // ensures y != Nil ==> forall t: ListC :: (t in NewAux(orig, x, y) ==> ListConc(Rep(t.left), Rep(t.right)) == orig)
  {
    RepAssociation(x, y);
    match y 
    case Nil => [Conc(x, NilC)]
    case Cons(head, tail) => NewAux(orig, Conc(x, El(head)), tail) + [Conc(x, SimpleCoding(y))]
    // {Conc(Conc(x, El(head)), SimpleCoding(tail))}
    //{AssociateLeft(x, head, SimpleCoding(y))}
  }

  function method NewComplex(l: List): seq<ListC> 
    ensures l != Nil ==> forall t: ListC :: (t in NewComplex(l) ==> t.Conc?)
    ensures l != Nil ==> forall t: ListC :: (t in NewComplex(l) && !t.left.Conc?) ==> t == SimpleCoding(l)
    // ensures l != Nil ==> forall t: ListC :: (t in NewComplex(l) && t.left.Conc?) ==> InitDecomposableC(t.left)
    // ensures l != Nil ==> forall t: ListC :: (t in NewComplex(l) ==> ListConc(Rep(t.left), Rep(t.right)) == l)
  {
    // AuxProperty(l, El(l.head), l.tail);
    // NewAux(NilC, l) // maybe instead El(l.head), l.tail?
    if l == Nil then [NilC] else NewAux(l, El(l.head), l.tail)
  }

  /**** ListC -> List representation function ****/
  function method Rep(x: ListC): List 
    ensures (x.Conc? && SnocStructure(x)) ==> Rep(x).Cons?
  {
    match x
    case NilC => Nil 
    case El(a) => Cons(a, Nil) 
    case Conc(a, b) => ListConc(Rep(a), Rep(b))
  }

  /**** Lemmas about converting between list types ****/
  // Rep is a left inverse of SimpleCoding 
  lemma SimpleRepInverse(l: List, x: ListC)
    requires x == SimpleCoding(l)
    ensures Rep(x) == l
  {
    match l 
    case Nil => {} 
    case Cons(head, tail) => {
      assert Rep(x) == ListConc(Rep(x.left), Rep(x.right));
    }
  }

  lemma ListConcAssoc(x: List, y: List, z: List)
    ensures ListConc(ListConc(x, y), z) == ListConc(x, ListConc(y, z))
  {
  }

  lemma AssocRepEquiv(x: ListC, y: ListC, z: ListC)
    ensures Rep(Conc(Conc(x, y), z)) == Rep(Conc(x, Conc(y, z)))
  {
    ListConcAssoc(Rep(x), Rep(y), Rep(z));
  }

  predicate AuxPreconditions(orig: List, x: ListC, y: List) 
  {
    (x.El? || x.Conc?) &&
    (!x.Conc? ==> orig == Cons(x.val, y)) && 
    (x.Conc? ==> InitDecomposableC(x)) && 
    (!x.Conc? ==> ListConc(Rep(NilC), Cons(x.val, y)) == orig) && 
    (x.Conc? ==> ListConc(Rep(x.left), Cons(x.right.val, y)) == orig)
  }

  // Separating out the induction proof from the definition of Aux
  // seems to be helpful 
  lemma AuxProperty(orig: List, x: ListC, y: List) 
    decreases y
    requires x.El? || x.Conc?
    requires !x.Conc? ==> orig == Cons(x.val, y) // Special case
    requires SnocStructure(x) // Structure of x 
    requires !x.Conc? ==> ListConc(Rep(NilC), Cons(x.val, y)) == orig
    requires x.Conc? ==> ListConc(Rep(x.left), Cons(x.right.val, y)) == orig 
    ensures forall t: ListC :: (t in NewAux(orig, x, y) ==> ListConc(Rep(t.left), Rep(t.right)) == orig)
  {
    match y 
    case Nil => {} 
    case Cons(hd, tl) => {
      RepAssociation(x, y);
      AuxProperty(orig, Conc(x, El(hd)), tl);
      var t := Conc(x, SimpleCoding(y));
      SimpleRepInverse(y, SimpleCoding(y));
      assert ListConc(Rep(t.left), Rep(t.right)) == orig;
    }
  }

  lemma ListConcRightIdentity(a: List, b: List)
    requires b == Nil 
    ensures ListConc(a, b) == a 
  {

  }

  // Specifies the structure of x in NewAux
  predicate SnocStructure(x: ListC) 
  {
    (x.Conc? || x.El?) && 
    (x.Conc? ==> (InitDecomposableC(x) && SnocStructure(x.left)))
  }

  lemma ConcSingleton(a: int, y: List) 
    ensures Cons(a, y) == ListConc(Cons(a, Nil), y)
  {

  }

  lemma RepAssociation(x: ListC, y: List)
    decreases x 
    requires SnocStructure(x)
    ensures x.Conc? ==> ListConc(Rep(x.left), Cons(x.right.val, y)) == ListConc(Rep(x), y) 
  {
    match x 
    case NilC => {} 
    case El(a) => {}
    case Conc(a, b) => {
      assert ListConc(Rep(x.left), Cons(x.right.val, Nil)) == Rep(x);
      ConcSingleton(x.right.val, y);
      ListConcAssoc(Rep(x.left), Cons(x.right.val, Nil), y);
    }
  }

  lemma RepInverse(x: ListC, l: List)
    requires x in NewComplex(l)
    ensures Rep(x) == l
  {
    match x 
    case NilC => {}
    case El(a) => {}
    case Conc(a, b) => {
      assert Rep(x) == ListConc(Rep(a), Rep(b));
      // This is really a statement about NewComplex
      AuxProperty(l, El(l.head), l.tail); 
    }
  }

  // Sanity check
  method Main() {
    // var l := Cons(5, Cons(-2, Cons(3, Cons(-2, Cons(3, Nil)))));
    // // var l := Cons(5, Cons(2, Nil));
    // // var l := Nil;
    // // var assoc := ComplexCoding(l);
    // var assoc := NewComplex(l);
    // // var c := assoc;
    // // while c != {} 
    // //   decreases c;
    // // {
    // //   var y :| y in c;
    // //   print PrintListC(y) + "\n";
    // //   c := c - { y };
    // // }
    // var i := 0;
    // while i < |assoc|
    //   invariant i <= |assoc|
    // {
    //   print PrintListC(assoc[i]) + "\n";
    //   i := i + 1;
    // }
    // var y := Cons(1, Cons(2, Nil)); // (., (., ?))
    // var x := Conc(Conc(El(3), El(4)), El(5)); // ((., .), .)
    // var res1 := ListConc(Rep(x.left), Cons(x.right.val, y));
    // var res2 := ListConc(Rep(x), y);
    // print PrintList(res1) + "\n";
    // print PrintList(res2);
  }

}