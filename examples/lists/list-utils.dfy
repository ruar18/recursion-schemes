/*
Some useful list-related definitions, including: 
  - Datatype definitions 
  - Common functions on lists
  - Coding functions between list types 
  - Representation function
  - Lemmas about the coding and representation functions
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
  predicate InitDecomposableC(x: ListC) 
    requires x.Conc?
  {
    x.right.El?
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


  function method Aux(orig: List, x: ListC, y: List): set<ListC> 
    decreases y
    requires x.El? || x.Conc?
    requires !x.Conc? ==> orig == Cons(x.val, y) // Special case
    requires SnocStructure(x) // Structure of x 
    requires !x.Conc? ==> ListConc(Rep(NilC), Cons(x.val, y)) == orig
    requires x.Conc? ==> ListConc(Rep(x.left), Cons(x.right.val, y)) == orig 
    ensures forall t: ListC :: t in Aux(orig, x, y) ==> t.Conc? // Results are always decomposable
    ensures forall t: ListC :: (t in Aux(orig, x, y) && !t.left.Conc?) ==> t == SimpleCoding(orig) // Special case of the results
    ensures forall t: ListC :: (t in Aux(orig, x, y) && t.left.Conc?) ==> InitDecomposableC(t.left) // Structure of the left sublist
    ensures Conc(x, SimpleCoding(y)) in Aux(orig, x, y)  // Info about which lists are included 
    ensures ListConc(Rep(x), y) == orig 
    ensures y == Nil ==> (forall t: ListC :: t in Aux(orig, x, y) ==> ListConc(Rep(t.left), Rep(t.right)) == orig) 
  {
    // Needed for the postcondition that ListConc(Rep(x), y) == orig 
    RepAssociation(x, y);
    match y 
    case Nil => {Conc(x, NilC)}
    case Cons(head, tail) => Aux(orig, Conc(x, El(head)), tail) + {Conc(x, SimpleCoding(y))}
  }

  function method Coding(l: List): set<ListC> 
    ensures l != Nil ==> forall t: ListC :: (t in Coding(l) ==> t.Conc?)
    ensures l != Nil ==> forall t: ListC :: (t in Coding(l) && !t.left.Conc?) ==> t == SimpleCoding(l)
  {
    if l == Nil then {NilC} else Aux(l, El(l.head), l.tail)
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

  // Cons-list concatenation is associative
  lemma ListConcAssoc(x: List, y: List, z: List)
    ensures ListConc(ListConc(x, y), z) == ListConc(x, ListConc(y, z))
  {
  }

  // The concatenation of x and y in the definition of Aux is orig.
  // Separating out the induction proof from the definition of Aux.
  lemma AuxConcProperty(orig: List, x: ListC, y: List) 
    decreases y
    requires x.El? || x.Conc?
    requires !x.Conc? ==> orig == Cons(x.val, y) 
    requires SnocStructure(x) // Structure of x 
    requires !x.Conc? ==> ListConc(Rep(NilC), Cons(x.val, y)) == orig
    requires x.Conc? ==> ListConc(Rep(x.left), Cons(x.right.val, y)) == orig 
    ensures forall t: ListC :: (t in Aux(orig, x, y) ==> ListConc(Rep(t.left), Rep(t.right)) == orig)
  {
    match y 
    case Nil => {} 
    case Cons(hd, tl) => {
      // This is needed to ensure the recursive call meets 
      // the 5th precondition of AuxConcProperty
      RepAssociation(x, y);
      AuxConcProperty(orig, Conc(x, El(hd)), tl);
      var t := Conc(x, SimpleCoding(y));
      SimpleRepInverse(y, SimpleCoding(y));
      assert ListConc(Rep(t.left), Rep(t.right)) == orig;
    }
  }

  // Specifies the structure of x in Aux
  predicate SnocStructure(x: ListC) 
  {
    (x.Conc? || x.El?) && 
    (x.Conc? ==> (InitDecomposableC(x) && SnocStructure(x.left)))
  }

  // Concatenation of a singleton in front is like Cons
  lemma ConcSingleton(a: int, y: List) 
    ensures Cons(a, y) == ListConc(Cons(a, Nil), y)
  {

  }

  // Associating an element differently between two lists
  // being concatenated does not affect the concatenation
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

  // Rep is a left inverse to Coding
  lemma RepInverse(x: ListC, l: List)
    requires x in Coding(l)
    ensures Rep(x) == l
  {
    match x 
    case NilC => {}
    case El(a) => {}
    case Conc(a, b) => {
      assert Rep(x) == ListConc(Rep(a), Rep(b));
      // This is really a statement about Coding
      AuxConcProperty(l, El(l.head), l.tail); 
    }
  }
}