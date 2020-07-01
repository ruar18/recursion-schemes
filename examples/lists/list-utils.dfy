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

  // function method Aux(orig: List, right: List, x: ListC, a: int, y: ListC): set<ListC> 
  //   decreases y 
  //   requires SimpleCoding(right) == Conc(El(a), y) 
  //   requires Rep(AssociateRight(x, a, y)) == orig
  //   requires y != NilC ==> y.Conc? 
  //   requires y != NilC ==> y.left.El? // specifies the structure of y
  //   requires x.Conc? ==> InitDecomposableC(x)
  //   requires x == NilC ==> Conc(El(a), y) == SimpleCoding(orig)
  //   ensures forall t: ListC :: (t in Aux(orig, right, x, a, y)) ==> t.Conc?
  //   ensures forall t: ListC :: (t in Aux(orig, right, x, a, y)) ==> (t.left.Conc? ==> InitDecomposableC(t.left))
  //   ensures forall t: ListC :: (t in Aux(orig, right, x, a, y)) ==> t.left != NilC
  //   ensures AssociateLeft(x, a, y) in Aux(orig, right, x, a, y) ==> AssociateRight(x, a, y) in Aux(orig, right, x, a, y)
  //   ensures Rep(AssociateRight(x, a, y)) == orig
  // {
  //   RepInvariant(x, a, y);
  //   // assume Rep(AssociateRight(x, a, y)) == orig;
  //   if y == NilC then {AssociateRight(x, a, y)}
  //                else Aux(orig, right.tail, if x == NilC then El(a) else Conc(x, El(a)), y.left.val, y.right) + {AssociateRight(x, a, y)}
  // }

  // function method ComplexCoding(l: List): set<ListC>
  //   ensures l != Nil ==> forall t: ListC :: t in ComplexCoding(l) ==> t.Conc?
  //   ensures l != Nil ==> forall t: ListC :: (t in ComplexCoding(l) && t.Conc? && t.left.Conc?) ==> InitDecomposableC(t.left)
  //   // ensures forall x: ListC, a: int, y: ListC :: AssociateLeft(x, a, y) in ComplexCoding(l) ==> AssociateRight(x, a, y) in ComplexCoding(l)
  // {
  //   assume l.Cons? ==> Rep(AssociateRight(NilC, l.head, SimpleCoding(l.tail))) == l;
  //   if l == Nil then {NilC} else Aux(l, l, NilC, l.head, SimpleCoding(l.tail))
  // }

  function method NewAux(x: ListC, y: List): set<ListC> 
    decreases y
    ensures forall t: ListC :: t in NewAux(x, y) ==> t.Conc?
  {
    match y 
    case Nil => {} 
    case Cons(head, tail) => NewAux(Conc(x, El(head)), tail) + {Conc(x, SimpleCoding(y))}
    // {Conc(Conc(x, El(head)), SimpleCoding(tail))}
    //{AssociateLeft(x, head, SimpleCoding(y))}
  }

  function method NewComplex(l: List): set<ListC> 
  {
    NewAux(NilC, l) // maybe instead El(l.head), l.tail?
  }

  /**** ListC -> List representation function ****/
  function method Rep(x: ListC): List 
  {
    match x
    case NilC => Nil 
    case El(a) => Cons(a, Nil) 
    case Conc(a, b) => ListConc(Rep(a), Rep(b))
    // if Rep(a) == Nil then Rep(b) else Rep(a).(tail := Rep(b)) // datatype update syntax 
  }

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
    // match x 
    // case Nil => {} 
    // case Cons(x_head, x_tail) => {
    //   match y 
    //   case Nil => {}
    //   case Cons(y_head, y_tail) => {
    //     match z
    //     case Nil => {
    //       assert ListConc(ListConc(x, y), z) == ListConc(x, y);
    //     } 
    //     case Cons(z_head, z_tail) => {}
    //   }
    // }
  }

  lemma AssocRepEquiv(x: ListC, y: ListC, z: ListC)
    ensures Rep(Conc(Conc(x, y), z)) == Rep(Conc(x, Conc(y, z)))
  {
    ListConcAssoc(Rep(x), Rep(y), Rep(z));
  }

  lemma RepInverse(l: List, x: ListC) 
    decreases x.left
    requires x in NewComplex(l)
    ensures Rep(x) == l
  {
    if x == Conc(NilC, SimpleCoding(l)) {
      SimpleRepInverse(l, SimpleCoding(l));
    }
    else {
      assume x.left.Conc?;
      assume InitDecomposableC(x.left);
      assume Conc(x.left.left, Conc(x.left.right, x.right)) in NewComplex(l);
      RepInverse(l, Conc(x.left.left, Conc(x.left.right, x.right)));
      AssocRepEquiv(x.left.left, x.left.right, x.right);
    }
  }

  // Sanity check
  method Main() {
    var l := Cons(5, Cons(-2, Cons(3, Cons(-2, Cons(3, Nil)))));
    // var assoc := ComplexCoding(l);
    var assoc := NewComplex(l);
    var c := assoc;
    while c != {} 
      decreases c;
    {
      var y :| y in c;
      print PrintListC(y) + "\n";
      c := c - { y };
    }
  }

}