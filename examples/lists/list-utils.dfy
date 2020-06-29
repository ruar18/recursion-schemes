/*
Some useful list-related definitions, including: 
  - Datatype definitions 
  - Common functions on lists
  - Definitions for decomposing cons-lists and concatenation lists.
  - Coding functions between list types 
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

  function method Aux(orig: List, right: List, x: ListC, a: int, y: ListC): set<ListC> 
    decreases y 
    requires SimpleCoding(right) == Conc(El(a), y) 
    requires y != NilC ==> y.Conc? 
    requires y != NilC ==> y.left.El? // specifies the structure of y
    ensures forall t: ListC :: (t in Aux(orig, right, x, a, y)) ==> t.Conc?
  {
    if y == NilC then {AssociateRight(x, a, y)}
                 else Aux(orig, right.tail, if x == NilC then El(a) else Conc(x, El(a)), y.left.val, y.right) + {AssociateRight(x, a, y)}
  }

  function ComplexCoding(l: List): set<ListC>
  {
    if l == Nil then {NilC} else Aux(l, l, NilC, l.head, SimpleCoding(l.tail))
  }

  // Sanity check
  // method Main() {
  //   var l := Cons(5, Cons(-2, Cons(3, Cons(-2, Cons(3, Nil)))));
  //   var assoc := ComplexCoding(l);
  //   var c := assoc;
  //   while c != {} 
  //     decreases c;
  //   {
  //     var y :| y in c;
  //     print PrintListC(y) + "\n";
  //     c := c - { y };
  //   }
  // }

}