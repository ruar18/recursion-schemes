/*
Just an implementation of insertion sort as a self-fold single-pass function.
For experimentation.
*/

include "../lists/list-utils.dfy"
module InsertionSort {
  import opened Lists 

  type FoldRep = (List, int, bool)
  const S_0 := (Nil, 0, false);

  // This is the outer fold
  function method F(acc: FoldRep, l: List): FoldRep
  {
    match l 
    case Nil => S_0
    case Cons(a, tl) => F(T(a, acc), tl)
  } 

  // \otimes, the outer fold operator
  function method T(a: int, acc: FoldRep): FoldRep
  {
    Post(G(Init(a, acc), acc.0), a)
  }

  // This is the inner fold. Here the list is the list part of acc.
  function method G(acc: FoldRep, l: List): FoldRep 
  {
    match l 
    case Nil => acc 
    case Cons(e, tl) => G(P(acc, e), tl)
  }

  // \oplus, the inner fold operator
  function method P(acc: FoldRep, e: int): FoldRep 
  {
    // if (acc.1 < e && !acc.2) 
    // then (Cons(acc.0))
  }

  // function method MainF(l: List): (List, int, bool)
  // {

  // }
}