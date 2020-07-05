/*
Here we try the maximum tail sum example of recsynt Section A.1.3.
We use a trivial coding function.
*/

datatype List = Nil | Cons(int, List) // Type T
datatype ListC = NilC | El(int) | Conc(ListC, ListC) // type T'


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

// Simple coding function
function method C(l: List): ListC 
{
  match l 
  case Nil => NilC 
  case Cons(a, x) => Conc(El(a), C(x))
}

lemma EquivalentSchemes(l: List)
  ensures MainF(l) == MainG(C(l)) // pass through the coding function
{
  match l 
  case Nil => {} 
  case Cons(a, x) => {
    assert MainF(l) == Join(G(El(a)), G(C(x)));
  }
}

// Sanity check
// method Main() {
//   var l := Cons(5, Cons(-2, Cons(3, Cons(-2, Cons(3, Nil)))));
//   var f_result := F(l);
//   print f_result;
//   var g_result := G(C(l));
//   print g_result;
//   var x := Cons(4, Cons(3, Cons(10, Nil)));
//   var conc := ListConc(x, l);
//   print conc;
// }