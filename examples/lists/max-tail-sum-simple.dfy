/*
Here we try the maximum tail sum example of recsynt Section A.1.3.
We use a trivial coding function.
WARNING: messy.
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

// Prepend the reverse of l to aux 
// function method ReverseAux(l: List, aux: List): List 
// {
//   match l 
//   case Nil => aux
//   case Cons(a, x) => ReverseAux(x, Cons(a, aux))
// }

// function method Reverse(l: List): List 
// {
//   ReverseAux(l, Nil)
// }

// Concatenation of Cons-lists - helper function
function method ListConcHelper(x: List, y: List, aux: List): List 
  decreases x, aux 
{
  match x 
  case Nil => // time to use aux, which now stores the reverse of x
    match aux 
    {
      case Nil => y 
      case Cons(a, rest) => ListConcHelper(x, Cons(a, y), rest)
    }
  case Cons(a, rest) => ListConcHelper(rest, y, Cons(a, aux))
}

function method ListConc(x: List, y: List): List 
{
  ListConcHelper(x, y, Nil)
}

// Representation function 
function method R(l: ListC): List 
{
  match l 
  case NilC => Nil 
  case El(a) => Cons(a, Nil) 
  case Conc(x, y) => ListConc(R(x), R(y))
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

// An alternative proof
// lemma EquivalentSchemes(l: List)
//   ensures MainF(l) == MainG(C(l)) // pass through the coding function
// {
//   match l 
//   case Nil => {} 
//   case Cons(a, x) => {
//     assume MainF(Cons(a, Nil)) == MainG(El(a));
//   }
// }

// /**** What can we do with the lemma? ****/
// So far, nothing, really. Below are failed attempts. 


// lemma LeftInverse(x: List) 
//   ensures R(C(x)) == x
// {
//   assume R(C(x)) == x;
// }

// /**** What can we do with the lemma? ****/
// lemma HomC(x: List, y: List) 
//   ensures ListConc(x, y) == R(Conc(C(x), C(y)))
// {
//   assume C(ListConc(x, y)) == Conc(C(x), C(y));
// }
// // MainF(R(Conc(C(x), C(y))))
// // MainF(ListConc(x, y))
// lemma HomF(x: List, y: List) 
//   ensures MainF(R(Conc(C(x), C(y)))) == Join(MainF(x), MainF(y))
// {
//   EquivalentSchemes(ListConc(x, y));
//   // HomC(x, y); // COMPOSITION OF HOMOMORPHISMS? 
//   LeftInverse(x); LeftInverse(y);
//   assume MainG(C(ListConc(x, y))) == MainG(Conc(C(x), C(y)));
//   EquivalentSchemes(x); EquivalentSchemes(y);
// }



// Sanity check
method Main() {
  var l := Cons(5, Cons(-2, Cons(3, Cons(-2, Cons(3, Nil)))));
  var f_result := F(l);
  print f_result;
  var g_result := G(C(l));
  print g_result;
  var x := Cons(4, Cons(3, Cons(10, Nil)));
  var conc := ListConc(x, l);
  print conc;
}