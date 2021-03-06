/*
Here we test proving equivalence of functions defined on plane trees
and  on labelled binary trees. In both cases, the function computes
the maximum preorder prefix sum. 
We use the coding function presented in recsynt B.1.6: TreeP --> TreeLB.
*/

/**** Declaring Types ****/
datatype List <T> = Nil | Cons(hd: T, tl: List)
datatype ListC <T> = NilC | El(val: T) | Conc(left: ListC, right: ListC)

datatype TreeLB = NilLB | NodeLB(a: Maybe<int>, left: TreeLB, right: TreeLB) 
// TreeP will only have integer labels, don't know a cleaner way
datatype TreeP = NilP | NodeP(a: int, l: List<TreeP>)

// eps := Nothing
datatype Maybe <T> = Nothing | Just(val: T)


/**** Declaring preliminaries ****/
function method Max(x: int, y: int): int 
{
  if x > y then x else y 
}

// Special tree value used for modifying C, 
// making it possible to define an R having the desirable properties. 
const EpsTree: TreeLB := NodeLB(Nothing, NilLB, NilLB);

// Coding function
function method C(t: TreeP): TreeLB
{
  match t 
  {
    case NilP => NilLB 
    // NOTE THIS MODIFICATION
    case NodeP(a, l) => NodeLB(Just(a), EpsTree, Process(l)) 
  }
}

// Processes a list of TreePs by spacing them out with eps-nodes
function method Process(l: List<TreeP>): TreeLB 
{
  match l 
  {
    case Nil => NilLB 
    case Cons(hd, tl) => NodeLB(Nothing, C(hd), Process(tl))
  }
}

// This is true iff t is a tree in the image of Process
predicate method IsProcessedTree(t: TreeLB)
{
  t == NilLB || (t.a == Nothing && IsProcessedTree(t.right) && IsInImageC(t.left))
}

// This is true iff t is a tree in the image of C 
predicate method IsInImageC(t: TreeLB)
{
  t == NilLB || (t.a != Nothing && t.left == EpsTree && IsProcessedTree(t.right))
}

/*
Representation function. 
We check if t is in the image of c (1);
if not, we just preserve the structure of the tree (2). 
Note that if t is in the image of c, then either t = NilLB, 
or t.a is an int and t.left = EpsTree. 
*/
function method R(t: TreeLB): TreeP 
{
  match t 
  {
    case NilLB => NilP // (1)
    case NodeLB(a, left, right) => 
      if IsInImageC(t) then NodeP(a.val, RConvert(right)) // (1)
      else NodeP(MaybeToInt(a), Cons(R(left), Cons(R(right), Nil))) // (2)
  }
}

// Really, this only makes sense if t is an epsilon-rooted tree
// of the type used in defining C, but maybe it doesn't matter 
function method RConvert(t: TreeLB): List<TreeP> 
{
  match t 
  {
    case NilLB => Nil // rightmost leaf in the subtree 
    case NodeLB(a, left, right) => Cons(R(left), RConvert(right))
  }
}

lemma EpsRootedTreeEquivalence(t: TreeLB, t': TreeLB)
  requires t.NodeLB? && t'.NodeLB?
  requires t.a == t'.a == Nothing 
  requires R(t) == R(t')
  ensures R(t.left) == R(t'.left)
{

}

lemma R_LeftInverse(t: TreeP)
  ensures R(C(t)) == t
{
  assume R(C(t)) == t;
}
 

lemma RConvert_Monotonicity(y: TreeLB, y': TreeLB)
  requires R(y) == R(y')
  requires IsProcessedTree(y) && IsProcessedTree(y')
  ensures RConvert(y) == RConvert(y')
{
  match y 
  {
    case NilLB => {}
    case NodeLB(a, left, right) => {
      assert y'.NodeLB?;
      EpsRootedTreeEquivalence(y, y');
      assert R(left) == R(y'.left);
      RConvert_Monotonicity(right, y'.right);
    }
  }
}

lemma R_Monotonicity(a: Maybe<int>, x: TreeLB, y: TreeLB, x': TreeLB, y': TreeLB)
  decreases IsInImageC(NodeLB(a, x, y)), IsInImageC(NodeLB(a, x', y')) // cool 
  requires R(x) == R(x') && R(y) == R(y')
  ensures R(NodeLB(a, x, y)) == R(NodeLB(a, x', y'))
{
  var t, t' := NodeLB(a, x, y), NodeLB(a, x', y');
  // a few cases 
  if (!IsInImageC(t) && !IsInImageC(t')) {
    // assert R(t) == NodeP(MaybeToInt(a), Cons(R(x), Cons(R(y), Nil)));
    // assert R(t') == NodeP(MaybeToInt(a), Cons(R(x'), Cons(R(y'), Nil)));
  }
  else if (IsInImageC(t) && IsInImageC(t')) {
    RConvert_Monotonicity(y, y');
  }
  else if (!IsInImageC(t) && IsInImageC(t')) {
    assume R(NodeLB(a, x, y)) == R(NodeLB(a, x', y'));
  }
  else {
    // assert !IsInImageC(t') && IsInImageC(t);
    R_Monotonicity(a, x', y', x, y); 
  }
}

// This is \mathcal{K}
function method Link(a: Maybe<int>, t1: TreeP, t2: TreeP): TreeP 
{
  R(NodeLB(a, C(t1), C(t2)))
}

// Don't know how to deal with this in general
function method MaybeToInt(a: Maybe<int>): int 
{
  if a.Just? then a.val else 0 
}

lemma LinkFact(a: Maybe<int>, t1: TreeP, t2: TreeP)
  ensures Link(a, t1, t2) == NodeP(MaybeToInt(a), Cons(t1, Cons(t2, Nil)))
{
  assume Link(a, t1, t2) == NodeP(MaybeToInt(a), Cons(t1, Cons(t2, Nil)));
}


/**** Declaring f (PreOrder) ****/
function method f(t: TreeP): (int, int)
{
  F1((0,0), t)
}

function method F1(s: (int, int), t: TreeP): (int, int)
  decreases t 
{
  match t 
  {
    case NilP => s 
    case NodeP(a, l) => F2(OPlusF(s, a), l)
  }
}

function method OPlusF(s: (int, int), a: int): (int, int) 
{
  (s.0 + a, Max(s.1, s.0 + a))
}

function method F2(s: (int, int), l: List<TreeP>): (int, int)
  decreases l
{
  match l 
  {
    case Nil => s 
    case Cons(hd, tl) => F2(OTimesF(s, F1((0, 0), hd)), tl) // update accumulator
    // Had some trouble here with the "decreases", 
    // when I used f(hd) instead of F1(0, hd). Why? 
  }
}

function method OTimesF(s: (int, int), r: (int, int)): (int, int) 
{
  (s.0 + r.0, Max(s.1, s.0 + r.1))
}


/**** Declaring g (PreOrder) ****/
function method g(t: TreeLB): (int, int) 
{
  G((0, 0), t)
}
 
function method G(s: (int, int), t: TreeLB): (int, int)
  requires s.1 >= s.0
  ensures G(s, t).1 >= G(s, t).0
  decreases t 
{
  match t 
  {
    case NilLB => s 
    case NodeLB(a, l, r) => G(G(OPlusG(s, MaybeToInt(a)), l), r)
  }
}

function method OPlusG(s: (int, int), a: int): (int, int) 
{
  (s.0 + a, Max(s.1, s.0 + a))
}

// This is an operator introduced later. 
// Discovering and proving that it works is outside the scope
// of this example.
function method OTimesG(s: (int, int), r: (int, int)): (int, int)
{
  (s.0 + r.0, Max(s.1, s.0 + r.1))
} 

lemma OTimesOPlusLemma(s: (int, int), a: int, r: (int, int))
  requires s.1 >= s.0 && r.1 >= r.0 
  ensures OTimesG(OPlusG(s, a), r) == OTimesG(s, OTimesG(OPlusG((0,0), a), r))
{

}

lemma OTimesGAssoc(x: (int, int), y: (int, int), z: (int, int))
  requires x.1 >= x.0 && y.1 >= y.0 && z.1 >= z.0  
  ensures OTimesG(OTimesG(x, y), z) == OTimesG(x, OTimesG(y, z))
{

}

// Always slightly annoying to prove - the need for a 
// predicate concerns me 
lemma OTimesGBehaviour(s: (int, int), t: TreeLB)
  requires s.1 >= s.0 
  ensures G(s, t) == OTimesG(s, g(t))
  decreases t
{
  match t 
  case NilLB => {} 
  case NodeLB(a, l, r) => {
    var a_val := MaybeToInt(a);
    calc == {
      G(s, t);
        {OTimesGBehaviour(G(OPlusG(s, a_val), l), r);}
      OTimesG(G(OPlusG(s, a_val), l), g(r));
      OTimesG(OTimesG(OPlusG(s, a_val), g(l)), g(r));
        {
          OTimesOPlusLemma(s, a_val, g(l));
          OTimesGAssoc(s, OTimesG(OPlusG((0,0), a_val), g(l)), g(r));
        }
      OTimesG(s, OTimesG(OTimesG(OPlusG((0,0), a_val), g(l)), g(r)));
    }
  }
}


/**** THE LEMMAS ****/
lemma BaseCase()
  ensures f(R(NilLB)) == g(NilLB)
{
}


lemma SimplifiedProblem(a: int, r1: (int, int), r2: (int, int))
  // requires r1.1 >= r1.0 && r2.1 >= r2.0 // in this case not required, since the problem is so simple
  ensures OTimesG(OTimesG(OPlusG((0, 0), a), r1), r2) == OTimesF(OTimesF(OPlusF((0,0), a), r1), r2)
{

}

lemma MainLemma(a: Maybe<int>, t1: TreeP, t2: TreeP)
  ensures f(Link(a, t1, t2)) == OTimesG(OTimesG(OPlusG((0, 0), MaybeToInt(a)), f(t1)), f(t2))
{
  var r1, r2 := f(t1), f(t2);
  LinkFact(a, t1, t2);
  // Just some expanding... 
  calc == {
    f(Link(a, t1, t2));
    // Nice, Dafny understands MaybeToInt 
    F2(OPlusF((0, 0), MaybeToInt(a)), Cons(t1, Cons(t2, Nil)));
    F2(OTimesF(OPlusF((0, 0), MaybeToInt(a)), f(t1)), Cons(t2, Nil));
    OTimesF(OTimesF(OPlusF((0,0), MaybeToInt(a)), r1), r2);
  }
  SimplifiedProblem(MaybeToInt(a), r1, r2);
}

// After this lemma, just need to use R_LeftInverse...
lemma EquivalentSchemesHelper(t': TreeLB)
  ensures f(R(t')) == g(t')
{
  match t' 
  {
    case NilLB => {
      BaseCase();
    }
    // despite the mess below, this should be automatable 
    case NodeLB(a, l, r) => {
      calc == {
        f(R(NodeLB(a, l, r)));
        // This justification is general
          {
            R_LeftInverse(R(l)); R_LeftInverse(R(r));
            R_Monotonicity(a, l, r, C(R(l)), C(R(r)));
          }
        f(R(NodeLB(a, C(R(l)), C(R(r)))));
        f(Link(a, R(l), R(r)));
          {MainLemma(a, R(l), R(r));}
        // Below is the g <- f term 
        OTimesG(OTimesG(OPlusG((0, 0), MaybeToInt(a)), f(R(l))), f(R(r)));
          {
            EquivalentSchemesHelper(l); 
            EquivalentSchemesHelper(r);
          }
        // Now we're pretty much done, just use the definitions
        OTimesG(OTimesG(OPlusG((0, 0), MaybeToInt(a)), g(l)), g(r));
          {OTimesGBehaviour(OTimesG(OPlusG((0, 0), MaybeToInt(a)), g(l)), r);}
        G(OTimesG(OPlusG((0, 0), MaybeToInt(a)), g(l)), r);
          {OTimesGBehaviour(OPlusG((0, 0), MaybeToInt(a)), l);}
        G(G(OPlusG((0, 0), MaybeToInt(a)), l), r);
      }
    }
  }
}

// Our goal
lemma EquivalentSchemes(t: TreeP)
  ensures f(t) == g(C(t))
{
  EquivalentSchemesHelper(C(t));
  R_LeftInverse(t);
}