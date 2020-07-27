/*
Here we test proving equivalence of functions defined on plane trees
and  on labelled binary trees. In both cases, the function just computes
the sum of all the node labels (we're sticking with a simple example for now). 
We use the coding function presented in recsynt B.1.6: TreeP --> TreeLB
*/


datatype List <T> = Nil | Cons(hd: T, tl: List)
datatype ListC <T> = NilC | El(val: T) | Conc(left: ListC, right: ListC)

datatype TreeLB = NilLB | NodeLB(a: int, left: TreeLB, right: TreeLB) 
datatype TreeP = NilP | NodeP(a: int, l: List<TreeP>)

// For simplicity, avoid testing TreePs with eps as one of the nodes
const eps: int := 0;

// Coding function
function method C(t: TreeP): TreeLB
{
  match t 
  case NilP => NilLB 
  case NodeP(a, l) => NodeLB(a, NilLB, Process(l))
}

// Processes a list of TreePs by spacing them out with eps-nodes
function method Process(l: List<TreeP>): TreeLB 
{
  match l 
  case Nil => NilLB 
  case Cons(hd, tl) => NodeLB(eps, C(hd), Process(tl))
}

// Representation function. 
// TODO: we want this to work naturally for all t, not just ones 
// produced by the coding function. How? 
function method R(t: TreeLB): TreeP 
{
  // match t 
  // case NilLB => NilP 
  // case NodeLB(a, left, right) => 
  //   if a == eps then // processing an eps-rooted tree
  //     (if right == NilLB then NodeP(eps, Cons(left.a, Nil))   // last in a list
  //       else NodeP(eps, Cons(left.a, R(right).l))) // right: an eps-rooted tree 
  //   else if right == NilLB then NodeP(a, Nil) // leaf 
  //   else NodeP(a, R(right).l)
  NilP 
}

// Assume this when needed
predicate R_LeftInverse()
{
  forall t: TreeP :: R(C(t)) == t
}

// Assume this when needed 
predicate R_Monotonicity(a: int, t1: TreeLB, t2: TreeLB, t1': TreeLB, t2': TreeLB)
  requires R(t1) == R(t1) && R(t2) == R(t2')
{
  R(NodeLB(a, t1, t2)) == R(NodeLB(a, t1', t2'))
}

// This is \mathcal{K}
function method Link(a: int, t1: TreeP, t2: TreeP): TreeP 
{
  R(NodeLB(a, C(t1), C(t2)))
}