datatype tree = nil | node(int, tree, tree)



// Declaring components of the in-order scheme 
// This is x_0 
const x_f: seq<int> := [];
function method f_0(x: seq<int>): seq<int> 
{
  x
}

function method lblJoin(r1: seq<int>, a: int): seq<int>
{
  r1 + [a]
}

function method F(x: seq<int>, t: tree): seq<int> 
  decreases t 
{
  match t 
  case nil => f_0(x)
  case node(a, l, r) => F(lblJoin(F(x,l), a), r)
}

function method MainF(t: tree): seq<int>
{
  F(x_f, t)
}

// Declaring components of the BFTH scheme 
// This is x_0 for the scheme
const x_g: seq<int> := [];

function method combine(a: int, res1: seq<int>, res2: seq<int>): seq<int> 
{
  res1 + [a] + res2
}

function method G(t: tree): seq<int> 
{
  match t 
  case nil => x_g 
  case node(a, l, r) => combine(a, G(l), G(r))
}

function method MainG(t: tree): seq<int> 
{
  G(t)
}

// Declaring the \otimes operator 
function method accJoin(x: seq<int>, res: seq<int>): seq<int> 
{
  x + res 
}

lemma AccJoinLblJoin(x: seq<int>, res: seq<int>, a: int) 
  ensures lblJoin(accJoin(x, res), a) == accJoin(x, lblJoin(res, a))
{}


// Verifying that \otimes has the desired property 
lemma AccJoinBehaviour(x: seq<int>, t: tree)
  ensures F(x, t) == accJoin(x, MainF(t))
  decreases t
{
  match t 
  case nil => {}
  case node(a, l, r) => {
    // Just expanding... but it seems like Dafny would need 
    // AccJoinCombine (or to be able to prove it without help) for this 
    // assertion to actually prove the lemma. Quite strange.
    assert F(x, t) == accJoin(x, accJoin(lblJoin(MainF(l), a), MainF(r))); 
  }
}

lemma AccJoinCombine(a: int, res1: seq<int>, res2: seq<int>)
  ensures combine(a, res1, res2) == accJoin(lblJoin(res1, a), res2)
{

}

lemma EquivalentSchemes(t: tree)
  ensures MainF(t) == MainG(t)
{
  match t 
  case nil => {} 
  case node(a, l, r) => {
    // Follow the structure of the proof given on the Overleaf document
    var s := lblJoin(MainF(l), a);
    AccJoinBehaviour(s, r);
    // AccJoinCombine(a, MainF(l), MainF(r));
    EquivalentSchemes(l);
    EquivalentSchemes(r);
  }
}
