datatype tree = nil | node(int, tree, tree)


// Straightforward preorder example.
function method F1(s: int, t: tree): int
  decreases t
{
  match t 
  case nil => s 
  case node(x, l, r) => 
    var num := F1(s + 1, l); // preorder
    F1(num, r)
}

function method F(t: tree): int 
{
  F1(0, t)
}

function method G(t: tree): int 
{
  match t 
  case nil => x0() 
  case node(x, l, r) => 
    var r1, r2 := G(l), G(r);
    combine(x, r1, r2)
}

function method x0(): int
{
	0
}

function method combine(lbl: int, r1: int, r2: int): int 
{
  1 + r1 + r2 
}

function conc(x: int, l: tree, r: tree): tree
{
	node(x, l, r)
}

function method accJoin(s: int, res: int): int 
{
  s + res 
}

// Since this is preorder, we'll need to apply this to both l and r 
lemma NumBehaviour(s: int, t: tree)
  ensures F1(s, t) == accJoin(s, F(t))
  decreases t
{
  match t 
  case nil => {} 
  case node(x, l, r) => {
   calc == {
     s + F(t);
     s + F1(F1(1, l), r);
     F1(F1(1, l) + s, r);
     F1(F1(1 + s, l), r);
   } 
  }
}

lemma FHom(x: int, l: tree, r: tree)
	ensures F(conc(x,l,r)) == combine(x, F(l),  F(r))
{
  var t := conc(x, l, r);
  calc == {
    F(t); 
    F1(F1(1, l), r);
      {NumBehaviour(F1(1, l), r);}
    F1(1, l) + F(r);
      {NumBehaviour(1, l);}
    1 + F(l) + F(r);
  }
}


lemma EquivalentSchemes(t: tree)
	ensures F(t) == G(t)
{
  match t 
  case nil => {} 
  case node(x, l, r) => {
    var num := F1(1, l);
    NumBehaviour(num, r); // this makes the right call independent of the accumulator
    NumBehaviour(1, l); // this makes the left call independent of the accumulator
  }
}


