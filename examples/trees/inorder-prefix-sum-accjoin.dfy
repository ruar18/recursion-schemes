/*
A reworked version of inorder-prefix-sum, trying to find 
patterns in the definition of \otimes (accJoin). 
*/
datatype tree = nil | node(int, tree, tree)

function method max(x: int, y: int): int
{
	if x < y then y else x
}

// The in-order recursion scheme
function method f_0(x: (int, int)): (int, int)  
{
  x
}

function method lblJoin(r: (int, int), a: int): (int, int) 
{
	// (sum, MPS)
	(r.0 + a, max(r.0 + a, r.1))
}



function F(x: (int, int), t: tree): (int, int)
	decreases t
{
	match t 
	case nil => f_0(x)
	case node(a, l, r) => F(lblJoin(F(x, l), a), r)
}

function MainF(t: tree): (int, int)
{
	F((0,0), t)
}

// The BFTH recursion scheme
const x_g: (int, int) := (0, 0);

function method combine(a: int, r1: (int, int), r2: (int, int)): (int, int)
{
	var (sum1, m1) := r1;
	var (sum2, m2) := r2; 
	var msum := sum1 + a + sum2;
	var m := max(max(m1, sum1 + a), sum1 + a + m2);
	(msum, m)
}


function method G(t: tree): (int, int)
{
	match t
	case nil => x_g
	case node(a, l, r) => combine(a, G(l), G(r))
}

function method MainG(t: tree): (int, int) 
{
	G(t)
}

/**** Declaring the \otimes operator ****/
function method accJoin(x: (int, int), res: (int, int)): (int, int) 
{
	(x.0 + res.0, max(x.1, x.0 + res.1))
}

// This version also works, of course 
// function method accJoin(x: (int, int), res: (int, int)): (int, int) 
// {
// 	(x.0 + res.0, max(max(x.1, x.0), x.0 + res.1))
// }

// We know how to generate this automatically.
// It's not surprising that Dafny can prove this automatically - it's really simple!  
lemma InductiveFact(a: int, l: tree, r: tree)
	ensures combine(a, MainG(l), MainG(r)) == accJoin(lblJoin(MainG(l), a), MainG(r))
{

}

lemma AccJoinBehaviour(x: (int, int), t: tree)
	requires x.1 >= x.0 // How to identify this automatically?
	ensures F(x, t) == accJoin(x, MainF(t))
	decreases t 
{
	match t 
	case nil => {} 
	case node(a, l, r) => {
		// Just need to unfold slightly - worked in num-nodes too! 
		calc == {
			accJoin(x, MainF(t));
			accJoin(x, F(lblJoin(F((0,0), l), a), r));
		}
	}
}

// Version of AccJoinBehaviour with weaker preconditions
// In particular, there's no need to identify predicates
lemma AccJoinBehaviour2(res: (int, int), lbl: int, t: tree)
	ensures F(lblJoin(res, lbl), t) == accJoin(lblJoin(res, lbl), MainF(t))
	decreases t 
{
	match t 
	{
		case nil => {} 
		case node(a, l, r) => {  
			var x := lblJoin(res, lbl);
			// Just need to unfold slightly - worked in num-nodes too! 
			calc == {
				accJoin(x, MainF(t));
				// accJoin(x, F(lblJoin(F((0,0), l), a), r));
				accJoin(x, F(lblJoin(MainF(l), a), r));
					{AccJoinBehaviour2(MainF(l), a, r);}
				accJoin(x, accJoin(lblJoin(MainF(l), a), MainF(r)));
				// accJoin(accJoin(x, lblJoin(MainF(l), a)), MainF(r)); // assoc 
				// accJoin(lblJoin(accJoin(x, MainF(l)), a), MainF(r)); // ad hoc property
				// 	{AccJoinBehaviour2(res, a, l);}
				accJoin(lblJoin(F(x, l), a), MainF(r));
					{AccJoinBehaviour2(F(x, l), a, r);}
				F(lblJoin(F(x, l), a), r);
				// F(x, t);
			}
		}
	}
}




// The desired equivalence
lemma EquivalentSchemes(t: tree)
	ensures MainF(t) == MainG(t)
{
	match t 
	case nil => {}
	case node(a, l, r) => {
		// Follow the structure of the proof given on the Overleaf document
    var s := lblJoin(MainF(l), a);
		AccJoinBehaviour2(MainF(l), a, r);
    // AccJoinBehaviour(s, r);
    // InductiveFact(a, l, r);
    EquivalentSchemes(l);
    EquivalentSchemes(r);
	}
}
