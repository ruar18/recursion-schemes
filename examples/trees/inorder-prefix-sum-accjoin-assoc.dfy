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
	requires x.1 >= x.0 
	ensures f_0(x).1 >= f_0(x).0 
{
  x
}

function method lblJoin(r: (int, int), a: int): (int, int) 
	requires r.1 >= r.0 
	ensures lblJoin(r, a).1 >= lblJoin(r, a).0
{
	// (sum, MPS)
	(r.0 + a, max(r.0 + a, r.1))
}



function F(x: (int, int), t: tree): (int, int)
	requires x.1 >= x.0 
	decreases t
	ensures F(x, t).1 >= F(x, t).0
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

lemma AccJoinAssoc(x: (int, int), y: (int, int), z: (int, int))
	// requires x.1 >= x.0 && y.1 >= y.0 && z.1 >= z.0 
	ensures accJoin(accJoin(x, y), z) == accJoin(x, accJoin(y, z))
{

}

// Very interesting 
lemma LblJoinAccJoin(x: (int, int), r: (int, int), a: int)
	requires x.1 >= x.0 && r.1 >= r.0
	ensures lblJoin(accJoin(x, r), a) == accJoin(x, lblJoin(r, a))
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
		// Reduce the recursion scheme 
		AccJoinAssoc(x, lblJoin(MainF(l), a), MainF(r));
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
    AccJoinBehaviour(s, r);
    EquivalentSchemes(l);
    EquivalentSchemes(r);
	}
}
