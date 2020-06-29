datatype tree = nil | node(int, tree, tree)

function max(x: int, y: int): int
{
	if x < y then y else x
}

// The in-order recursion scheme
function F1(s: (int, int), t: tree): (int, int)
	decreases t
{
	match t 
	case nil => s
	case node(x, l, r) => 
		var (sum1, m1) := F1(s, l);
		F1((sum1 + x, max(sum1 + x, m1)), r)
}

function F(t: tree): (int, int)
{
	F1((0,0), t)
}

// The BFTH recursion scheme
function G(t: tree): (int, int)
{
	match t
	case nil => whenNull()
	case node(x, l, r) => 
		var r1, r2 := G(l), G(r);
		combine(x, r1, r2)
}

function whenNull(): (int, int)
{
	(0, 0)
}

function combine(lbl: int, r1: (int, int), r2: (int, int)): (int, int)
{
	var (sum1, m1) := r1;
	var (sum2, m2) := r2; 
	var msum := sum1 + lbl + sum2;
	var m := max(max(m1, sum1 + lbl), sum1 + lbl + m2);
	(msum, m)
}

// These two are the important lemmas. 
lemma SumBehaviour(s: (int, int), t: tree)
	ensures F1(s, t).0 == s.0 + F1((0,0), t).0 // this is a sort of join, like in a fold... 
	decreases t
{}

lemma MaxBehaviour(s: (int, int), t: tree)
	requires s.1 >= s.0
	ensures F1(s, t).1 == max(s.1, s.0 + F1((0,0), t).1)
	decreases t
{
	match t 
	case nil => {} 
	case node(x, l, r) => {
		// This is neat 
		SumBehaviour(s, l);
	}
}

// "Concatenation" on trees - definitely not necessary for the proof, 
// but feels convenient...
function conc(x: int, l: tree, r: tree): tree
{
	node(x, l, r)
}

// A lemma analogous to our list homomorphism lemmas
lemma FHom(x: int, l: tree, r: tree)
	ensures F(conc(x,l,r)) == combine(x, F(l),  F(r))
{
	var (sum1, m1) := F(l);
	var s := (sum1 + x, max(sum1 + x, m1));
	SumBehaviour(s, r);
	MaxBehaviour(s, r);
}

// The desired equivalence
lemma EquivalentSchemes(t: tree)
	ensures F(t) == G(t)
{
	match t 
	case nil => {}
	case node(x, l, r) => {
		FHom(x, l, r);
	}
}
