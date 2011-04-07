package lcs

import (
	"testing"
//	quick "testing/quick"
)

// SKI-combinator calculus variables
var (
	X = Var{"X"}
	Y = Var{"Y"}
	Z = Var{"Z"}
	I = Lam{X, X} // \x. x
	K = Lam{X, Lam{Y, X}} // \x,y. x
	S = Lam{X, Lam{Y, Lam{Z, App{App{X, Z}, App{Y, Z}}}}} // \x,y,z . xz(yz)
	SKSK = App{App{App{S, K}, S}, K} // SKSK
)


func TestEqualSelf(t *testing.T) {
	for _, e := range []T{X, Y, Z, I, K, S, SKSK} {
		if !Equal(e, e) {
			t.Errorf("%v =/= %v\n", e, e)
		}
	}
}

func TestEvalValues(t *testing.T) {
	for _, value := range []T{X, Y, Z, I, K, S} {
		// shouldn't panic
		via_pattern := Eval(value)
		t.Logf("-- via_pattern := %v\n", via_pattern)
	}
}

func TestEvalAppIToX(t *testing.T) {
	for _, app := range []T{ App{I, X}, SKSK } {
		// shouldn't panic
		via_pattern := Eval(app)
		t.Logf("-- via_pattern := %v\n", via_pattern)
	}
}

func TestEvalSKSK(t *testing.T) {
	expected := K
	t.Logf("-- expected := %v\n", expected)
	computed := Eval(SKSK)
	t.Logf("-- computed := %v\n", computed)
	if !Equal(expected, computed) {
		t.Errorf("%v =/= %v\n", expected, computed)
	}
}

func TestEvalSKx(t *testing.T) {
	// SKx is effectively \x.x; however, computation is delayed by a lamba
	// so SKx.E() gives (\Z . (((\_x121 . (\_x122 . _x121)) Z) (X Z)))
	// To test functional equivalence to I, evaluate SKx and I applied to Y
	// and verify that Y is returned.
	SKx := App{App{S, K}, X}
	t.Logf("**** SKx := %v\n", SKx)
	expected := Eval(App{Eval(I), Y})
	t.Logf("-- expected := %v\n", expected)
	computed := Eval(App{Eval(SKx), Y})
	t.Logf("-- computed := %v\n", computed)
	if !Equal(expected, computed) {
		t.Errorf("%v =/= %v\n", expected, computed)
	}
}
