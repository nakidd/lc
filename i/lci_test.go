package lci

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
		if !e.Equal(e) {
			t.Errorf("%v =/= %v\n", e, e)
		}
	}
}

func TestEvalValues(t *testing.T) {
	for _, value := range []T{X, Y, Z, I, K, S} {
		via_interface := value.E()
		t.Logf("-- via_interface := %v\n", via_interface)
	}
}

func TestEvalAppIToX(t *testing.T) {
	for _, app := range []T{ App{I, X}, SKSK } {
		via_interface := app.E()
		t.Logf("-- via_interface := %v\n", via_interface)
	}
}

func TestEvalSKSK(t *testing.T) {
	expected := K
	t.Logf("-- expected := %v\n", expected)
	computed := SKSK.E()
	t.Logf("-- computed := %v\n", computed)
	if !expected.Equal(computed) {
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
	expected := App{I.E(), Y}.E()
	t.Logf("-- expected := %v\n", expected)
	computed := App{SKx.E(), Y}.E()
	t.Logf("-- computed := %v\n", computed)
	if !expected.Equal(computed) {
		t.Errorf("%v =/= %v\n", expected, computed)
	}
}
