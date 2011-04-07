package lci

import (
	"fmt"
	"strconv"
)

var (
	counter = 100 // fresh variable names in the sequence _x100, _x101, ...
)

type (
	T interface {
		// Force all structs satisfying this interface declare to do so
		IsLambdaTerm() bool

		/* @return string representation of self.
		 * Var{x} ==> "x"
		 * Lam{x,e} ==> "(\x." + e.String() + ")"
		 * App{e1, e2} ==> (e1.String() e2.String())
		 */
		String() string
		Equal(t T) bool    // @return self =alpha= t?
		FV() []string      // Free Variables
		S(y T, x string) T // Substitute y for x in the interface value 'self'
		E() T              // Evaluate
	}

	Var struct {
		Name string
	}

	Lam struct {
		Var  Var
		Body T
	}

	App struct {
		Closure T
		Arg     T
	}
)

func next_var() string {
	counter++
	return "_x" + strconv.Itoa(counter)
}

//----------------------
// IsLambdaTerm
//----------------------
func (_ Var) IsLambdaTerm() bool { return true }
func (_ Lam) IsLambdaTerm() bool { return true }
func (_ App) IsLambdaTerm() bool { return true }

//----------------------
// String
//----------------------
func (self Var) String() string {
	return self.Name
}

func (self Lam) String() string {
	return fmt.Sprintf("(\\%v . %v)", self.Var, self.Body)
}

func (self App) String() string {
	return fmt.Sprintf("(%v %v)", self.Closure, self.Arg)
}

//----------------------
// Equal
//----------------------
func (self Var) Equal(t T) bool {
	switch that := t.(type) {
	case Var:
		// Variables are alpha-equiv
		return true
	}
	return false
}

func (self Lam) Equal(t T) bool {
	switch that := t.(type) {
	case Lam:
		// Given self = \x.e1 and that = \y.e2, find a unique name
		// unique name z \notin {x, y}
		z := next_var()
		for z == self.Var.Name || z == that.Var.Name {
			z = next_var()
		}
		// alpha rename e1 and e2 to [z/x]e1 and [z/y]e2, resp. 
		alpha_var := Var{z}
		renamed_self_body := self.Body.S(alpha_var, self.Var.Name)
		renamed_that_body := that.Body.S(alpha_var, that.Var.Name)
		return renamed_self_body.Equal(renamed_that_body)
	}
	return false
}

func (self App) Equal(t T) bool {
	switch that := t.(type) {
	case App:
		self_fvs := self.FV()
		that_fvs := that.FV()
		// Two equal terms must have the same # of free variables
		if len(self_fvs) == len(that_fvs) {
			that_renamed := that
			self_renamed := self
			for i, _ := range self_fvs {
				z := Var{next_var()} // TODO(nkidd) ignores collisions with self_fvs and that_fvs
				that_renamed = that_renamed.S(z, that_fvs[i]).(App)
				self_renamed = self_renamed.S(z, self_fvs[i]).(App)
			}
			return self_renamed.Closure.Equal(that_renamed.Closure) && self_renamed.Arg.Equal(that_renamed.Arg)
		}
	}
	return false
}

//----------------------
// FV for Free Variables
//----------------------
func (self Var) FV() []string {
	return append(make([]string, 0), self.Name)
}

func (self Lam) FV() []string {
	fv_body := self.Body.FV()
	for i, s := range fv_body {
		if self.Var.Name == s {
			before_s := fv_body[0:i]
			after_s := fv_body[i+1:]
			return append(before_s, after_s...)
		}
	}
	return fv_body
}

func (self App) FV() []string {
	// @return union of FVs of self.Closure and self.Arg
	closure_fvs := self.Closure.FV()
	arg_fvs := self.Arg.FV()
	fvs := make([]string, len(closure_fvs))
	copy(fvs, closure_fvs) // fvs = {closure_fvs}
outer: // nested loop performs union
	for _, a_fv := range arg_fvs {
		for _, c_fv := range closure_fvs {
			if c_fv == a_fv {
				continue outer
			}
		}
		fvs = append(fvs, a_fv)
	}
	return fvs
}

// For substitution [x -> s] \y . t, y must be different from x and all FVs of s. 
func fresh_var(x string, s T, y string) string {
	s_fvs := s.FV()
	conflicts := func(candidate string) bool {
		for _, s_fv := range s_fvs {
			if s_fv == candidate {
				return true
			}
		}
		return false
	}
	varName := y
	for varName == x || conflicts(varName) {
		varName = next_var()
	}
	return varName
}

//----------------------
// S for Substitution
//----------------------
func (self Var) S(y T, x string) T {
	if self.Name == x {
		return y
	}
	return self
}

func (self Lam) S(y T, x string) T {
	alpha_name := fresh_var(x, y, self.Var.Name)
	if alpha_name == self.Var.Name {
		// capture-avoiding substitution, no rename necessary
		return Lam{Var: self.Var, Body: self.Body.S(y, x)}
	}

	// 1. rename l.Var.Name to alpha_name in the body
	newBody := self.Body.S(Var{alpha_name}, self.Var.Name)
	//fmt.Printf("%v --S(%s, %s)--> %v\n", self.Body, self.Var.Name, alpha_name, newBody)

	// 2. [y/x] newBody
	return Lam{Var: Var{alpha_name}, Body: newBody.S(y, x)}
}

func (self App) S(y T, x string) T {
	return App{Closure: self.Closure.S(y, x), Arg: self.Arg.S(y, x)}
}

//----------------------
// E for Evaluation
//----------------------
func (self Var) E() T {
	return self
}

func (self Lam) E() T {
	return self
}

func (self App) E() T {
	lhs := self.Closure.E()

	// 1. Evaluating self.Arg corresponds to eager evaluation
	// rhs := self.Arg.E()

	// 2. Not evaluating self.Arg is lazy eval (i.e., leftmost outermost) 
	rhs := self.Arg

	switch lam := lhs.(type) {
	case Lam:
		e := lam.Body.S(rhs, lam.Var.Name)
		return e.E()
	}
	panic(fmt.Sprintf("Stuck: %v.E()", self) )
}
