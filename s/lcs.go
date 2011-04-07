package lcs

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

		String() string
		//Equal(t T) bool
		//FV() []string      // Free Variables
		//S(y T, x string) T // Substitute y for x in the interface value 'self'
		//E() T              // Evaluate
		//
		// **NOTE: Above commented out functions implemeted via type switching, 
		//         i.e., shallow pattern matching. String() left as interface
		//         to work with Printf
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
// IsLambdaTerm
//----------------------
func (_ Var) IsLambdaTerm() bool { return true }
func (_ Lam) IsLambdaTerm() bool { return true }
func (_ App) IsLambdaTerm() bool { return true }

//----------------------
// Equal
//----------------------
func Equal(t T, u T) bool {
// Not allowed, why  not?
	// if t.(type) != u.(type) {
// 		return false
// 	}
	switch self := t.(type) {
	case Var:
		switch that := u.(type) {
		case Var:
			// vars are alpha-equiv
			return true
		}
		return false
	case Lam:
		switch that := u.(type) {
		case Lam:
			// Given self = \x.e1 and that = \y.e2, find a unique name
			// unique name z \notin {x, y}
			z := next_var()
			for z == self.Var.Name || z == that.Var.Name {
				z = next_var()
			}
			// alpha rename e1 and e2 to [z/x]e1 and [z/y]e2, resp. 
			alpha_var := Var{z}
			renamed_self_body := Substitute(alpha_var, self.Var.Name, self.Body)
			renamed_that_body := Substitute(alpha_var, that.Var.Name, that.Body)
			return Equal(renamed_self_body, renamed_that_body)
		}
		return false
	case App:
		switch that := u.(type) {
		case App:
			self_fvs := FV(self)
			that_fvs := FV(that)
			// Two equal terms must have the same # of free variables
			if len(self_fvs) == len(that_fvs) {
				that_renamed := that
				self_renamed := self
				for i, _ := range self_fvs {
					z := Var{next_var()} // TODO(nkidd) ignores collisions with self_fvs and that_fvs
					that_renamed = Substitute(z, that_fvs[i], that_renamed).(App)
					self_renamed = Substitute(z, self_fvs[i], self_renamed).(App)
				}
				self_eq := Equal(self_renamed.Closure, that_renamed.Closure)
				return self_eq && Equal(self_renamed.Arg, that_renamed.Arg)
			}
			return false
		}
	}
	panic(fmt.Sprintf("Non-lambda term : %v", t))
}

//----------------------
// FV for Free Variables
//----------------------
func FV(t T) []string {
	switch self := t.(type) {
	case Var:
		return append(make([]string, 0), self.Name)
	case Lam:
		fv_body := FV(self.Body)
		for i, s := range fv_body {
			if self.Var.Name == s {
				before_s := fv_body[0:i]
				after_s := fv_body[i+1:]
				return append(before_s, after_s...)
			}
		}
		return fv_body
	case App:
		closure_fvs := FV(self.Closure)
		arg_fvs := FV(self.Arg)
		fvs := make([]string, len(closure_fvs))
		copy(fvs, closure_fvs)
	outer:
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
	panic(fmt.Sprintf("Oops. Argument not a lamda expression: %v", t))
}

//----------------------
// Substitute
//----------------------

// For substitution [x -> s] \y . t, y must be different from x and
// all free variables of s. In the cas
func fresh_var(x string, s T, y string) string {
	s_fvs := FV(s)
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

func Substitute(y T, x string, e T) T {
	switch self := e.(type) {
	case Var:
		if self.Name == x {
			return y
		}
		return self
	case Lam:
		alpha_name := fresh_var(x, y, self.Var.Name)
		if alpha_name == self.Var.Name {
			// capture-avoiding substitution, no rename necessary
			return Lam{Var: self.Var, Body: Substitute(y, x, self.Body)}
		}

		// 1. rename l.Var.Name to alpha_name in the body
		newBody := Substitute(Var{alpha_name}, self.Var.Name, self.Body)
		fmt.Printf("%v --S(%s, %s)--> %v\n", self.Body, self.Var.Name, alpha_name, newBody)

		// 2. [y/x] newBody
		return Lam{Var: Var{alpha_name}, Body: Substitute(y, x, newBody)}
	case App:
		return App{Substitute(y, x, self.Closure), Substitute(y, x, self.Arg)}
	}
	panic(fmt.Sprintf("Non-lambda term in Substitute : %v", e))
}

//----------------------
// Eval
//----------------------
func Eval(t T) T {
	switch self := t.(type) {
	case Var:
		return self
	case Lam:
		return self
	case App:
		lhs := Eval(self.Closure)
		rhs := self.Arg
		switch lam := lhs.(type) {
		case Lam:
			e := Substitute(rhs, lam.Var.Name, lam.Body)
			return Eval(e)
		}
	}
	panic(fmt.Sprintf("Stuck: Eval(%v)", t))
}
