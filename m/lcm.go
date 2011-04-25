package lcm

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
		// **NOTE: Above commented out functions implemeted via hypothetical
		// pattern matching over types. String() left as interface
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
func mString(t T) string {
	match t {
	case Var{s}: return s
	case Lam{x,t}: return fmt.Sprintf("(\\%v . %v)", x, t)
	case App{t1, t2}: return fmt.Sprintf("(%v %v)", t1, t2)
	}
	panic("Not a term")
}

func (self Var) String() string { mString(self) }
func (self Lam) String() string { mString(self) }
func (self App) String() string { mString(self) }

//----------------------
// Equal
//----------------------
func Equal(t T, u T) bool {
	match t, u {
	case Var{x}, Var{y}:
		return true
	case Lam{x,t1}, Lam{y, t2}:
		// find a unique name z \notin {x, y}
		z := next_var()
		for z == x.Name || z == y.Name {
			z = next_var()
		}
		// alpha rename t1 and t2 to [z/x]t1 and [z/y]t2, resp. 
		alpha_var := Var{z}
		renamed_t1 := Substitute(alpha_var, x.Name, t1)
		renamed_t2 := Substitute(alpha_var, y.Name, t2)
		return Equal(renamed_t1, renamed_t2)
	case App{t1, t2}, App{u1, u2}:
		t_fvs := FV(t)
		u_fvs := FV(u)
		// Two equal terms must have the same # of free variables
		if len(t_fvs) == len(u_fvs) {
			t_renamed := t
			u_renamed := u
			for i, _ := range t_fvs {
				z := Var{next_var()} // TODO(nkidd) ignores collisions with u_fvs and u_fvs
				t_renamed = Substitute(z, t_fvs[i], t_renamed).(App)
				u_renamed = Substitute(z, u_fvs[i], u_renamed).(App)
			}
			return Equal(t_renamed.Closure, u_renamed.Closure)
			       && Equal(t_renamed.Arg, u_renamed.Arg)
		}
		return false
	}
	return false;
}

//----------------------
// FV for Free Variables
//----------------------
func FV(t T) []string {
	math t {
	case Var{x}:
		return append(make([]string, 0), x)
	case Lam{x, t}:
		fv_body := FV(t)
		for i, s := range fv_body {
			if x.Name == s {
				before_s := fv_body[0:i]
				after_s := fv_body[i+1:]
				return append(before_s, after_s...)
			}
		}
		return fv_body
	case App{t1, t2}:
		t1_fvs := FV(t1)
		t2_fvs := FV(t2)
		fvs := make([]string, len(t1_fvs))
		copy(fvs, t1_fvs)
	outer:
		for _, a_fv := range t2_fvs {
			for _, c_fv := range t1_fvs {
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
	match e {
	case Var{z}:
		if z == x {
			return y
		}
		return e
	case Lam{z, t}:
		alpha_name := fresh_var(x, y, z.Name)
		if alpha_name == z.Name {
			// capture-avoiding substitution, no rename necessary
			return Lam{Var: z, Body: Substitute(y, x, t)}
		}

		// 1. rename z.Name to alpha_name in t
		newBody := Substitute(Var{alpha_name}, z.Name, t)
		fmt.Printf("%v --S(%s, %s)--> %v\n", t, z.Name, alpha_name, newBody)

		// 2. [y/x] newBody
		return Lam{Var: Var{alpha_name}, Body: Substitute(y, x, newBody)}
	case App{t1, t2}:
		return App{Substitute(y, x, t1), Substitute(y, x, t2)}
	}
	panic(fmt.Sprintf("Non-lambda term in Substitute : %v", e))
}

//----------------------
// Eval
//----------------------
func Eval(t T) T {
	match t {
	case Var{_}:
	case Lam{_,_}:
		return t
	case App{t1, t2}:
		match lhs := Eval(t1) {
		case Lam{x, t3}:
			e := Substitute(t2, x.Name, t3)
			return Eval(e)
		default:
			panic(fmt.Sprintf("Stuck: Eval(%v)", App{lhs, t2}))
		}
	}
	panic(fmt.Sprintf("Not a term: %v", t))
}
