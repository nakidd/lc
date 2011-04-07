datatype term = Var of string
              | Lambda of string * term
              | App of term * term

(* (String t) *)
fun String (Var x) = x
  | String (Lambda(x, e)) = "("^x^" . "^(String e)^")"
  | String (App(e1, e2)) =  "("^(String e1)^" . "^(String e2)^")"

(* (Equal(t1, t2)) structural equality for free in SML *)
fun Equal (t1:term, t2:term) = t1 = t2

(* (FV t) *)
fun FV (Var x) = [x]
  | FV (Lambda (x,t)) = List.filter (fn y => x <> y) (FV t)
  | FV (App (t1,t2)) =
    let val (fvs1, fvs2) = ((FV t1), (FV t2)) in
      (* add fv from fvs1 not in fvs2 to fvs2 *)
      List.foldl 
        (fn (y, fvs) => 
          if (List.exists (fn z => z = y) fvs) then fvs else y::fvs)
        fvs2 fvs1
    end

(* (Substitute (y, x string, t)) = [y/x]t *)
val next_var : unit -> string = 
  let val counter = ref 0
  in fn () => (counter := (!counter) + 1; ("_x" ^ (Int.toString (!counter))))
  end

fun fresh_var (x:string, s:term, y:string) =
  let val s_fvs = (FV s)
    val conflicts = 
      (fn (candidate:string) => 
        List.exists (fn s_fv => candidate = s_fv) s_fvs)
    fun search var_name =
      if var_name = x orelse (conflicts var_name) then (search (next_var()))
      else var_name
  in search y
  end

fun Substitute (y:term, x:string, (Var z)) = if x = z then y else (Var z)
  | Substitute (y:term, x:string, (Lambda (z,t))) = 
    let val alpha_name = (fresh_var (x, y, z)) in
      case (alpha_name = z)
        of true => (Lambda (z, (Substitute(y, x, t))))
         | false =>
             let val newBody = Substitute ((Var alpha_name), z, t)
             in 
               Lambda (alpha_name, (Substitute (y, x, newBody))) 
             end
    end
  | Substitute (y:term, x:string, (App (t1, t2))) =
    App ((Substitute(y, x, t1)), (Substitute(y, x, t2)))

(* (Eval t) *)
fun Eval (t as (Var _)) = t
  | Eval (t as (Lambda(_,_))) = t
  | Eval (App(t1, t2)) =
  let val v = Eval t1 in
    case v
      of (Lambda(y, t3)) => (Eval (Substitute(t2, y, t3)))
       | _ => raise (Fail ("Stuck: Eval("^(String v)^")"))
  end

val X = (Var "X")
val Y = (Var "Y")
val Z = (Var "Z")
val I = (Lambda ("X", X)) 
val K = (Lambda ("X", (Lambda ("Y", X))))
val S = (Lambda ("X", 
          (Lambda ("Y", 
            (Lambda ("Z", 
              (App ( (App(X,Z)) , (App(Y,Z))))))))))
val SKSK = (App ( (App ( (App(S,K)),S)), K))

val _ = print ((String I) ^ "\n")
val _ = print (Bool.toString (Equal (I, I)) ^ "\n")

(* TestEqualSelf *)
val _ = 
  if (List.all (fn t => Equal(t,t)) [X,Y,Z,I,K,S,SKSK])
  then print "PASS[TestEqualSelf]\n"
  else raise (Fail "TestEqualSelf")

val _ = (* TstEvalValues *)
  (List.app (fn t => ignore((Eval t))) [X, Y, Z, I, K, S];
   print "PASS[TestEvalValues]\n")

val _ = (* TestEvalAppIToX *)
  (List.app (fn t => ignore((Eval t))) [(App(I, X)), SKSK];
   print "PASS[TestEvalAppIToX]\n")

val _ = (* TestEvalSKSK *)
  if (not (Equal (K, (Eval SKSK))))
  then raise (Fail "TestEvalSKSK")
  else print "PASS[TestEvalSKSK]\n"

val _ = (* TestEvalSKx *)
let val SKx = App ((App (S,K)), X)
    val expected = Eval (App ((Eval I), Y))
    val computed = Eval (App ((Eval SKx), Y))
in
  if Equal (expected, computed)
  then print "PASS[TestEvalSKx]\n"
  else raise (Fail "TestEvalSKx")
end
