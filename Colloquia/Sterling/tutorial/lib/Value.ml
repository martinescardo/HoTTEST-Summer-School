


type var = Lvl of int

type value =
  | Pi of value * closure
  | Sg of value * closure
  | Lam of closure
  | Bool
  | True
  | False
  | Pair of value * value
  | Stuck of stuck * value (* second argument is the type *)

and stuck =
  | Var of var
  | Fst of stuck
  | Snd of stuck
  | App of {fn : stuck; arg : value; base : value}
  (* Fst (Pair ... ... ) *)
  | BoolInd of {motive : closure; tcase : value; fcase : value; scrut : stuck}

and closure =
  | C of {binder : Syntax.term Syntax.binder; env : env}
  (* Gamma, x : A |- binder : B
     env : for each z:C in Gamma, a value *)

and env =
  | Emp
  | Extend of env * value
