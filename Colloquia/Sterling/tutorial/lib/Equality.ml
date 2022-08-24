


module V = Value
module S = Syntax

exception Todo
exception Unequal

(* G |- A == B type *)

let rec equate_tp : int -> V.value -> V.value -> unit =
  fun len tp0 tp1 ->
  match tp0, tp1 with
  | V.Pi (base0, V.C {binder = B fam0; env = env0}), V.Pi (base1, V.C {binder = B fam1; env = env1}) ->
    equate_tp len base0 base1;
    let var : V.value = V.Stuck (V.Var (V.Lvl len), base0) in
    let fiber0 = Eval.eval (V.Extend (env0, var)) fam0 in
    let fiber1 = Eval.eval (V.Extend (env1, var)) fam1 in
    equate_tp (len + 1) fiber0 fiber1
  | V.Pi _, _ ->
    raise Unequal
  | V.Bool, V.Bool -> ()
  | V.Bool, _ -> raise Unequal
  | _ -> raise Todo

let rec equate : int -> V.value -> V.value -> V.value -> unit =
  fun len tp val0 val1 ->
  match tp with
  | V.Pi (base, V.C {binder = B fam; env = env}) ->
    let var : V.value = V.Stuck (V.Var (V.Lvl len), base) in
    let result0 = Eval.app val0 var in
    let result1 = Eval.app val1 var in
    let fiber = Eval.eval (V.Extend (env, var)) fam in
    equate (len + 1) fiber result0 result1
  | V.Sg (base, V.C {binder = B fam; env = env}) ->
    let fst0 = Eval.fst val0 in
    let fst1 = Eval.fst val1 in
    equate len base fst0 fst1;
    let snd0 = Eval.snd val0 in
    let snd1 = Eval.snd val1 in
    let fiber = Eval.eval (V.Extend (env, fst1)) fam in
    equate len fiber snd0 snd1
  | _ ->
    match val0, val1 with
    | V.True, V.True -> ()
    | V.True, _ -> raise Unequal
    | V.False, V.False -> ()
    | V.False, _ -> raise Unequal
    | V.Stuck (stuck0, tp0), V.Stuck (stuck1, tp1) ->
      equate_tp len tp0 tp1;
      equate_stuck len stuck0 stuck1
    | _ ->
      raise Unequal

and equate_stuck : int -> V.stuck -> V.stuck -> unit =
  fun len stuck0 stuck1 ->
  match stuck0, stuck1 with
  | V.Var lvl0, V.Var lvl1 ->
    if lvl0 = lvl1 then () else raise Unequal
  | V.Fst stuck'0, V.Fst stuck'1 ->
    equate_stuck len stuck'0 stuck'1
  | V.Snd stuck'0, V.Snd stuck'1 ->
    equate_stuck len stuck'0 stuck'1
  | V.App {fn = fn0; arg = arg0; base = base0}, V.App {fn = fn1; arg = arg1; base = base1} ->
    equate_stuck len fn0 fn1;
    equate_tp len base0 base1;
    equate len base0 arg0 arg1
  | _, _->
    raise Unequal
