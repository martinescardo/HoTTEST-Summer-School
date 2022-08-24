



exception Todo
module V = Value
module S = Syntax

let rec proj : V.env -> int -> V.value =
  fun env i ->
  match env with
  | Emp -> failwith "Can't happen!!!"
  | Extend (env', v) ->
    if i == 0 then v else
    if i > 0 then
      proj env' (i - 1)
    else
      failwith "can't happen!!"

let rec eval : V.env -> S.term -> V.value =
  fun env term ->
  match term with
  | S.Var (S.Ix i) ->
    proj env i
  | S.Pi (base, fam) ->
    let vbase = eval env base in
    let cfam = V.C {binder = fam; env = env} in
    V.Pi (vbase, cfam)
  | S.Sg (base, fam) ->
    let vbase = eval env base in
    let cfam = V.C {binder = fam; env = env} in
    V.Sg (vbase, cfam)
  | S.Lam binder ->
    V.Lam (V.C {binder = binder; env = env})
  | S.App (fn, arg) ->
    let vfn = eval env fn in
    let varg = eval env arg in
    app vfn varg
  | S.Pair (term1, term2) ->
    let value1 = eval env term1 in
    let value2 = eval env term2 in
    V.Pair (value1, value2)
  | S.Fst pair ->
    let vpair = eval env pair in
    fst vpair
  | S.Snd pair ->
    let vpair = eval env pair in
    snd vpair
  | _ ->
    raise Todo

and fst : V.value -> V.value =
  fun vpair ->
  match vpair with
  | V.Pair (u, _) ->
    u
  | V.Stuck (stuck, tp) ->
    begin
      match tp with
      | V.Sg (base, _) ->
        V.Stuck (V.Fst stuck, base)
      | _ -> failwith "can't happen!"
    end
  | _ ->
    failwith "can't happen!!!"

and snd : V.value -> V.value =
  fun vpair ->
  match vpair with
  | V.Pair (_, v) ->
    v
  | V.Stuck (stuck, tp) ->
    begin
      match tp with
      | V.Sg (_, V.C {binder = B fam; env}) ->
        let u = fst vpair in
        let fiber = eval (V.Extend (env, u)) fam in
        V.Stuck (V.Snd stuck, fiber)
      | _ -> failwith "can't happen!"
    end
  | _ ->
    failwith "can't happen!!!"


and app : V.value -> V.value -> V.value =
  fun vfn varg ->
  match vfn with
  | V.Lam (V.C {binder = B term; env}) ->
    let env' = V.Extend (env, varg) in
    eval env' term
  | V.Stuck (stuck, tp) ->
    begin
      match tp with
      | V.Pi (base, V.C {binder = B fam; env}) ->
        (*
         M : Pi(x:A).B[x]
         M(N) : B[N]
            *)
        let stuck = V.App {fn = stuck; arg = varg; base = base} in
        let fiber = eval (V.Extend (env, varg)) fam in
        V.Stuck (stuck, fiber)
      | _ ->
        failwith "can't happen!!"
    end

  | _ ->
    failwith "can't happen!!"
