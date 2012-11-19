
open Heptagon
open Global_mapfold
open Hept_mapfold



let my_exp funs _ e = match e.e_desc with
  | Eapp ({a_op = Ebang}, e_l, _)
  | Eiterator (_, {a_op = Ebang}, _, _, e_l, _) ->
      let e' = Misc.assert_1 e_l in
      exp_it funs () e'
  | _ ->
      exp funs () e

let my_app _ _ a = {a with a_async = None }, ()

let my_static_exp funs _ se = match se.Signature.se_desc with
  | Signature.Sasync se' ->
      static_exp_it funs () se'
  | _ ->
      static_exp funs () se

let my_ty funs _ t = match t with
  | Signature.Tfuture (_, t') ->
      ty_it funs () t'
  | _ -> raise Errors.Fallback


let program p =
  let funs =
    { defaults with
        exp = my_exp;
        app = my_app;
        global_funs = {Global_mapfold.defaults with
          static_exp = my_static_exp;
          ty = my_ty } }
  in
  let p, _ = program_it funs () p in
  p
  (*Typing.program p*)