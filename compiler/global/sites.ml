
open Names
open Types

type site =
  | Scentralized
  | Svar of link ref
  | Slocalized of name

and link =
  | Sindex of int
  | Slink of site
	     
type tsite =
  | Ssite of site
  | Sprod of tsite list
       
exception Unify

let invalid_site = Sprod []

let index = ref 0

let gen_index () = (incr index; !index)

(** returns a new site variable *)
let fresh_site _ = Svar { contents = Sindex (gen_index ()); }

let rec fresh_tsite ty = match ty with
  | Tprod [] -> Ssite (fresh_site ())
  | Tprod ty_list -> Sprod (List.map fresh_tsite ty_list)
  | Tarray (_, _) | Tid _ | Tinvalid -> Ssite (fresh_site ())
			 
let rec site_repr s = match s with
  | Scentralized | Slocalized _
  | Svar { contents = Sindex _ } -> s
  | Svar (({ contents = Slink s }) as link) ->
	  let s = site_repr s in
	  link := Slink s;
	  s

let unify_site s1 s2 =
  let s1 = site_repr s1 in
  let s2 = site_repr s2 in
  if s1 == s2 then ()
  else
    match s1, s2 with
    | Scentralized, Scentralized -> ()
    | Slocalized n1, Slocalized n2 when (n1 = n2) -> ()
    | Svar { contents = Sindex n1 }, Svar { contents = Sindex n2 } when (n1 = n2) -> ()
    | Svar ({ contents = Sindex n } as v), s
    | s, Svar ({ contents = Sindex n } as v) ->
       v := Slink s
    | _ -> raise Unify

let rec unify ts1 ts2 =
  if ts1 == ts2 then ()
  else
    match ts1, ts2 with
    | Ssite s1, Ssite s2 ->
       unify_site s1 s2
    | Sprod ts1_l, Sprod ts2_l ->
       begin try List.iter2 unify ts1_l ts2_l
       with _ -> raise Unify
       end
    | _ -> raise Unify

let rec skeleton s = function
  | Tprod ty_list ->
      (match ty_list with
        | [_] -> Ssite s
        | l -> Sprod (List.map (skeleton s) l))
  | Tarray _ | Tid _ | Tinvalid -> Ssite s

let prod = function
  | [s] -> s
  | s_l -> Sprod s_l

(* Get the site of a site type, assuming this type is only one site *)
let site_of_tsite = function
  | Ssite s -> s
  | _ -> failwith "Site type is a product"

let rec first_site ts = match ts with
  | Ssite s -> s
  | Sprod [] -> assert false
  | Sprod (ts::_) -> first_site ts
