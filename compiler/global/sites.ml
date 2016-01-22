
open Idents
open Types

type site =
  | Scentralized
  | Svar of link ref
  | Slocalized of var_ident

and link =
  | Sindex of int
  | Slink of site
	     
type tsite =
  | Ssite of site
  | Sprod of site list
       
exception Unify

let invalid_site = Sprod []

let index = ref 0

let gen_index () = (incr index; !index)

(** returns a new site variable *)
let fresh_site _ = Svar { contents = Sindex (gen_index ()); }

let rec fresh_tsite ty = match ty with
  | Tprod [] -> Ssite (fresh_site ())
  | Tprod ty_list -> Sprod (List.map fresh_site ty_list)
  | Tarray (_, _) | Tid _ | Tinvalid -> Ssite (fresh_site ())
			 
let rec site_repr s = match s with
  | Scentralized | Slocalized _
  | Svar { contents = Sindex _ } -> s
  | Svar (({ contents = Slink s }) as link) ->
	  let s = site_repr s in
	  link := Slink s;
	  s
