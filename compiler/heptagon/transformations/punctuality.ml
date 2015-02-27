open Heptagon

exception Not_implemented


let funs = Hept_mapfold.defaults

let program p =
  let p, _ = Hept_mapfold.program_it funs () p in
  p


let funs = 

let interface i =
  (*  raise Not_implemented *)
  i
