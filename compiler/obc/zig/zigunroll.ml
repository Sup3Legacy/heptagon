open Zig

let unroll id start stop body =
  let rec aux i l =
    let rec exp e = match e with
      | Ziguop (s, e) -> Ziguop (s, exp e)
      | Zigbop (s, e1, e2) -> Zigbop (s, exp e1, exp e2)
      | Zigfun_call (s, e_l) -> Zigfun_call (s, List.map exp e_l)
      | Zigaddrof e -> Zigaddrof (exp e)
      | Zigstructlit (s, e_l) -> Zigstructlit (s, List.map exp e_l)
      | Zigarraylit e_l -> Zigarraylit (List.map exp e_l)
      | Zigconst c -> Zigconst c
      | Zigvar s -> if s = id then Zigconst (Zigint i) else Zigvar s
      | Zigderef e -> Zigderef (exp e)
      | Zigfield (e, qn) -> Zigfield (exp e, qn)
      | Zigarray (e1, e2) -> Zigarray (exp e1, exp e2)
      | ZigUnnamedStruct l -> ZigUnnamedStruct (List.map exp l)

    and lhs l = match l with
      | ZigLvar s -> ZigLvar s
      | ZigLderef l -> ZigLderef (lhs l)
      | ZigLfield (l, qn) -> ZigLfield (lhs l, qn)
      | ZigLarray (l, e) -> ZigLarray (lhs l, exp e)

    and stm s = match s with
      | Zigsexpr e -> Zigsexpr (exp e)
      | Zigsblock b -> Zigsblock (block b)
      | Zigskip -> Zigskip
      | Zigaffect (l, e) -> Zigaffect (lhs l, exp e)
      | Zigif (e, l1, l2) -> Zigif (exp e, List.map stm l1, List.map stm l2)
      | Zigswitch (e, cl_l) -> Zigswitch (exp e, List.map (fun (s, s_l) -> s, List.map stm s_l) cl_l)
      | Zigwhile (e, s_l) -> Zigwhile (exp e, List.map stm s_l)
      | Zigfor _ -> assert false
      | Zigreturn e -> Zigreturn (exp e)

    and block b = { b with block_body = List.map stm b.block_body; }

    in

    if i = stop then List.concat (List.rev l) else aux (i + 1) ((List.map stm body) :: l)

  in

  aux start []

let static_eval e = match e with
  | Zigconst (Zigint i) -> Some i
  | _ -> None

let rec stm s = match s with
  | Zigsexpr _ | Zigskip | Zigaffect _ | Zigreturn _ -> s
  | Zigsblock b -> Zigsblock (block b)
  | Zigif (e, l1, l2) -> Zigif (e, List.map stm l1, List.map stm l2)
  | Zigswitch (e, cl_l) -> Zigswitch (e, List.map (fun (s, s_l) -> s, List.map stm s_l) cl_l)
  | Zigwhile (e, s_l) -> Zigwhile (e, List.map stm s_l)
  | Zigfor (x, start, stop, body) ->
    let body = List.map stm body in
    (match static_eval start, static_eval stop with
      | Some i, Some j -> Zigsblock { var_decls = []; block_body = unroll x i j body; }
      | _ -> Zigfor (x, start, stop, body))

and block b = { b with block_body = List.map stm b.block_body; }

let zigdef d = match d with
  | Zigfundef def ->
    let body = { def.f_body with block_body = List.map stm def.f_body.block_body; } in
    Zigfundef { def with f_body = body; }
  | _ -> d

let zigfile ((s, d): Zig.zigfile) : Zig.zigfile = 
  let (a, b) = d in (s, (a, (List.map zigdef b)))
