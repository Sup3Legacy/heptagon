
open Chrono


module ChrEnv =
struct
  include Map.Make(struct type t = label let compare = compare end)
  let append env0 env = fold (fun key v env -> add key v env) env0 env
  let printf env =
    iter
      (fun key v ->
            (Format.printf "%s :" key;
              List.iter (Format.printf " %s") v;
              Format.printf "\n"))
      env
end
module ChrSet =
struct include Set.Make(struct type t = label let compare = compare end)
end

let rec flush_line s ()=
  Scanf.bscanf s "%c" (function '\n' -> () | _ -> flush_line s ())

let parse vars s =
  let fullvars = List.fold_right ChrSet.add vars ChrSet.empty in
  let _add_var env v x =
    try ChrEnv.add v (x :: (ChrEnv.find v env)) env
    with | Not_found -> ChrEnv.add v [ x ] env in
  let add_var env uvar v x =
    let env = _add_var env v x in let uvar = ChrSet.add v uvar in (env, uvar) in
  let _parse_var s env uvar =
    Scanf.bscanf s "%s : %s\n" (add_var env uvar) in
  let _parse_step s env uvar =
    flush_line s ();
    let def x env = _add_var env x "." in
    let undefs = ChrSet.diff fullvars uvar in
    let env = ChrSet.fold def undefs env in (env, ChrSet.empty)
  in
  let rec _parse s env uvar =
    if Scanf.Scanning.end_of_input s
    then (env, uvar)
    else
      Scanf.bscanf s "%c"
        (function
          | '=' -> (let env, uvar = _parse_step s env uvar in _parse s env uvar)
          | ' ' -> (let env, uvar = _parse_var s env uvar in _parse s env uvar)
          | _ -> flush_line s (); _parse s env uvar)
  in
  let (env, _) = _parse s ChrEnv.empty ChrSet.empty
  in List.map (fun x -> List.rev (ChrEnv.find x env)) vars

let parse_chrono vars s size =
  let datas = parse vars s in
  let rows = List.map2 row_raw vars datas in
  let size = let ms = List.length (List.hd datas) in min size ms
  in chrono rows size

let main () =
  let size = ref 100 in
  let vars = ref []
  in
  (Arg.parse [ ("-size", (Arg.Set_int size), "") ]
      (fun v -> vars := v :: !vars) "";
    let chrono =
      parse_chrono (List.rev !vars) (Scanf.Scanning.from_channel stdin) !size
    in print chrono)

(** Launch the [main] *)
let _ = main ()