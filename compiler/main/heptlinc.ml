
open Modules
open Errors
open Signature
open Names
open Global_printer
open Format

let usage_msg = "Usage: " ^
  Sys.executable_name ^ " -mod <Module> -node <node> -exec <exec> [OPTION]...\n" ^
"       " ^  Sys.executable_name ^ " -sig <file>.epci -node <node> -exec <exec> [OPTION]..."
and doc_sig  = "<file>.epci\tCompiled interface containing node <node> (for backward compatibility)"
and doc_mod  = "<Module>\tModule containing node <node>"
and doc_node = "<node>\tName of simulated node"

let main () =

  let mod_name = ref "" in
  let node_name = ref "" in

  let mod_name_of_epci epci_name =
    if Filename.check_suffix epci_name ".epci" then
      begin
        let filename = Filename.chop_suffix epci_name ".epci" in
        mod_name := String.capitalize(Filename.basename filename)
      end
    else
      raise (Arg.Bad("Invalid compiled interface: " ^ epci_name)) in


  let arg_list =
    [
      "-sig",Arg.String mod_name_of_epci,doc_sig; (* Backward compatibility *)
      "-mod",Arg.Set_string mod_name,doc_mod;
      "-node",Arg.Set_string node_name,doc_node;
    ] in
  Arg.parse
    arg_list
    (fun s -> raise (Arg.Bad ("Invalid argument: " ^ s)))
    usage_msg;

  if (!mod_name = "") || (!node_name = "") then
    begin
      Arg.usage arg_list usage_msg;
      raise Error
    end;

  open_module (Module !mod_name);

  let signature = find_value { qual = (Module !mod_name);
                               name = !node_name } in


  let print_arg arg =
    let name = match arg.a_name with
    | None -> "<anonymous>"
    | Some name -> name
    in
    printf "%s : %a\n" name print_type arg.a_type
  in

  printf "Inputs :\n";
  List.iter print_arg signature.node_inputs;
  printf "Outputs :\n";
  List.iter print_arg signature.node_outputs
;;

let _ = main ()
