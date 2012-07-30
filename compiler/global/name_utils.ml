open Names
open Modules

let rec modul_of_string_list = function
  | [] -> Idents.local_qn
  | ["Pervasives"] -> pervasives_qn
  | [q] -> fun n -> { qual = Module q; name = n}
  | q::q_l ->
      fun n -> { qual = QualModule (modul_of_string_list q_l q); name = n }

let qualname_of_string s =
  let q_l_n = Misc.split_string s "." in
  match List.rev q_l_n with
    | [] -> Misc.internal_error "Names"
    | n::q_l -> modul_of_string_list q_l n

let modul_of_string s =
  let q_l = Misc.split_string s "." in
  let q = modul_of_string_list (List.rev q_l) "" in
  q.qual


(** Use a printer to generate a string compatible with a name *)
let print_pp_to_name p x =
  let oldi = !Compiler_options.full_type_info in
  let oldq = !Compiler_options.full_qual_info in
  let oldn = !Compiler_options.full_name in
  let olds = !Compiler_options.stateful_info in
  Compiler_options.full_type_info := false;
  Compiler_options.full_qual_info := false;
  Compiler_options.full_name := false;
  Compiler_options.stateful_info := false;
  let n = Misc.sanitize_string (Misc.print_pp_to_string p x) in
  Compiler_options.full_type_info := oldi;
  Compiler_options.full_qual_info := oldq;
  Compiler_options.full_name := oldn;
  Compiler_options.stateful_info := olds;
  n