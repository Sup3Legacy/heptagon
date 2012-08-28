
open String
open Format

type label = string

type data = string

type row = | Row of label * data list

type t = row list

let index n i = sprintf "%s_{%d}" n i

let row_constant label value size =
  let rec list_n v s acc = match s with
    | 0 -> acc
    | _ -> list_n v (s-1) (v::acc)
  in
  Row(label, list_n value size [])

let row label f size =
  let rec el i acc = if i = size then acc else el (i + 1) ((f i) :: acc)
  in Row (label, (List.rev (el 0 [])))

let row_nat label size = row label (fun i -> sprintf "%d" i) size

let row_var label size = row label (index label) size

let row_indexed label format_with_d size = row label (fun i -> sprintf format_with_d i) size

let row_fby ?(delay=1) label row1 row2 size =
  let Row(_, init) = row1 delay in
  let Row(_, rest) = row2 (size - delay) in
  Row (label, init@rest)

let row_raw label data size =
  (if (List.length data) < size
    then raise (Invalid_argument "raw datas too short")
    else ();
    row label (fun i -> List.nth data i) size)

let chrono rows size = List.map (fun f -> f size) rows

(************ PP_tools ***********)
let rec print_list print lp sep rp ff =
  function
  | [] -> ()
  | x :: l ->
      (fprintf ff "%s%a" lp print x;
        List.iter (fprintf ff "%s@,%a" sep print) l;
        fprintf ff "%s" rp)

let rec print_list_r print lp sep rp ff =
  function
  | [] -> ()
  | x :: l ->
      (fprintf ff "%s%a" lp print x;
        List.iter (fprintf ff "%s@ %a" sep print) l;
        fprintf ff "%s" rp)

(********** Printer ***********)
let gen_print_row ?(first_row = false) ?(sep = " & ")
    ?(endl = "\\\\ \\hline") ff r =
  let print_el ff s = pp_print_string ff s
  in
  (* if first_row then pp_set_tab ff () else pp_print_tab ff () *)
  fprintf ff "@[%a@]" (print_list_r print_el "" " &" endl) r

let print_first_row ff r = gen_print_row ~first_row: true ff r

let print_row ff r = gen_print_row ff r

let print_chrono ff ?(enter_env = "\\begin{chrono}")
    ?(exit_env = "\\end{chrono}") c =
  let raw = List.map (function Row (s, l) -> s :: l) c
  in
  (* pp_open_tbox ff (); let print_row ff r = fprintf ff "%a@\n"         *)
  (* print_row r in                                                      *)
  (fprintf ff "@[%s@\n  @[" enter_env;
    fprintf ff "%a@\n" print_first_row (List.hd raw);
    fprintf ff "@[<v>%a@]" (print_list print_row "" "" "") (List.tl raw);
    (* pp_close_tbox ff (); *)
    fprintf ff "@]@\n%s@]@." exit_env)

let print c = print_chrono Format.std_formatter c