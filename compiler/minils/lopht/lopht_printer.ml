(*******************************************************************************
 * Fiabilité et Sûreté de Fonctionnement
 * Copyright (c) 2013, 2014 Institut de Recherche Technologique SystemX
 * All rights reserved.
 *******************************************************************************)

open Lopht_input

exception Not_implemented


let print_list f fmt = function
  | [] -> ()
  | x :: l ->
      f fmt x ;
      List.iter (Format.fprintf fmt " %a" f) l

let print_id = Format.pp_print_string

(* Not all characters are allowed in comments, only alphanumeric, spaces and
   some symbols. See LoPhT grammar for more details. This function does not
     filter or translate incorrect characters. *)
let print_comment (fmt : Format.formatter) (comment : string) =
  Format.fprintf fmt "/* %s */" comment 

let pretty_print_head1 (fmt : Format.formatter) (head : string) =
  let n = String.length head in
  let s = String.make (n + 8) '=' in
  Format.fprintf fmt "/*%s*/\n/**/  %s  /**/\n/*%s*/" s head s

let pretty_print_head2 (fmt : Format.formatter) (head : string) =
  let n = String.length head in
  let s = String.make (n + 8) '-' in
  Format.fprintf fmt "\n\n/*%s*/\n/**/  %s  /**/\n/*%s*/" s head s

let pretty_print_head3 (fmt : Format.formatter) (head : string) =
  let n = String.length head in
  let s = String.make n '-' in
  Format.fprintf fmt "\n\n   %s   \n/* %s */\n\n" head s


let print_ty_idx fmt t =
  Format.fprintf fmt "Type:%d" t.ty_index

let print_fun_idx fmt f =
  Format.fprintf fmt "Function:%d" f.fun_index

let print_const_idx fmt c =
  Format.fprintf fmt "Const:%d" c.cst_index

let print_var_idx fmt v =
  Format.fprintf fmt "Variable:%d" v.var_index

let print_clk_idx fmt c =
  Format.fprintf fmt "Clock:%d" c.clk_index

let print_rel_idx fmt r =
  Format.fprintf fmt "Rel:%d" r.rel_index

let print_partition_idx fmt p =
  Format.fprintf fmt "Partition:%d" p.part_index

let print_block_idx fmt b =
  Format.fprintf fmt "Block:%d" b.block_index


let print_const_exp fmt = function
  | NamedConst cst -> print_const_idx fmt cst
  | Integer i -> Format.pp_print_int fmt i
  | Boolean (true) -> Format.pp_print_string fmt "true"
  | Boolean (false) -> Format.pp_print_string fmt "false"
  | Float f -> Format.pp_print_float fmt f
  | String s -> Format.fprintf fmt "\"%s\"" s

let rec print_value_exp fmt = function
  | Variable var ->
      print_var_idx fmt var
  | Function (f,l) ->
      Format.fprintf fmt "%a(%a)"
        print_fun_idx f
        (print_list print_value_exp) l
  | Const cst ->
      print_const_exp fmt cst 

let rec print_bool_exp fmt exp = match exp with
  | Predicate exp ->
      print_value_exp fmt exp
  | Equal (v,e)
  | NotEqual (v,e)
  | LowerEqual (v,e)
  | Lower (v,e)
  | Greater (v,e)
  | GreaterEqual (v,e) ->
      let operator = match exp with
        | Equal _ -> "="
        | NotEqual _ -> "#"
        | LowerEqual _ -> "<="
        | Lower _ -> "<"
        | GreaterEqual _ -> ">="
        | Greater _ -> ">"
        | _ -> assert false
      in
      Format.fprintf fmt "%a %s %a"
        print_var_idx v
        operator
        print_value_exp e
  | In (v,l) ->
      Format.fprintf fmt "%a in {%a}"
        print_var_idx v
        (print_list print_id) l
  | And (e1, e2)
  | Or (e1, e2)
  | Diff (e1, e2) ->
      let operator = match exp with
        | And _ -> "And"
        | Or _ -> "Or"
        | Diff _ -> "Diff"
        | _ -> assert false
      in
        Format.fprintf fmt "%s(%a %a)"
          operator
          print_bool_exp e1
          print_bool_exp e2
  | Not e ->
      Format.fprintf fmt "Not(%a)"
      print_bool_exp e

let rec print_clk_exp fmt clk = match clk with
  | BaseClock c ->
      print_clk_idx fmt c
  | Union (c1,c2) 
  | Intersection (c1,c2)
  | Difference  (c1,c2) ->
      let operator = match clk with
        | Union _ -> "Or"
        | Intersection _ -> "And"
        | Difference _ -> "Diff"
        | _ -> assert false
      in
        Format.fprintf fmt "%s(%a %a)"
          operator
          print_clk_exp c1
          print_clk_exp c2
  | Subsampling (_c,()) -> raise Not_implemented
  | Test (c,f) -> 
      Format.fprintf fmt "Test(%a %a)"
        print_clk_exp c
        print_bool_exp f


let print_type_def fmt ty_def =
  Format.fprintf fmt "%a\t%a\t"
    print_ty_idx ty_def
    print_id ty_def.ty_id ;
  begin match ty_def.ty_desc with
    | SimpleType -> Format.fprintf fmt "Simple" 
    | PredefinedType -> Format.fprintf fmt "Predefined"
    | EnumeratedType id_list -> Format.fprintf fmt "Enumerated = { %a }" (print_list print_id) id_list  
  end ;
  Format.fprintf fmt "\n"

let print_fun_def fmt fun_def =
  let print_arg fmt (id,ty) =
    Format.fprintf fmt "%a:%a"
      print_id id
      print_ty_idx ty
  in
  Format.fprintf fmt "%a\t%a\t(%a) -> (%a)\n"
    print_fun_idx fun_def
    print_id fun_def.fun_id
    (print_list print_arg) fun_def.fun_inputs
    (print_list print_arg) fun_def.fun_outputs

let print_const_def fmt cst_def =
  Format.fprintf fmt "%a\t%a\t"
    print_const_idx cst_def
    print_id cst_def.cst_id ;
  begin match cst_def.cst_desc with
    | ExternalConst ->
        Format.fprintf fmt "External"
    | InitFunctionConst (f,l) ->
        Format.fprintf fmt "%a(%a)"
            print_fun_idx f
            (print_list print_const_exp) l  
  end ;
  Format.fprintf fmt "\n"
        
let print_var_def fmt var_def =
  let source_id,source_block = var_def.var_source_port in 
  Format.fprintf fmt "%a\t%a\tSingle Assignment\t%a @@ %a"
    print_var_idx var_def
    print_ty_idx var_def.var_type
    print_id source_id
    print_block_idx source_block ;
  begin match var_def.var_allocation with
    | Some proc_def -> Format.fprintf fmt " On %a\n" ; raise Not_implemented
    | None -> Format.fprintf fmt "\n" 
  end

let print_clk_dep fmt (v,c) =
  Format.fprintf fmt "%a On %a"
    print_var_idx v
    print_clk_idx c

let print_clk_def fmt clock_def =
  print_clk_idx fmt clock_def ;
  begin match clock_def.clk_id with
    | Some id -> Format.fprintf fmt "\t%a" print_id id
    | None -> () 
  end ;
  Format.fprintf fmt "\t" ;
  begin match clock_def.clk_desc with
    | Primitive -> Format.fprintf fmt "Primitive"
    | Derived e -> print_clk_exp fmt e
  end ;
  Format.fprintf fmt "\t%a\n"
    (print_list print_clk_dep) clock_def.clk_dependencies

let print_rel_def fmt rel =
  let operator = match rel.rel_kind with
    | EqualClocks -> "="
    | ExclusiveClocks -> raise Not_implemented
    | LowerOrEqualClocks -> "<="
  in
  Format.fprintf fmt "%a\t%s(%a)\n"
    print_rel_idx rel
    operator
    (print_list print_clk_idx) rel.rel_clocks
    
let print_partition_def fmt part =
  Format.fprintf fmt "%a\t%a\n"
    print_partition_idx part
    print_id part.part_id

let print_block_def fmt block =
  let print_input_port fmt ip =
    Format.fprintf fmt "%a Is %a"
      print_id ip.input_port_name
      (print_list print_clk_dep) ip.input_port_arcs
  and print_output_port fmt op =
    Format.fprintf fmt "%a Is %a"
      print_id op.output_port_name
      print_var_idx op.output_port_var
  in
  Format.fprintf fmt "%a\t" print_block_idx block ;
  begin match block.block_id with
  | Some id -> Format.fprintf fmt "%a\t" print_id id
  | None -> ()
  end ;
  Format.fprintf fmt "%a\t(%a) -> (%a)\t"
    print_clk_idx block.block_clk
    (print_list print_input_port) block.block_inputs
    (print_list print_output_port) block.block_outputs ;
  begin match block.block_function with
  | DelayBlock delay ->
      Format.fprintf fmt "Delay %a Depth %d Init %a"
        print_ty_idx delay.delay_ty
        delay.delay_depth
        (print_list print_const_exp) delay.delay_init
  | FunBlock func ->
      print_fun_idx fmt func
  | ConstBlock const_exp ->
      Format.fprintf fmt "Constant:%a"
        print_const_exp const_exp
  end ;
  begin match block.block_preemptible with
  | Some true -> Format.fprintf fmt "\tPreemptible"
  | Some false -> Format.fprintf fmt "\tNot Preemptible"
  | None -> ()
  end ;
  begin match block.block_offset with
  | Some i -> Format.fprintf fmt "\tOffset:%d" i
  | None -> ()
  end ;
  begin match block.block_deadline with
  | Some (Finite (i,j)) -> Format.fprintf fmt "\tDeadline:%d:%d" i j 
  | Some (Infinite) -> Format.fprintf fmt "\tDeadline Linfinite"
  | None -> ()
  end ;
  begin match block.block_partitions with
  | [] -> ()
  | l -> Format.fprintf fmt "\tBelongs To:%a" (print_list print_partition_idx) l
  end ;
  begin match block.block_schedule with
  | Some _ -> raise Not_implemented
  | None -> ()
  end ;
  Format.fprintf fmt "\n"


let print_clocked_graph (fmt : Format.formatter) (cg : clocked_graph) =
  pretty_print_head1 fmt "ClockedGraph" ;
  (* Global definitions *)
  pretty_print_head2 fmt "Global definitions" ;
  pretty_print_head3 fmt "Type Table" ;
  List.iter (print_type_def fmt) cg.types ;
  pretty_print_head3 fmt "Function Table" ;
  List.iter (print_fun_def fmt) cg.functions ;
  pretty_print_head3 fmt "Const Table" ;
  List.iter (print_const_def fmt) cg.constants ;
  pretty_print_head3 fmt "Functional specification" ;
  pretty_print_head3 fmt "Variable Table" ;
  List.iter (print_var_def fmt) cg.variables ;
  pretty_print_head3 fmt "Clock Table" ;
  List.iter (print_clk_def fmt) cg.clocks ;
  pretty_print_head3 fmt "Rel Table" ;
  List.iter (print_rel_def fmt) cg.relations ;
  if cg.partitions <> [] then (
    pretty_print_head3 fmt "Partition Table" ;
    List.iter (print_partition_def fmt) cg.partitions) ;
  pretty_print_head3 fmt "Block Table" ;
  List.iter (print_block_def fmt) cg.blocks ;
  (* Architecture *)
  pretty_print_head2 fmt "Architecture"

