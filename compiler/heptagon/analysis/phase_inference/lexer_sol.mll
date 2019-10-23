{
open Lexing
open Parser_sol

exception Error

}

rule main = parse 
  | [' ' '\b' '\t']+                                    { main lexbuf }
  | '\n'                                                { new_line lexbuf; main lexbuf }
  | eof                                                 { EOF }
  | "->"											    { ARROW }
  | (['a'-'z''A'-'Z']['A'-'Z''_''0'-'9''a'-'z']+ as v)  { IDENT v }
  | (['-']?['0'-'9']+ as v)                         	{ INT (int_of_string v) }
  | _                                                   { raise Error }


