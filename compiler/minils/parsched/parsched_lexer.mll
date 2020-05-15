(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)


{
open Lexing
open Location
open Parsched_parser
open Compiler_utils

exception Lexical_error of lexical_error * location;;


let comment_depth = ref 0

let keyword_table = ((Hashtbl.create 10) : (string, token) Hashtbl.t);;

List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok) [
 "PROCESSORS", PROCESSORS;
 "DEVICES", DEVICES;
 "BLOCKS", BLOCKS;
 "END_BLOCKS", END_BLOCKS;
]
}

let newline = '\n' | '\r' '\n'

rule token = parse
  | newline         { new_line lexbuf; token lexbuf }
  | [' ' '\t'] +    { token lexbuf }
  
  | ':'             { TWODOTS }


  | (['A'-'Z' 'a'-'z' '_']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      { let s = Lexing.lexeme lexbuf in
        begin try Hashtbl.find keyword_table s
          with Not_found -> IDENT id
    	end
      }
  | ['0'-'9']+
  | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
  | '0' ['o' 'O'] ['0'-'7']+
  | '0' ['b' 'B'] ['0'-'1']+ 
    { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | eof            {EOF}
  | _     { raise (Lexical_error (Illegal_character,
                    Loc (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf))
                  )
          }
