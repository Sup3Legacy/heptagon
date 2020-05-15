%{
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

(* Author: Guillaume I *)

open Parsched

%}

%token PROCESSORS DEVICES BLOCKS END_BLOCKS TWODOTS

%token <string> IDENT
%token <int> INT
%token EOF

%start parsched
%type <Parsched.parsched> parsched

%%

/* *** Example of parallel schedule we might parse ***
PROCESSORS:2 DEVICES:2

BLOCKS:3  CPU_0
0    1000  f_step
1000 3000  h_step
5000 7000  l_step
END_BLOCKS

BLOCKS:3  CPU_1
1000 2000  g_step
4000 6000  k_step
7000 8000  m_step
END_BLOCKS

BLOCKS:1  DEVICE_0
2000 4000  vector_add_1_step
END_BLOCKS

BLOCKS:1  DEVICE_1
3000 5000  vector_add_2_step
END_BLOCKS
*/

reservation:
  s=INT e=INT name=IDENT
  { mk_funcall_res name s e }
;

lreservations:
  | reservation                 { [$1] }
  | reservation lreservations   { $1::$2 }
;

block_sched:
  BLOCKS TWODOTS ncomp=INT nature=IDENT lresa=lreservations END_BLOCKS
  { 
    if ((List.length lresa)!=ncomp) then (
      Format.eprintf "Number of reservation in block does not match number declared.@.";
      raise Errors.Error
    );
    mk_block_sched nature lresa
  }
;

lblock_sched:
  | block_sched               { [$1] }
  | block_sched lblock_sched  { $1::$2 }
;

parsched:
  PROCESSORS TWODOTS nproc=INT DEVICES TWODOTS ndevices=INT lbl=lblock_sched EOF
  {
   if ((List.length lbl) != (nproc + ndevices)) then (
      Format.eprintf "Number of blocks does not match number of declared proc and device.@.";
      raise Errors.Error
    );
    mk_parsched nproc ndevices lbl
  }
;

%%
