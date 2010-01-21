(*
 * Abstract syntax of OMakefiles.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; version 2
 * of the License.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 *
 * Additional permission is given to link this library with the
 * with the Objective Caml runtime, and to redistribute the
 * linked executables.  See the file LICENSE.OMake for more details.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
open Lm_symbol
open Lm_location

type var = symbol

(*
 * Shell flags indicating whether a body needs to be read.
 *)
type body_flag =
   NoBody
 | OptBody
 | ColonBody
 | ArrayBody

(*
 * Function applications can be tagged as Lazy or Eager.
 *)
type apply_strategy =
   LazyApply
 | EagerApply
 | NormalApply

(*
 * When a variable is defined, these are additional flags.
 * The bool is true if this is an array operation.
 *)
type define_kind =
   DefineString
 | DefineArray

type define_flag =
   DefineNormal
 | DefineAppend

(*
 * Patterns.
 *)
type exp =
   NullExp         of loc
 | StringExp       of string * loc
 | QuoteExp        of exp list * loc
 | QuoteStringExp  of char * exp list * loc
 | SequenceExp     of exp list * loc
 | ArrayExp        of exp list * loc
 | ApplyExp        of apply_strategy * var * exp list * loc
 | SuperApplyExp   of apply_strategy * var * var * exp list * loc
 | MethodApplyExp  of apply_strategy * var list * exp list * loc
 | CommandExp      of var * exp * exp list * loc
 | VarDefExp       of var list * define_kind * define_flag * exp * loc
 | VarDefBodyExp   of var list * define_kind * define_flag * exp list * loc
 | ObjectDefExp    of var list * define_flag * exp list * loc
 | FunDefExp       of var list * var list * exp list * loc
 | RuleExp         of bool * exp * exp * exp SymbolTable.t * exp list * loc
 | BodyExp         of exp list * loc
 | ShellExp        of exp * loc
 | CatchExp        of var * var * exp list * loc
 | ClassExp        of symbol list * loc
 | KeyExp          of apply_strategy * string * loc
 | KeyDefExp       of string * define_kind * define_flag * exp * loc
 | KeyDefBodyExp   of string * define_kind * define_flag * exp list * loc

type prog = exp list

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
