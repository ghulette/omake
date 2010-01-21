(*
 * Define an intermediate representation that is a little
 * easier to work with than the AST.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003-2007 Jason Hickey, California Institute of Technology
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
open Lm_location
open Lm_symbol

open Omake_node_sig
open Omake_node

(* %%MAGICBEGIN%% *)
(* Revision 11186: replaced static-rule function with the new memo-rule *)
type var = symbol

(*
 * Evaluation of lazy applications is delayed as much as possible.
 * Eager applications are evaluated even in the scope of a lazy
 * application.  Normal applications are evaluated eagerly, except
 * in the scope of a lazy application.
 *)
type apply_strategy =
   LazyApply
 | EagerApply
 | NormalApply

(*
 * Arity of functions.
 *)
type arity =
   ArityRange of int * int
 | ArityExact of int
 | ArityNone
 | ArityAny

(*
 * Kinds of matches.
 *)
type match_kind =
   MatchWild
 | MatchRegex

(*
 * Variable definitions have several forms.
 *    VarDefNormal: normal definition
 *    VarDefAppend: append the text
 *)
type var_def_kind =
   VarDefNormal
 | VarDefAppend

(*
 * Simple version of variables includes the kind of
 * scope, the location, and the variable name.
 *)
type var_info =
   VarPrivate        of loc * var
 | VarThis           of loc * var
 | VarVirtual        of loc * var
 | VarGlobal         of loc * var

(*
 * A symbol table maps variables to their info.
 *)
type senv = var_info SymbolTable.t

(*
 * Exporting.
 *)
type export_item =
   ExportRules
 | ExportPhonies
 | ExportVar of var_info

type export =
   ExportNone
 | ExportAll
 | ExportList of export_item list

(*
 * Expression that results in a string.
 *)
type string_exp =
   NoneString        of loc
 | ConstString       of loc * string
   (* ZZZ: FunString, MethodString *)
 | ApplyString       of loc * apply_strategy * var_info * string_exp list
 | SuperApplyString  of loc * apply_strategy * var * var * string_exp list
 | MethodApplyString of loc * apply_strategy * var_info * var list * string_exp list
 | SequenceString    of loc * string_exp list
 | ArrayString       of loc * string_exp list
 | ArrayOfString     of loc * string_exp
 | QuoteString       of loc * string_exp list
 | QuoteStringString of loc * char * string_exp list
 | ObjectString      of loc * exp list * export
 | BodyString        of loc * exp list * export
 | ExpString         of loc * exp list * export
 | CasesString       of loc * (var * string_exp * exp list * export) list
 | KeyApplyString    of loc * apply_strategy * string
 | VarString         of loc * var_info
 | ThisString        of loc

and source_exp = node_kind * string_exp

and source_table = string_exp SymbolTable.t

(*
 * Commands.
 *)
and rule_command =
   RuleSection of string_exp * exp
 | RuleString of string_exp

and exp =
   (* Definitions *)
   LetVarExp        of loc * var_info * var list * var_def_kind * string_exp
 | LetFunExp        of loc * var_info * var list * var list * exp list * export
 | LetObjectExp     of loc * var_info * var list * string_exp * exp list * export
 | LetThisExp       of loc * string_exp
 | LetKeyExp        of loc * string * var_def_kind * string_exp

   (* Applications *)
 | ApplyExp         of loc * var_info * string_exp list
 | SuperApplyExp    of loc * var * var * string_exp list
 | MethodApplyExp   of loc * var_info * var list * string_exp list
 | KeyExp           of loc * string

   (* Sequences *)
 | SequenceExp      of loc * exp list
 | SectionExp       of loc * string_exp * exp list * export

   (* StaticExp (loc, filename, id, el) *)
 | StaticExp        of loc * Node.t * symbol * exp list

   (* Conditional *)
 | IfExp            of loc * (string_exp * exp list * export) list

   (* Shell command *)
 | ShellExp         of loc * string_exp

   (*
    * StringExp (loc, s)
    *    This is just an identity, evaluating to s
    * ReturnExp (loc, s)
    *    This is a control operation, branching to the innermost ReturnBodyExp
    * ReturnBodyExp (loc, e)
    *    Return to here.
    *)
 | StringExp        of loc * string_exp
 | ReturnExp        of loc * string_exp
 | ReturnBodyExp    of loc * exp list

   (*
    * LetOpenExp (loc, v, id, file, link)
    *    id    : the current object
    *    file  : name of the file/object to open
    *    link  : link information for the rest of the variables in scope.
    *)
 | OpenExp          of loc * Node.t list
 | IncludeExp       of loc * string_exp * string_exp list

   (* Return the current object *)
 | ReturnObjectExp  of loc * symbol list
 | ReturnSaveExp    of loc

(*
 * The IR stored in a file.
 *    ir_classnames   : class names of the file
 *    ir_vars         : variables defined by this file
 *    ir_exp          : the expression
 *)
type ir =
   { ir_classnames   : symbol list;
     ir_vars         : senv;
     ir_exp          : exp
   }
(* %%MAGICEND%% *)

(*
 * Variable classes.
 *    private: variables local to the file, statically scoped.
 *    this: object fields, dynamically scoped.
 *    virtual: file fields, dynamically scoped.
 *    global: search each of the scopes in order (ZZZ: 0.9.8 only)
 *)
type var_scope =
   VarScopePrivate
 | VarScopeThis
 | VarScopeVirtual
 | VarScopeGlobal

(************************************************************************
 * Simplified variables.
 *)
type simple_var_info = var_scope * var

module SimpleVarCompare =
struct
   type t = simple_var_info

   let compare (s1, v1) (s2, v2) =
      match s1, s2 with
         VarScopePrivate, VarScopePrivate
       | VarScopeThis, VarScopeThis
       | VarScopeVirtual, VarScopeVirtual
       | VarScopeGlobal, VarScopeGlobal ->
            Lm_symbol.compare v1 v2
       | VarScopePrivate, VarScopeThis
       | VarScopePrivate, VarScopeVirtual
       | VarScopePrivate, VarScopeGlobal
       | VarScopeThis, VarScopeVirtual
       | VarScopeThis, VarScopeGlobal
       | VarScopeVirtual, VarScopeGlobal ->
            -1
       | VarScopeThis, VarScopePrivate
       | VarScopeVirtual, VarScopePrivate
       | VarScopeVirtual, VarScopeThis
       | VarScopeGlobal, VarScopePrivate
       | VarScopeGlobal, VarScopeThis
       | VarScopeGlobal, VarScopeVirtual ->
            1
end;;

module SimpleVarSet = Lm_set.LmMake (SimpleVarCompare);;
module SimpleVarTable = Lm_map.LmMake (SimpleVarCompare);;

(************************************************************************
 * Variable tables.  The const_flag and protected_flag are just
 * comments, and aren't part of the comparison.
 *)
module VarInfoCompare =
struct
   type t = var_info

   let compare info1 info2 =
      match info1, info2 with
         VarPrivate   (_, v1), VarPrivate   (_, v2)
       | VarThis (_, v1),      VarThis (_, v2)
       | VarVirtual (_, v1),   VarVirtual (_, v2)
       | VarGlobal (_, v1),    VarGlobal (_, v2) ->
            Lm_symbol.compare v1 v2
       | VarPrivate _,        VarThis _
       | VarPrivate _,        VarVirtual _
       | VarPrivate _,        VarGlobal _
       | VarThis _,           VarVirtual _
       | VarThis _,           VarGlobal _
       | VarVirtual _,        VarGlobal _ ->
            -1
       | VarThis _,           VarPrivate _
       | VarVirtual _,        VarPrivate _
       | VarVirtual _,        VarThis _
       | VarGlobal _,         VarPrivate _
       | VarGlobal _,         VarThis _
       | VarGlobal _,         VarVirtual _ ->
            1
end;;

module VarInfoSet =
struct
   module Set = Lm_set.LmMake (VarInfoCompare);;
   include Set;;

   let loc = bogus_loc "VarInfoSet"

   (* Remove classes of variables *)
   let remove_private set v =
      remove set (VarPrivate (loc, v))

   (* Parameters are always private *)
   let remove_param = remove_private
end;;

module VarInfoTable = Lm_map.LmMake (VarInfoCompare);;

let var_equal v1 v2 =
   VarInfoCompare.compare v1 v2 = 0

let var_of_var_info = function
   VarPrivate (loc, v)
 | VarThis (loc, v)
 | VarVirtual (loc, v)
 | VarGlobal (loc, v) ->
      loc, v

(************************************************************************
 * Path definitions.
 *)
type name_info =
   { name_static     : bool;
     name_scope      : var_scope option
   }

type method_name =
   NameEmpty   of name_info
 | NameMethod  of name_info * var * var list

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
