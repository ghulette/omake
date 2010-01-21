(*
 * Print IR expressions.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003-2007 MetaPRL Group, California Institute of Technology and
 * HRL Laboratories, LLC
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
 * Author: Jason Hickey @email{jyh@cs.caltech.edu}
 * Modified By: Aleksey Nogin @email{nogin@cs.caltech.edu}, @email{anogin@hrl.com}
 * @end[license]
 *)
open Lm_printf
open Lm_symbol
open Lm_location

open Omake_ir
open Omake_node
open Omake_ir_util
open Omake_node_sig
open Omake_print_util

let print_location = Omake_ast_print.print_location

let string_override s pp_fun complete buf arg =
   if complete then
      pp_fun true buf arg
   else
      pp_print_string buf s

(*
 * Match kind.
 *)
let pp_print_match_kind out kind =
   let s =
      match kind with
         MatchWild -> "switch"
       | MatchRegex -> "match"
   in
      pp_print_string out s

(*
 * Print the evaluation strategy.
 *)
let pp_print_strategy buf s =
   match s with
      LazyApply -> pp_print_char buf '\''
    | EagerApply -> pp_print_char buf ','
    | NormalApply -> ()

(*
 * Arities.
 *)
let pp_print_arity buf arity =
   match arity with
      ArityRange (lower, upper) ->
         fprintf buf "%d..%d" lower upper
    | ArityExact i ->
         pp_print_int buf i
    | ArityAny ->
         pp_print_string buf "varargs"
    | ArityNone ->
         pp_print_int buf 0

(*
 * Print a list of symbols.
 *)
let rec pp_print_symbol_list buf sl =
   match sl with
      [s] ->
         pp_print_symbol buf s
    | [] ->
         ()
    | s :: sl ->
         fprintf buf "%a, %a" pp_print_symbol s pp_print_symbol_list sl

(*
 * Print a variable definition kind.
 *)
let pp_print_var_def_kind buf kind =
   let s =
      match kind with
         VarDefNormal ->
            "="
       | VarDefAppend ->
            "+="
   in
      pp_print_string buf s

(*
 * Scope.
 *)
let pp_print_var_scope buf kind =
   let s =
      match kind with
         VarScopePrivate   -> "private."
       | VarScopeThis      -> "this."
       | VarScopeVirtual   -> "public."
       | VarScopeGlobal    -> "global."
   in
      pp_print_string buf s

(*
 * Variables.
 *)
let pp_print_var_info buf v =
   match v with
      VarPrivate (_, v) ->
         fprintf buf "private.%a" (**)
            pp_print_symbol v
    | VarThis (_, v) ->
         fprintf buf "this.%a" (**)
            pp_print_symbol v
    | VarVirtual (_, v) ->
         fprintf buf "public.%a" (**)
            pp_print_symbol v
    | VarGlobal (_, v) ->
         fprintf buf "global.%a" (**)
            pp_print_symbol v

(*
 * Print the export info.
 *)
let pp_print_export_item buf item =
   match item with
      ExportRules ->
         pp_print_string buf ".RULE"
    | ExportPhonies ->
         pp_print_string buf ".PHONY"
    | ExportVar v ->
         pp_print_var_info buf v

let rec pp_print_export_items buf items =
   match items with
      [item] ->
         pp_print_export_item buf item
    | item :: items ->
         fprintf buf "%a@ %a" pp_print_export_item item pp_print_export_items items
    | [] ->
         ()

let pp_print_export_info buf info =
   match info with
      ExportNone ->
         ()
    | ExportAll ->
         fprintf buf "@ export <all>"
    | ExportList items ->
         fprintf buf "@ @[<b 3>export %a@]" pp_print_export_items items

(*
 * Print a string expression.
 *)
let rec pp_print_string_exp complete buf s =
   match s with
      NoneString _ ->
         fprintf buf "<none>"
    | ConstString (_, s) ->
         fprintf buf "\"%s\"" (String.escaped s)
    | KeyApplyString (_, strategy, s) ->
         fprintf buf "$%a|%s|" pp_print_strategy strategy s
    | VarString (_, v) ->
         fprintf buf "`%a" pp_print_var_info v
    | ApplyString (_, strategy, v, []) ->
         fprintf buf "@[<hv 3>$%a(%a)@]" (**)
            pp_print_strategy strategy
            pp_print_var_info v
    | ApplyString (_, strategy, v, args) ->
         fprintf buf "@[<hv 3>$%a(%a %a)@]" (**)
            pp_print_strategy strategy
            pp_print_var_info v
            (pp_print_string_exp_list complete) args
    | SuperApplyString (_, strategy, super, v, []) ->
         fprintf buf "@[<hv 3>$%a(%a::%a)@]" (**)
            pp_print_strategy strategy
            pp_print_symbol super
            pp_print_symbol v
    | SuperApplyString (_, strategy, super, v, args) ->
         fprintf buf "@[<hv 3>$%a(%a::%a %a)@]" (**)
            pp_print_strategy strategy
            pp_print_symbol super
            pp_print_symbol v
            (pp_print_string_exp_list complete) args
    | MethodApplyString (_, strategy, v, vl, []) ->
         fprintf buf "@[<hv 3>$%a(%a.%a)@]" (**)
            pp_print_strategy strategy
            pp_print_var_info v
            pp_print_method_name vl
    | MethodApplyString (_, strategy, v, vl, args) ->
         fprintf buf "@[<hv 3>$%a(%a.%a %a)@]" (**)
            pp_print_strategy strategy
            pp_print_var_info v
            pp_print_method_name vl
            (pp_print_string_exp_list complete) args
    | SequenceString (_, sl) ->
         fprintf buf "@[<hv 1>(%a)@]" (**)
            (pp_print_string_exp_list complete) sl
    | ArrayOfString (_, s) ->
         fprintf buf "@[<hv 1>(array-of-string@ %a)@]" (**)
            (pp_print_string_exp complete) s
    | ArrayString (_, sl) ->
         fprintf buf "@[<hv 1>[|%a|]@]" (**)
            (pp_print_string_exp_list complete) sl
    | QuoteString (_, sl) ->
         fprintf buf "@[<hv 1>(quote %a)@]" (**)
            (pp_print_string_exp_list complete) sl
    | QuoteStringString (_, c, sl) ->
         fprintf buf "@[<hv 1>(quote %c%a%c)@]" (**)
            c (pp_print_string_exp_list complete) sl c
    | ObjectString (_, e, export) ->
         if complete then
            fprintf buf "@[<hv 3>object@ %a%a@]" (**)
               (pp_print_exp_list complete) e
               pp_print_export_info export
         else
            pp_print_string buf "<object...>"
    | BodyString (_, e, export) ->
         if complete then
            fprintf buf "@[<hv 3>body@ %a%a@]" (**)
               (pp_print_exp_list complete) e
               pp_print_export_info export
         else
            pp_print_string buf "<body...>"
    | ExpString (_, e, export) ->
         if complete then
            fprintf buf "@[<hv 3>exp@ %a%a@]" (**)
               (pp_print_exp_list complete) e
               pp_print_export_info export
         else
            pp_print_string buf "<exp...>"
    | CasesString (_, cases) ->
         if complete then begin
            fprintf buf "@[<hv 3>cases:";
            List.iter (fun (v, e1, e2, export) ->
                  fprintf buf "@ @[<hv 3>%a %a:@ %a%a@]" (**)
                     pp_print_symbol v
                     (pp_print_string_exp complete) e1
                     (pp_print_exp_list complete) e2
                     pp_print_export_info export) cases;
            fprintf buf "@]"
         end else
            pp_print_string buf "<cases...>"
    | ThisString loc ->
         pp_print_string buf "$<this>"

and pp_print_string_exp_list complete buf sl =
   match sl with
      [s] ->
         pp_print_string_exp complete buf s
    | [] ->
         ()
    | s :: sl ->
         fprintf buf "%a,@ %a" (pp_print_string_exp complete) s (pp_print_string_exp_list complete) sl

(*
 * Print an expression.
 *)
and pp_print_exp complete buf e =
   if complete && !print_location then
      fprintf buf "<%a>" pp_print_location (loc_of_exp e);
   match e with
      LetVarExp (_, v, vl, kind, s) ->
         fprintf buf "@[<hv 3>%a%a %a@ %a@]" (**)
            pp_print_var_info v
            pp_print_method_name vl
            pp_print_var_def_kind kind
            (pp_print_string_exp complete) s
    | LetFunExp (_, v, vl, params, el, export) ->
         fprintf buf "@[<hv 3>%a%a(%a) =@ %a%a@]" (**)
            pp_print_var_info v
            pp_print_method_name vl
            pp_print_symbol_list params
            (string_override "<...>" pp_print_exp_list complete) el
            pp_print_export_info export
    | LetObjectExp (_, v, vl, s, el, export) ->
         fprintf buf "@[<v 3>%a%a. =@ extends %a@ %a%a@]" (**)
            pp_print_var_info v
            pp_print_method_name vl
            (pp_print_string_exp complete) s
            (string_override "<...>" pp_print_exp_list complete) el
            pp_print_export_info export
    | LetThisExp (_, e) ->
         fprintf buf "@[<hv 3><this> =@ %a@]" (pp_print_string_exp complete) e
    | ShellExp (_, e) ->
         fprintf buf "@[<hv 3>shell(%a)@]" (pp_print_string_exp complete) e
    | IfExp (_, cases) ->
         if complete then begin
            fprintf buf "@[<hv 0>if";
            List.iter (fun (s, el, export) ->
                  fprintf buf "@ @[<hv 3>| %a ->@ %a%a@]" (**)
                     (pp_print_string_exp complete) s
                     (pp_print_exp_list complete) el
                     pp_print_export_info export) cases;
            fprintf buf "@]"
         end else
            pp_print_string buf "<if ... then ... [else ...]>"
    | SequenceExp (_, el) ->
         fprintf buf "@[<hv 3>sequence@ %a@]" (**)
            (pp_print_exp_list complete) el
    | SectionExp (_, s, el, export) ->
         fprintf buf "@[<hv 3>section %a@ %a%a@]" (**)
            (pp_print_string_exp complete) s
            (string_override "<...>" pp_print_exp_list complete) el
            pp_print_export_info export
    | OpenExp (_, nodes) ->
         fprintf buf "@[<hv 3>open";
         List.iter (fun node -> fprintf buf "@ %a" pp_print_node node) nodes;
         fprintf buf "@]"
    | IncludeExp (_, s, commands) ->
         fprintf buf "@[<hv 3>include %a:%a@]" (**)
            (pp_print_string_exp complete) s
            (pp_print_commands complete) commands
    | ApplyExp (_, v, args) ->
         fprintf buf "@[<hv 3>%a(%a)@]" (**)
            pp_print_var_info v
            (pp_print_string_exp_list complete) args
    | SuperApplyExp (_, super, v, args) ->
         fprintf buf "@[<hv 0>%a::%a(%a)@]" (**)
            pp_print_symbol super
            pp_print_symbol v
            (pp_print_string_exp_list complete) args
    | MethodApplyExp (_, v, vl, args) ->
         fprintf buf "@[<hv 3>%a.%a(%a)@]" (**)
            pp_print_var_info v
            pp_print_method_name vl
            (pp_print_string_exp_list complete) args
    | ReturnBodyExp (_, el) ->
         fprintf buf "@[<hv 3>return-body@ %a@]"
            (string_override "<...>" pp_print_exp_list complete) el
    | StringExp (_, s) ->
         fprintf buf "string(%a)" (pp_print_string_exp complete) s
    | ReturnExp (_, s) ->
         fprintf buf "return(%a)" (pp_print_string_exp complete) s
    | ReturnSaveExp _ ->
         pp_print_string buf "return-current-file"
    | ReturnObjectExp (_, names) ->
         fprintf buf "@[<b 3>return-current-object";
         List.iter (fun v -> fprintf buf "@ %a" pp_print_symbol v) names;
         fprintf buf "@]"
    | KeyExp (_, v) ->
         fprintf buf "$|%s|" v
    | LetKeyExp (_, v, kind, s) ->
         fprintf buf "@[<hv 3>$|%s| %a@ %a@]" (**)
            v
            pp_print_var_def_kind kind
            (pp_print_string_exp complete) s
    | StaticExp (_, node, key, el) ->
         fprintf buf "@[<hv 3>static(%a.%a):@ %a@]" (**)
            pp_print_node node
            pp_print_symbol key
            (string_override "<...>" pp_print_exp_list complete) el

and pp_print_exp_list complete buf el =
   match el with
      [e] ->
         pp_print_exp complete buf e
    | e :: el ->
         pp_print_exp complete buf e;
         pp_print_space buf ();
         pp_print_exp_list complete buf el
    | [] ->
         ()

and pp_print_commands complete buf el =
   List.iter (fun e -> fprintf buf "@ %a" (pp_print_string_exp complete) e) el

(*
 * Print simple parts, abbreviating others as "<exp>"
 *)
let pp_print_exp_list_simple = pp_print_exp_list false

(*
 * The complete printers.
 *)
let pp_print_exp = pp_print_exp true
let pp_print_string_exp = pp_print_string_exp true
let pp_print_string_exp_list = pp_print_string_exp_list true

let pp_print_exp_list = pp_print_exp_list true

let pp_print_prog buf el =
   fprintf buf "@[<v 0>%a@]" pp_print_exp_list el

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
