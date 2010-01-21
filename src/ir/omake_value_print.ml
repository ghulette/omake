(*
 * Value printing.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2006 Mojave Group, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
open Lm_printf
open Lm_symbol
open Lm_location

open Omake_ir
open Omake_node
open Omake_wild
open Omake_ir_print
open Omake_print_util
open Omake_value_type
open Omake_command_type

(************************************************************************
 * Simple printing.
 *)
let pp_print_string_list buf sl =
   List.iter (fun s -> fprintf buf "@ %s" s) sl

let pp_print_node_list buf l =
   List.iter (fun s -> fprintf buf "@ %a" pp_print_node s) l

let pp_print_node_set buf set =
   NodeSet.iter (fun s -> fprintf buf "@ %a" pp_print_node s) set

let pp_print_wild_list buf wl =
   List.iter (fun w -> fprintf buf "@ %a" pp_print_wild_in w) wl

let pp_print_source buf (_, source) =
   match source with
      SourceWild wild ->
         pp_print_wild_out buf wild
    | SourceNode node ->
         pp_print_node buf node

let pp_print_source_list buf sources =
   List.iter (fun source -> fprintf buf "@ %a" pp_print_source source) sources

let pp_print_target buf target =
   match target with
      TargetNode node ->
         pp_print_node buf node
    | TargetString s ->
         pp_print_string buf s

(************************************************************************
 * Path printing.
 *)
let rec pp_print_path buf = function
   PathVar info ->
      pp_print_var_info buf info
 | PathField (path, obj, v) ->
      fprintf buf "%a.%a" pp_print_symbol v pp_print_path path

(************************************************************************
 * Value printing.
 *)
let rec pp_print_value buf v =
   match v with
      ValNone ->
         pp_print_string buf "<none>"
    | ValInt i ->
         fprintf buf "%d : Int" i
    | ValFloat x ->
         fprintf buf "%g : Float" x
    | ValData s ->
         fprintf buf "@[<v 3><data \"%s\"> : String@]" (String.escaped s)
    | ValQuote vl ->
         fprintf buf "@[<v 3><string%a>@ : String@]" pp_print_value_list vl
    | ValString s ->
         fprintf buf "\"%s\" : Sequence" (String.escaped s)
    | ValQuoteString (c, vl) ->
         fprintf buf "@[<v 3><string %c%a%c>@ : String@]" c pp_print_value_list vl c
    | ValSequence [v] ->
         pp_print_value buf v
    | ValSequence vl ->
         fprintf buf "@[<hv 3><sequence%a>@ : Sequence@]" pp_print_value_list vl
    | ValArray vl ->
         fprintf buf "@[<v 3><array%a>@ : Array@]" pp_print_value_list vl
    | ValApply (_, f, args) ->
         fprintf buf "@[<hv 3>$(apply %a%a)@]" (**)
            pp_print_var_info f
            pp_print_value_list args
    | ValSuperApply (_, super, f, args) ->
         fprintf buf "@[<hv 3>$(apply %a::%a%a)@]" (**)
            pp_print_symbol super
            pp_print_symbol f
            pp_print_value_list args
    | ValMethodApply (_, v, vl, args) ->
         fprintf buf "@[<hv 3>$(%a%a%a)@]" (**)
            pp_print_var_info v
            pp_print_method_name vl
            pp_print_value_list args
    | ValMaybeApply (_, v) ->
         fprintf buf "@[<hv 3>ifdefined(%a)@]" (**)
            pp_print_var_info v
    | ValFun (arity, _, _, _, _)
    | ValFunValue (arity, _, _, _) ->
         fprintf buf "<fun %a>" pp_print_arity arity
    | ValPrim (_, special, name) ->
         if special then
            fprintf buf "<special-function %a>" pp_print_symbol name
         else
            fprintf buf "<prim-function %a>" pp_print_symbol name
    | ValRules rules ->
         fprintf buf "<@[<hv 3>rules:";
         List.iter (fun erule -> fprintf buf "@ %a" pp_print_node erule) rules;
         fprintf buf "@]>"
    | ValDir dir ->
         fprintf buf "%a : Dir" pp_print_dir dir
    | ValNode node ->
         fprintf buf "%a : File" pp_print_node node
    | ValBody (_, el, export) ->
         fprintf buf "@[<v 0>%a%a@ : Body@]" pp_print_exp_list el pp_print_export_info export
    | ValObject env ->
         pp_print_env buf env
    | ValMap map ->
         fprintf buf "@[<hv 3>map";
         ValueTable.iter (fun v e -> fprintf buf "@ %a@ = %a" pp_print_value v pp_print_value e) map;
         fprintf buf "@]"
    | ValChannel (InChannel, _) ->
         fprintf buf "<channel> : InChannel"
    | ValChannel (OutChannel, _) ->
         fprintf buf "<channel> : OutChannel"
    | ValChannel (InOutChannel, _) ->
         fprintf buf "<channel> : InOutChannel"
    | ValClass c ->
         fprintf buf "@[<hv 3>class";
         SymbolTable.iter (fun v _ ->
               fprintf buf "@ %a" pp_print_symbol v) c;
         fprintf buf "@]"
    | ValCases cases ->
         fprintf buf "@[<hv 3>cases";
         List.iter (fun (v, e1, e2, export) ->
               fprintf buf "@[<hv 3>%a %a:@ %a%a@]" (**)
                  pp_print_symbol v
                  pp_print_value e1
                  pp_print_exp_list e2
                  pp_print_export_info export) cases;
         fprintf buf "@]"
    | ValKeyApply (_, v) ->
         fprintf buf "key $|%s|" v
    | ValVar (_, v) ->
         fprintf buf "`%a" pp_print_var_info v
    | ValOther (ValLexer _) ->
         fprintf buf "<lexer> : Lexer"
    | ValOther (ValParser _) ->
         fprintf buf "<parser> : Parser"
    | ValOther (ValLocation loc) ->
         fprintf buf "<location %a> : Location" pp_print_location loc
    | ValOther (ValExitCode code) ->
         fprintf buf "<exit-code %d> : Int" code
    | ValOther (ValEnv _) ->
         fprintf buf "<env>"
    | ValDelayed { contents = ValValue v } ->
         fprintf buf "<delayed:normal %a>" pp_print_value v
    | ValDelayed { contents = ValStaticApply (key, v) } ->
         fprintf buf "<delayed:memo %a::%a>" pp_print_value key pp_print_symbol v

and pp_print_value_list buf vl =
   List.iter (fun v -> fprintf buf "@ %a" pp_print_value v) vl

and pp_print_env buf env =
   let tags = venv_get_class env in
   let env = SymbolTable.remove env class_sym in
      fprintf buf "@[<v 3>@[<hv 3>class";
      SymbolTable.iter (fun v _ -> fprintf buf "@ %a" pp_print_symbol v) tags;
      fprintf buf "@]";
      SymbolTable.iter (fun v e -> fprintf buf "@ %a = %a" pp_print_symbol v pp_print_value e) env;
      fprintf buf "@]"

(************************************************************************
 * Simplified printing.
 *)
let rec pp_print_simple_value buf v =
   match v with
      ValNone ->
         pp_print_string buf "<none>"
    | ValInt i ->
         pp_print_int buf i
    | ValFloat x ->
         pp_print_float buf x
    | ValData s ->
         Omake_command_type.pp_print_arg buf [ArgData s]
    | ValString s ->
         Omake_command_type.pp_print_arg buf [ArgString s]
    | ValQuote vl ->
         fprintf buf "\"%a\"" pp_print_simple_value_list vl
    | ValQuoteString (c, vl) ->
         fprintf buf "%c%a%c" c pp_print_simple_value_list vl c
    | ValSequence vl ->
         pp_print_simple_value_list buf vl
    | ValArray vl ->
         pp_print_simple_arg_list buf vl
    | ValApply (_, f, args) ->
         fprintf buf "$(%a%a)" (**)
            pp_print_var_info f
            pp_print_simple_arg_list args
    | ValSuperApply (_, super, f, args) ->
         fprintf buf "$(%a::%a%a)" (**)
            pp_print_symbol super
            pp_print_symbol f
            pp_print_simple_arg_list args
    | ValMethodApply (_, v, vl, args) ->
         fprintf buf "$(%a%a%a)" (**)
            pp_print_var_info v
            pp_print_method_name vl
            pp_print_value_list args
    | ValMaybeApply (_, v) ->
         fprintf buf "$?(%a)" (**)
            pp_print_var_info v
    | ValFun _
    | ValFunValue _ ->
         pp_print_string buf "<fun>"
    | ValPrim _ ->
         pp_print_string buf "<prim>"
    | ValRules _ ->
         pp_print_string buf "<rules>"
    | ValDir dir ->
         pp_print_dir buf dir
    | ValNode node ->
         pp_print_node buf node
    | ValBody _ ->
         pp_print_string buf "<body>"
    | ValObject _ ->
         pp_print_string buf "<object>"
    | ValMap _ ->
         pp_print_string buf "<map>"
    | ValChannel _ ->
         pp_print_string buf "<channel>"
    | ValClass _ ->
         pp_print_string buf "<class>"
    | ValCases _ ->
         pp_print_string buf "<cases>"
    | ValKeyApply (_, v) ->
         fprintf buf "$|%s|" v
    | ValVar (_, v) ->
         fprintf buf "`%a" pp_print_var_info v
    | ValOther (ValLexer _) ->
         pp_print_string buf "<lexer>"
    | ValOther (ValParser _) ->
         pp_print_string buf "<parser>"
    | ValOther (ValLocation _) ->
         pp_print_string buf "<location>"
    | ValOther (ValExitCode i) ->
         pp_print_int buf i
    | ValOther (ValEnv _) ->
         pp_print_string buf "<env>"
    | ValDelayed { contents = ValValue v } ->
         pp_print_simple_value buf v
    | ValDelayed { contents = ValStaticApply _ } ->
         pp_print_string buf "<static>"

and pp_print_simple_value_list buf vl =
   List.iter (pp_print_simple_value buf) vl

and pp_print_simple_arg_list buf vl =
   match vl with
      [] ->
         ()
    | [v] ->
         pp_print_simple_value buf v
    | v :: vl ->
         pp_print_simple_value buf v;
         pp_print_char buf ' ';
         pp_print_simple_arg_list buf vl

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
