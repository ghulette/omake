(*
 * Operations:
 *    1. Check that all return/export operations are in legal
 *       places.
 *    2. Add final operations to sequences that don't already
 *       have them.
 *    3. Add return handlers to functions that have nontrivial
 *       return statements.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2005 Mojave Group, Caltech
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
open Lm_printf
open Lm_location

open Omake_ir
open Omake_env
open Omake_pos
open Omake_options
open Omake_ir_util
open Omake_value_type

module Pos = MakePos (struct let name = "Omake_ir_semant" end)
open Pos

(*
 * Synthesized attributes.
 *    renv_has_return : is there a non-tail return?
 *    renv_is_final : code after this point is never executed
 *)
type renv =
   { renv_has_return : bool;
     renv_is_final   : bool;
     renv_is_value   : bool
   }

(*
 * Inherited attributes.
 *    env_in_function : currently within a function body
 *    env_in_cond     : currently within a conditional
 *    env_is_tail     : the current expression is in final position
 *)
type env =
   { env_warnings      : loc option ref;
     env_in_function   : bool;
     env_in_cond       : bool;
     env_section_tail  : bool;
     env_function_tail : bool
   }

(*
 * Return environments.
 *)
let renv_empty =
   { renv_has_return = false;
     renv_is_final   = false;
     renv_is_value   = false
   }

let renv_value =
   { renv_has_return   = false;
     renv_is_final     = false;
     renv_is_value     = true
   }

let renv_final =
   { renv_has_return   = false;
     renv_is_final     = true;
     renv_is_value     = true
   }

let renv_return =
   { renv_has_return   = true;
     renv_is_final     = true;
     renv_is_value     = true
   }

(*
 * Normal environment, not in a function.
 *)
let env_empty () =
   { env_warnings      = ref None;
     env_in_function   = false;
     env_in_cond       = false;
     env_section_tail  = false;
     env_function_tail = false
   }

let env_object env =
   { env_warnings      = env.env_warnings;
     env_in_function   = false;
     env_in_cond       = false;
     env_section_tail  = false;
     env_function_tail = false
   }

let env_object_tail env =
   { env_warnings      = env.env_warnings;
     env_in_function   = false;
     env_in_cond       = false;
     env_section_tail  = true;
     env_function_tail = true
   }

(*
 * Fresh environment for a function body.
 *)
let env_fun env =
   { env_warnings      = env.env_warnings;
     env_in_function   = true;
     env_in_cond       = false;
     env_section_tail  = true;
     env_function_tail = true
   }

let update_return renv has_return =
   { renv with renv_has_return = renv.renv_has_return || has_return }

(*
 * Error checkers.
 *)
let check_return_placement env loc =
   if not env.env_in_function then
      let pos = string_pos "check_in_function" (loc_exp_pos loc) in
      let print_error buf =
         fprintf buf "@[<v 0>Misplaced return statement.";
         fprintf buf "@ The return is not within a function.@]"
      in
         raise (OmakeException (pos, LazyError print_error))
   else if not (env.env_function_tail || env.env_section_tail && env.env_in_cond) then begin
      eprintf "@[<v 3>*** omake warning: %a@ statements after this return are not reached@]@." pp_print_location loc;
      env.env_warnings := Some loc
   end

let check_section_tail env loc =
   if not env.env_section_tail then
      let pos = string_pos "check_section_tail" (loc_exp_pos loc) in
         raise (OmakeException (pos, StringError "This should be the last expression in the section."))

let check_object_tail env loc =
   if env.env_in_function || not env.env_section_tail then
      let pos = string_pos "check_object_tail" (loc_exp_pos loc) in
         raise (OmakeException (pos, StringError "This should be the last expression in the object."))

(*
 * Convert a string expression.
 *)
let rec build_string env s =
   let env = { env with env_function_tail = false } in
   match s with
      NoneString _
    | ConstString _
    | ThisString _
    | KeyApplyString _
    | VarString _ ->
         false, s
    | ApplyString (loc, strategy, v, args) ->
         let has_return, args = build_string_list env args in
            has_return, ApplyString (loc, strategy, v, args)
    | SuperApplyString (loc, strategy, v1, v2, args) ->
         let has_return, args = build_string_list env args in
            has_return, SuperApplyString (loc, strategy, v1, v2, args)
    | MethodApplyString (loc, strategy, v, vl, args) ->
         let has_return, args = build_string_list env args in
            has_return, MethodApplyString (loc, strategy, v, vl, args)
    | SequenceString (loc, sl) ->
         let has_return, sl = build_string_list env sl in
            has_return, SequenceString (loc, sl)
    | ArrayString (loc, sl) ->
         let has_return, sl = build_string_list env sl in
            has_return, ArrayString (loc, sl)
    | ArrayOfString (loc, s) ->
         let has_return, s = build_string env s in
            has_return, ArrayOfString (loc, s)
    | QuoteString (loc, sl) ->
         let has_return, sl = build_string_list env sl in
            has_return, QuoteString (loc, sl)
    | QuoteStringString (loc, c, sl) ->
         let has_return, sl = build_string_list env sl in
            has_return, QuoteStringString (loc, c, sl)
    | ObjectString (loc, el, export) ->
         let el = build_object_exp env el in
            (* XXX: we should handle the case when an object contains a return *)
            false, ObjectString (loc, el, export)
    | BodyString (loc, el, export) ->
         let renv, el = build_sequence_exp env el in
            renv.renv_has_return, BodyString (loc, el, export)
    | ExpString (loc, el, export) ->
         let renv, el = build_sequence_exp env el in
            renv.renv_has_return, ExpString (loc, el, export)
    | CasesString (loc, cases) ->
         let env = { env with env_in_cond = true } in
         let has_return, cases =
            List.fold_left (fun (has_return, cases) (v, s, el, export) ->
                  let has_return2, s = build_string env s in
                  let renv, e = build_sequence_exp env el in
                  let has_return = has_return || has_return2 || renv.renv_has_return in
                     has_return, (v, s, e, export) :: cases) (false, []) cases
         in
            has_return, CasesString (loc, List.rev cases)

and build_string_list env sl =
   let has_return, sl =
      List.fold_left (fun (has_return, sl) s ->
            let has_return2, s = build_string env s in
               has_return || has_return2, s :: sl) (false, []) sl
   in
      has_return, List.rev sl

(*
 * Convert the current expression.
 *)
and build_exp env e =
   match e with
      LetFunExp (loc, v, vl, vars, el, export) ->
         let renv, el = build_sequence_exp (env_fun env) el in
         let el =
            if renv.renv_has_return then
               [ReturnBodyExp (loc, el)]
            else
               el
         in
         let e = LetFunExp (loc, v, vl, vars, el, export) in
            renv_empty, e
    | LetObjectExp (loc, v, vl, s, el, export) ->
         let el = build_object_exp env el in
         let has_return, s = build_string env s in
         let e = LetObjectExp (loc, v, vl, s, el, export) in
            update_return renv_empty has_return, e
    | StaticExp (loc, node, v, el) ->
         let el = build_object_exp env el in
         let e = StaticExp (loc, node, v, el) in
            renv_empty, e
    | IfExp (loc, cases) ->
         let renv, cases = build_cases_exp env cases in
         let e = IfExp (loc, cases) in
            renv, e
    | SequenceExp (loc, el) ->
         let renv, el = build_sequence_exp env el in
         let e = SequenceExp (loc, el) in
            renv, e
    | SectionExp (loc, s, el, export) ->
         let has_return, s = build_string env s in
         let renv, el = build_sequence_exp env el in
         let e = SectionExp (loc, s, el, export) in
            update_return renv has_return, e
    | ReturnBodyExp (loc, el) ->
         let renv, el = build_sequence_exp env el in
         let el = ReturnBodyExp (loc, el) in
            renv, el
    | LetVarExp (loc, v, vl, kind, s) ->
         let has_return, s = build_string env s in
         let e = LetVarExp (loc, v, vl, kind, s) in
            update_return renv_empty has_return, e
    | IncludeExp (loc, s, sl) ->
         let has_return1, s = build_string env s in
         let has_return2, sl = build_string_list env sl in
         let e = IncludeExp (loc, s, sl) in
            update_return renv_empty (has_return1 || has_return2), e
    | ApplyExp (loc, v, args) ->
         let has_return, args = build_string_list env args in
         let e = ApplyExp (loc, v, args) in
            update_return renv_empty has_return, e
    | SuperApplyExp (loc, v1, v2, args) ->
         let has_return, args = build_string_list env args in
         let e = SuperApplyExp (loc, v1, v2, args) in
            update_return renv_empty has_return, e
    | MethodApplyExp (loc, v, vl, args) ->
         let has_return, args = build_string_list env args in
         let e = MethodApplyExp (loc, v, vl, args) in
            update_return renv_empty has_return, e
    | LetKeyExp (loc, v, kind, s) ->
         let has_return, s = build_string env s in
         let e = LetKeyExp (loc, v, kind, s) in
            update_return renv_empty has_return, e
    | LetThisExp (loc, s) ->
         let has_return, s = build_string env s in
         let e = LetThisExp (loc, s) in
            update_return renv_empty has_return, e
    | ShellExp (loc, s) ->
         let has_return, s = build_string env s in
         let e = ShellExp (loc, s) in
            update_return renv_value has_return, e
    | KeyExp _
    | OpenExp _ ->
         renv_empty, e
    | StringExp (loc, s) ->
         let has_return, s = build_string env s in
         let e = StringExp (loc, s) in
            update_return renv_value has_return, e
    | ReturnExp (loc, s) ->
         check_return_placement env loc;
         let has_return, s = build_string env s in
            if env.env_function_tail then
               update_return renv_final has_return, StringExp (loc, s)
            else
               renv_return, ReturnExp (loc, s)
    | ReturnObjectExp (loc, _)
    | ReturnSaveExp loc ->
         check_object_tail env loc;
         renv_final, e

(*
 * An object expression is an expression sequence,
 * but it is not in a function.
 *)
and build_object_exp_aux env el =
   match el with
      [e] ->
         let _, e = build_exp (env_object_tail env) e in
            [e]
    | e :: el ->
         let _, e = build_exp env e in
         let el = build_object_exp_aux env el in
            e :: el
    | [] ->
         []

and build_object_exp env el =
   build_object_exp_aux (env_object env) el

(*
 * A new sequence expression.
 * It should be terminated with a final statement.
 *)
and build_sequence_exp env el =
   let env_non_tail =
      { env with env_section_tail = false;
                 env_function_tail = false
      }
   in
   let rec build_sequence_core has_return rel el =
      match el with
         [e] ->
            let env_tail = { env with env_section_tail = true } in
            let renv, e = build_exp env_tail e in
            let rel = e :: rel in
               update_return renv has_return, rel
       | e :: el ->
            let renv, e = build_exp env_non_tail e in
            let has_return = has_return || renv.renv_has_return in
            let rel = e :: rel in
               build_sequence_core has_return rel el
       | [] ->
            renv_empty, []
   in
   let renv, rel = build_sequence_core false [] el in
      renv, List.rev rel

(*
 * Cases are slightly different from sequences because
 * returns are always allowed.  Note that the completeness is
 * not checked, so even if all cases end in a return,
 * evaluation may continue from here.
 *)
and build_cases_exp env cases =
   let env =
      { env with env_in_cond = true;
                 env_section_tail = true
      }
   in
   let has_return, cases =
      List.fold_left (fun (has_return, cases) (s, el, export) ->
            let renv, el = build_sequence_exp env el in
            let has_return = has_return || renv.renv_has_return in
               has_return, (s, el, export) :: cases) (false, []) cases
   in
   let cases = List.rev cases in
   let renv =
      { renv_is_final   = false;
        renv_is_value   = true;
        renv_has_return = has_return
      }
   in
      renv, cases

(************************************************************************
 * Main function
 *)
let build_prog venv e =
   let env = env_empty () in
   let _, e = build_exp env e in
   let count = !(env.env_warnings) in
   let () =
      match count with
         Some loc when opt_warn_error (venv_options venv) ->
            raise (OmakeException (loc_exp_pos loc, StringError "warnings treated as errors"))
       | _ ->
            ()
   in
      e

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
