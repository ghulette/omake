(*
 * Table indexed by opaque handles.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2007 Mojave Group, Caltech
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
open Lm_int_set

(*
 * Handles.  These need to be heap allocated so that we can register
 * finalization functions.
 *)
module type HandleTableSig =
sig
   type 'a t
   type handle

   val create : unit -> 'a t
   val add : 'a t -> 'a -> handle
   val find : 'a t -> handle -> 'a
end;;

module HandleTable : HandleTableSig =
struct
   type 'a t =
      { mutable hand_table : 'a IntTable.t;
        mutable hand_index : int
      }

   (* This must be heap-allocated *)
   type handle = { handle_index : int }

   let create () =
      { hand_table = IntTable.empty;
        hand_index = 0
      }

   let free table hand =
      table.hand_table <- IntTable.remove table.hand_table hand.handle_index

   let add table x =
      let i = table.hand_index in
      let hand = { handle_index = i } in
         Gc.finalise (free table) hand;
         table.hand_index <- succ i;
         table.hand_table <- IntTable.add table.hand_table i x;
         hand

    let find table hand =
       IntTable.find table.hand_table hand.handle_index
end;;

(*
 * -*-
 * Local Variables:
 * Fill-column: 100
 * End:
 * -*-
 * vim:ts=3:et:tw=100
 *)
