(*
 * Copyright (C) 2010 Ethan Burns
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)
(** A set of integers. *)

module IS = Set.Make(struct
		       type t = int
		       let compare = compare
		     end)

include IS

let of_list lst =
  (** [intset_of_list l] builds an IntSet from the list of integers
      [l] . *)
  List.fold_left (fun s v -> add v s) empty lst

let map f set =
  (** [intset_map f s] maps the function [f] over each element of [s]
      creating a new set with the result of each application. *)
  fold (fun elm s -> add (f elm) s) set empty

