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
(**
   Finite automata.
*)

open Printf

(* ******************** Symbol ******************** *)

module Symbol = struct
  (** Symbols matched by the FA.  Symbols are represented by integers
      (ASCII) and the epsilon value which is one greater than the greatest
      matchable character representation. *)

  type t = int
      (** Symbols are represented as integers. *)

  let compare = compare

  let epsilon = 256
    (** This is the epsilon transition (a transition on no symbols), it
	is an integer that is out of range of the ASCII alphabet.  I
	guess this is not very unicode friendly...  I am not sure that
	OCaml's 'char' is unicode friendly anyway. *)


  let nsymbols = epsilon + 1
    (** The number of symbols. *)


  let all_symbols =
    (** A list of all of the symbols available to the FA (not counting
	epsilon) . This is useful for the Dot operator in regular
	expressions. *)
    let rec ints_to accum n =
      if n < 0
      then accum
      else ints_to (n :: accum) (n - 1)
    in List.filter (( <> ) epsilon) (ints_to [] (nsymbols - 1))


  let of_char = int_of_char
    (** Get the symbol for a given character. *)


  let to_string s =
    if s = epsilon
    then "<e>"
    else sprintf "%c" (char_of_int s)
      (** Get the string representation of the given symbol. *)

end

(* ******************** State ******************** *)

module State = struct
  (** A state in the FA matches symbols to sets of destination states.*)

  module SymbolMap = Map.Make(Symbol)
    (** A map from symbols to destination state.s *)

  type t = Intset.t SymbolMap.t
      (** A state is represented by a map from symbols to destination
	  sets. *)

  let empty = SymbolMap.empty
    (** The empty state. *)

  let iter f state =
    (** Iterate over all sym intset pairs in the state. *)
    SymbolMap.iter f state

  let offset_dests offs state =
    (** Add an [offs] to all of the destinations for each edge in [state]. *)
    SymbolMap.map (fun arcs -> Intset.map (( + ) offs) arcs) state

  let dests state sym =
    (** Get the destinations for [sym] in [state]. *)
    try SymbolMap.find sym state with Not_found -> Intset.empty

  let add_edge state sym dest =
    (** Add an edge from the [from] state to the [dest] state on
	symbol [sym]. *)
    SymbolMap.add sym (Intset.add dest (dests state sym)) state

  let combine astate bstate =
    (** Combine the edges of two states. *)
    SymbolMap.mapi
      (fun sym adests -> Intset.union adests (dests bstate sym))
      astate
end

(* ******************** Finite Automata ******************** *)

type t = {
  states : State.t array;
  (* Array of states where each state is a transition array indexed on
     characters.  Zero is always the start state. *)

  accepting : Intset.t;
  (* Set of accepting states. *)
}


let nstates t = Array.length t.states
  (** Get the number of states. *)


let is_accepting t s =
  (** Test if state [s] is an accepting state in [t] *)
  if s < nstates t
  then Intset.mem s t.accepting
  else invalid_arg (sprintf "Invalid state: %d" s)


let accepting_state t =
  (** If the FA has a single accepting state, then get it. *)
  if Intset.cardinal t.accepting <> 1
  then invalid_arg (sprintf "FA has more than one accepting state")
  else List.hd (Intset.elements t.accepting)


let offset_dests offs t =
  (** Add a [offs] to all edges in all states in [t]. *)
  { t with states = Array.map (State.offset_dests offs) t.states }


let add_edge t s sym d =
  (** Add an edge to the [t] for state [s] on [sym] to [d]. *)
  if s < nstates t
  then t.states.(s) <- State.add_edge t.states.(s) sym d
  else invalid_arg (sprintf "Invalid state: %d" s)


let empty =
  (** [empty] the empty FA.  A start state with no transitions and no
      accepting states.  This is useful for a placeholder. *)
  {
    states = [| State.empty |];
    accepting = Intset.empty;
  }


let make syms =
  (** Make a simple FA with one start state and one accepting state
      where each symbol in [syms] has a transition from the start to the
      accepting state. *)
  {
    states =
      [|
	List.fold_left
	  (fun state sym -> State.add_edge state sym 1)
	  State.empty
	  syms;
	State.empty
      |];
    accepting = Intset.singleton 1;
  }

let concat a b =
  (** Concatinate the two state machines [a] and [b]. *)
  let b_offs = (nstates a) - 1 in
  let a_accepting = accepting_state a
  and b_accepting = accepting_state b in
  let new_b = offset_dests b_offs b in
  let new_states =
    Array.append a.states (Array.sub new_b.states 1 ((nstates b) - 1)) in
    new_states.(a_accepting) <-
      State.combine new_b.states.(0) new_states.(a_accepting);
    {
      states = new_states;
      accepting = Intset.singleton (b_accepting + b_offs);
    }

let disjunct a b =
  (** Make a state machine for the disjunction [a] or [b]. *)
  let a_offs = 1 in
  let b_offs = (nstates a) + a_offs in
  let new_acc_num = b_offs + (nstates b) in
  let new_start_state =
    List.fold_left
      (fun state dest -> State.add_edge state Symbol.epsilon dest)
      State.empty
      [ a_offs; b_offs ]
  and new_a = offset_dests a_offs a
  and new_b = offset_dests b_offs b in
  let a_acc = accepting_state a
  and b_acc = accepting_state b in
    add_edge new_a a_acc Symbol.epsilon new_acc_num;
    add_edge new_b b_acc Symbol.epsilon new_acc_num;
    {
      states =
	Array.concat
	  [ [| new_start_state |];
	    new_a.states;
	    new_b.states;
	    [| State.empty |]; ];
      accepting = Intset.singleton new_acc_num;
    }

let star a =
  (** Make the state machine that matches zero or more of whatever [a]
      matches *)
  let offs = 1 in
  let new_a = offset_dests offs a in
  let a_acc = accepting_state a in
  let new_acc_num = (nstates a) + offs in
  let new_start_state =
    List.fold_left
      (fun state dest -> State.add_edge state Symbol.epsilon dest)
      State.empty
      [ new_acc_num; offs ] in
    add_edge new_a a_acc Symbol.epsilon offs;
    add_edge new_a a_acc Symbol.epsilon new_acc_num;
    {
      states =
	Array.concat [
	  [| new_start_state |];
	  new_a.states;
	  [| State.empty |]
	];
      accepting = Intset.singleton new_acc_num;
    }

let question a =
  (** A state machine that matches zero or one of what ever [a]
      matches. *)
  let offs = 1 in
  let new_a = offset_dests offs a in
  let a_acc = accepting_state a in
  let new_acc_num = (nstates a) + offs in
  let new_start_state =
    List.fold_left
      (fun state dest -> State.add_edge state Symbol.epsilon dest)
      State.empty
      [new_acc_num; offs] in
    add_edge new_a a_acc Symbol.epsilon new_acc_num;
    {
      states =
	Array.concat [
	  [| new_start_state |];
	  new_a.states;
	  [| State.empty |]
	];
      accepting = Intset.singleton new_acc_num;
    }


let mux fas =
  (** [mux fas] multiplexes a list of FAs into one FA with multiple
      accepting states.  The result is the aggregate FA and a list
      where each element is the accepting state set added by the FA
      from the respective position in the input list. *)
  let rec do_mux ?(accum = []) fa fas =
    match fas with
      | [] -> fa, List.rev accum
      | hd :: tl ->
	  let offs = nstates fa in
	  let new_hd = offset_dests offs hd in
	  let new_states = Array.append fa.states new_hd.states in
	  let new_acc = Intset.map ((+) offs) hd.accepting in
	  let new_fa = { states = new_states;
			 accepting = Intset.union new_acc fa.accepting }
	  in add_edge new_fa 0 Symbol.epsilon offs;
	    do_mux ~accum:(new_acc :: accum) new_fa tl
  in do_mux empty fas


let to_string t =
  (** [to_string fa] gets the string representation (human readable)
      for the finite automata [fa]. *)
  let b = Buffer.create 100 in
    Array.iteri
      (fun snum syms ->
	 let acc_char =
	   if Intset.mem snum t.accepting
	   then '*'
	   else ' '
	 in Buffer.add_string b (sprintf "%c%2d:" acc_char snum);
	   State.iter
	     (fun sym dests ->
		if not (Intset.is_empty dests)
		then
		  let tran_string =
		    Intset.fold
		      (fun e str -> (if str = ""
				     then sprintf "%2d" e
				     else sprintf "%s; %2d" str e))
		      dests
		      "" in
		    Buffer.add_string b (sprintf " (%s, [%s])"
					   (Symbol.to_string sym)
					   tran_string))
	     syms;
	   Buffer.add_string b "\n")
      t.states;
    Buffer.contents b


let e_closure t snum =
  (** [e_closure t snum] computes the epsilon closure of the state
      with the number [snum] in [t]. *)
  let rec do_e_closure accum states =
    if Intset.is_empty states
    then accum
    else
      let dests =
	Intset.fold
	  (fun snum set ->
	     let state = t.states.(snum) in
	       Intset.union set (State.dests state Symbol.epsilon))
	  states
	  Intset.empty
      in do_e_closure (Intset.union accum dests) dests
  in do_e_closure Intset.empty (Intset.singleton snum)


let e_closures t snums =
  (** [e_closures t snums] computes the e_closure over a set of state
      numbers. *)
  Intset.fold
    (fun snum set -> Intset.union set (e_closure t snum))
    snums
    snums


let all_dests t sym snums =
  (** [dests t sym snums] gets the set of destination states for each
      state in [snums] on in symbol [sym] unioned with the e_closures
      of all destinations. *)
  let dests =
    Intset.fold
      (fun snum set ->
	 let state = t.states.(snum) in
	   Intset.union set (State.dests state sym))
      snums
      Intset.empty
  in Intset.union dests (e_closures t dests)


let simulate t s =
  (** [simulate t s] simulates the finite automata [t] on the
      character stream [s].  The result is a tuple containing the longest
      matched string of characters and the accepting state number that
      terminates the string. *)
  let rec do_simulate accum states i =
    if Intset.is_empty states
    then "", Intset.empty
    else
      let c = try Some (Char_stream.nth s i) with End_of_file -> None in
	match c with
	  | None -> accum, (Intset.inter states t.accepting)
	  | Some c ->
	      let sym = Symbol.of_char c in
	      let dests = all_dests t sym states in
	      let smatch, acc =
		do_simulate (sprintf "%s%c" accum c) dests (i + 1)
	      in
		if Intset.is_empty acc
		then accum, (Intset.inter states t.accepting)
		else smatch, acc
  in
    if Char_stream.is_empty s
    then "", Intset.empty
    else do_simulate "" (Intset.union (Intset.singleton 0) (e_closure t 0)) 0
