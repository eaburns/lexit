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
(** Handles the lexer description, tokenization, etc.

    @author eaburns
    @since 2009-06-26
*)

open Printf

type t = {
  rules : lrule list;
  accepting_map : (int, lrule) Hashtbl.t;
  fa : Fa.t;
}

and lrule = {
  name : string;
  prio : int;
  regexp : string;
  automaton : Fa.t;
}

and token =
  | Token of string * string
  | End
  | Error


exception Lexical_error
  (** Raised if an invalid character is seen. *)

(************************************************************)

let lexer rules =
  (** [lexer regexps] creates a lexer from the given list of
      (rule-name, regular-expression) tuples. *)
  let _, rules =
    List.fold_left (fun (i, accum) reg ->
		      let r = { name = fst reg;
				prio = i;
				regexp = snd reg;
				automaton = Regexp.compile (snd reg);
			      }
		      in (i + 1, r :: accum))
      (0, []) rules in
  let fa, accs = Fa.mux (List.map (fun r -> r.automaton) rules) in
  let tbl = Hashtbl.create 100 in
    List.iter2 (fun r accs ->
		  Intset.iter
		    (fun a -> Hashtbl.add tbl a r)
		    accs)
      rules accs;
    {
      rules = rules;
      accepting_map = tbl;
      fa = fa
    }


let next_token lexer stream =
  (** [next_token lexer stream] get the next token from the stream. *)
  let mstr, accepting = Fa.simulate lexer.fa stream in
    if Intset.is_empty accepting
    then
      if Char_stream.is_empty stream then End else Error
    else
      let rules =
	List.map
	  (fun a -> Hashtbl.find lexer.accepting_map a)
	  (Intset.elements accepting) in
      let r =
	List.fold_left
	  (fun m r -> if r.prio < m.prio then r else m)
	  (List.hd rules)
	  (List.tl rules)
      in Char_stream.junk stream (String.length mstr);
	Token (r.name, mstr)


let tokenize lexer stream =
  (** [tokenize lexer stream] returns a list of the tokens from the
      input stream as (token-name, matching-text) tuples, *not* as
      token types. *)
  let rec do_tokenize () =
    match next_token lexer stream with
      | End -> []
      | Error -> raise Lexical_error
      | Token (n, s) -> (n, s) :: (do_tokenize ())
  in do_tokenize ()

(************************************************************)
(* Parsing lexer descriptions                               *)
(************************************************************)

let desc_rules =
  (** The lexical rules for lexer description files. *)
  [
    ("Space", "( |\t)+");
    ("Newline", "\n");
    ("Comment", "#[^\n]*");
    ("Ident", "[a-zA-Z][a-zA-Z0-9_]*");
    ("Arrow", "->");
    ("Regexp", "'[^\n]*'");
    ("Error", ".");
  ]


let rec parse ?(accum = []) = function
  | [] -> List.rev accum
  | (("Ident", name), _) :: (("Arrow", _), _) :: (("Regexp", exp), _) :: tl ->
      (* strip off ' characters. *)
      let exp = String.sub exp 1 ((String.length exp) - 2) in
	parse ~accum:((name, exp) :: accum) tl
  | (("Error", c), lineno) :: tl ->
      failwith (sprintf "Unexpected character on line %d: %s" lineno c)
  | ((n, r), lineno) :: _ ->
      invalid_arg (sprintf "Unknown token on line %d: (%s, %s)" lineno n r)


let from_char_stream strm =
  (** [of_char_stream strm] creates a lexer from the description in
      the given character stream. *)
  let tokens =
    List.rev
      (fst (List.fold_left
	      (fun (accum, l) t ->
		 if (fst t) <> "Space" && (fst t) <> "Comment"
		 then
		   if (fst t) = "Newline"
		   then accum, l + 1
		   else ((t, l) :: accum), l
		 else accum, l)
	      ([], 1)
	      (tokenize (lexer desc_rules) strm)))
  in lexer (parse tokens)


let from_channel ch =
  (** [from_channel ch] creates a lexer from the description in the
      given channel. *)
  from_char_stream (Char_stream.of_channel ch)
