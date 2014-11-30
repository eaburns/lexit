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
   Parsing of regular expressions.

   The top-down parser grammer looks something like this:

   exp -> starexps | exp
   exp -> starexps
   starexps -> starexp starexps
   starexps -> starexp
   starexp -> baseexp *
   starexp -> baseexp +
   starexp -> baseexp ?
   starexp -> baseexp
   baseexp -> ( exp )
   baseexp -> { name }
   baseexp -> [ symbols ]
   baseexp -> .
   baseexp -> <symbol>
*)

open Printf

let debug = false
  (** Optionally enable debugging. *)

module Lex = struct
  (** Lexing for regular expressions. *)

  type t =
    | Symbol of char
    | O_paren
    | C_paren
    | O_cbrace
    | C_cbrace
    | O_sbracket
    | C_sbracket
    | Star
    | Plus
    | Dot
    | Question
    | Bar


  let special_chars = [ '('; ')'; '{'; '}'; '['; ']';
			'*'; '+'; '.'; '?'; '|' ]

  let is_special ch = List.mem ch special_chars
    (** Test if [ch] is a special character. *)

  let to_string = function
    | Symbol ch when is_special ch -> (sprintf "\\%c" ch)
    | Symbol ch -> (sprintf "%c" ch)
    | O_paren -> "("
    | C_paren -> ")"
    | O_cbrace -> "{"
    | C_cbrace -> "}"
    | O_sbracket -> "["
    | C_sbracket -> "]"
    | Star -> "*"
    | Plus -> "+"
    | Dot -> "."
    | Question -> "?"
    | Bar -> "|"

  let tokenize string =
    let len = String.length string in

    let rec escaped i str =
      if i < len then
	match String.get str i with
	  | 'n' -> Symbol '\n'
	  | 't' -> Symbol '\t'
	      (* TODO: add other escaped characters... *)
	  | ch when is_special ch -> Symbol ch
	  | ch -> invalid_arg (sprintf "Unknown escape character %c" ch)
      else invalid_arg (sprintf "Unexpected end of input after escape")
    in

    let rec do_tokenize i str =
      if i < len then
	match String.get str i with
	  | '\\' -> escaped (i + 1) str :: do_tokenize (i + 2) str
	  | '(' -> O_paren :: do_tokenize (i + 1) str
	  | ')' -> C_paren :: do_tokenize (i + 1) str
	  | '{' -> O_cbrace :: do_tokenize (i + 1) str
	  | '}' -> C_cbrace :: do_tokenize (i + 1) str
	  | '[' -> O_sbracket :: do_tokenize (i + 1) str
	  | ']' -> C_sbracket :: do_tokenize (i + 1) str
	  | '*' -> Star :: do_tokenize (i + 1) str
	  | '.' -> Dot :: do_tokenize (i + 1) str
	  | '+' -> Plus :: do_tokenize (i + 1) str
	  | '?' -> Question :: do_tokenize (i + 1) str
	  | '|' -> Bar :: do_tokenize (i + 1) str
	  | ch -> assert (not (is_special ch));
	      Symbol ch :: do_tokenize (i + 1) str
      else []
    in do_tokenize 0 string
end

type t =
  | Or of t * t
  | Cat of t *t
  | Star of t
  | Question of t
  | Symbols of Fa.Symbol.t list
  | Nil

exception Parse_error of string

let unexpected t exp =
  raise (Parse_error
	   (sprintf "Unexpected token %s expected %s"
	      (Lex.to_string t) exp))

let rec expression tokens =
  (** Parse an expression.  The result is the parsed expression and
      the remaining tokens. *)
  if debug
  then eprintf "expression: hd=%s\n%!" (Lex.to_string (List.hd tokens));

  let left, rest = starexps tokens in
    match rest with
      | [] -> left, []
      | Lex.Bar :: rest ->
	  let exp, rest = expression rest in
	    Or (left, exp), rest
      | _ -> left, rest

and starexps tokens =
  (** Parse a starexps.  The result is the parsed starexps and the
      remaining tokens. *)
  if debug
  then eprintf "starexps: hd=%s\n%!" (Lex.to_string (List.hd tokens));

  let left, rest = starexp tokens in
    if left = Nil
    then left, rest
    else match rest with
      | [] -> left, []
      | _ ->
	  let right, rest = starexps rest in
	    if right = Nil
	    then left, rest
	    else Cat (left, right), rest

and starexp tokens =
  (** Parse a starexp.  The result is the parsed starexp and the
      remaining tokens. *)
  if debug
  then eprintf "starexp: hd=%s\n%!" (Lex.to_string (List.hd tokens));

  let left, rest = baseexp tokens in
    if left = Nil then left, rest
    else match rest with
      | Lex.Star :: rest -> Star left, rest
      | Lex.Plus :: rest -> Cat (left, Star left), rest
      | Lex.Question :: rest -> Question left, rest
      | _ ->
	  if debug && left = Nil
	  then eprintf "starexp returning Nil\n%!";
	  left, rest

and baseexp tokens =
  (** Parse a baseexp.  The result is the parsed baseexp and the
      remaining tokens. *)
  if debug
  then eprintf "baseexp: hd=%s\n%!" (Lex.to_string (List.hd tokens));

  match tokens with
    | Lex.O_paren :: rest ->
	let exp, rest = expression rest in
	  begin match rest with
	    | Lex.C_paren :: rest -> exp, rest
	    | t :: _ -> unexpected t ")"
	    | [] -> raise (Parse_error "Unexpected end of input")
	  end
    | Lex.O_cbrace :: rest ->
	failwith "Named sub-expressions are unimplemented"
	  (* This will just be a node that holds a name which the
	     regexp compiler should be able to look up.  The name will be
	     another expression that was previously defined in the lexer
	     description. *)
    | Lex.O_sbracket :: rest ->
	let syms, rest = symbols rest in Symbols syms, rest
    | Lex.Dot :: rest -> Symbols Fa.Symbol.all_symbols, rest
    | (Lex.Symbol s) :: rest -> Symbols [Fa.Symbol.of_char s], rest
    | t :: rest ->
	if debug then eprintf "baseexp returning Nil\n%!";
	Nil, tokens
    | [] -> Nil, tokens

and symbols tokens =
  (** [symbols str] builds a big disjunction of each character in the
      square brackets. *)
  let rec find_syms ?(accum = []) toks =
    match toks with
      | [] -> raise (Parse_error "Unexpected end of input in []")
      | Lex.C_sbracket :: rest ->
	  List.fold_left
	    (fun set c -> Intset.add (int_of_char c) set)
	    Intset.empty
	    accum,
	  rest
      | Lex.O_paren :: rest -> find_syms ~accum:('(' :: accum) rest
      | Lex.C_paren :: rest -> find_syms ~accum:(')' :: accum) rest
      | Lex.O_cbrace :: rest -> find_syms ~accum:('{' :: accum) rest
      | Lex.C_cbrace :: rest -> find_syms ~accum:('}' :: accum) rest
      | Lex.O_sbracket :: rest -> find_syms ~accum:('[' :: accum) rest
      | Lex.Star :: rest -> find_syms ~accum:('*' :: accum) rest
      | Lex.Plus :: rest -> find_syms ~accum:('+' :: accum) rest
      | Lex.Dot :: rest -> find_syms ~accum:('.' :: accum) rest
      | Lex.Question :: rest -> find_syms ~accum:('?' :: accum) rest
      | Lex.Bar :: rest -> find_syms ~accum:('|' :: accum) rest
      | Lex.Symbol a :: Lex.Symbol '-' :: Lex.Symbol b :: rest ->
	  let lst = ref [] in
	    for i = int_of_char a to int_of_char b do
	      lst := (char_of_int i) :: !lst;
	    done;
	    find_syms ~accum:(!lst @ accum) rest
      | Lex.Symbol s :: rest -> find_syms ~accum:(s :: accum) rest
  in
  let neg, toks = match tokens with
    | Lex.Symbol '^' :: rest -> true, rest
    | toks -> false, toks in
  let symset, rest = find_syms toks in
    if Intset.is_empty symset
    then raise (Parse_error "Expected characters between []")
    else
      let chars =
	if not neg
	then List.map char_of_int (Intset.elements symset)
	else
	  let lst = ref [] in
	    for i = 0 to 255 do
	      if not (Intset.mem i symset) then
		lst := (char_of_int i) :: !lst
	    done;
	    !lst
      in (List.map Fa.Symbol.of_char chars), rest


let parse string =
  (** [parse s] parses [s] into an AST.  [Parse_error] is rasied if
      there is an error with the parsing.  [Invalid_arugment] is
      raised if there is an error with the lexical analysis. *)
  let exp, rest = expression (Lex.tokenize string) in
    match rest with
      | [] -> exp
      | t :: _ -> unexpected t "end of input"


let compile string =
  (** [compile s] compiles the regular expression [s] into a finite
      automata.  [Parse_error] is raised if there is an error parsing
      the expression.  [Invalid_arugment] is raised if there is an
      error with the lexical analysis. *)
  let rec do_compile = function
    | Or (left, right) -> Fa.disjunct (do_compile left) (do_compile right)
    | Cat (left, right) -> Fa.concat (do_compile left) (do_compile right)
    | Star left -> Fa.star (do_compile left)
    | Question left -> Fa.question (do_compile left)
    | Symbols syms -> Fa.make syms
    | Nil -> failwith "Unexpected Nil found in AST."
  in do_compile (parse string)
