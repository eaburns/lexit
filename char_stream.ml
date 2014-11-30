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
   A buffered stream of characters.
*)

open Printf

type t = {
  buf : Buffer.t;
  (* The buffer of characters. *)
  src : char Stream.t
    (* The source of the characters. *)
}

let populate_buffer t num =
  (** [populate_buffer t num] adds [num] more characters to the buffer
      from the source.  Raises [End_of_file] if there are not enough
      characters available in the source.  *)
  let rec do_populate num =
    if num = 0
    then ()
    else
      if Stream.peek t.src = None
      then raise End_of_file
      else begin
	Buffer.add_char t.buf (Stream.next t.src);
	do_populate (num - 1)
      end
  in do_populate num


let is_empty t =
  (** [is_empty t] tests if the char stream is empty. *)
  ((Buffer.length t.buf)= 0) && (Stream.peek t.src) = None


let of_string str =
  (** [of_string str] creates a new char stream from the given
      string. *)
  { buf = Buffer.create 100;
    src = Stream.of_string str }


let of_stream str =
  (** [of_stream str] creates a new char stream from the given
      stream. *)
  { buf = Buffer.create 100;
    src = str; }


let of_channel ch =
  (** [of_channel ch] creates a new char stream from the given
      channel. *)
  { buf = Buffer.create 100;
    src = Stream.of_channel ch; }

let nth t i =
  (** [nth t i] gets the [i]th character in the stream [t]. *)
  let len = Buffer.length t.buf in
    if i >= len then populate_buffer t (len - i + 1);
    Buffer.nth t.buf i


let junk t i =
  (** [junk t i] junks the first [i] characters in the buffer. *)
  let len = Buffer.length t.buf in
    if i > len
    then invalid_arg (sprintf "Char_stream.junk: %d is larger than stream" i)
    else let str = Buffer.sub t.buf i (len - i) in
      Buffer.clear t.buf;
      Buffer.add_string t.buf str
