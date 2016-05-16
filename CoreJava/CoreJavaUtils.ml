(* Representation of variable state *)
type varname = string
type classname = string

(* This is the type returned by calls to eval *)
type stackvalue = IntV of int | StringV of string
                | BoolV of bool | NullV | Location of location

and location = int

type environment = (varname * stackvalue) list

type heapvalue = Object of classname * environment

type store = heapvalue list

type state = environment * store

exception TypeError of string      (* e.g. 1 + true *)
exception RuntimeError of string   (* e.g. division by zero *)
exception NotImplemented of string (* anything you haven't done yet *)

let string_of_stackval v = match v with
     IntV i -> string_of_int i
   | StringV s -> s
   | BoolV b ->  string_of_bool b
   | NullV -> "null"
   | Location loc -> string_of_int loc

