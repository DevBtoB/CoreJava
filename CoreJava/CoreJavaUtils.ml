type varname = string
type classname = string

type stackvalue = IntV of int | BoolV of bool | NullV | Location of location | StringV of string

and location = int

type varenv = (varname * stackvalue) list

type heapvalue = Object of classname * varenv

type heap = heapvalue list

type state = varenv * heap

exception TypeError of string
exception RuntimeError of string

let string_of_stackval v = 
	match v with
   		| IntV i -> string_of_int i
   		| BoolV b ->  string_of_bool b
   		| NullV -> "null"
   		| Location loc -> string_of_int loc
		| StringV s -> s
