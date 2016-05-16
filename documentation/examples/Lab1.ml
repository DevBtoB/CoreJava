type typ = TInt | TBool

type primitive = 
    | Int of int 
    | Bool of bool 
    | Float of float 
    | Unit of unit

type typ = 
    | Prm of primitive 
    | Cn of string

type field = 
    |Field of  typ*string
    |Unit of unit


type expr =
    | Var of string
    | Int of int 
    | Bool of bool 
    | Float of float 
    | Unit of unit
    | Primitive of primitive
    | Add of expr*expr
    | Mult of expr*expr
    | Let of string*typ*expr*expr
    | And of expr*expr
    | Or of expr*expr
    | Not of expr
    | If of expr*expr*expr
    | While of expr*expr
    | New of string*field list (*instanciates a new class member, followed by atributes*)
    | Call of string*string (*class member and method name*)

type meth= Meth of typ*string*field list*expr

type cl = string*field list*meth list

type def = string*cl*field list*meth list

type program = def list

let is_value = function
  | Primitive _-> true
  | _ -> false

let subst e1 e2 x =
  let rec subst' e = match e with
    | Var y -> if x=y then e2 else e
    | Int _ | Bool _ | Float _ | Unit _ -> e
    | Add(el,er) -> Add(subst' el, subst' er)
    | Mult(el,er) -> Mult(subst' el, subst' er)
    | And(el,er) -> And(subst' el, subst' er)
    | Let(y,t,ebind,ebody) when x=y -> Let(y, t, subst' ebind, ebody)
    | Let(y,t,ebind,ebody) -> Let(y, t, subst' ebind, subst' ebody)
    | If(eguard,ethen,eelse) -> If(subst' eguard, subst' ethen, subst' eelse)
    | While(eguard, edo) -> While(subst' eguard, subst' edo)
    | _ ->failwith "Run-time type error: subst error"
  in subst' e1

(*-step implementation,
  -one step at a time*)
let rec step = function
  | Primitive _ -> failwith "Does not step"
  | Var _ -> failwith "Unbound variable"
  | Add(e1, e2) -> step_add e1 e2
  | And(e1, e2) -> step_and e1 e2
  | Let(x,t,e1,e2) -> step_let x t e1 e2
  | If(e1,e2,e3) -> step_if e1 e2 e3
  | Mult(e1,e2) -> step_mult e1 e2
  | Or(e1,e2)  -> step_or e1 e2
  | Not(e) -> step_not e
  | While(e1,e2) -> step_while e1 e2
  (*| New(st,li) -> step_new st li
    | Call(st1,st2) -> step_call st1 st2  ///to be implemented*)
  | _ -> failwith "Run-time type error: unknown command"

and

  step_add e1 e2 =
  if is_value e1
  then if is_value e2
    then match (e1,e2) with
      | (Int i,Int j) -> Int (i+j)
      | (Float i, Float j) ->Float (i+.j)
      | _ -> failwith "Run-time type error: add"
    else Add(e1, step e2)
  else Add(step e1, e2)
and

  step_mult e1 e2 =
  if is_value e1
  then if is_value e2
    then match(e1,e2) with
      | (Int i,Int j) -> Int (i*j)
      | (Float i, Float j) ->Float (i*.j)
      | _ -> failwith "Run-time type error: mult"
    else Mult(e1, step e2)
  else Mult(step e1, e2)

and


  step_and e1 e2 =
  if is_value e1
  then if is_value e2
    then match (e1,e2) with
      | (Bool x,Bool y) -> Bool (x&&y)
      | _ -> failwith "Run-time type error: and"
    else And(e1, step e2)
  else And(step e1, e2)

and

  step_let x t e1 e2 =
  if is_value e1 then subst e2 e1 x
  else Let(x,t,step e1,e2)

and

  step_if e1 e2 e3 =
  if is_value e1 then
    match e1 with
      | Bool true -> e2
      | Bool false -> e3
      | _ -> failwith "Run-time type error (if)"
  else If(step e1, e2, e3)

and
  step_or e1 e2 =
  if is_value e1
  then if is_value e2
    then match (e1,e2) with
      | (Bool x,Bool y) -> Bool (x||y)
      | _ -> failwith "Run-time type error: or"
    else And(e1, step e2)
  else And(step e1, e2)

and

  step_not e =
  if is_value e  
  then match  e with
    | Bool x -> Bool (not x)
    | _ -> failwith "Run-time type error: not"
  else Not(step e)

and
  step_while e1 e2 =
  if is_value e1
  then  match  e1 with
    | Bool true -> While(e1, step e2)
    | Bool false -> e2
    | _-> failwith "Run-time type error: while"
  else While(step e1, e2)

(*multistep*)

let rec multistep e =
  if is_value e then e
  else multistep (step e)

(*lookup*)
let lookup ctx x =
  try List.assoc x ctx with
    | Not_found -> failwith "Type error (unbound variable)"

(*extend*)
let extend ctx x t =
  (x,t)::ctx

(*type check*)

let rec typecheck ctx = function
  | Var x -> lookup ctx x
  | Int _ -> TInt
  | Bool _ -> TBool
  | Add(e1,e2) -> typecheck_add ctx e1 e2
  | And(e1,e2) -> typecheck_and ctx e1 e2
  (*| Let(x,t,e1,e2) -> typecheck_let ctx x t e1 e2 *)
  | If(e1,e2,e3) -> typecheck_if ctx e1 e2 e3
  | _ ->failwith "Type check error"

and

  typecheck_add ctx e1 e2 =
  match (typecheck ctx e1, typecheck ctx e2) with
    | (TInt,TInt) -> TInt
    | _ -> failwith "Type error (add)"

and

  typecheck_and ctx e1 e2 =
  match (typecheck ctx e1, typecheck ctx e2) with
    | (TBool,TBool) -> TBool
    | _ -> failwith "Type error (and)"

and

  (*typecheck_let ctx x t e1 e2 =
    let e1t = typecheck ctx e1 in
    let e2t = typecheck (extend ctx x t) e2 in
    if e1t = t then e2t
    else failwith Type error (let) 

    and  ////out of order*)

  typecheck_if ctx e1 e2 e3 =
  let e1t = typecheck ctx e1 in
  let e2t = typecheck ctx e2 in
  let e3t = typecheck ctx e3 in
    if e1t = TBool && e2t = e3t then e2t
    else failwith "Type error (if)"


