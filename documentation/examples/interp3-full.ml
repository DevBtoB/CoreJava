(* An interpreter for arithmetic expressions with integers and addition,
   bools and conjunction, let bindings and if expressions. *)

(*** SYNTAX ***)

(* An OCaml type to represent types in the expression language. *)
type typ = TInt | TBool

(* The type of the abstract syntax tree (AST). We now require the
   programmer to annotate each let binding with the type of the
   bound variable.  That annotation burden could be eliminated
   if we implemented type inference.  *)
type expr =
  | Var of string
  | Int of int
  | Bool of bool
  | Add of expr*expr
  | And of expr*expr
  | Let of string*typ*expr*expr
  | If of expr*expr*expr

(* [is_value e] is whether [e] is a syntactic value *)
let is_value = function
  | Int _ | Bool _ -> true
  | _ -> false

(*** DYNAMIC SEMANTICS ***)

(* [subst e1 e2 x] is [e1] with [e2] substituted for [x]. *)
let subst e1 e2 x =
  let rec subst' e = match e with
  | Var y -> if x=y then e2 else e
  | Int _ | Bool _ -> e
  | Add(el,er) -> Add(subst' el, subst' er)
  | And(el,er) -> And(subst' el, subst' er)
  | Let(y,t,ebind,ebody) when x=y -> Let(y, t, subst' ebind, ebody)
  | Let(y,t,ebind,ebody) -> Let(y, t, subst' ebind, subst' ebody)
  | If(eguard,ethen,eelse) ->
    If(subst' eguard, subst' ethen, subst' eelse)
  in subst' e1

(* A single step of evaluation, i.e., the e-->e' judgement. 
   Now that the implementation is getting larger, we've factored
   the code into multiple helper functions. *)
let rec step = function
  | Int _ | Bool _ -> failwith "Does not step"
  | Var _ -> failwith "Unbound variable"
  | Add(e1, e2) -> step_add e1 e2
  | And(e1, e2) -> step_and e1 e2
  | Let(x,t,e1,e2) -> step_let x t e1 e2
  | If(e1,e2,e3) -> step_if e1 e2 e3

and

  step_add e1 e2 =
    if is_value e1
    then if is_value e2
         then match (e1,e2) with
              | (Int i,Int j) -> Int (i+j)
              | _ -> failwith "Run-time type error: add"
         else Add(e1, step e2)
    else Add(step e1, e2)

and

  step_and e1 e2 =
    if is_value e1
    then if is_value e2
         then match (e1,e2) with
              | (Bool x,Bool y) -> Bool (x&&y)
              | _ -> failwith "Run-time type error: and"
         else And(e1, step e2)
    else And(step e1, e2)

(* Note how [step_add] and [step_and] are largely the same code.
   Certainly if we added other binary operators, we'd end up 
   repeating even more code.  That suggests we should find a way 
   to abstract that code... But we'll leave that as an exercise. *)
        
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

(* The reflexive, transitive closure of [step], 
   i.e., the e --> e' judgement. *)
let rec multistep e =
  if is_value e then e
  else multistep (step e)

(*** STATIC SEMANTICS ***)

(* Here we implement typing context with association lists. *)

(* The empty context. *)
let empty = []

(* [lookup c x] is the type of [x] according to context [c]. *)
let lookup ctx x =
  try List.assoc x ctx with
  | Not_found -> failwith "Type error (unbound variable)"

(* [extend c x t] is the same context as [c], but with [x] bound
   to type [t].  If [x] was already bound, its previous binding
   is shadowed by [t]. *)
let extend ctx x t =
  (x,t)::ctx

(* The typing judgement.
   If [typecheck ctx e] yields [t], then ctx |- e : t. 
   Raises Failure if [e] is not well-typed in [ctx]. *)
let rec typecheck ctx = function
  | Var x -> lookup ctx x
  | Int _ -> TInt
  | Bool _ -> TBool
  | Add(e1,e2) -> typecheck_add ctx e1 e2
  | And(e1,e2) -> typecheck_and ctx e1 e2
  | Let(x,t,e1,e2) -> typecheck_let ctx x t e1 e2
  | If(e1,e2,e3) -> typecheck_if ctx e1 e2 e3

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

  typecheck_let ctx x t e1 e2 =
    let e1t = typecheck ctx e1 in
    let e2t = typecheck (extend ctx x t) e2 in
    if e1t = t then e2t
    else failwith "Type error (let)"

and

  typecheck_if ctx e1 e2 e3 =
    let e1t = typecheck ctx e1 in
    let e2t = typecheck ctx e2 in
    let e3t = typecheck ctx e3 in
    if e1t = TBool && e2t = e3t then e2t
    else failwith "Type error (if)"

(*** Interpreter ***)

(* [interp e] first type checks [e] in the empty 
   environment.  If that succeeds, then [interp]
   evaluates [e] to a value [v], where e -->* v.
   That evaluation should never raise an exception,
   becuase [e] typechecks. *)
let interp e =
  ignore(typecheck empty e); multistep e

(* A few test cases *)
let assert_raises f x =
  try ignore(f x); false with
  | _ -> true
let _ = assert (Int 22 = interp (Int 22))
let _ = assert (Int 22 = interp (Add(Int 11,Int 11)))
let _ = assert (Int 22 = interp (Add(Add(Int 10, Int 1),Add(Int 5, Int 6))))
let _ = assert (Int 22 = interp (Let("x",TInt,Int 22,Var "x")))
let _ = assert (Int 22 = interp (Let("x",TInt,Int 0,
                                     Let("x",TInt,Int 22,Var "x"))))
let _ = assert_raises (typecheck []) (Let("x",TBool,Int 22,Var "x"))
let _ = assert_raises (typecheck []) (If(Int 22,Var "x",Var "y"))
