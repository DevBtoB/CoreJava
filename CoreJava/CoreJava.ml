open List
open CoreJavaAST
open CoreJavaUtils

let rec asgn (id:string) (v:stackvalue) (env:environment) : environment =
  match env with
    | [] -> raise (TypeError ("Assignment to unbound variable " ^ id))
    | (id1,v1) :: t -> if id = id1 then (id,v) :: t
                        else (id1,v1) :: asgn id v t

let rec binds (id:string) (env:environment) : bool =
  match env with
    | [] -> false
    | (id1, _)::t -> id=id1 || binds id t

(* gets the value of the variable from the environment*)
let rec fetch (id:string) (env:environment) : stackvalue =
  match env with
    | [] -> raise (TypeError ("Unbound variable: "^id))
    | (id1, v)::t -> if id=id1 then v else fetch id t

let rec mklist (i:int) (v:stackvalue) : stackvalue list =
       if i=0 then [] else v :: mklist (i-1) v

let rec zip (lis1:string list) (lis2:stackvalue list) : environment =
  match (lis1, lis2) with
    | ([], []) -> [] 
    | (h1::t1, h2::t2) -> (h1,h2) :: zip t1 t2
    | _ -> raise (TypeError ("Mismatched formal and actual param lists"))

let zipscalar (lis:string list) (v:stackvalue) : environment =
  zip lis (mklist (length lis) v)

let rec varnames (varlis:var_decl list) : string list =
  match varlis with
    | [] -> [] 
    | (Var(_, s))::t -> s :: varnames t

let getMethodInClass (id:string) (Class(_, _, _, methlis)) : method_decl =
  let rec aux methlis = 
    match methlis with
      | [] -> raise (TypeError ("No such method: "^id))
      | (Method(_, m, _, _, _, _) as themethod) :: t -> if id=m then themethod else aux t
    in aux methlis

let extend (st:store) (hval:heapvalue) : store = st @ [hval]

let storefetch (st:store) (loc:int) : heapvalue = List.nth st loc
  
let asgn_fld (obj:heapvalue) (id:varname) (sv:stackvalue) : heapvalue =
  let Object(c,flds) = obj in Object(c, asgn id sv flds)

let rec replace_nth i x lis = 
  match (i, lis) with
    | (0, _::t) -> x :: t
    | (n, h::t) -> h :: replace_nth (n-1) x t

let asgn_sto (sto:store) (loc:int) (obj:heapvalue) =
  replace_nth loc obj sto;;

let getClass (c:string) (Program classlis) : class_decl =
  let rec aux classlis = 
    match classlis with
      | [] -> raise (TypeError ("No such class: "^c))
      | (Class(c1, _, _, _) as theclass) :: t -> if c=c1 then theclass else aux t
    in aux classlis

let rec getMethod (id:string) (c:string) (prog:program) : method_decl =
  let rec hasMethod (id:string) (methlis: method_decl list) : bool =
    match methlis with
      | [] -> false
      | Method(_,m,_,_,_,_)::t -> id=m or hasMethod id t
    in let Class(_,s,_,methlis) as cls = getClass c prog
      in if hasMethod id methlis then getMethodInClass id cls
          else if s="" then raise (TypeError ("No such method: "^id))
            else getMethod id s prog

let fields (cls:string) (prog:program) : string list =
  let rec aux1 flds = 
    match flds with
      | [] -> []
      | (Var(_,id))::t -> id :: aux1 t
  and aux2 c = 
    let (Class(_,s,flds,_)) = getClass c prog
      in aux1 flds @ (if s="" then [] else aux2 s)
  in aux2 cls

let applyOp (bop:binary_operation)
            (v1:stackvalue) (v2:stackvalue) : stackvalue =
  match bop with
    | Plus -> (match (v1, v2) with
        | (IntV i, IntV j) -> IntV (i + j)
        | _ -> raise (TypeError "Plus: Failed to convert arguments"))
    | Minus -> (match (v1, v2) with
        | (IntV i, IntV j) -> IntV (i - j)
        | _ -> raise (TypeError "Minus: Failed to convert arguments"))
    | Multiplication -> (match (v1, v2) with
        | (IntV i, IntV j) -> IntV (i * j)
        | _ -> raise (TypeError "Multiplication: Failed to convert arguments"))
    | Division -> (match (v1, v2) with
        | (IntV _, IntV 0) -> raise (RuntimeError "Division by zero")
        | (IntV i, IntV j) -> IntV (i / j)
        | _ -> raise (TypeError "Division: Failed to convert arguments"))
    | LessThan -> (match (v1, v2) with
        | (IntV i, IntV j) -> BoolV (i < j)
        | _ -> raise (TypeError "LessThan: Failed to convert arguments"))
    | Equal -> (match (v1, v2) with
          (IntV i, IntV j) -> BoolV (i=j)
        | (BoolV b1, BoolV b2) -> BoolV (b1=b2)
        | (NullV, NullV) -> BoolV true
        | (NullV, _) -> BoolV false
        | (_, NullV) -> BoolV false
        | _ -> raise (TypeError "Equal: Failed to convert arguments"))
    | _ -> raise (RuntimeError "applyOp: Operator not supported")

let rec eval (e:exp) ((env,sto) as sigma:state) (prog:program) : stackvalue * store =
  match e with
    | Integer i -> (IntV i, sto)
    | True -> (BoolV true, sto)
    | False -> (BoolV false, sto)
    | Null -> (NullV, sto)
    | Id id -> if binds id env
               then (fetch id env, sto)
               else (match fetch "this" env with
                      | Location loc -> let Object(_,flds) = storefetch sto loc
                           in (fetch id flds, sto)
                      | _ -> raise (TypeError ("Undefined variable: "^id)))
    | This -> (fetch "this" env, sto)
    | Not e1 -> let (v,sto1) = eval e1 sigma prog
                in (match v with
                  | BoolV b -> (BoolV (not b), sto1)
                  | _ -> raise (TypeError "Not applied to non-bool"))
    | Operation(e1, And, e2) ->
          let (v,sto1) = eval e1 sigma prog
          in (match v with
            | BoolV true -> eval e2 (env,sto1) prog
            | BoolV false -> (BoolV false, sto1)
            | _ -> raise (TypeError "And applied to non-boolean"))
    | Operation(e1, Or, e2) ->
          let (v,sto1) = eval e1 sigma prog
          in (match v with
            | BoolV true -> (BoolV true, sto1)
            | BoolV false -> eval e2 (env,sto1) prog
            | _ -> raise (TypeError "And applied to non-boolean"))
    | Operation(e1, bop, e2) ->
          let (vl,sto1) = evallist [e1; e2] sigma prog
          in (applyOp bop (hd vl) (hd (tl vl)), sto1)
    | NewId c -> let newloc = List.length sto and flds = fields c prog
                  in let obj = Object(c, zipscalar flds NullV)
                  in (Location newloc, extend sto obj)
    | MethodCall(e1, id, args) ->
          let (sv,sto1) = eval e1 sigma prog 
          in (match sv with
            | (Location loc) as this ->
              let Object(c,flds) = storefetch sto1 loc
              in let Method(_, _, args, locals, stms, retval) = getMethod id c prog
                and (argvals,sto2) = evallist args (env,sto1) prog
                  in let parambindings = zip (varnames args) argvals
                    and localbindings = zipscalar (varnames locals) NullV
                      in let env' = ("this",this) :: (parambindings @ localbindings)
                        in evalMethodCall stms retval (env',sto2) prog
            | _ -> raise (TypeError "Receiver not an object in method call"))
    | _ -> raise (RuntimeError "eval: Expression not supported")

and evallist (el:exp list) ((env,sto) as sigma:state) (prog:program) : stackvalue list * store = 
    match el with
      | [] -> ([], sto)
      | h::t -> let (sv,sto1) = eval h sigma prog
          in let (svl,sto2) = evallist t (env,sto1) prog
            in (sv::svl, sto2)

and evalMethodCall (stms:statement list) (retval:exp) (sigma:state)
      (prog:program) : stackvalue * store =
    let sigma1 = execstmtlis stms sigma prog
      in eval retval sigma1 prog

and execstmt (s:statement) ((env,sto) as sigma:state) (prog:program) : state =
    match s with
      | Assignment(id,e) ->
           let (sv,sto1) = eval e (env,sto) prog
           in if binds id env
              then (asgn id sv env, sto1)
              else (match fetch "this" env with
                    | Location loc ->
                       let obj = storefetch sto1 loc
                       in (env, asgn_sto sto1 loc (asgn_fld obj id sv))
                    | _ -> raise (TypeError("Assignment to ndefined variable: "^id)))
      | If(e,s1,s2) -> let (sv,sto1) = eval e (env,sto) prog
                     in (match sv with
                        | BoolV true -> execstmt s1 (env,sto1) prog
                        | BoolV false -> execstmt s2 (env,sto1) prog
                        | _ -> raise (TypeError "Non-bool in if stmt"))
      | Block sl -> execstmtlis sl sigma prog
      | _ -> raise (RuntimeError "execstmt: Statement not supported")

and execstmtlis (sl:statement list) (sigma:state) (prog:program) : state =
    match sl with
      | [] -> sigma
      | s::slt -> let sigma1 = execstmt s sigma prog
                    in execstmtlis slt sigma1 prog

let run_with_args (Program(Class(cname,_,_,_) :: _) as prog)
                  (args:exp list) : string =
   let env = [("this", Location 0)]
   and sto = [Object(cname, [])]
   in let (v,_) = eval (MethodCall(Id "this", "main", args))
                       (env,sto) prog
      in string_of_stackval v

let run (prog:program) : string = run_with_args prog [Integer 2]

let eval_exp (prog:program) : string =
   let Program [Class(_, _, _, [meth])] = prog
   in let Method(_,_,_,_,_,retval) = meth
      in string_of_stackval (fst (eval retval ([],[]) prog))

let state1 = [("x", IntV 4); ("y", IntV 4); ("z", BoolV true)];;
asgn "y" (IntV 10) state1;;

assert(binds "y" state1 = true);;
assert(string_of_stackval (fetch "y" state1) = "4");;

print_endline (string_of_bool (binds "y" state1));;
print_endline (string_of_stackval (fetch "y" state1));;
mklist 3 (IntV 1);;
zip ["a"; "b"] [IntV 10; BoolV true];;
zipscalar ["a"; "b"] NullV;;
varnames [Var(IntType, "i"); Var(BoolType, "isEof")];;

let sto1 = [Object("C", [("x", IntV 4); ("y", BoolV true)])];;
extend sto1 (Object("D", [("a", IntV 7); ("b", Location 0)]));;

let obj1 = Object("C", [("x", IntV 4); ("y", BoolV false)]);;
asgn_fld obj1 "y" (Location 3);;

let sto2 = [Object("C", [("x", IntV 4); ("y", BoolV true)]);
Object("D", [("a", IntV 7); ("b", Location 0)])];;
let obj2 = Object ("C", [("x", IntV 4); ("y", Location 3)]);;
asgn_sto sto2 1 obj2;;

let p1 = Program
   [Class ("Main", "", [],
     [Method (IntType, "main",
       [Var (IntType, "n")],
       [Var (IntType, "r")],
       [If
         (Operation (Id "n", Equal,
           Integer 0),
         Block
          [Assignment ("r", Integer 1)],
         Block
          [Assignment ("r",
            Operation (Id "n",
             Multiplication,
             MethodCall (Id "this", "main",
              [Operation (Id "n", Minus,
                Integer 1)])))])],
       Id "r")])];;

let p2 = Program
   [Class ("Main", "", [],
     [Method (IntType, "main", [], [Var (IntType, "r")], [Assignment ("r", Integer 1)], Id "r")])];;

let p3 = 
  Program [
    Class("Main","", [], 
      [Method (IntType, "main", 
        [], [Var (IntType, "t"); Var (IntType, "r")], 
        [Assignment ("t", (NewId "Lake"));
         Assignment ("r", MethodCall(Id "t", "depth", []))], 
      Id "r")]);
    Class("Tree","",[],[Method (IntType, "depth", [], [], [], Integer 3)]);
    Class("Lake","Tree",[],[])];;

print_endline (run_with_args p3 []);;
