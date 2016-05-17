open List
open CoreJavaAST
open CoreJavaUtils

let rec assign (id:string) (v:stackvalue) (env:varenv) : varenv =
  match env with
    | [] -> raise (TypeError ("Assignment to unbound variable " ^ id))
    | (id1,v1) :: t -> if id = id1 then (id,v) :: t
                        else (id1,v1) :: assign id v t

let rec binds (id:string) (env:varenv) : bool =
  match env with
    | [] -> false
    | (id1, _)::t -> id=id1 || binds id t

(* gets the value of the variable from the environment*)
let rec get_value (id:string) (env:varenv) : stackvalue =
  match env with
    | [] -> raise (TypeError ("Unbound variable: "^id))
    | (id1, v)::t -> if id=id1 then v else get_value id t

let rec make_list (i:int) (v:stackvalue) : stackvalue list =
       if i=0 then [] else v :: make_list (i-1) v

let rec make_pair (lis1:string list) (lis2:stackvalue list) : varenv =
  match (lis1, lis2) with
    | ([], []) -> [] 
    | (h1::t1, h2::t2) -> (h1,h2) :: make_pair t1 t2
    | _ -> raise (TypeError ("Mismatched formal and actual param lists"))

let pair_with_element (lis:string list) (v:stackvalue) : varenv =
  make_pair lis (make_list (length lis) v)

let rec var_names (varlis:var_decl list) : string list =
  match varlis with
    | [] -> [] 
    | (Var(_, s))::t -> s :: var_names t

let get_method_in_class (id:string) (Class(_, _, _, methlis)) : method_decl =
  let rec aux methlis = 
    match methlis with
      | [] -> raise (TypeError ("No such method: "^id))
      | (Method(_, m, _, _, _, _) as themethod) :: t -> if id=m then themethod else aux t
    in aux methlis

let extend_heap (st:heap) (hval:heapvalue) : heap = st @ [hval]

let get_heap_value (st:heap) (loc:int) : heapvalue = List.nth st loc
  
let assign_field (obj:heapvalue) (id:varname) (sv:stackvalue) : heapvalue =
  let Object(c,flds) = obj in Object(c, assign id sv flds)

let rec replace_nth i x lis = 
  match (i, lis) with
    | (0, _::t) -> x :: t
    | (n, h::t) -> h :: replace_nth (n-1) x t

let assign_object (sto:heap) (loc:int) (obj:heapvalue) =
  replace_nth loc obj sto;;

let get_class (c:string) (Program classlis) : class_decl =
  let rec aux classlis = 
    match classlis with
      | [] -> raise (TypeError ("No such class: "^c))
      | (Class(c1, _, _, _) as theclass) :: t -> if c=c1 then theclass else aux t
    in aux classlis

let rec get_method (id:string) (c:string) (prog:program) : method_decl =
  let rec hasMethod (id:string) (methlis: method_decl list) : bool =
    match methlis with
      | [] -> false
      | Method(_,m,_,_,_,_)::t -> id=m or hasMethod id t
    in let Class(_,s,_,methlis) as cls = get_class c prog
      in if hasMethod id methlis then get_method_in_class id cls
          else if s="" then raise (TypeError ("No such method: "^id))
            else get_method id s prog

let get_field_list (cls:string) (prog:program) : string list =
  let rec aux1 flds = 
    match flds with
      | [] -> []
      | (Var(_,id))::t -> id :: aux1 t
  and aux2 c = 
    let (Class(_,s,flds,_)) = get_class c prog
      in aux1 flds @ (if s="" then [] else aux2 s)
  in aux2 cls

let apply_operation (bop:binary_operation)
            (v1:stackvalue) (v2:stackvalue) : stackvalue =
  match bop with
    | Plus -> (match (v1, v2) with
        | (IntV i, IntV j) -> IntV (i + j)
        | (StringV i, StringV j) -> StringV (i ^ j)
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
    | _ -> raise (RuntimeError "apply_operation: Operator not supported")

let rec eval (e:exp) ((env,sto) as sigma:state) (prog:program) : stackvalue * heap =
  match e with
    | String s -> (StringV s, sto)
    | Integer i -> (IntV i, sto)
    | True -> (BoolV true, sto)
    | False -> (BoolV false, sto)
    | Null -> (NullV, sto)
    | Id id -> if binds id env
               then (get_value id env, sto)
               else (match get_value "this" env with
                      | Location loc -> let Object(_,flds) = get_heap_value sto loc
                           in (get_value id flds, sto)
                      | _ -> raise (TypeError ("Undefined variable: "^id)))
    | This -> (get_value "this" env, sto)
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
          let (vl,sto1) = eval_list [e1; e2] sigma prog
          in (apply_operation bop (hd vl) (hd (tl vl)), sto1)
    | NewId c -> let newloc = List.length sto and flds = get_field_list c prog
                  in let obj = Object(c, pair_with_element flds NullV)
                  in (Location newloc, extend_heap sto obj)
    | MethodCall(e1, id, args) ->
          let (sv,sto1) = eval e1 sigma prog 
          in (match sv with
            | (Location loc) as this ->
              let Object(c,flds) = get_heap_value sto1 loc
              in let Method(_, _, args, locals, stms, retval) = get_method id c prog
                and (argvals,sto2) = eval_list args (env,sto1) prog
                  in let parambindings = make_pair (var_names args) argvals
                    and localbindings = pair_with_element (var_names locals) NullV
                      in let env' = ("this",this) :: (parambindings @ localbindings)
                        in eval_method_call stms retval (env',sto2) prog
            | _ -> raise (TypeError "Receiver not an object in method call"))
    | _ -> raise (RuntimeError "eval: Expression not supported")

and eval_list (el:exp list) ((env,sto) as sigma:state) (prog:program) : stackvalue list * heap = 
    match el with
      | [] -> ([], sto)
      | h::t -> let (sv,sto1) = eval h sigma prog
          in let (svl,sto2) = eval_list t (env,sto1) prog
            in (sv::svl, sto2)

and eval_method_call (stms:statement list) (retval:exp) (sigma:state)
      (prog:program) : stackvalue * heap =
    let sigma1 = exec_statement_list stms sigma prog
      in eval retval sigma1 prog

and exec_statement (s:statement) ((env,sto) as sigma:state) (prog:program) : state =
    match s with
      | Assignment(id,e) ->
           let (sv,sto1) = eval e (env,sto) prog
           in if binds id env
              then (assign id sv env, sto1)
              else (match get_value "this" env with
                    | Location loc ->
                       let obj = get_heap_value sto1 loc
                       in (env, assign_object sto1 loc (assign_field obj id sv))
                    | _ -> raise (TypeError("Assignment to ndefined variable: "^id)))
      | If(e,s1,s2) -> let (sv,sto1) = eval e (env,sto) prog
                     in (match sv with
                        | BoolV true -> exec_statement s1 (env,sto1) prog
                        | BoolV false -> exec_statement s2 (env,sto1) prog
                        | _ -> raise (TypeError "Non-bool in if stmt"))
      | Block sl -> exec_statement_list sl sigma prog
      | _ -> raise (RuntimeError "exec_statement: Statement not supported")

and exec_statement_list (sl:statement list) (sigma:state) (prog:program) : state =
    match sl with
      | [] -> sigma
      | s::slt -> let sigma1 = exec_statement s sigma prog
                    in exec_statement_list slt sigma1 prog

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
assign "y" (IntV 10) state1;;

assert(binds "y" state1 = true);;
assert(string_of_stackval (get_value "y" state1) = "4");;

print_endline (string_of_bool (binds "y" state1));;
print_endline (string_of_stackval (get_value "y" state1));;
make_list 3 (IntV 1);;
make_pair ["a"; "b"] [IntV 10; BoolV true];;
pair_with_element ["a"; "b"] NullV;;
var_names [Var(IntType, "i"); Var(BoolType, "isEof")];;

let sto1 = [Object("C", [("x", IntV 4); ("y", BoolV true)])];;
extend_heap sto1 (Object("D", [("a", IntV 7); ("b", Location 0)]));;

let obj1 = Object("C", [("x", IntV 4); ("y", BoolV false)]);;
assign_field obj1 "y" (Location 3);;

let sto2 = [Object("C", [("x", IntV 4); ("y", BoolV true)]);
Object("D", [("a", IntV 7); ("b", Location 0)])];;
let obj2 = Object ("C", [("x", IntV 4); ("y", Location 3)]);;
assign_object sto2 1 obj2;;

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

let p4 = Program [
	Class ("Main", "", [],
		[Method (IntType, "main", [],
			[Var (StringType, "a"); Var (StringType, "b"); Var (StringType, "c"); Var (StringType, "e")],
			[Assignment ("a", (NewId "Cat")); 
        Assignment ("b", MethodCall(Id "a", "meow", [])); 
        Assignment ("a", (NewId "RubberCat")); 
        Assignment ("c", MethodCall(Id "a", "meow", [])); 
        Assignment ("e", Operation(Id "b", Plus, Operation(String " ", Plus, Id "c")))],
			Id "e");]);
	Class ("AbstractCat", "", [], [Method (StringType, "meow", [], [], [], String "biip")]);
	Class ("Cat", "AbstractCat", [], [Method (StringType, "meow", [], [], [], String "meow")]);
	Class ("RubberCat", "AbstractCat", [], []);	
];;

print_endline (run_with_args p4 []);;
