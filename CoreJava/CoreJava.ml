open List
open CoreJavaAST
open CoreJavaUtils

let rec assign (id:string) (v:stackvalue) (env:varenv) : varenv =
  match env with
    | [] -> raise (TypeError ("unbound variable " ^ id))
    | (id1,v1) :: t -> if id = id1 then (id,v) :: t
                        else (id1,v1) :: assign id v t

let rec binds (id:string) (env:varenv) : bool =
  match env with
    | [] -> false
    | (id1, _)::t -> id=id1 || binds id t

(* gets the value of the variable from the environment*)
let rec get_value (id:string) (env:varenv) : stackvalue =
  match env with
    | [] -> raise (TypeError ("unbound variable: "^id))
    | (id1, v)::t -> if id=id1 then v else get_value id t

let rec make_list (i:int) (v:stackvalue) : stackvalue list =
       if i=0 then [] else v :: make_list (i-1) v

let rec make_pair (lis1:string list) (lis2:stackvalue list) : varenv =
  match (lis1, lis2) with
    | ([], []) -> [] 
    | (h1::t1, h2::t2) -> (h1,h2) :: make_pair t1 t2
    | _ -> raise (TypeError ("formal and actual param lists does not match"))

let pair_with_element (lis:string list) (v:stackvalue) : varenv =
  make_pair lis (make_list (length lis) v)

let rec var_names (varlis:var_decl list) : string list =
  match varlis with
    | [] -> [] 
    | (Var(_, s))::t -> s :: var_names t

let get_method_in_class (id:string) (Class(_, _, _, methlis)) : method_decl =
  let rec aux methlis = 
    match methlis with
      | [] -> raise (TypeError ("no such method: " ^ id))
      | (Method(_, m, _, _, _, _) as the_method) :: t -> if id=m then the_method else aux t
    in aux methlis

let extend_heap (st:heap) (hval:heapvalue) : heap = st @ [hval]

let get_heap_value (st:heap) (loc:int) : heapvalue = List.nth st loc
  
let assign_field (obj:heapvalue) (id:varname) (sv:stackvalue) : heapvalue =
  let Object(c,flds) = obj in Object(c, assign id sv flds)

let rec replace_nth i x lis = 
  match (i, lis) with
    | (0, _::t) -> x :: t
    | (n, h::t) -> h :: replace_nth (n-1) x t
    | (_,_) -> raise (RuntimeError "memory error")

let assign_object (heap:heap) (loc:int) (obj:heapvalue) =
  replace_nth loc obj heap;;

let get_class (c:string) (Program classlis) : class_decl =
  let rec aux classlis = 
    match classlis with
      | [] -> raise (TypeError ("no such class: " ^ c))
      | (Class(c1, _, _, _) as the_class) :: t -> if c=c1 then the_class else aux t
    in aux classlis

let rec get_method (id:string) (c:string) (prog:program) : method_decl =
  let rec has_mathod (id:string) (methlis: method_decl list) : bool =
    match methlis with
      | [] -> false
      | Method(_,m,_,_,_,_)::t -> id=m || has_mathod id t
    in let Class(_,s,_,methlis) as cls = get_class c prog
      in if has_mathod id methlis then get_method_in_class id cls
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
        | _ -> raise (TypeError "plus failed"))
    | Minus -> (match (v1, v2) with
        | (IntV i, IntV j) -> IntV (i - j)
        | _ -> raise (TypeError "minus failed"))
    | Multiplication -> (match (v1, v2) with
        | (IntV i, IntV j) -> IntV (i * j)
        | _ -> raise (TypeError "multiplication failed"))
    | Division -> (match (v1, v2) with
        | (IntV _, IntV 0) -> raise (RuntimeError "division by zero")
        | (IntV i, IntV j) -> IntV (i / j)
        | _ -> raise (TypeError "division failed"))
    | LessThan -> (match (v1, v2) with
        | (IntV i, IntV j) -> BoolV (i < j)
        | _ -> raise (TypeError "less than failed"))
    | Equal -> (match (v1, v2) with
          (IntV i, IntV j) -> BoolV (i=j)
        | (BoolV b1, BoolV b2) -> BoolV (b1=b2)
        | (NullV, NullV) -> BoolV true
        | (NullV, _) -> BoolV false
        | (_, NullV) -> BoolV false
        | _ -> raise (TypeError "equal failed"))
    | _ -> raise (RuntimeError "operator not supported")

let rec eval (e:exp) ((env,heap) as currstate:state) (prog:program) : stackvalue * heap =
  match e with
    | String s -> (StringV s, heap)
    | Integer i -> (IntV i, heap)
    | True -> (BoolV true, heap)
    | False -> (BoolV false, heap)
    | Null -> (NullV, heap)
    | Id id -> if binds id env
               then (get_value id env, heap)
               else (match get_value "this" env with
                      | Location loc -> let Object(_,flds) = get_heap_value heap loc
                           in (get_value id flds, heap)
                      | _ -> raise (TypeError ("undefined variable: "^id)))
    | This -> (get_value "this" env, heap)
    | Not e1 -> let (v,heap1) = eval e1 currstate prog
                in (match v with
                  | BoolV b -> (BoolV (not b), heap1)
                  | _ -> raise (TypeError "non-bool"))
    | Operation(e1, And, e2) ->
          let (v,heap1) = eval e1 currstate prog
          in (match v with
            | BoolV true -> eval e2 (env,heap1) prog
            | BoolV false -> (BoolV false, heap1)
            | _ -> raise (TypeError "non-boolean"))
    | Operation(e1, Or, e2) ->
          let (v,heap1) = eval e1 currstate prog
          in (match v with
            | BoolV true -> (BoolV true, heap1)
            | BoolV false -> eval e2 (env,heap1) prog
            | _ -> raise (TypeError "non-boolean"))
    | Operation(e1, bop, e2) ->
          let (vl,heap1) = eval_list [e1; e2] currstate prog
          in (apply_operation bop (hd vl) (hd (tl vl)), heap1)
    | NewId c -> let newloc = List.length heap and flds = get_field_list c prog
                  in let obj = Object(c, pair_with_element flds NullV)
                  in (Location newloc, extend_heap heap obj)
    | MethodCall(e1, id, args) ->
          let (sv,heap1) = eval e1 currstate prog 
          in (match sv with
            | (Location loc) as this ->
              let Object(c,flds) = get_heap_value heap1 loc
              in let Method(_, _, args, locals, stms, retval) = get_method id c prog
                and (argvals,heap2) = eval_list args (env,heap1) prog
                  in let parambindings = make_pair (var_names args) argvals
                    and localbindings = pair_with_element (var_names locals) NullV
                      in let env1 = ("this",this) :: (parambindings @ localbindings)
                        in eval_method_call stms retval (env1,heap2) prog
            | _ -> raise (TypeError "object not found"))
    | _ -> raise (RuntimeError "eval failed")

and eval_list (el:exp list) ((env,heap) as currstate:state) (prog:program) : stackvalue list * heap = 
    match el with
      | [] -> ([], heap)
      | h::t -> let (sv,heap1) = eval h currstate prog
          in let (svl,heap2) = eval_list t (env,heap1) prog
            in (sv::svl, heap2)

and eval_method_call (stms:statement list) (retval:exp) (currstate:state)
      (prog:program) : stackvalue * heap =
    let currstate1 = exec_statement_list stms currstate prog
      in eval retval currstate1 prog

and exec_statement (s:statement) ((env,heap) as currstate:state) (prog:program) : state =
    match s with
      | Assignment(id,e) ->
           let (sv,heap1) = eval e (env,heap) prog
           in if binds id env
              then (assign id sv env, heap1)
              else (match get_value "this" env with
                    | Location loc ->
                       let obj = get_heap_value heap1 loc
                       in (env, assign_object heap1 loc (assign_field obj id sv))
                    | _ -> raise (TypeError("undefined variable: "^id)))
      | If(e,s1,s2) -> let (sv,heap1) = eval e (env,heap) prog
                     in (match sv with
                        | BoolV true -> exec_statement s1 (env,heap1) prog
                        | BoolV false -> exec_statement s2 (env,heap1) prog
                        | _ -> raise (TypeError "non-bool"))
      | Block sl -> exec_statement_list sl currstate prog
      | _ -> raise (RuntimeError "statement not supported")

and exec_statement_list (sl:statement list) (currstate:state) (prog:program) : state =
    match sl with
      | [] -> currstate
      | s::slt -> let currstate1 = exec_statement s currstate prog
                    in exec_statement_list slt currstate1 prog

let run_with_args (Program(Class(cname,_,_,_) :: _) as prog)
                  (args:exp list) : string =
   let env = [("this", Location 0)]
   and heap = [Object(cname, [])]
   in let (v,_) = eval (MethodCall(Id "this", "main", args))
                       (env,heap) prog
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

let heap1 = [Object("C", [("x", IntV 4); ("y", BoolV true)])];;
extend_heap heap1 (Object("D", [("a", IntV 7); ("b", Location 0)]));;

let obj1 = Object("C", [("x", IntV 4); ("y", BoolV false)]);;
assign_field obj1 "y" (Location 3);;

let heap2 = [Object("C", [("x", IntV 4); ("y", BoolV true)]);
Object("D", [("a", IntV 7); ("b", Location 0)])];;
let obj2 = Object ("C", [("x", IntV 4); ("y", Location 3)]);;
assign_object heap2 1 obj2;;

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

print_endline (run_with_args p2 []);;

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
			[Var (StringType, "a"); Var (StringType, "b"); Var (StringType, "c"); Var (StringType, "e"); Var (StringType, "d")],
			[Assignment ("a", (NewId "Cat")); 
        Assignment ("b", MethodCall(Id "a", "meow", [])); 
        Assignment ("a", (NewId "RubberCat")); 
        Assignment ("c", MethodCall(Id "a", "meow", [])); 
        Assignment ("e", Operation(Id "b", Plus, Operation(String " ", Plus, Id "c")));
	Assignment ("d", Operation(Id "e", Plus, MethodCall(Id "this", "callPiu", [])))],
			Id "d");
		 Method (IntType, "callPiu", [], [Var (StringType, "rCat"); Var (StringType, "what")],
			[Assignment ("rCat", (NewId "RubberCat"));
			Assignment ("what", MethodCall(Id "rCat", "rub", []))], Id "what")]);
	Class ("AbstractCat", "", [], [Method (StringType, "meow", [], [], [], String "biip")]);
	Class ("Cat", "AbstractCat", [], [Method (StringType, "meow", [], [], [], String "meow")]);
	Class ("RubberCat", "AbstractCat", [], [Method (StringType, "rub", [], [], [], String "piuuuuuu")]);	
];;

print_endline (run_with_args p4 []);;

(* NULL object *)
let p5 = Program [
	Class("Main", "", [], 
		[
			Method (IntType, "main", [], 
				[
					Var (StringType, "car");
					Var (StringType, "sound");
				],
				[
					Assignment ("sound", MethodCall(Id "car", "start", []))
				], Id "sound")
		]);
	Class("Car", "", [], [
		Method (StringType, "start", [], [], [], String "vruuuum!!")	
	]);
];;

print_endline (run_with_args p5 []);;

