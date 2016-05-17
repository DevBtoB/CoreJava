type program = Program of (class_decl list)

and class_decl = Class of string * string   
        * (var_decl list) 
        * (method_decl list)

and method_decl = Method of exp_type 
        * string 
        * (var_decl list) 
        * (var_decl list) 
        * (statement list) 
        * exp

and var_decl = Var of exp_type * string

and statement = Block of (statement list)
    | If of exp * statement * statement
    | While of exp * statement
    | Assignment of string * exp

and exp = Operation of exp * binary_operation * exp
    | MethodCall of exp * string * (exp list)
    | Integer of int
    | True
    | False
    | Id of string
    | This
    | NewId of string
    | Not of exp
    | Null
    | Float of float
    | String of string

and binary_operation = And
    | Or
    | Equal
    | LessThan
    | LessThanEq
    | GreaterThan
    | GreaterThanEq
    | Plus
    | Minus
    | Multiplication
    | Division

and exp_type =
    | BoolType 
    | IntType
    | ObjectType of string
    | FloatType
    | StringType