type program = Program of (class_decl list)

and class_decl = Class of id * id   
        * (var_decl list) 
        * (method_decl list)

and method_decl = Method of exp_type 
        * id 
        * (var_decl list) 
        * (var_decl list) 
        * (statement list) 
        * exp

and var_decl = Var of exp_type * id

and statement = Block of (statement list)
    | If of exp * statement * statement
    | While of exp * statement
    | Assignment of id * exp

and exp = Operation of exp * binary_operation * exp
    | MethodCall of exp * id * (exp list)
    | Integer of int
    | True
    | False
    | Id of id
    | This
    | NewId of id
    | Not of exp
    | Null
    | Float of float

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
    | ObjectType of id
    | FloatType

and id = string

and variable =
    | Field of class_name
        * exp_type
        * string

and class_name =
    string

and method_name =
    string


