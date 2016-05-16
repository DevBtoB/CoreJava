type program = Program of (class_decl list)

and class_decl = Class of id * id   
        * ((var_kind * var_decl) list) 
        * (method_decl list)

and method_decl = Method of exp_type 
        * id 
        * (var_decl list) 
        * (var_decl list) 
        * (statement list) 
        * exp

and var_decl = Var of exp_type * id

and var_kind = Static | NonStatic

and statement = Block of (statement list)
    | If of exp * statement * statement
    | While of exp * statement
    | Println of exp
    | Assignment of id * exp
    | ArrayAssignment of id * exp * exp
    | Break
    | Continue

and exp = Operation of exp * binary_operation * exp
    | Subscript of exp * exp
    | Length of exp
    | MethodCall of exp * id * (exp list)
    | FieldRef of exp * id
    | Integer of int
    | True
    | False
    | Id of id
    | This
    | NewArray of exp_type * exp
    | NewId of id
    | Not of exp
    | Null
    | String of string
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

and exp_type = ArrayType of exp_type
    | BoolType 
    | IntType
    | ObjectType of id 
    | StringType
    | FloatType

and id = string


type symbol_table =
    (class_name * class_name * variable list * (method_name * variable list) list) list 

and method_info = (method_name * variable list)

and variable =
    Field of class_name
        * exp_type
        * string
    | Argument of exp_type
        * string
    | MethodVar of exp_type
        * string

and class_name =
    string

and method_name =
    string


