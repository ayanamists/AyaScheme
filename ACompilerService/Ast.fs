module Ast

type Identifier = string

type ExprOp =
| Add = 0
| Sub = 1
| Mult = 2
| Div = 3

let printOp (op:ExprOp) = 
    match op with
    | ExprOp.Add -> "+"
    | ExprOp.Sub -> "-"
    | ExprOp.Mult -> "*"
    | ExprOp.Div -> "/"
    | _ -> Failure ("Impossible") |> raise

type Expr = 
| Int of int64
| Id of Identifier
| LetExp of ((Identifier * Expr) list) * Expr
| OpExp of ExprOp * Expr * Expr
