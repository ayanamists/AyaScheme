module Ast

type Value = 
| IntValue of int64

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

type Index = int
type Pass1Out = 
| P1Int of int64
| P1Id of Index
| P1LetExp of ((Index * Pass1Out) list) * Pass1Out
| P1OpExp of ExprOp * Pass1Out * Pass1Out

type Expr = 
| Int of int64
| Id of Identifier
| LetExp of ((Identifier * Expr) list) * Expr
| OpExp of ExprOp * Expr * Expr

