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

type Expr = 
| Int of int64
| Id of Identifier
| LetExp of ((Identifier * Expr) list) * Expr
| OpExp of ExprOp * Expr * Expr

type Index = int

type Pass1Out = 
| P1Int of int64
| P1Id of Index
| P1LetExp of ((Index * Pass1Out) list) * Pass1Out
| P1OpExp of ExprOp * Pass1Out * Pass1Out

type Pass2Atm = 
| P2Int of int64
| P2Var of Index
type Pass2Out =
| P2Atm of Pass2Atm
| P2LetExp of Index * Pass2Out * Pass2Out
| P2OpExp of ExprOp * Pass2Atm * Pass2Atm
let P2IntAtm x = P2Int x |> P2Atm
let P2VarAtm x = P2Var x |> P2Atm

type Pass3Info = string
type Pass3Atm =
| P3Int of int64
| P3Var of Index
type Pass3Exp = 
| P3Atm of Pass3Atm
| P3BPrim of ExprOp * Pass3Atm * Pass3Atm
type Pass3Stmt =
| P3Assign of Index * Pass3Exp
type Pass3Tail = 
| P3Return of Pass3Exp
| P3Seq of Pass3Stmt * Pass3Tail
type Pass3Label = string
type Pass3Block = Pass3Label * Pass3Tail  
type Pass3Out = 
| P3Program of Pass3Info * Pass3Block list
let emptyInfo = ""
let startLabel = "_start"
let p3IntAtm i = P3Int i |> P3Atm
let p3VarAtm i = P3Var i |> P3Atm
