module ACompilerService.Ast

open Utils

type Value = 
| IntValue of int64
| BoolValue of bool

type Identifier = string

type ExprOp =
| Add = 0 | Sub = 1 | Mult = 2 | Div = 3
| Eq = 4
| IEq = 5 | IEqB = 6 | IEqL = 7 | IB = 8 | IL = 9
| And = 10 | Or = 11 

type ExprUOp =
| Not = 0
let printOp (op:ExprOp) = 
    match op with
    | ExprOp.Add -> "+"
    | ExprOp.Sub -> "-"
    | ExprOp.Mult -> "*"
    | ExprOp.Div -> "/"
    | ExprOp.Eq -> "eq?"
    | ExprOp.IEq -> "="
    | ExprOp.IEqB -> ">="
    | ExprOp.IEqL -> "<="
    | ExprOp.IB -> ">"
    | ExprOp.IL -> "<"
    | ExprOp.And -> "and"
    | ExprOp.Or -> "or"
    | _ -> Failure ("Impossible") |> raise

type Expr = 
| Int of int64
| Bool of bool
| Id of Identifier
| LetExp of ((Identifier * Expr) list) * Expr
| IfExp of Expr * Expr * Expr
| OpExp of ExprOp * Expr * Expr
| UOpExp of ExprUOp * Expr

type Pass1Out = 
| P1Int of int64
| P1Bool of bool
| P1Id of Index
| P1LetExp of ((Index * Pass1Out) list) * Pass1Out
| P1OpExp of ExprOp * Pass1Out * Pass1Out
| P1IfExp of Pass1Out * Pass1Out * Pass1Out
| P1UOpExp of ExprUOp * Pass1Out

type Pass2Atm = 
| P2Int of int64
| P2Var of Index
| P2Bool of bool

type Pass2Out =
| P2Atm of Pass2Atm
| P2LetExp of Index * Pass2Out * Pass2Out
| P2OpExp of ExprOp * Pass2Atm * Pass2Atm
| P2UOpExp of ExprUOp * Pass2Atm
| P2IfExp of Pass2Out * Pass2Out * Pass2Out
let P2IntAtm x = P2Int x |> P2Atm
let P2VarAtm x = P2Var x |> P2Atm

type Info = string
type Label = string

type Pass3Info = Info
type Pass3Label = Label
type Pass3Atm =
| P3Int of int64
| P3Var of Index
| P3Bool of bool
type Pass3Exp = 
| P3Atm of Pass3Atm
| P3BPrim of ExprOp * Pass3Atm * Pass3Atm
| P3UPrim of ExprUOp * Pass3Atm
type Pass3Goto = P3Goto of Label
type Pass3Stmt =
| P3Assign of Index * Pass3Exp
type Pass3Tail = 
| P3Return of Pass3Exp
| P3Seq of Pass3Stmt * Pass3Tail
| P3TailGoto of Pass3Goto
| P3If of Pass3Exp * Pass3Goto * Pass3Goto
type Pass3Block = Pass3Label * Pass3Tail  
type Pass3Out = 
| P3Program of Pass3Info * Pass3Block list
let emptyInfo = ""
let startLabel = "_start"
let conclusionLabel = "conclusion"
let p3IntAtm i = P3Int i |> P3Atm
let p3VarAtm i = P3Var i |> P3Atm
let p3BoolAtm b = P3Bool b |> P3Atm

type Reg = 
| Rax = 0 | Rbx = 1 | Rcx = 2  | Rdx = 3  | Rsi = 4  | Rbi = 5  | Rsp = 6  | Rbp = 7
| R8 = 8  | R9 = 9  | R10 = 10 | R11 = 11 | R12 = 12 | R13 = 13 | R14 = 14 | R15 = 15

type InstrUOp = 
| Neg = 3
| Mul = 4
| IMul = 5
| IDiv = 6
| Push = 7
| Pop = 8

type InstrBOp =
| Add = 0
| Mov = 1
| Sub = 2
| And = 3
| Or = 4
| Xor = 5
| Cmp = 6

type InstrCtrOp = 
| Ret = 0
| Call = 1
| Jmp = 2

type Pass4RegForVar = NoReg | Reg4Var of Reg
type Pass4Info = Info
type Pass4Label = Label 
type Pass4Atm =
| P4Var of Index
| P4Int of int64
| P4Reg of Reg
type Pass4Instr = 
| P4CtrOp of InstrCtrOp * Label
| P4UOp of InstrUOp * Pass4Atm
| P4BOp of InstrBOp * Pass4Atm * Pass4Atm
type Pass4Block = Label * Info *  Pass4Instr list
type Pass4Out = 
| P4Program of Pass4Info * Pass4Block list

let emptyP4BlockInfo = ""
let isEqualP4Atm atm1 atm2 = 
    match atm1, atm2 with
    | P4Var v1, P4Var v2 -> v1 = v2
    | P4Int v1, P4Int v2 -> v1 = v2
    | P4Reg r1, P4Reg r2 -> r1 = r2
    | _ -> false
let isUselessP4Instr instr = 
    match instr with
    | P4BOp (InstrBOp.Mov, atm1, atm2) -> isEqualP4Atm atm1 atm2
    | _ -> false

type MemOffset = int64

type Pass5Info = Info
type Pass5Label = Label 
type Pass5Atm =
| P5Int of int64
| P5Reg of Reg
| P5Stack of MemOffset * Reg
type Pass5Instr = 
| P5CtrOp of InstrCtrOp * Label
| P5UOp of InstrUOp * Pass5Atm
| P5BOp of InstrBOp * Pass5Atm * Pass5Atm
type Pass5Block = Label * Info *  Pass5Instr list
type Pass5Out = 
| P5Program of Pass5Info * Pass5Block list

let isEqualP5Atm atm1 atm2 = 
    match atm1, atm2 with
    | P5Reg r1, P5Reg r2 -> r1 = r2
    | P5Stack (r1, s1), P5Stack (r2 ,s2) -> s1 = s2 && r1 = r2
    | _ -> false
let isUselessP5Instr instr = 
    match instr with
    | P5BOp (InstrBOp.Mov, atm1, atm2) -> isEqualP5Atm atm1 atm2
    | _ -> false

let p4InstrRW instr =
    let handleAtm atm =
        match atm with
        | P4Int _ -> []
        | P4Var _ -> [atm]
        | P4Reg _ -> [atm]
    let comb res1 res2 =
        let (r1, w1) = res1
        let (r2, w2) = res2
        (r1 @ r2, w1 @ w2)
    match instr with
    | P4CtrOp _ -> ([], [])
    | P4UOp (op, atm) ->
        match op with
        | InstrUOp.Neg -> (handleAtm atm, handleAtm atm)
        | InstrUOp.Mul | InstrUOp.IMul | InstrUOp.IDiv -> (handleAtm atm, [Reg.Rax |> P4Reg])
        | InstrUOp.Push -> (handleAtm atm, [])
        | InstrUOp.Pop -> ([], handleAtm atm)
        | _ -> Impossible () |> raise
    | P4BOp (op, atm1, atm2) ->
        match op with
        | InstrBOp.Add | InstrBOp.Sub -> (handleAtm atm1 @ handleAtm atm2, handleAtm atm2)
        | InstrBOp.Mov -> (handleAtm atm1, handleAtm atm2)
        | _ -> Impossible () |> raise