module ACompilerService.Ast

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
type CompileState =  { mutable newVarIdx: Index; }
let emptyCompileState () = { newVarIdx = 0; }
let genSym state = 
    let idx = state.newVarIdx
    state.newVarIdx <- idx + 1
    idx
let getMaxIdxOfSym state =
     state.newVarIdx 

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

type Info = string
type Label = string
type Pass3Info = Info
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
type Pass3Label = Label
type Pass3Block = Pass3Label * Pass3Tail  
type Pass3Out = 
| P3Program of Pass3Info * Pass3Block list
let emptyInfo = ""
let startLabel = "_start"
let conclusionLable = "conclusion"
let p3IntAtm i = P3Int i |> P3Atm
let p3VarAtm i = P3Var i |> P3Atm


type Reg = 
| Rax = 0 | Rbx = 1 | Rcx = 2  | Rdx = 3  | Rsi = 4  | Rbi = 5  | Rsp = 6  | Rbp = 7
| R8 = 8  | R9 = 9  | R10 = 10 | R11 = 11 | R12 = 12 | R13 = 13 | R14 = 14 | R15 = 15

type InstrOp = 
| Add = 0
| Mov = 1
| Sub = 2
| Neg = 3
| Mul = 4
| IMul = 5
| IDiv = 6
| Push = 7
| Pop = 8

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
| P4UOp of InstrOp * Pass4Atm
| P4BOp of InstrOp * Pass4Atm * Pass4Atm
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
    | P4BOp (InstrOp.Mov, atm1, atm2) -> isEqualP4Atm atm1 atm2
    | _ -> false
