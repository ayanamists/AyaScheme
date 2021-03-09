module ACompilerService.IrParser

open FParsec
open Ast
open Parser

let parseVar : Parser<_, unit> =
    pchar '(' >>. spaces >>. pstring "var" >>. spaces >>. pint32  .>>  pchar ')'
let parseP3Var = parseVar |>> P3Var
let parseP3Int : Parser<_, unit> = pint64 |>> P3Int
let parseP3Bool : Parser<_, unit> =
    pchar '#' >>. ((pchar 't' |>> (fun _ -> true))
                   <|> (pchar 'f' |>> (fun _ -> false ))) |>> P3Bool

let parseP3Atm = (parseP3Var <|> parseP3Bool <|> parseP3Int) 
let parseP3Atm' = parseP3Atm |>> P3Atm
let parseP3BOp = pchar '+' |>> (fun _ -> ExprOp.Add)
                <|> (pchar '-' |>> (fun _ -> ExprOp.Sub))
                <|> (pchar '*' |>> (fun _ -> ExprOp.Mult))
                <|> (pchar '/' |>> (fun _ -> ExprOp.Div))
                <|> (pstring "and" |>> (fun _ -> ExprOp.And))
                <|> (pstring "or" |>> (fun _ -> ExprOp.Or))
                <|> (pstring "eq?" |>> (fun _ -> ExprOp.Eq))
                <|> (pchar '=' |>> (fun _ -> ExprOp.IEq))
                <|> (pchar '>' |>> (fun _ -> ExprOp.IB))
                <|> (pstring ">=" |>> (fun _ -> ExprOp.IEqB))
                <|> (pchar '<' |>> (fun _ -> ExprOp.IL))
                <|> (pstring "<=" |>> (fun _ -> ExprOp.IEqL))

let parseP3UOp = pstring "not" |>> (fun _ -> ExprUOp.Not)

let parseP3BOpExpr = 
    parseP3BOp .>>. 
        (spaces >>. pchar '(' >>. parseP3Atm .>>. 
            (pchar ',' >>. spaces >>. parseP3Atm .>> spaces) .>> pchar ')')
    |>> fun (op, (atm1, atm2)) -> (op, atm1, atm2) |> P3BPrim
   
let parseP3UOpExpr = 
    parseP3UOp .>>.
        (spaces >>. parseP3Atm) 
    |>> fun (op, atm1) -> (op, atm1) |> P3UPrim

let parseP3Exp = parseP3Atm' <|> parseP3BOpExpr <|> parseP3UOpExpr

let parseP3Assign = 
    parseVar .>>. (spaces >>. pchar '=' >>. spaces >>. parseP3Exp)
    |>> fun (i, exp) -> (i, exp) |> P3Assign

let parseLabel = 
    pstring "label" >>. pchar '(' >>. charsTillString ")" false 100 .>> pchar ')'
let parseP3Goto = pstring "goto" >>. spaces >>. parseLabel |>> P3Goto
let parseP3Return = pstring "return" >>. spaces >>. parseP3Exp |>> fun x -> x |> P3Return
let parseP3If = 
    pstring "if" >>. spaces1 >>. parseP3Exp .>>. 
    (spaces1 >>. parseP3Goto .>>. (spaces1 >>. parseP3Goto)) 
    |>> fun (exp1, (exp2, exp3)) -> P3If (exp1, exp2, exp3)
let parseP3TailGoto = parseP3Goto |>> P3TailGoto

let parseP3Tail, parseP3TailRef = createParserForwardedToRef<Pass3Tail, unit> ()
do parseP3TailRef :=
    parseP3TailGoto <|> parseP3If 
                    <|> ((parseP3Assign .>>. (spaces1 >>. parseP3Tail)) 
                        |>> fun (a, s) -> P3Seq (a, s))
                    <|> parseP3Return

let parseP3Block = 
    (spaces >>. (charsTillString ":" false 100) 
        .>> spaces .>> pchar ':' .>> spaces ) 
    .>>. parseP3Tail
    |>> fun (label, tail) -> (label, tail)

let parseP3' = sepEndBy parseP3Block spaces |>> fun x -> (emptyInfo, x) |> P3Program

let parseP3 x = 
    match (run parseP3' x) with
    | Success(res, _, _) -> res
    | Failure(e, _, _) -> 
        printfn "%A" e
        P3Program (emptyInfo, [])

let parseReg : Parser<Reg, unit> = 
    (pstring "rax" >>% Reg.Rax)
    <|> (pstring "rbx" >>% Reg.Rbx) <|> (pstring "rcx" >>% Reg.Rcx) 
    <|> (pstring "rdx" >>% Reg.Rdx) <|> (pstring "rsi" >>% Reg.Rsi)
    <|> (pstring "rdi" >>% Reg.Rdi) <|> (pstring "rbp" >>% Reg.Rbp)
    <|> (pstring "rsp" >>% Reg.Rsp) <|> (pstring "r8" >>% Reg.R8)
    <|> (pstring "r9" >>% Reg.R9) <|> (pstring "r10" >>% Reg.R10)
    <|> (pstring "r11" >>% Reg.R11) <|> (pstring "r12" >>% Reg.R12)
    <|> (pstring "r13" >>% Reg.R13) <|> (pstring "r14" >>% Reg.R14)
    <|> (pstring "r15" >>% Reg.R8)

let parseP4Var = parseVar |>> P4Var
let parseP4Int = pint64 |>> P4Int
let parseP4Reg = parseReg |>> P4Reg
let parseLabelChar = asciiLetter <|> (pchar '-') <|> (digit) 
let parseRawLabel = many1CharsTill parseLabelChar spaces1
let parseP4Atm = parseP4Var <|> parseP4Int <|> parseP4Reg
let parseInstrBOp : Parser<InstrBOp, unit> = 
    (pstring "movzb" >>%  InstrBOp.MovZb)
    <|> (pstring "add" >>% InstrBOp.Add)
    <|> (pstring "sub" >>% InstrBOp.Sub)
    <|> (pstring "mov" >>% InstrBOp.Mov)
    <|> (pstring "and" >>% InstrBOp.And)
    <|> (pstring "or" >>% InstrBOp.Or)
    <|> (pstring "cmp" >>% InstrBOp.Cmp)
    <|> (pstring "xor" >>% InstrBOp.Xor)
    <|> (pstring "test" >>% InstrBOp.Test)
let parseInstrUOp : Parser<InstrUOp, unit> =
    (pstring "neg" >>% InstrUOp.Neg)
    <|> (pstring "mul" >>% InstrUOp.Mul) <|> (pstring "imul" >>% InstrUOp.IMul)
    <|> (pstring "idiv" >>% InstrUOp.IDiv) <|> (pstring "push" >>% InstrUOp.Push)
    <|> (pstring "pop" >>% InstrUOp.Pop) <|> (pstring "sete" >>% InstrUOp.SetE)
    <|> (pstring "setge" >>% InstrUOp.SetGe) <|> (pstring "setbe" >>% InstrUOp.SetBe)
    <|> (pstring "setg" >>% InstrUOp.SetG) <|> (pstring "setb" >>% InstrUOp.SetB)
let parseInstrCtrOp : Parser<InstrCtrOp, unit> = 
    (pstring "jmp" >>% InstrCtrOp.Jmp) <|> (pstring "call" >>% InstrCtrOp.Call)
    <|> (pstring "ret" >>% InstrCtrOp.Ret) <|> (pstring "jz" >>% InstrCtrOp.Jz)
    <|> (pstring "jge" >>% InstrCtrOp.Jge) <|> (pstring "jg" >>% InstrCtrOp.Jg) 
    <|> (pstring "jbe" >>% InstrCtrOp.Jbe) <|> (pstring "jb" >>% InstrCtrOp.Jb)
    <|> (pstring "jnz" >>% InstrCtrOp.Jnz)
let parseP4BOp = 
    parseInstrBOp .>>. (spaces1 >>. parseP4Atm .>>. 
        (spaces >>. pchar ',' >>. spaces >>. parseP4Atm))
    |>> fun (op, (atm1, atm2)) -> P4BOp (op, atm1, atm2)
let parseP4UOp = 
    parseInstrUOp .>>. (spaces1 >>. parseP4Atm)
    |>> fun (op, atm) -> P4UOp (op, atm)
let parseP4CtrOp = 
    parseInstrCtrOp .>>. (spaces1 >>. parseRawLabel)
    |>> fun (op, label) -> P4CtrOp (op, label)
let parseP4Instr = parseP4BOp <|> parseP4CtrOp <|> parseP4UOp
let parseP4InstrSeq =  
    sepEndBy parseP4Instr spaces
let parseP4Block : Parser<Pass4Block, unit> = 
    (spaces >>. (charsTillString ":" false 100) 
        .>> spaces .>> pchar ':' .>> spaces ) 
    .>>. parseP4InstrSeq
    |>> fun (label, instrs) -> (label, emptyP4BlockInfo, instrs)
let parseP4' = 
    sepEndBy parseP4Block spaces |>> fun x -> P4Program (emptyInfo, x)
let parseP4 x = 
    match (run parseP4' x) with
    | Success(res, _, _) -> res
    | Failure(e, _, _) -> 
        printfn "%A" e
        P4Program (emptyInfo, [])


