module ACompilerService.IrParser

open FParsec
open Ast
open Parser
open Utils
open System

let int64ToInt32 (i:int64) = System.Convert.ToInt32(i)

let rec s2Type s =
    match s with
    | SId "int" -> IntType () |> Result.Ok
    | SId "bool" -> BoolType () |> Result.Ok
    | SExp l -> result {
        let! l' = resultMap s2Type l
        return l' |> Array.ofList |> VecType }
    | SId "void" -> VoidType () |> Result.Ok
    | _ -> Result.Error (SyntaxError (sprintf "type syntax error in %A" s))

let pIndex = (pchar '$' >>. pint32) <|> (pchar '_' >>% -1)
let pIndexP1 = pIndex |>> P1Id
let rec s2P1 s = 
    match s with
    | SInt i -> P1Int i |> Result.Ok
    | SBool b -> P1Bool b |> Result.Ok
    | SId id -> runParser pIndexP1 id
    | SExp [SId "void"] -> P1Void () |> Result.Ok
    | SExp [SId "let"; SExp [(SExp [(SId id); value])]; exp] -> result {
        let! x = runParser pIndex id
        let! value' = s2P1 value
        let! exp' = s2P1 exp
        return P1LetExp (x, value', exp') }
    | SExp [SId op; exp1; exp2] when strExprOpMap.ContainsKey op -> result {
        let! exp1' = s2P1 exp1
        let! exp2' = s2P1 exp2
        return P1OpExp (strExprOpMap.TryGetValue (op) |> snd, exp1', exp2') }
    | SExp [SId op; exp1 ] when strExprUOpMap.ContainsKey op -> result {
        let! exp1' = s2P1 exp1
        return P1UOpExp (strExprUOpMap.TryGetValue op |> snd, exp1') }
    | SExp [SId "if"; exp1; exp2; exp3 ] -> result {
        let! exp1' = s2P1 exp1
        let! exp2' = s2P1 exp2
        let! exp3' = s2P1 exp3
        return P1IfExp (exp1', exp2', exp3') }
    | SExp [SId "vector-ref"; exp1; SInt i] -> result {
        let! exp1' = s2P1 exp1
        return P1VectorRef (exp1', int64ToInt32 i) }
    | SExp [SId "vector-set!"; exp1; SInt i; exp2] -> result {
        let! exp1' = s2P1 exp1
        let! exp2' = s2P1 exp2
        return P1VectorSet (exp1', int64ToInt32 i, exp2') }
    | SExp [SId "vector"; (SExp l); t] -> result {
        let! l' = resultMap s2P1 l
        let! t = s2Type t
        return P1Vector (l', t) }
    | SExp [SId "global"; SId s] -> P1Global s |> Result.Ok
    | SExp [SId "allocate"; SInt i; t] -> result {
        let! t = s2Type t
        return P1Allocate (int64ToInt32 i, t) }
    | SExp [SId "collect"; SInt i] -> P1Collect (int64ToInt32 i) |> Result.Ok
    | _ -> Result.Error (SyntaxError (sprintf "syntax error in %A" s))


let parseP1 str = result {
    let! s = parse str
    return! s2P1 s
}

let pIndexP2 = pIndex |>> P2Var
let pP2Atm exp = 
    match exp with
    | SInt i -> P2Int i |> Result.Ok
    | SBool b -> P2Bool b |> Result.Ok
    | SId i -> runParser pIndexP2 i 
    | SExp [SId "global"; SId s] -> P2Global s |> Result.Ok
    | SExp _ -> Result.Error (SyntaxError "should be atm")
let getId exp = 
    match exp with
    | P2Var i -> i |> Result.Ok
    | _ -> Result.Error (SyntaxError "should be $id")

let rec s2P2 s = 
    match s with
    | SInt _ 
    | SBool _ 
    | SExp [SId "global"; SId _] 
    | SId _ -> pP2Atm s >>= (Result.Ok .- P2Atm)
    | SExp [SId "void"] -> P2Void () |> Result.Ok
    | SExp [SId "let"; SExp [(SExp [(SId id); value])]; exp] -> result {
        let! x = runParser pIndex id
        let! value' = s2P2 value
        let! exp' = s2P2 exp
        return P2LetExp (x, value', exp') }
    | SExp [SId op; exp1; exp2] when strExprOpMap.ContainsKey op -> result {
        let! exp1' = pP2Atm exp1
        let! exp2' = pP2Atm exp2
        return P2OpExp (strExprOpMap.TryGetValue (op) |> snd, exp1', exp2') }
    | SExp [SId op; exp1 ] when strExprUOpMap.ContainsKey op -> result {
        let! exp1' = pP2Atm exp1
        return P2UOpExp (strExprUOpMap.TryGetValue op |> snd, exp1') }
    | SExp [SId "if"; exp1; exp2; exp3 ] -> result {
        let! exp1' = s2P2 exp1
        let! exp2' = s2P2 exp2
        let! exp3' = s2P2 exp3
        return P2IfExp (exp1', exp2', exp3') }
    | SExp [SId "vector-ref"; exp1; SInt i] -> result {
        let! exp1 = pP2Atm exp1 >>= getId
        return P2VectorRef (exp1, int64ToInt32 i) }
    | SExp [SId "vector-set!"; exp1; SInt i; exp2] -> result {
        let! exp1' = pP2Atm exp1 >>= getId
        let! exp2' = pP2Atm exp2
        return P2VectorSet (exp1', int64ToInt32 i, exp2') }
    | SExp [SId "allocate"; SInt i; t] -> result {
        let! t = s2Type t
        return P2Allocate (int64ToInt32 i, t) }
    | SExp [SId "collect"; SInt i] -> P2Collect (int64ToInt32 i) |> Result.Ok
    | _ -> Result.Error (SyntaxError (sprintf "syntax error in %A" s))

let parseP2 str = result {
    let! s = parse str
    return! s2P2 s
}

let parseVar : Parser<_, unit> =
    pchar '(' >>. spaces >>. pstring "var" >>. spaces >>. pint32  .>>  pchar ')'
let parseP3Var = parseVar |>> P3Var
let parseP3Int : Parser<_, unit> = pint64 |>> P3Int
let parseP3Bool : Parser<_, unit> =
    pchar '#' >>. ((pchar 't' |>> (fun _ -> true))
                   <|> (pchar 'f' |>> (fun _ -> false ))) |>> P3Bool
let parseGlobal : Parser<_, unit> = 
    pstring "global" >>. pchar '(' >>. (many1Chars (noneOf [')'])) .>> pchar ')' |>> string
let parseP3Global = parseGlobal |>> P3Global    
let parseP3Atm = (parseP3Var <|> parseP3Bool <|> parseP3Int <|> parseP3Global) 
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
    
let parseVecRef :Parser<Pass3Exp,unit> =
    pstring "vector-ref" >>.
        (spaces >>. pchar '(' >>. pint32) .>>.
        (pchar ',' >>. spaces >>. pint32 .>> spaces) .>> pchar ')'
    |>> P3VectorRef

let parseVecSet :Parser<Pass3Stmt, unit> =
    pstring "vector-set!" >>.
        (spaces >>. pchar '(' >>. pint32 ) .>> spaces .>>.
        (pchar ','  >>. spaces >>.pint32 .>> spaces) .>>.
        (pchar ',' >>.spaces >>.parseP3Atm .>> spaces) .>> pchar ')'
    |>> (fun ((v, idx), atm) -> P3VectorSet (v, idx, atm))

let parseP3Allocate :Parser<Pass3Exp, unit> =
    pstring "allocate" >>.
        (spaces >>. pchar '(' >>. pint32 .>> spaces) .>>.
        (pchar ',' >>. spaces >>. pType  .>> pchar ')') |>> P3Allocate

let parseP3Exp = parseP3Atm' <|> parseP3BOpExpr <|> parseP3UOpExpr
                 <|> parseP3Allocate <|> parseVecRef

let parseP3Assign = 
    parseVar .>>. (spaces >>. pchar '=' >>. spaces >>. parseP3Exp)
    |>> fun (i, exp) -> (i, exp) |> P3Assign
let parseP3Collect =
    pstring "collect" >>. pchar '(' >>. pint32 .>> pchar ')' |>> P3Collect
let parseP3Stmt = parseP3Collect <|> parseP3Assign <|> parseVecSet

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
                    <|> ((parseP3Stmt .>>. (spaces1 >>. parseP3Tail)) 
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
    <|> (pstring "cqto" >>% InstrUOp.Cqto)
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
    |>> fun (label, instrs) -> (label, instrs)
let parseP4' = 
    sepEndBy parseP4Block spaces |>> fun x -> P4Program (emptyInfo, x)
let parseP4 x = 
    match (run parseP4' x) with
    | Success(res, _, _) -> res
    | Failure(e, _, _) -> 
        printfn "%A" e
        P4Program (emptyInfo, [])
        
let parseP5Int = pint64 |>> P5Int
let parseP5Reg = parseReg |>> P5Reg
let parseP5Mem =
    pstring "mem" >>. pchar '('
    >>.spaces >>.parseReg .>> spaces .>>.
    (pchar ',' >>.spaces >>. pint64 .>> spaces .>> pchar ')')
    |>> fun (reg, offset) -> P5Stack (offset, reg)
let parseP5Atm = parseP5Int <|> parseP5Reg <|> parseP5Mem
let parseP5BOp = 
    parseInstrBOp .>>. (spaces1 >>. parseP5Atm .>>. 
        (spaces >>. pchar ',' >>. spaces >>. parseP5Atm))
    |>> fun (op, (atm1, atm2)) -> P5BOp (op, atm1, atm2)
let parseP5UOp = 
    parseInstrUOp .>>. (spaces1 >>. parseP5Atm)
    |>> fun (op, atm) -> P5UOp (op, atm)
let parseP5CtrOp = 
    parseInstrCtrOp .>>. (spaces1 >>. parseRawLabel)
    |>> fun (op, label) -> P5CtrOp (op, label)
let parseP5Instr = parseP5BOp <|> parseP5CtrOp <|> parseP5UOp
let parseP5InstrSeq =  
    sepEndBy parseP5Instr spaces
let parseP5Block : Parser<Pass5Block, unit> = 
    (spaces >>. (charsTillString ":" false 100) 
        .>> spaces .>> pchar ':' .>> spaces ) 
    .>>. parseP5InstrSeq
let parseP5' info = 
    sepEndBy parseP5Block spaces |>> fun x -> P5Program (info, x)
let parseP5'' x info = 
    match (run (parseP5' info) x) with
    | Success(res, _, _) -> res
    | Failure(e, _, _) -> 
        printfn "%A" e
        P5Program (info, [])

let parseP5 x =  parseP5'' x emptyInfo

