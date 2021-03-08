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
    pstring "if" >>. spaces1 >>. parseP3BOpExpr .>>. 
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
