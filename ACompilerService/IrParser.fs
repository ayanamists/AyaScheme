module ACompilerService.IrParser

open FParsec
open Ast
open Parser

let parseP3Var : Parser<Pass3Exp, unit> =
    pchar '(' >>. spaces >>. pstring "var" >>. (pint32 |>> p3VarAtm)  .>>  pchar ')'
let parseP3Int : Parser<Pass3Exp, unit> = pint64 |>> p3IntAtm
let parseP3Bool : Parser<Pass3Exp, unit> =
    pchar '#' >>. ((pchar 't' |>> (fun _ -> true |> p3BoolAtm))
                   <|> (pchar 'f' |>> (fun _ -> false |> p3BoolAtm)))

let parseP3Atm = parseP3Var <|> parseP3Bool <|> parseP3Int
let parseBOp = pchar '+' |>> (fun _ -> ExprOp.Add)
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

let parseUOp = pstring "not" |>> (fun _ -> ExprUOp.Not)
let parseP3BOp : Parser<Pass3Exp, unit> =
    
    
