module Parser

open FParsec
open Ast

type SExpression = 
| SId of string
| SInt of int64
| SExp of SExpression list

let pLPair = pchar '('
let pRPair = pchar ')'

let idChar = noneOf (List.append ['(' ; ')' ; ' '; '\n'] (List.map (fun x -> (string x).[0]) [0 .. 9]))
let pId : Parser<SExpression, unit> = many1Chars idChar |>> SId
let pNum : Parser<SExpression, unit> = pint64 |>> SInt

let pIds, pIdsRef = 
     createParserForwardedToRef<SExpression list, unit>()

let pSExp = pLPair >>. spaces >>. pIds |>> SExp
let pAll = pNum <|> pId <|> pSExp

do pIdsRef := many1Till (pAll .>> spaces) pRPair

let parse str = 
    match (run pAll str) with
    | Success(res, _, _) -> Result.Ok res
    | Failure(errorMsg, _, _) -> Result.Error errorMsg

