module ACompilerService.Parser

open FParsec
open ACompilerService.Ast

type SExpression = 
| SId of string
| SInt of int64
| SExp of SExpression list

let pLPair = pchar '(' <|> pchar '[' <|> pchar '{'
let pRPair = pchar ')' <|> pchar ']' <|> pchar '}'

let notIdentifierChar = 
    (List.append ['(' ; ')' ; ' '; '\n'; '['; ']'; '{' ; '}'] 
        (List.map (fun x -> (string x).[0]) [0 .. 9]))

let idChar = noneOf notIdentifierChar
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

exception ExcepOfExpToAst of string
exception NotSExp of string

let rec sExpToAst sexp = 
    match sexp with
    | SId id -> Id id 
    | SInt inner -> Int inner
    | SExp sl -> 
        match sl with
        | [] -> ExcepOfExpToAst ("Impossible") |> raise
        | hd :: tl -> 
            match hd with
            | SId id -> 
                match id with
                | "let" -> letToAst tl
                | "+" -> handleBOp1 ExprOp.Add tl
                | "-" -> handleBOp2 ExprOp.Sub tl
                | "*" -> handleBOp1 ExprOp.Mult tl
                | "/" -> handleBOp2 ExprOp.Div tl
                | _ -> ExcepOfExpToAst ("Not Implement") |> raise
            | SInt _ -> (ExcepOfExpToAst "Int should not be called") |> raise
            | SExp _ -> ExcepOfExpToAst ("Not Implement") |> raise 
and letToAst lsexp = 
    match lsexp with
    | (SExp sl) :: [ expr ] ->
        ( ( List.map ( fun x ->
            match x with
            | SExp (SId x :: [ y ]) -> (x, sExpToAst y) 
            | _ -> ExcepOfExpToAst ("Syntax error") |> raise) sl ), 
          sExpToAst expr ) |> LetExp
    | _ -> ExcepOfExpToAst ("Syntax error") |> raise
and handleBOp1 op lsexp = 
    match lsexp with
    | hd1 :: [ hd2 ] -> OpExp (op, sExpToAst hd1, sExpToAst hd2)
    | hd1 :: hd2 :: tl -> 
        let Sop = SId (printOp op) in
        OpExp (op, sExpToAst hd1, SExp (Sop :: hd2 :: tl) |> sExpToAst)
    | _ -> ExcepOfExpToAst ("Syntax error") |> raise
and handleBOp2 op lsexp = 
    match lsexp with
    | hd1 :: [ hd2 ] -> OpExp (op, sExpToAst hd1, sExpToAst hd2) 
    | _ -> ExcepOfExpToAst ("Syntax error") |> raise

let parseToAst code = 
    match parse code with
    | Result.Ok res -> sExpToAst res
    | Result.Error err -> NotSExp err |> raise 
