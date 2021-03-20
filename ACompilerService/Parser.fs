module ACompilerService.Parser

open FParsec
open ACompilerService.Ast
open ACompilerService.Utils

type SExpression = 
| SId of string
| SInt of int64
| SBool of bool
| SExp of SExpression list

let pType, pTypeRef = createParserForwardedToRef<ExprValueType, unit>()

let pIntType = pstring "int" >>% ExprValueType.IntType ()
let pBoolType = pstring "bool" >>% ExprValueType.BoolType ()
let pVecType = 
    pchar '(' >>.
    (pType  .>>. manyTill (spaces >>. pchar ',' >>. spaces >>. pType .>> spaces) (pchar ')'))
    |>> fun (x, l) -> x :: l |> Array.ofList |> ExprValueType.VecType
let pVoidType = pstring "void" >>% ExprValueType.VoidType ()

do pTypeRef := pIntType <|> pBoolType <|> pVecType <|> pVoidType

let pLPair = pchar '(' <|> pchar '[' <|> pchar '{'
let pRPair = pchar ')' <|> pchar ']' <|> pchar '}'

let notIdentifierChar = 
    (List.append ['(' ; ')' ; ' '; '\n'; '['; ']'; '{' ; '}'; '#'] 
        (List.map (fun x -> (string x).[0]) [0 .. 9]))

let idChar = noneOf notIdentifierChar
let pId : Parser<SExpression, unit> = many1Chars idChar |>> SId
let pNum : Parser<SExpression, unit> = pint64 |>> SInt
let pBool : Parser<SExpression, unit> = pchar '#'  >>.
                                        (pchar 't' |>> (fun x -> true |> SBool)
                                    <|> (pchar 'f' |>> (fun x -> false |> SBool)))

let pIds, pIdsRef = 
     createParserForwardedToRef<SExpression list, unit>()

let pSExp = pLPair >>. spaces >>. pIds |>> SExp
let pAll = spaces >>. ( pNum <|> pId  <|> pBool <|> pSExp ) .>> spaces

do pIdsRef := many1Till pAll pRPair

let parse str = 
    match (run pAll str) with
    | Success(res, _, _) -> Result.Ok res
    | Failure(errorMsg, _, _) -> Result.Error (SyntaxError errorMsg)

let rec sExpToAst sexp = 
    match sexp with
    | SId id -> Id id |> Result.Ok
    | SBool t -> Bool t |> Result.Ok
    | SInt inner -> Int inner |> Result.Ok
    | SExp sl -> 
        match sl with
        | [] -> Result.Error (SyntaxError "empty s-expression")
        | hd :: tl -> 
            match hd with
            | SId id -> 
                match id with
                | "let" -> letToAst tl
                | "+" -> handleBOp1 ExprOp.Add tl
                | "-" -> handleBOp2 ExprOp.Sub tl
                | "*" -> handleBOp1 ExprOp.Mult tl
                | "/" -> handleBOp2 ExprOp.Div tl
                | "eq?" -> handleBOp2 ExprOp.Eq tl
                | "=" -> handleBOp2 ExprOp.IEq tl
                | ">=" -> handleBOp1 ExprOp.IEqB tl
                | "<=" -> handleBOp1 ExprOp.IEqL tl
                | ">"  -> handleBOp1 ExprOp.IB tl
                | "<"  -> handleBOp1 ExprOp.IL tl
                | "and" -> handleBOp1 ExprOp.And tl
                | "or" -> handleBOp1 ExprOp.Or tl
                | "if" -> ifToAst tl
                | "not" -> handleUOp ExprUOp.Not tl
                | "vector-length" -> handleUOp ExprUOp.VecLen tl
                | "vector-ref" -> handleVecRef tl
                | "vector-set!" -> handleVecSet tl
                | "vector" -> handleVec tl
                | _ -> SyntaxError (sprintf "%A Not Implemented" id) |> Result.Error
            | SInt _ -> SyntaxError ("Int should not be applied") |> Result.Error
            | SBool _ -> SyntaxError ("Int should not be applied") |> Result.Error
            | _ -> SyntaxError (sprintf "%A Not Implemented" hd) |> Result.Error
and letToAst lsexp = 
    match lsexp with
    | (SExp sl) :: [ expr ] ->
        let rec handleSL l =
            match l with
            | [] -> [] |> Result.Ok
            | (SExp [SId id; t]) :: tl -> result {
                let! tl' = handleSL tl
                let! t' = sExpToAst t
                return (id, t') :: tl' }
            | _ -> SyntaxError ("Illegal Let Expr") |> Result.Error
        result {
           let! sl' = handleSL sl
           let! expr' = sExpToAst expr
           return LetExp (sl', expr')
        }
    | _ -> SyntaxError ("Illegal Let Expr") |> Result.Error
and ifToAst lsexp =
    match lsexp with
    | expr1 :: expr2 :: [ expr3 ] -> result {
        let! expr1' = sExpToAst expr1
        let! expr2' = sExpToAst expr2
        let! expr3' = sExpToAst expr3
        return IfExp(expr1', expr2', expr3')
        }
    | _ -> SyntaxError ("Illegal If Expr") |> Result.Error
and handleUOp op lsexp =
    match lsexp with
    | [expr1] -> result {
        let! expr1' = sExpToAst expr1
        return UOpExp(op, expr1')
        }
    | _ -> SyntaxError ("Illegal UOp Expr ") |> Result.Error
and handleBOp1 op lsexp = 
    match lsexp with
    | hd1 :: [ hd2 ] -> result {
        let! hd1' = sExpToAst hd1
        let! hd2' = sExpToAst hd2
        return OpExp(op, hd1', hd2')
        }
    | hd1 :: hd2 :: tl -> 
        result {
            let! hd1' = sExpToAst hd1
            let! tl = handleBOp1 op (hd2 :: tl)
            return OpExp(op, hd1', tl)
        }
    | _ -> SyntaxError (sprintf "Illegal %A Expr" op) |> Result.Error
and handleBOp2 op lsexp = 
    match lsexp with
    | hd1 :: [ hd2 ] -> result {
                                let! hd1' = sExpToAst hd1
                                let! hd2' = sExpToAst hd2
                                return OpExp(op, hd1', hd2')
                                }
    | _ -> SyntaxError (sprintf "Illegal %A Expr" op) |> Result.Error
and handleVecRef lsexp =
    match lsexp with
    | exp1 :: [ (SInt i)] -> result1 sExpToAst exp1 (fun x -> VectorRef (x, (int32)i))
    | _ -> SyntaxError "Illegal vector-ref Expr" |> Result.Error
and handleVecSet lsexp =
    match lsexp with
    | exp1 :: (SInt i) :: [ exp3 ] -> result2' sExpToAst exp1 exp3 (fun x z -> VectorSet (x, (int32)i, z))
    | _ -> SyntaxError "Illegal vector-set! Expr" |> Result.Error
and handleVec lsexp =
    result {
        let! l = resultMap sExpToAst lsexp
        return (l |> Vector)
    }
let parseToAst code =
    result{
        let! code' = parse code
        return! sExpToAst code'
    }
    
let runParser parser str = 
    match (run parser str) with
    | Success(res, _, _) -> Result.Ok res
    | Failure(errorMsg, _, _) -> Result.Error (SyntaxError errorMsg)
let parseType str = runParser pType