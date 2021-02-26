module ACompilerService.Interpreter

open Ast
open FSharp.Collections

exception VarNotBound of string
type BlockEnv = Map<Identifier, Value>
type Env = Map<Identifier, Value> list

exception TypeError of string
let getIntValue value = 
    match value with
    | IntValue v -> v
    | _ -> TypeError (sprintf "%A should be Int" value) |> raise

exception ShouldNotBeCalled of string

let rec searchEnv (env:Env) var =
    match env with 
    | hd :: tl -> if hd.ContainsKey(var) then hd.[var] |> Ok else searchEnv tl var
    | [] -> Error () 

let rec evalWithEnv exp env = 
    let rec loop exp (env:Env) = 
        match exp with
        | Expr.Int i -> IntValue i
        | Expr.Id i -> 
            match (searchEnv env i) with
            | Ok res -> res
            | Error _ -> VarNotBound (sprintf "Var %A not bound" i) |> raise
        | Expr.LetExp (l, expr) -> 
            let nowEnv = 
                List.fold ( fun (nEnv:BlockEnv) (var, vexp) ->
                    let vvexp = evalWithEnv vexp env
                    nEnv.Add(var, vvexp)
                ) (BlockEnv []) l
            loop expr (nowEnv::env)
        | Expr.OpExp (op, expr1, expr2) ->
            let val1 = loop expr1 env |> getIntValue
            let val2 = loop expr2 env |> getIntValue
            match op with
            | ExprOp.Add -> IntValue (val1 + val2)
            | ExprOp.Sub -> IntValue (val1 - val2)
            | ExprOp.Mult -> IntValue (val1 * val2)
            | ExprOp.Div -> IntValue (val1 / val2)
            | _ -> ShouldNotBeCalled (sprintf "%A should not be called" op) |> raise
    loop exp []    

let eval exp = evalWithEnv exp []