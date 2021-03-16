module ACompilerService.Interpreter

open System
open Ast
open FSharp.Collections

exception VarNotBound of string
type BlockEnv = Map<Identifier, Value>
type Env = Map<Identifier, Value> list

exception TypeError of string
exception VecOutOfLength of string
let getIntValue value = 
    match value with
    | IntValue v -> v
    | _ -> TypeError (sprintf "%A should be Int" value) |> raise
 
let getBoolValue value =
    match value with
    | BoolValue b -> b
    | _ -> TypeError (sprintf "%A should be Bool" value) |> raise
    
let getVecValue value =
    match value with
    | VecValue v -> v
    | _ -> TypeError (sprintf "%A should be Vec" value) |> raise
    
exception ShouldNotBeCalled of string

let rec searchEnv (env:Env) var =
    match env with 
    | hd :: tl -> if hd.ContainsKey(var) then hd.[var] |> Ok else searchEnv tl var
    | [] -> Error ()
    
    
let testVecIdx v idx =
    if idx < Array.length v then ()
    else
        VecOutOfLength (sprintf "%A out of length of %A" idx v) |> raise
        
let evalBinaryExpr v1 v2
                   (valueGetter1: Value->'a) (valueGetter2: Value->'a)
                   (f: 'a->'a->Value) =
    let val1 = v1 |> valueGetter1
    let val2 = v2 |> valueGetter2
    f val1 val2
    
let evalUnaryExpr v1 valueGetter1 f =
    let val1 = v1 |> valueGetter1
    f val1

let rec evalWithEnv exp env = 
        match exp with
        | Expr.Int i -> IntValue i
        | Expr.Bool b -> BoolValue b
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
            evalWithEnv expr (nowEnv::env)
        | Expr.OpExp (op, expr1, expr2) ->
            let v1 = evalWithEnv expr1 env
            let v2 = evalWithEnv expr2 env
            let evalIntF f = evalBinaryExpr v1 v2 getIntValue getIntValue
                                 (fun v1 v2 -> f v1 v2 |> IntValue)
            let evalIntIntBool f = evalBinaryExpr v1 v2 getIntValue getIntValue
                                    (fun v1 v2 -> f v1 v2 |> BoolValue)
            let evalBoolF f = evalBinaryExpr v1 v2 getBoolValue getBoolValue
                                  (fun v1 v2 -> f v1 v2 |> BoolValue)
            match op with
            | ExprOp.Add -> evalIntF (+)
            | ExprOp.Sub -> evalIntF (-)
            | ExprOp.Mult -> evalIntF ( * )
            | ExprOp.Div -> evalIntF (/)
            | ExprOp.And -> evalBoolF (&&)
            | ExprOp.Or -> evalBoolF (||)
            | ExprOp.IEq -> evalIntIntBool (=)
            | ExprOp.IEqB -> evalIntIntBool (>=)
            | ExprOp.IEqL -> evalIntIntBool (<=)
            | ExprOp.IB -> evalIntIntBool (>)
            | ExprOp.IL -> evalIntIntBool (<)
            | ExprOp.Eq ->
                match v1, v2 with
                | IntValue i1, IntValue i2 -> i1 = i2 |> BoolValue
                | BoolValue b1, BoolValue b2 -> b1 = b2 |> BoolValue
                | _ -> false |> BoolValue
            | _ -> ShouldNotBeCalled (sprintf "%A should not be called" op) |> raise
        | Expr.UOpExp (op, expr) ->
            let v1 = evalWithEnv expr env
            match op with
            | ExprUOp.Not -> evalUnaryExpr v1 getBoolValue (fun x -> not x |> BoolValue)
            | _ -> ShouldNotBeCalled (sprintf "%A should not be called" op) |> raise
        | Expr.IfExp (cond, ifTrue, ifFalse) ->
            let v1 = evalWithEnv cond env |> getBoolValue
            if v1
            then evalWithEnv ifTrue env
            else evalWithEnv ifFalse env
        | Expr.Vector l ->
            let l' = List.map (fun x -> evalWithEnv x env) l
            VecValue [| for i in l' -> i |]
        | Expr.VectorRef (v, idx) ->
            let v' = evalWithEnv v env |> getVecValue
            let idx' = evalWithEnv idx env |> getIntValue |> int32
            testVecIdx v' idx'
            v'.[idx']
        | Expr.VectorSet (v, idx, value) ->
            let v' = evalWithEnv v env |> getVecValue
            let idx' = evalWithEnv idx env |> getIntValue |> int32
            testVecIdx v' idx'
            let value' = evalWithEnv value env
            v'.[idx'] <- value'
            VoidValue ()

let eval exp = evalWithEnv exp []