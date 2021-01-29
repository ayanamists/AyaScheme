module Pass

open Ast

(*
    Pass 1: Lexical Address
    e.g. 
         in  -> (let ([a 10] [b 20])
                  (let ([c 11] [a 12])
                     (+ a b))
         out ->
                (let ([#0 10] [#1 20])
                  (let ([#2 11] [#3 12])
                    (+ #3 #1)))
*)

exception VarNotBound of string
type Pass1Env = Map<Identifier, Index> list
let rec searchEnv (env:Pass1Env) var =
    match env with 
    | hd :: tl -> if hd.ContainsKey(var) then hd.[var] |> Ok else searchEnv tl var
    | [] -> Error () 

let lexicalAddress exp =
    let genSym = 
        let mutable idx = 0
        fun x ->
            if x = 0 then
                let thisIdx = idx
                idx <- idx + 1
                thisIdx
            else
                idx

    let rec loop exp (env:Pass1Env) = 
        match exp with
        | Expr.Int i -> P1Int i 
        | Expr.Id i -> 
            match (searchEnv env i) with
            | Ok res -> res |> Pass1Out.P1Id
            | Error _ -> VarNotBound (sprintf "Var %A not bound" i) |> raise
        | Expr.LetExp (l, expr) -> 
            let (nowEnv, nowL) = 
                List.fold ( fun (thisEnv:Map<Identifier, Index>, l) (var, vexp) -> 
                    let idx = genSym 0
                    (thisEnv.Add(var, idx), (idx, loop vexp env) :: l)
                ) (Map<Identifier, Index>([]), []) l
            let nowExpr = loop expr (nowEnv::env)
            Pass1Out.P1LetExp ((List.rev nowL), nowExpr)
        | Expr.OpExp (op, expr1, expr2) ->
            Pass1Out.P1OpExp (op, loop expr1 env,  loop expr2 env )
    let res = loop exp []
    let idx = genSym 1 
    (res, idx)

let pass1 = lexicalAddress

(*
    Approach 1 : Pass 2 Administrative Normal Form
*)
let anf exp = 0
