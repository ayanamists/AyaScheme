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

let genSym init = 
    let mutable idx = init
    fun x ->
        if x = 0 then
            let thisIdx = idx
            idx <- idx + 1
            thisIdx
        else
            idx

let lexicalAddress exp =
    let genSym = genSym 0
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

let isAtomPass1Out p1o = 
    match p1o with
    | P1Id -> true
    | P1Int -> true
    | _ -> false

let anf exp maxIndex = 
    let genSym = genSym maxIndex
    let rec loop exp = 
        match exp with 
        | P1Int i -> P2Int i |> P2Atm
        | P1Id i -> P2Var i |> P2Atm
        | P1LetExp (l, exp) -> 
            match l with
            | [] -> loop exp
            | (var, vexp) :: tl -> P2LetExp (var, (loop vexp), (loop (P1LetExp (tl, exp))))
        | P1OpExp (op, expr1, expr2) -> 
            anfList (fun [e1; e2] -> P2OpExp (op, e1, e2)) [expr1; expr2]
    and anfList func expl =
        let rec handleExpl expl ids = 
            match expl with
            | [] -> List.rev ids |> func
            | hd :: tl -> 
                match hd with
                | P1Id i -> handleExpl tl ((P2Var i) :: ids)
                | P1Int i -> handleExpl tl ((P2Int i) :: ids)
                | _ -> let sym = genSym 0 in P2LetExp (sym, loop hd, handleExpl tl ((P2Var sym) :: ids))        
        handleExpl expl [] 
    loop exp

let pass2 = anf

(*
    Approach 1 : Pass 3 Explicit Control
*)
let p2AtmToP3Atm atm = 
    match atm with
    | P2Int i -> P3Int i
    | P2Var i -> P3Var i
let p2OpExpToP3OpExp op atm1 atm2 =
    P3BPrim (op, atm1 |> p2AtmToP3Atm, atm2 |> p2AtmToP3Atm)

let explicitControl exp =
    let rec explicitTail exp = 
        match exp with
        | P2Atm atm -> let p3Atm = p2AtmToP3Atm atm in P3Atm p3Atm |> P3Return
        | P2LetExp (idx, rhs, e) -> let cont = explicitTail e in explicitAssign idx rhs cont
        | P2OpExp (op, atm1, atm2) -> let p3Opbp = p2OpExpToP3OpExp op atm1 atm2 in P3Return p3Opbp
    and explicitAssign idx rhs cont = 
        match rhs with
        | P2Atm atm -> let p3Atm = p2AtmToP3Atm atm in P3Seq (P3Assign (idx, p3Atm |> P3Atm), cont)
        | P2LetExp (idx2, rhs2, e) -> 
            let contE = explicitAssign idx e cont
            explicitAssign idx2 rhs2 contE
        | P2OpExp (op, atm1, atm2) -> 
            let p3Opbp = p2OpExpToP3OpExp op atm1 atm2
            P3Seq (P3Assign (idx, p3Opbp), cont)
    let tail = explicitTail exp
    P3Program (emptyInfo, [ (startLabel, tail) ])

let pass3 = explicitControl

