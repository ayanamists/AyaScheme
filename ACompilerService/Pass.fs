module ACompilerService.Pass

open Ast
open Utils

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
exception Impossible of unit
type Pass1BlockEnv = Map<Identifier, Index>
type Pass1Env =  Pass1BlockEnv list
let rec searchEnv (env:Pass1Env) var =
    match env with 
    | hd :: tl -> if hd.ContainsKey(var) then hd.[var] |> Ok else searchEnv tl var
    | [] -> Error () 

let lexicalAddress exp =
    let rec loop exp (env:Pass1Env) = 
        match exp with
        | Expr.Int i -> P1Int i |> stateRet 
        | Expr.Id i -> 
            match (searchEnv env i) with
            | Ok res -> res |> Pass1Out.P1Id |> stateRet
            | Error _ -> VarNotBound (sprintf "Var %A not bound" i) |> raise
        | Expr.LetExp (l, expr) ->
            let rec handleList l nowL (nowEnv:Pass1BlockEnv) =
                match l with
                | [] -> stateRet (nowL, nowEnv)
                | (id , exp) :: tl ->
                    stateComb stateGet (fun cs ->
                        let idx = genSym cs
                        stateComb (loop exp env) (fun x ->
                            handleList tl ((idx, x) :: nowL) (nowEnv.Add(id, idx))
                            )
                        )
            stateComb (handleList l [] (Pass1BlockEnv [])) (fun (nowL, nowEnv) ->
                stateComb (loop expr (nowEnv :: env)) (fun nowExpr -> 
                    Pass1Out.P1LetExp ((List.rev nowL), nowExpr) |> stateRet
                )
            )
        | Expr.OpExp (op, expr1, expr2) ->
            stateComb (loop expr1 env) (fun e1 ->
                stateComb (loop expr2 env) (fun e2 ->
                    Pass1Out.P1OpExp (op, e1, e2 ) |> stateRet
                )
            )
    loop exp []

let pass1 = lexicalAddress

(*
    Approach 1 : Pass 2 Administrative Normal Form
*)

let isAtomPass1Out p1o = 
    match p1o with
    | P1Id _ -> true
    | P1Int _ -> true
    | _ -> false

let anf exp = 
    let rec loop exp = 
        match exp with 
        | P1Int i -> P2Int i |> P2Atm |> stateRet
        | P1Id i -> P2Var i |> P2Atm |> stateRet
        | P1LetExp (l, exp) -> 
            match l with
            | [] -> loop exp
            | (var, vexp) :: tl ->
                stateComb (loop vexp) (fun v ->
                    stateComb (loop (P1LetExp (tl, exp))) (fun t ->
                        P2LetExp (var, v , t) |> stateRet
                    )
                )
        | P1OpExp (op, expr1, expr2) -> 
            anfList (fun [e1; e2] -> P2OpExp (op, e1, e2)) [expr1; expr2]
    and anfList func expl =
        let rec handleExpl expl ids = 
            match expl with
            | [] -> List.rev ids |> func |> stateRet
            | hd :: tl -> 
                match hd with
                | P1Id i -> handleExpl tl ((P2Var i) :: ids)
                | P1Int i -> handleExpl tl ((P2Int i) :: ids)
                | _ -> stateComb stateGet (fun cs ->
                    let sym = genSym cs
                    stateComb (loop hd) (fun hdR ->
                        stateComb (handleExpl tl ((P2Var sym) :: ids)) (fun tlR ->
                            P2LetExp (sym, hdR, tlR) |> stateRet
                        )
                    )
                 )
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

let explicitControl (exp, cs) =
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
    (P3Program (emptyInfo, [ (startLabel, tail) ]), cs)

let pass3 = explicitControl

(*
    Pass 4 Select Instructions
*)
let p3AtmToP4Atm p3Atm = 
    match p3Atm with
    | P3Int i -> P4Int i
    | P3Var i -> P4Var i

let isReg atm reg =
    match atm with
    | P4Reg r -> r = reg
    | _ -> false

let genFromBPrim op atm1 atm2 leftAtm cs = 
    let case1 op a1 a2 = [ P4BOp (InstrOp.Mov, a2, leftAtm)
                           P4BOp (op, a1, leftAtm) ]
    let case2 op a1 a2 = [ P4BOp (InstrOp.Mov, a1, leftAtm)
                           P4BOp (op, a2, leftAtm)]
    let case3 op a1 a2 = 
        if isReg leftAtm Reg.Rax
        then 
            [P4BOp (InstrOp.Mov, a1, leftAtm)
             P4UOp (op, a2)]
        else 
            let tempVar = genSym cs |> P4Var
            [ 
               P4BOp (InstrOp.Mov, P4Reg Reg.Rax, tempVar )
               P4BOp (InstrOp.Mov, a1, P4Reg (Reg.Rax))
               P4UOp (op, a2)
               P4BOp (InstrOp.Mov, P4Reg (Reg.Rax), leftAtm)
               P4BOp (InstrOp.Mov, tempVar, P4Reg Reg.Rax) ]
    let newAtm1 = p3AtmToP4Atm atm1
    let newAtm2 = p3AtmToP4Atm atm2
    let target = 
        match op with
        | ExprOp.Add -> 
            match atm1, atm2 with
            | P3Int i1, P3Var i2 -> case1 InstrOp.Add newAtm1 newAtm2
            | P3Var i1, P3Int i2 -> case1 InstrOp.Add newAtm2 newAtm1
            | P3Var i1, P3Var i2 -> case1 InstrOp.Add newAtm1 newAtm2
            | P3Int i1, P3Int i2 -> case1 InstrOp.Add (P4Int i1) (P4Int i2)
        | ExprOp.Sub -> 
            match atm1, atm2 with
            | P3Int i1, P3Var i2 -> case2 InstrOp.Sub newAtm1 newAtm2
            | P3Var i1, P3Int i2 -> case2 InstrOp.Sub newAtm1 newAtm2
            | P3Var i1, P3Var i2 -> case2 InstrOp.Sub newAtm1 newAtm2
            | P3Int i1, P3Int i2 -> case2 InstrOp.Sub (P4Int i1) (P4Int i2)
        | ExprOp.Mult -> case3 InstrOp.IMul newAtm1 newAtm2
        | ExprOp.Div -> case3 InstrOp.IDiv newAtm1 newAtm2
        | _ -> Impossible () |> raise
    let res = List.filter (fun x -> isUselessP4Instr x |> not) target
    res

let selectInstructions (p3Prg, cs) = 
    let rec handleTail (t:Pass3Tail) acc =
        match t with
        | P3Seq (P3Assign (idx, p3Exp), tail) ->
            match p3Exp with
            | P3Atm atm -> 
                let thisCode = P4BOp (InstrOp.Mov, p3AtmToP4Atm atm, idx |> P4Var)
                handleTail tail (thisCode :: acc)
            | P3BPrim (op, atm1, atm2) ->
                let thisCode1 = genFromBPrim op atm1 atm2 (P4Var idx) cs
                handleTail tail ( (List.rev thisCode1) @ acc )
        | P3Return (p3Exp) -> 
            let retCode = P4CtrOp (InstrCtrOp.Jmp, conclusionLable)
            match p3Exp with
            | P3Atm atm ->
                let thisCode = P4BOp (InstrOp.Mov, p3AtmToP4Atm atm, P4Reg Reg.Rax)
                retCode :: thisCode :: acc |> List.rev
            | P3BPrim (op, atm1, atm2) ->
                let thisCode = genFromBPrim op atm1 atm2 (P4Reg Reg.Rax) cs
                retCode :: (List.rev thisCode) @ acc |> List.rev
    match p3Prg with
    | P3Program (info, blocks) -> 
        let newBlocks = List.map (fun (l, t) -> (l, emptyP4BlockInfo, handleTail t [])) blocks
        (P4Program (info, newBlocks), cs)

let pass4 = selectInstructions

(*
    Pass 5 : Register Allocation
*)


