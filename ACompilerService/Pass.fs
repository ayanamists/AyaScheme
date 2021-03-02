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
                    state {
                        let! cs = stateGet
                        let idx = genSym cs
                        let! x = loop exp env
                        return! handleList tl ((idx, x) :: nowL) (nowEnv.Add(id, idx))
                    }
            state {
               let! (nowL, nowEnv) = (handleList l [] (Pass1BlockEnv []))
               let! nowExpr = loop expr (nowEnv :: env)
               return Pass1Out.P1LetExp ((List.rev nowL), nowExpr)
            }
        | Expr.OpExp (op, expr1, expr2) ->
            state {
                let! e1 = loop expr1 env
                let! e2 = loop expr2 env
                return Pass1Out.P1OpExp (op, e1, e2 ) 
            }
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
                state {
                    let! v = loop vexp
                    let! t = (P1LetExp (tl, exp)) |> loop
                    return P2LetExp (var, v, t)
                }
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
                | _ -> state {
                    let! cs = stateGet
                    let sym = genSym cs
                    let! hdR = loop hd
                    let! tlR = handleExpl tl ((sym |> P2Var) :: ids)
                    return P2LetExp (sym, hdR, tlR)
                }
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
    P3Program (emptyInfo, [ (startLabel, tail) ]) |> stateRet

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

let genFromBPrim op atm1 atm2 leftAtm = 
    let case1 op a1 a2 = [ P4BOp (InstrBOp.Mov, a2, leftAtm)
                           P4BOp (op, a1, leftAtm) ] |> stateRet
    let case2 op a1 a2 = [ P4BOp (InstrBOp.Mov, a1, leftAtm)
                           P4BOp (op, a2, leftAtm)] |> stateRet
    let case3 op a1 a2 = 
        if isReg leftAtm Reg.Rax
        then 
            [P4BOp (InstrBOp.Mov, a1, leftAtm)
             P4UOp (op, a2)] |> stateRet
        else
            state {
                let! cs = stateGet                
                let tempVar = genSym cs |> P4Var
                return  [ 
                   P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, tempVar )
                   P4BOp (InstrBOp.Mov, a1, P4Reg (Reg.Rax))
                   P4UOp (op, a2)
                   P4BOp (InstrBOp.Mov, P4Reg (Reg.Rax), leftAtm)
                   P4BOp (InstrBOp.Mov, tempVar, P4Reg Reg.Rax) ]
            }
    let newAtm1 = p3AtmToP4Atm atm1
    let newAtm2 = p3AtmToP4Atm atm2
    let target = 
        match op with
        | ExprOp.Add -> 
            match atm1, atm2 with
            | P3Int i1, P3Var i2 -> case1 InstrBOp.Add newAtm1 newAtm2
            | P3Var i1, P3Int i2 -> case1 InstrBOp.Add newAtm2 newAtm1
            | P3Var i1, P3Var i2 -> case1 InstrBOp.Add newAtm1 newAtm2
            | P3Int i1, P3Int i2 -> case1 InstrBOp.Add (P4Int i1) (P4Int i2)
        | ExprOp.Sub -> 
            match atm1, atm2 with
            | P3Int i1, P3Var i2 -> case2 InstrBOp.Sub newAtm1 newAtm2
            | P3Var i1, P3Int i2 -> case2 InstrBOp.Sub newAtm1 newAtm2
            | P3Var i1, P3Var i2 -> case2 InstrBOp.Sub newAtm1 newAtm2
            | P3Int i1, P3Int i2 -> case2 InstrBOp.Sub (P4Int i1) (P4Int i2)
        | ExprOp.Mult -> case3 InstrUOp.IMul newAtm1 newAtm2
        | ExprOp.Div -> case3 InstrUOp.IDiv newAtm1 newAtm2
        | _ -> Impossible () |> raise
    state {
        let! target = target
        return (List.filter (fun x -> isUselessP4Instr x |> not) target)
    }

let selectInstructions p3Prg = 
    let rec handleTail (t:Pass3Tail) acc =
        match t with
        | P3Seq (P3Assign (idx, p3Exp), tail) ->
            match p3Exp with
            | P3Atm atm -> 
                let thisCode = P4BOp (InstrBOp.Mov, p3AtmToP4Atm atm, idx |> P4Var)
                handleTail tail (thisCode :: acc)
            | P3BPrim (op, atm1, atm2) ->
                state {
                    let! thisCode1 = genFromBPrim op atm1 atm2 (P4Var idx)
                    return! handleTail tail ( (List.rev thisCode1) @ acc ) }
        | P3Return (p3Exp) -> 
            let retCode = P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
            match p3Exp with
            | P3Atm atm ->
                let thisCode = P4BOp (InstrBOp.Mov, p3AtmToP4Atm atm, P4Reg Reg.Rax)
                retCode :: thisCode :: acc |> List.rev |> stateRet
            | P3BPrim (op, atm1, atm2) ->
                state {
                    let! thisCode = genFromBPrim op atm1 atm2 (P4Reg Reg.Rax)
                    return retCode :: (List.rev thisCode) @ acc |> List.rev
                }
    match p3Prg with
    | P3Program (info, blocks) ->
        let newBlocks = stateMap (fun (l, t) ->
                    state {
                        let! newTail = (handleTail t []) 
                        return (l, emptyP4BlockInfo, newTail) } ) blocks
        state {
            let! newBlocks = newBlocks
            return P4Program (info, newBlocks)
        }

let pass4 = selectInstructions

(*
    Pass 5 : Register Allocation
*)
let removeEqual (l : Pass4Instr list) =
    let compare atm1 atm2 = 
        match atm1, atm2 with
        | P4Reg r1 , P4Reg r2 -> r1 < r2
        | P4Reg r1, P4Var v2 -> true
        | P4Var v1, P4Reg r2 -> false
        | P4Var v1, P4Var v2 -> v1 < v2
    let changeAtm atm m =
        match atm with
        | P4Int t -> atm
        | _ ->
            match Map.tryFind atm m with
            | Some atm' -> atm'
            | None -> atm
    let giveNewBOp m op atm1 atm2 = P4BOp (op, changeAtm atm1 m , changeAtm atm2 m)
    let giveNewUOp m op atm = P4UOp (op, changeAtm atm m)
    List.fold ( fun (l', g) instr ->
        match instr with
        | P4BOp (InstrBOp.Mov, atm1, atm2) ->
           if existEdge g atm1 atm2 then (l', addEdge g atm1 atm2)
           else giveNewBOp g
    )
let createInfGraph (l : Pass4Instr list) =
    let handle1 instr (g:Graph<Pass4Atm>) (s:Set<Pass4Atm>) p =
        let (r, w) = p4InstrRW instr
        let s' = Set.difference s (Set w)
        let g' = List.fold
                     (fun g' writeV ->
                        List.fold (fun g'' setV ->
                            if (p writeV setV) then addEdge g'' writeV setV
                            else g'')
                            g' [for i in s' -> i]
                     )
                    g w
        (s', g')
    let rec loop l (g:Graph<Pass4Atm>) (s:Set<Pass4Atm>) =
        let pBasic v1 v2 = not (v1 = v2)
        match l with
        | [] -> g
        | [instr] -> handle1 instr g s pBasic |> snd
        | instrNow :: instrLast :: tl ->
            let (s' , g') = 
                match instrLast with
                | P4BOp (InstrBOp.Mov, atm1, atm2) ->
                    let pNow v1 v2 = pBasic v1 v2 && not (v1 = atm1 && v2 = atm2) &&
                                     not (v1 = atm2 && v2 = atm1)
                    handle1 instrNow g s pNow
                | _ -> handle1 instrNow g s pBasic
            loop (instrLast :: tl) g' s'
    loop l (createGraph []) (Set [])
let regAlloc p4Prg =
    let mergeBlocks (blocks:Pass4Block list) =
        List.fold (fun l nowBlock ->
            match nowBlock with
            | (label, info, l') -> l @ l') [] blocks
        
    match p4Prg with
    | P4Program (info, blocks) ->
        let blocksForAssign = mergeBlocks blocks
        let infGraph = createInfGraph blocksForAssign
        ()
        