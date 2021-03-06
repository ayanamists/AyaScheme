﻿module ACompilerService.Pass

open System
open Ast
open FSharpx.Collections
open Utils
open Coloring


(*
    type-check
*)
type ExprValueType = IntType = 0 | BoolType = 1


let rec transformP1If cond =
    match cond with
    | P1OpExp (ExprOp.And, c1, c2) -> 
        let c1' = transformP1If c1
        let c2' = transformP1If c2
        P1IfExp (c1', c2', P1Bool false)
    | P1OpExp (ExprOp.Or, c1, c2) -> 
        let c1' = transformP1If c1
        let c2' = transformP1If c2
        P1IfExp (c1', P1Bool true, c2')
    | _ -> cond

     
let makeVarNotBoundError i = (VarNotBoundError (sprintf "%A is Not bound" i))
let typeCheck exp =
    let rec typeCheckWithEnv exp env =
        let typeEqual exp1 exp2 t1 t2 =
            if t1 = t2
            then t1 |> Result.Ok
            else TypeError (sprintf "%A and %A should be same type" exp1 exp2) |> Result.Error
        let typeEqualTo exp1 t1 target =
            if t1 = target
            then t1 |> Result.Ok
            else TypeError (sprintf "%A should be %A, but have type %A" exp1 target t1) |> Result.Error
        let opType exp1 exp2 t1 t2 target1 target2 target3 =
            Result.bind (fun _ ->
            Result.bind (fun _ ->
                target3 |> Result.Ok
            ) (typeEqualTo exp2 t2 target2)
            ) (typeEqualTo exp1 t1 target1)
        match exp with
        | P1Int _ -> (exp, ExprValueType.IntType) |> Result.Ok
        | P1Bool _ -> (exp, ExprValueType.BoolType) |> Result.Ok
        | P1Id i ->
            match searchEnv env i with
            | Some t -> (exp, t) |> Result.Ok
            | None -> Impossible () |> raise 
        | P1LetExp (l, expr) ->
            let rec handleL l =
                match l with
                | [] -> ([], env) |> Result.Ok
                | (id, exp) :: tl ->
                    result {
                        let! (exp', t) = typeCheckWithEnv exp env
                        let! (l', env') = handleL tl
                        return ((id, exp') :: l', addEnv env' id t)
                    }
            result {
                let! (l', env') = handleL l
                let! (exp', t) = typeCheckWithEnv expr env'
                return (P1LetExp (l', exp'), t)
            }
        | P1IfExp (cond, ifTrue, ifFalse) ->
            result {
                let! (cond', tCond) = (typeCheckWithEnv cond env)
                let! (ifTrue', tIfTrue) = (typeCheckWithEnv ifTrue env)
                let! (ifFalse', tIfFalse) = (typeCheckWithEnv ifFalse env)
                let! _ = (typeEqualTo cond tCond ExprValueType.BoolType)
                let! _ = (typeEqual ifTrue' ifFalse' tIfFalse tIfTrue)
                return (P1IfExp (transformP1If cond', ifTrue', ifFalse'), tIfTrue)
            }
        | P1OpExp (op, exp1, exp2) ->
            Result.bind (fun (exp1', expT1) ->
            Result.bind (fun (exp2', expT2) ->
                let makeBOp t1 t2 t3 =
                     result {
                       let! t = opType exp1' exp2' expT1 expT2 t1 t2 t3
                       return (P1OpExp (op, exp1', exp2'), t)
                     } 
                match op with
                | ExprOp.Add | ExprOp.Sub | ExprOp.Div | ExprOp.Mult ->
                    makeBOp ExprValueType.IntType ExprValueType.IntType ExprValueType.IntType
                | ExprOp.And | ExprOp.Or ->
                    makeBOp ExprValueType.BoolType ExprValueType.BoolType ExprValueType.BoolType
                | ExprOp.IEqB | ExprOp.IEq | ExprOp.IEqL | ExprOp.IB | ExprOp.IL ->
                    makeBOp ExprValueType.IntType ExprValueType.IntType ExprValueType.BoolType
                 | ExprOp.Eq ->
                     if not (expT1 = expT2) then (P1Bool false, ExprValueType.BoolType) |> Result.Ok
                     else (P1OpExp (op, exp1', exp2'), ExprValueType.BoolType) |> Result.Ok
                | _ -> Impossible () |> raise
            ) (typeCheckWithEnv exp2 env)
            ) (typeCheckWithEnv exp1 env)
        | P1UOpExp (op, exp1) ->
            result {
                let! (exp1', t) = (typeCheckWithEnv exp1 env)
                let _ = typeEqualTo exp1' t ExprValueType.BoolType
                return (P1UOpExp (op, exp1'), t)
            }
    typeCheckWithEnv exp emptyEnv

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


let lexicalAddress exp =
    let rec loop exp (env:Env<Identifier, Index>) = 
        match exp with
        | Expr.Int i -> P1Int i |> Result.Ok
        | Expr.Bool b -> P1Bool b |> Result.Ok
        | Expr.Id i -> 
            match (searchEnv env i) with
            | Some res -> res |> Pass1Out.P1Id |> Result.Ok
            | None -> makeVarNotBoundError i |> Result.Error
        | Expr.LetExp (l, expr) ->
            let rec handleList l nowL (nowEnv:Env<Identifier, Index>) =
                match l with
                | [] -> (nowL, nowEnv) |> Result.Ok
                | (id , exp) :: tl ->
                    result {
                        let idx = genSym ()
                        let! x = loop exp env
                        return! handleList tl ((idx, x) :: nowL) (addEnv nowEnv id idx)
                    }
            result {
                let! (nowL, nowEnv) = (handleList l [] env)
                let! nowExpr = loop expr nowEnv
                return Pass1Out.P1LetExp ((List.rev nowL), nowExpr)
            }
        | Expr.OpExp (op, expr1, expr2) ->
            result {
                let! e1 = loop expr1 env
                let! e2 = loop expr2 env
                return Pass1Out.P1OpExp (op, e1, e2 )
            }
        | Expr.IfExp (cond, ifTrue, ifFalse) ->
            result {
                let! e1 = loop cond env
                let! e2 = loop ifTrue env
                let! e3 = loop ifFalse env
                return P1IfExp (e1, e2, e3)
            }
        | Expr.UOpExp (op, exp) ->
            result {
                let! exp' = loop exp env
                return P1UOpExp (op, exp')
            }
    loop exp emptyEnv<Identifier, Index>

let pass1 x = result {
    let! x' = lexicalAddress x
    let! (x'', _) = typeCheck x'
    return x''
} 

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
        | P1Int i -> P2Int i |> P2Atm 
        | P1Id i -> P2Var i |> P2Atm
        | P1Bool b -> P2Bool b |> P2Atm
        | P1LetExp (l, exp) -> 
            match l with
            | [] -> loop exp
            | (var, vexp) :: tl ->
                    let v = loop vexp
                    let t = (P1LetExp (tl, exp)) |> loop
                    P2LetExp (var, v, t)
        | P1OpExp (op, expr1, expr2) -> 
            anfList (fun [e1; e2] -> P2OpExp (op, e1, e2)) [expr1; expr2]
        | P1UOpExp (op, expr1) ->
            anfList (fun [e1;] -> P2UOpExp (op, e1)) [expr1]
        | P1IfExp (exp1, exp2, exp3) ->
            let exp1' = loop exp1
            let exp2' = loop exp2
            let exp3' = loop exp3
            P2IfExp (exp1', exp2', exp3')
    and anfList func expl =
        let rec handleExpl expl ids = 
            match expl with
            | [] -> List.rev ids |> func 
            | hd :: tl -> 
                match hd with
                | P1Id i -> handleExpl tl ((P2Var i) :: ids)
                | P1Int i -> handleExpl tl ((P2Int i) :: ids)
                | P1Bool b -> handleExpl tl ((P2Bool b) :: ids)
                | _ -> 
                    let sym = genSym ()
                    let hdR = loop hd
                    let tlR = handleExpl tl ((sym |> P2Var) :: ids)
                    P2LetExp (sym, hdR, tlR)
        handleExpl expl [] 
    loop exp |> Result.Ok

let pass2 = anf

(*
    Approach 1 : Pass 3 Explicit Control
*)
let p2AtmToP3Atm atm = 
    match atm with
    | P2Int i -> P3Int i
    | P2Var i -> P3Var i
    | P2Bool b -> P3Bool b
let p2OpExpToP3OpExp op atm1 atm2 =
    P3BPrim (op, atm1 |> p2AtmToP3Atm, atm2 |> p2AtmToP3Atm)
let p2UOpExpToP3 op atm1 = P3UPrim (op, atm1 |> p2AtmToP3Atm)

let explicitControl exp =
    let mutable acc = []
    let addBlock instrs label = 
        acc <- (label, instrs) :: acc
    let addBlock' instrs = 
        acc <- (genBlockLabel (), instrs) :: acc
    let rec explicitTail exp = 
        match exp with
        | P2Atm atm -> let p3Atm = p2AtmToP3Atm atm in P3Atm p3Atm |> P3Return
        | P2LetExp (idx, rhs, e) -> let cont = explicitTail e in explicitAssign idx rhs cont
        | P2OpExp (op, atm1, atm2) -> let p3Opbp = p2OpExpToP3OpExp op atm1 atm2 in P3Return p3Opbp
        | P2UOpExp (op, atm1) -> p2UOpExpToP3 op atm1 |> P3Return
        | P2IfExp (cond, ifTrue, ifFalse) -> 
            let ifTrue' = lazy explicitTail ifTrue
            let ifFalse' = lazy explicitTail ifFalse
            explicitCond cond ifTrue' ifFalse'
    and explicitAssign idx rhs cont = 
        match rhs with
        | P2Atm atm -> let p3Atm = p2AtmToP3Atm atm in P3Seq (P3Assign (idx, p3Atm |> P3Atm), cont)
        | P2LetExp (idx2, rhs2, e) -> 
            let contE = explicitAssign idx e cont
            explicitAssign idx2 rhs2 contE
        | P2OpExp (op, atm1, atm2) -> 
            let p3Opbp = p2OpExpToP3OpExp op atm1 atm2
            P3Seq (P3Assign (idx, p3Opbp), cont)
        | P2UOpExp (op, atm1) ->
            let p3Uop = p2UOpExpToP3 op atm1
            P3Seq (P3Assign (idx, p3Uop), cont)
        | P2IfExp (cond, ifTrue, ifFalse) ->
            let contLabel = genBlockLabel ()
            let ifCont = P3Goto contLabel |> P3TailGoto
            let ifTrue' = lazy explicitAssign idx ifTrue ifCont
            let ifFalse' = lazy explicitAssign idx ifFalse ifCont
            addBlock cont contLabel
            explicitCond cond ifTrue' ifFalse'
    and explicitCond cond ifTrue ifFalse =
        let makeGoto (expr:Lazy<Pass3Tail>) =
            lazy match (expr.Force ()) with
                 | P3TailGoto (P3Goto (label)) -> (label) |> P3Goto
                 | other ->
                     let label = genBlockLabel ()
                     addBlock other label
                     label |> P3Goto
        let simpleExp cond (exp1:Lazy<Pass3Tail>) (exp2:Lazy<Pass3Tail>) = 
            P3If (cond, ((makeGoto exp1).Force ()) ,
                  ((makeGoto exp2).Force ()) )
        match cond with
        | P2Atm (P2Int _) -> Impossible () |> raise
        | P2Atm (P2Bool b) -> if b then ifTrue.Force () else ifFalse.Force ()
        | P2Atm (P2Var i) -> simpleExp (P3Var i |> P3Atm) ifTrue ifFalse
        | P2OpExp (op, atm1, atm2) -> simpleExp (p2OpExpToP3OpExp op atm1 atm2) ifTrue ifFalse
        | P2UOpExp (op, atm1) -> simpleExp (p2UOpExpToP3 op atm1) ifTrue ifFalse
        | P2LetExp (var, value, exp) ->
            let cont = explicitCond exp ifTrue ifFalse
            explicitAssign var value cont
        | P2IfExp (cond', ifTrue', ifFalse') ->
            let gotoIfTrue = lazy ((makeGoto ifTrue).Force () |> P3TailGoto)
            let gotoIfFalse = lazy ((makeGoto ifFalse).Force () |> P3TailGoto)
            let ifTrue'' = lazy explicitCond ifTrue' gotoIfTrue gotoIfFalse
            let ifFalse'' = lazy explicitCond ifFalse' gotoIfTrue gotoIfFalse
            explicitCond cond' ifTrue'' ifFalse''
    let tail = explicitTail exp
    P3Program (emptyInfo, (startLabel, tail) :: acc) |> Result.Ok

let pass3 = explicitControl

(*
    Pass 4 Select Instructions
*)
let p3AtmToP4Atm p3Atm = 
    match p3Atm with
    | P3Int i -> P4Int i
    | P3Var i -> P4Var i
    | P3Bool b -> (if b then 0L else 1L) |> P4Int

let isReg atm reg =
    match atm with
    | P4Reg r -> r = reg
    | _ -> false

let genFromBPrim op atm1 atm2 leftAtm =
    let newAtm1 = p3AtmToP4Atm atm1
    let newAtm2 = p3AtmToP4Atm atm2
    let simpleOp op a1 a2 = [ P4BOp (InstrBOp.Mov, a1, leftAtm)
                              P4BOp (op, a2, leftAtm)] 
    let mult a1 a2 = 
        [ 
           P4BOp (InstrBOp.Mov, a1, P4Reg (Reg.Rax))
           P4UOp (InstrUOp.IMul, a2)
           P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, leftAtm ) ]
    let div a1 a2 =
        [
            P4BOp (InstrBOp.Mov, a1, P4Reg (Reg.Rax))
            P4UOp (InstrUOp.Cqto, P4Reg (Reg.Rdx))
            P4UOp (InstrUOp.IDiv, a2)
            P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, leftAtm)
        ]
    let commOp op atm1 atm2 =
        match atm1, atm2 with
        | P4Int _, P4Var _ -> simpleOp op atm2 atm1
        | _, _ -> simpleOp op atm1 atm2
    let cmpOp op atm1 atm2 = 
        [ P4BOp (InstrBOp.Cmp, atm1, atm2)
          P4UOp (op, P4Reg Reg.Rax)
          P4BOp (InstrBOp.MovZb, P4Reg Reg.Rax, leftAtm)
        ]
    let target = 
        match op with
        | ExprOp.Add -> commOp InstrBOp.Add newAtm1 newAtm2
        | ExprOp.Sub -> simpleOp InstrBOp.Sub newAtm1 newAtm2
        | ExprOp.Mult -> mult newAtm1 newAtm2
        | ExprOp.Div -> div newAtm1 newAtm2
        | ExprOp.And -> commOp InstrBOp.And newAtm1 newAtm2
        | ExprOp.Or -> commOp InstrBOp.Or newAtm1 newAtm2
        | ExprOp.IEq -> cmpOp InstrUOp.SetE newAtm1 newAtm2
        | ExprOp.IB -> cmpOp InstrUOp.SetB newAtm1 newAtm2
        | ExprOp.IL -> cmpOp InstrUOp.SetG newAtm1 newAtm2
        | ExprOp.IEqB -> cmpOp InstrUOp.SetBe newAtm1 newAtm2
        | ExprOp.IEqL -> cmpOp InstrUOp.SetGe newAtm1 newAtm2
        | _ -> Impossible () |> raise
    let target = target
    (List.filter (fun x -> isUselessP4Instr x |> not) target)

let makeJmpByOp op = 
    match op with
    | ExprOp.Eq | ExprOp.IEq -> (InstrCtrOp.Jz, InstrCtrOp.Jmp)
    | ExprOp.IEqB -> (InstrCtrOp.Jbe, InstrCtrOp.Jmp)
    | ExprOp.IB -> (InstrCtrOp.Jb, InstrCtrOp.Jmp)
    | ExprOp.IL -> (InstrCtrOp.Jg, InstrCtrOp.Jmp)
    | ExprOp.IEqL -> (InstrCtrOp.Jge, InstrCtrOp.Jmp)
    | _ -> Impossible () |> raise
let rec genFromIfExpr cond ifTrue ifFalse =
    let trueLabel = getP3GotoLabel ifTrue
    let falseLabel = getP3GotoLabel ifFalse
    match cond with
    | P3Atm (P3Var v) -> [ P4BOp (InstrBOp.Test, P4Var v, P4Var v)  
                           P4CtrOp (InstrCtrOp.Jnz, trueLabel)
                           P4CtrOp (InstrCtrOp.Jmp, falseLabel) ]
    | P3Atm (P3Bool b) -> [ P4CtrOp (InstrCtrOp.Jmp, if b then trueLabel else falseLabel) ]
    | P3BPrim (op, atm1, atm2) ->
        let newAtm1 = p3AtmToP4Atm atm1
        let newAtm2 = p3AtmToP4Atm atm2
        let (j1, j2) = makeJmpByOp op
        [ P4BOp (InstrBOp.Cmp, newAtm1, newAtm2)
          P4CtrOp (j1, trueLabel)
          P4CtrOp (j2, falseLabel)
        ]
    | P3UPrim (op, atm1) -> genFromIfExpr (P3Atm atm1) ifFalse ifTrue
    | _ -> Impossible () |> raise
let genFromUOp op atm1 = 
    match op with
    | ExprUOp.Not -> P4BOp (InstrBOp.Xor, P4Int 0x1L, p3AtmToP4Atm atm1)
    | _ -> Impossible () |> raise

let selectInstructions p3Prg = 
    let rec handleTail (t:Pass3Tail) acc =
        match t with
        | P3Seq (P3Assign (idx, p3Exp), tail) ->
            match p3Exp with
            | P3Atm atm -> 
                let thisCode = P4BOp (InstrBOp.Mov, p3AtmToP4Atm atm, idx |> P4Var)
                handleTail tail (thisCode :: acc)
            | P3BPrim (op, atm1, atm2) ->
                let thisCode1 = genFromBPrim op atm1 atm2 (P4Var idx)
                handleTail tail ( (List.rev thisCode1) @ acc )
            | P3UPrim (op, atm1) -> 
                let thisCode = genFromUOp op atm1
                handleTail tail (thisCode :: acc)
        | P3Return (p3Exp) -> 
            let lastCode = P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
            match p3Exp with
            | P3Atm atm ->
                let thisCode = P4BOp (InstrBOp.Mov, p3AtmToP4Atm atm, P4Reg Reg.Rax)
                lastCode :: thisCode :: acc |> List.rev 
            | P3BPrim (op, atm1, atm2) ->
                let thisCode = genFromBPrim op atm1 atm2 (P4Reg Reg.Rax)
                lastCode :: (List.rev thisCode) @ acc |> List.rev
            | P3UPrim (op, atm1) -> 
                let thisCode = genFromUOp op atm1
                lastCode :: thisCode :: acc |> List.rev
        | P3TailGoto (P3Goto label) -> P4CtrOp (InstrCtrOp.Jmp, label) :: acc |> List.rev
        | P3If (cond, ifTrue, ifFalse) -> 
            let thisCode = genFromIfExpr cond ifTrue ifFalse
            (thisCode |> List.rev) @ acc |> List.rev
    match p3Prg with
    | P3Program (info, blocks) ->
        let newBlocks = List.map (fun (l, t) ->
                        let newTail = (handleTail t []) 
                        (l,  newTail) ) blocks
        P4Program (info, conclusionP4Block :: newBlocks) |> Result.Ok

let pass4 = selectInstructions

(*
    Pass 5 : Register Allocation
*)
let makeCtrFlowGraph p4Prg =
    let rec handleBlocks g (label,  instrs) =
        let g' = addVex g label
        let foldF g instr =
            match instr with
            | P4CtrOp (op, label') ->
                match op with
                | InstrCtrOp.Jmp | InstrCtrOp.Jz | InstrCtrOp.Jnz
                | InstrCtrOp.Jb  | InstrCtrOp.Jbe | InstrCtrOp.Jg | InstrCtrOp.Jge ->
                    addEdgeD g label label'
                | _ -> g 
            | _ -> g
        List.fold foldF g' instrs
    match p4Prg with
    | P4Program (info, blocks) ->
        List.fold handleBlocks (createGraph [||]) blocks 
        
let getP4Blocks p4Prg =
    match p4Prg with
    | P4Program (_, blocks) -> blocks
let makeLiveSets p4Prg =
    let ctrFlowGraph = makeCtrFlowGraph p4Prg
    let order = topoSort ctrFlowGraph |> List.rev
    let instrMap = Map.ofList (getP4Blocks p4Prg)
    let rec handleBlocks acc set l =
        match l with
        | [] -> set :: acc
        | instr :: tl ->
            let (r, w) = p4InstrRW instr
            let set' = Set.union (Set.difference set (Set w)) (Set r)
            handleBlocks (set :: acc) set' tl
    let foldF setMap now =
        let successors = getNeighbor ctrFlowGraph now
        if successors.IsEmpty
        then
            let m = handleBlocks [] (Set []) (Map.find now instrMap |> List.rev)
            Map.add now m setMap
        else
            let s = List.map (fun x -> setMap.[x] |> List.head) successors
                    |> List.reduce Set.union
            let instrL = Map.find now instrMap |> List.rev
            let m = handleBlocks [] s instrL 
            Map.add now m setMap
    List.fold foldF (Map []) order

let createInfGraph setMap blocks =
    let foldF0 p writeV g setV =
        if p setV then g else addEdge g writeV setV
    let foldF1 g (instr, set) =
        match instr with
        | P4BOp(InstrBOp.Mov, atm1, atm2) ->
            List.fold (foldF0 (fun v -> v = atm1 || v = atm2) atm2) g
                      (Set.toList set)
        | _ ->
            let (r, w) = p4InstrRW instr
            match w with
            | [] -> g
            | [atm1] ->
                List.fold (foldF0 (fun v -> v = atm1) atm1) g (Set.toList set)
            | [atm1; atm2] ->
                let g' = addEdge g atm1 atm2
                let g'' = List.fold (foldF0 (fun v -> v = atm1) atm1) g' (Set.toList set)
                List.fold (foldF0 (fun v -> v = atm1) atm1) g'' (Set.toList set)
            | _ -> Impossible () |> raise
    let foldF2 g (label, block) =
        List.zip block (List.tail (Map.find label setMap))
        |> List.fold foldF1 g
    List.fold foldF2 (createGraph [||]) blocks

let pass4ToInfGraph p4 =
    let blocks = getP4Blocks p4
    let sets = makeLiveSets p4
    createInfGraph sets blocks
    
let regAlloc p4Prg =
    let mutable maxStack = 0
    let assignToAtm m =
      let varColorLst = [ for KeyValue(r, c) in m -> (r, c) ] 
      let max = maxColor m
      if max = 0 then fun _ -> P5Reg (enum<Reg>0) else
      let foldF l (x, c) =
          match x with
          | P4Reg r -> (c, r) :: l
          | _ -> l
      let (assignColor, assignReg) = List.fold foldF [] varColorLst |> List.unzip
      let assignRegMap = List.zip assignColor assignReg |> Map.ofList
      let regList = [ 0; 2; 1; 3 ] |> List.map (fun x -> (enum<Reg>x))
      let regCount = List.length regList
      let unuseReg = regList |> List.filter (fun x -> not (List.contains x assignReg))
      let rec makeMapping varColorL regL (arr: Pass5Atm array) =
          match varColorL with
          | [] -> arr
          | color :: tl ->
              match (assignRegMap.TryFind color) with
              | Some t ->
                  arr.[color] <- t |> P5Reg
                  makeMapping tl regL arr
              | None ->
                  match regL with
                  | [] ->
                      let offset = -8L * (int64)(color - regCount + 1)
                      arr.[color] <- (offset, Reg.Rbp) |> P5Stack
                      maxStack <- (-(int32)offset)
                      makeMapping tl regL arr
                  | hd :: tl' ->
                      arr.[color] <- hd |> P5Reg
                      makeMapping tl tl' arr
      let arr = makeMapping [0 .. max - 1] unuseReg (Array.create max (P5Reg Reg.Rax))
      fun color -> arr.[color]
    match p4Prg with
    | P4Program (info, blocks) ->
        let infGraph = pass4ToInfGraph p4Prg
        let assignMap = coloringGraph infGraph
        let assignManager = assignToAtm assignMap
        let mapAtm atm =
            match atm with
            | P4Reg r -> P5Reg r 
            | P4Var _ ->
                match Map.tryFind atm assignMap with
                | Some t ->
                    t |> assignManager 
                | None -> 0 |> assignManager
            | P4Int i -> P5Int i 
        let foldF l instr =
            if isUselessP4Instr instr then l
            else
                match instr with
                | P4BOp (op, atm1, atm2) ->
                    let p5Instr = P5BOp (op,mapAtm atm1, mapAtm atm2)
                    if isUselessP5Instr p5Instr then l else p5Instr :: l 
                | P4UOp (op, atm1) ->
                    P5UOp (op, mapAtm atm1) :: l 
                | P4CtrOp (op, t) -> P5CtrOp (op, t) :: l
        let allocList l = List.fold foldF [] l |> List.rev
        let newBlocks =
            List.map (fun (label, block) -> (label, allocList block)) blocks
        P5Program ({ stackSize = maxStack }, newBlocks) |> Result.Ok

let pass5 = regAlloc
        
(*
    Pass 6: patch instructions
*)

let patchReg = Reg.R8
let patchReg2 = Reg.R9

let isInt32 x =
    (int64)Int32.MaxValue >= x  && x >= (int64)Int32.MinValue
    

let rec patchInstr instr =
    match instr with
    | P5BOp (op, atm1, atm2) -> 
        match atm1, atm2 with
        | P5Stack (r1, off1), P5Stack (r2, off2) ->
            [
                P5BOp (InstrBOp.Mov, atm1, P5Reg patchReg)
                P5BOp (op, P5Reg patchReg, atm2)
            ]
        | _, P5Int _ ->
            [
                P5BOp (InstrBOp.Mov, atm2, P5Reg patchReg)
                P5BOp (op, atm1, P5Reg patchReg)
            ]
            |> List.map patchInstr |> List.reduce (@)
        | P5Int i, atm2 ->
            if isInt32 i then [ instr ]
            else
                match op, atm2 with
                | InstrBOp.Mov, (P5Reg _) -> [ instr ]
                | _ ->
                    [
                        P5BOp (InstrBOp.Mov, P5Int i, P5Reg patchReg2)
                        P5BOp (op, P5Reg patchReg2, atm2)
                    ]
        | P5Reg r, P5Stack (off1, r1) ->
            match op with
            | InstrBOp.MovZb ->
                [
                    P5BOp (InstrBOp.MovZb, atm1, P5Reg patchReg)
                    P5BOp (InstrBOp.Mov, P5Reg patchReg, atm2)
                ]
            | _ -> [ instr ]
        | _, _ -> [ instr ]
    | P5UOp (op, atm1) ->
        match atm1 with
        | P5Int i ->
            [
                P5BOp (InstrBOp.Mov, P5Int i, P5Reg patchReg)
                P5UOp (op, P5Reg patchReg)
            ]
        | _ -> [ instr ]
    | P5CtrOp _ -> [ instr ]

let conclusionBlock = ("conclusion", [ P5CtrOp (InstrCtrOp.Ret, "") ])
let patchInstructions p5Prg =
    match p5Prg with
    | P5Program (info, blocks) ->
       (info, List.map (fun (label, instrL) ->
                        (label, List.map patchInstr instrL
                                |> fun l -> if l.IsEmpty then [] else List.reduce (@) l)
                       ) blocks)
       |> P5Program |> Result.Ok
       
let pass6 = patchInstructions