module ACompilerService.Pass

open System.Collections.Generic
open System.Drawing
open Ast
open FSharpx.Collections
open Utils
open Coloring

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
let removeTemp (l : Pass4Instr list) =
    let changeMov _ atm1 = fun _ -> Some atm1
    let changeWrite _ = None
    let changeAtm m atm =
        match atm with
        | P4Var _ | P4Reg _ -> match Map.tryFind atm m with
                               | Some t -> t
                               |_ -> atm
        | _ -> atm
    let rec loop l m acc =
        match l with
        | [] -> acc
        | instr :: tl ->
            match instr with
            | P4BOp (InstrBOp.Mov, atm1, atm2) ->
                let newAtm1 = changeAtm m atm1
                let newM = Map.change atm2 (changeMov atm2 newAtm1) m
                let newInstr = P4BOp (InstrBOp.Mov, newAtm1, atm2)
                loop tl newM (newInstr :: acc)
            | P4BOp (op, atm1, atm2) ->
                let (r, w) = p4InstrRW instr
                let newM = List.fold (fun m x -> Map.change x changeWrite m) m w
                let changeAtm' = changeAtm m
                let newInstr = P4BOp (op, changeAtm' atm1, atm2)
                loop tl newM (newInstr :: acc)
            | P4UOp (op, atm1) ->
                let (r, w) = p4InstrRW instr
                let newM = List.fold (fun m x -> Map.change x changeWrite m) m w
                let changeAtm' = changeAtm m
                let newAtm = if List.exists (fun x -> x = atm1) w
                             then atm1 else changeAtm' atm1
                let newInstr = P4UOp (op, newAtm)
                loop tl newM (newInstr :: acc)
            | P4CtrOp _ -> loop tl m (instr :: acc)
    loop l (Map []) [] |> List.rev
let createInfGraph (l : Pass4Instr list) =
    let handle1 instr (g:Graph<Pass4Atm>) (s:Set<Pass4Atm>) p =
        let (r, w) = p4InstrRW instr
        //printfn "read : %A, write: %A" r w
        let s' = Set.difference s (Set w)
        //printfn "s' : %A" s'
        let (s'', g') = List.fold
                             (fun (s, g') readV ->
                                let g'' = addVex g' readV
                                (
                                     Set.add readV s, 
                                     List.fold (fun g'' setV ->
                                        if (p readV setV) then
                                            //printfn "writeV : %A,setV : %A" readV setV
                                            addEdge g'' readV setV
                                        else g'')
                                        g'' [for i in s -> i]
                                 )
                             )
                            (s', g) r
        (s'', g')
    let rec loop l (g:Graph<Pass4Atm>) (s:Set<Pass4Atm>) =
        let pBasic v1 v2 = not (v1 = v2)
        match l with
        | [] -> g
        | [instr] -> handle1 instr g s pBasic |> snd
        | instrNow :: tl ->
            let (s' , g') = handle1 instrNow g s pBasic
            loop tl g' s'
    loop (List.rev l) (createGraph [||]) (Set [])
let regAlloc p4Prg =
    let assignToAtm m =
      let varColorLst = [ for KeyValue(r, c) in m -> (r, c) ] 
      let max = maxColor m
      if max = 0 then (fun color -> Impossible () |> raise) else
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
                      makeMapping tl regL arr
                  | hd :: tl' ->
                      arr.[color] <- hd |> P5Reg
                      makeMapping tl tl' arr
      let arr = makeMapping [0 .. max - 1] unuseReg (Array.create max (P5Reg Reg.Rax))
      fun color -> arr.[color]
    match p4Prg with
    | P4Program (info, blocks) ->
        let (label, info', blocksForAssign) = blocks.[0]
        let instrs = removeTemp blocksForAssign
        let infGraph = createInfGraph instrs
        let assignMap = coloringGraph infGraph
        let assignManager = assignToAtm assignMap
        let mapAtm atm =
            match atm with
            | P4Reg r -> P5Reg r |> Some
            | P4Var _ ->
                match Map.tryFind atm assignMap with
                | Some t ->
                    t |> assignManager |> Some
                | None -> None
            | P4Int i -> P5Int i |> Some
        let foldF l instr =
            if isUselessP4Instr instr then l
            else
                let (>>=) m f =
                    match m with
                    | Some t -> (f t)
                    | None -> l
                match instr with
                | P4BOp (op, atm1, atm2) ->
                    (mapAtm atm1)     >>=   (fun a1 ->
                    (mapAtm atm2)     >>=   (fun a2 ->
                    let p5Instr = P5BOp (op, a1, a2)
                    if isUselessP5Instr p5Instr then l else p5Instr :: l ))
                | P4UOp (op, atm1) ->
                    (mapAtm atm1) >>=   (fun a1 ->
                    P5UOp (op, a1) :: l )
                | P4CtrOp (op, t) -> P5CtrOp (op, t) :: l
        let instrs' = List.fold foldF [] instrs |> List.rev
        P5Program(info, [ (label, info', instrs')  ]) |> stateRet
        