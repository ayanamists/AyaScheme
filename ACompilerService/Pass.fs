module ACompilerService.Pass

open System
open Ast
open FSharpx.Collections
open Utils
open Coloring
open GlobalVar
    
type CompileState =  { mutable newVarIdx: Index;
                       mutable blockIds: Index
                       mutable typeInfo: Map<Index, ExprValueType> }
let emptyCompileState () = { newVarIdx = 0; blockIds = 0; typeInfo = Map [] }
let mutable compileState = emptyCompileState ()
let renewCompileState () =
    compileState <- emptyCompileState ()
let genSym () = 
    let idx = compileState.newVarIdx
    compileState.newVarIdx <- idx + 1
    idx
let getMaxIdxOfSym state =
     state.newVarIdx
let genBlockLabel () =
    let idx = compileState.blockIds
    compileState.blockIds <- idx + 1
    idx |> sprintf "block-%A"
let getType idx =
    Map.tryFind idx compileState.typeInfo
let assignType idx t =
    compileState.typeInfo <- compileState.typeInfo.Add (idx, t)
    
let getVecType v idx =
    match v with
    | VecType v' -> if v'.Length <= idx then (makeVecOutBound idx v') |> Result.Error
                    else v'.[idx] |> Result.Ok
    | t -> makeTypeError VecType t |> Result.Error
    
let setVecType v idx t' =
    match v with
    | VecType v' -> if v'.Length <= idx then (makeVecOutBound idx v') |> Result.Error
                    else v'.[idx] <- t'
                         () |> Result.Ok
    | t -> makeTypeError VecType t |> Result.Error

(*
    Pass 1: Lexical Address
*)

        
let makeVarNotBoundError i = (VarNotBoundError (sprintf "%A is Not bound" i))

(*
    Pass 1-1 : Lexical Addressing
    e.g. 
         in  -> (let ([a 10] [b 20])
                  (let ([c 11] [a 12])
                     (+ a b))
         out ->
                (let ([$0 10] [$1 20])
                  (let ([$2 11] [$3 12])
                    (+ $3 $1)))
*)

let lexicalAddress exp =
    let rec loop (env:Env<Identifier, Index>) exp = 
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
                        let idx = if (id = "_") then -1 else genSym ()
                        let! x = loop env exp 
                        return! handleList tl ((idx, x) :: nowL) (addEnv nowEnv id idx)
                    }
            let decomp l expr = List.fold (fun res (id, expr) -> 
                P1LetExp (id, expr, res)) expr l
            result {
                let! (nowL, nowEnv) = (handleList l [] env)
                let! nowExpr = loop nowEnv expr
                return decomp nowL nowExpr
            }
        | Expr.OpExp (op, expr1, expr2) ->
            result {
                let! e1 = loop env expr1 
                let! e2 = loop env expr2 
                return Pass1Out.P1OpExp (op, e1, e2 )
            }
        | Expr.IfExp (cond, ifTrue, ifFalse) ->
            result {
                let! e1 = loop env cond 
                let! e2 = loop env ifTrue 
                let! e3 = loop env ifFalse 
                return P1IfExp (e1, e2, e3)
            }
        | Expr.UOpExp (op, exp) ->
            result {
                let! exp' = loop env exp 
                return P1UOpExp (op, exp')
            }
        | Expr.Vector l -> result {
            let! l' = resultMap (fun x -> loop env x ) l
            return P1Vector (l', voidType)
            }
        | Expr.VectorRef (v, idx) ->
            result1 (loop env) v (fun v' -> P1VectorRef (v', idx))
        | Expr.VectorSet (v, idx, value) ->
            result2' (loop env) v value (fun v' value'  -> P1VectorSet (v', idx, value'))
        | Void _ -> P1Void () |> Result.Ok
    loop emptyEnv<Identifier, Index> exp

(*
    Pass 1-2 : type-check
*)

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

     
let rec typeCheck exp =
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
    | P1Int _ -> (exp, ExprValueType.IntType ()) |> Result.Ok
    | P1Bool _ -> (exp, ExprValueType.BoolType ()) |> Result.Ok
    | P1Void _ -> (exp, ExprValueType.VoidType ()) |> Result.Ok
    | P1Id i ->
        match getType i with
        | Some t -> (exp, t) |> Result.Ok
        | None -> Impossible () |> raise
    | P1LetExp (id, exp1, exp2) ->
        result {
            let! exp1', t1 = typeCheck exp1
            assignType id t1
            let! (exp2', t2) = typeCheck exp2
            return (P1LetExp (id, exp1', exp2'), t2)
        }
    | P1IfExp (cond, ifTrue, ifFalse) ->
        result {
            let! (cond', tCond) = typeCheck cond
            let! (ifTrue', tIfTrue) = typeCheck ifTrue
            let! (ifFalse', tIfFalse) = typeCheck ifFalse
            let! _ = typeEqualTo cond tCond (ExprValueType.BoolType ())
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
                makeBOp intType intType intType
            | ExprOp.And | ExprOp.Or ->
                makeBOp boolType boolType boolType
            | ExprOp.IEqB | ExprOp.IEq | ExprOp.IEqL | ExprOp.IB | ExprOp.IL ->
                makeBOp intType intType boolType
            | ExprOp.Eq ->
                 if not (expT1 = expT2) then (P1Bool false, boolType) |> Result.Ok 
                 else (P1OpExp (op, exp1', exp2'), boolType) |> Result.Ok
            | _ -> Impossible () |> raise
        ) (typeCheck exp2)
        ) (typeCheck exp1)
    | P1UOpExp (op, exp1) ->
        result {
            let! (exp1', t) = (typeCheck exp1 )
            match op with
            | ExprUOp.Not ->
                let! _ = typeEqualTo exp1' t boolType
                return (P1UOpExp (op, exp1'), boolType)
            | ExprUOp.VecLen -> 
                let! _ = typeEqualTo exp1' t boolType
                return (P1UOpExp (op, exp1'), intType)
            | _ -> return Impossible () |> raise
        }
    | P1Vector (l, _) ->
        result {
            let! l' = resultMap typeCheck l
            let tl = List.map snd l'
            let vl = List.map fst l'
            let t = VecType (Array.ofList tl)
            return (P1Vector (vl, t), t)
        }
    | P1VectorSet (v, idx, value) ->
        result {
            let! (v', tv) = typeCheck v
            let! (value', tvalue) = typeCheck value
            let! _ = setVecType tv idx tvalue
            return (P1VectorSet (v', idx, value'), voidType)
        }
    | P1VectorRef (v, idx) ->
        result {
            let! (v', tv) = typeCheck v
            let! tvv = getVecType tv idx
            return (P1VectorRef (v', idx), tvv)
        }
    | P1Allocate _
    | P1Collect _
    | P1Global _ -> Impossible () |> raise

(*
    Pass 1-3 : Expose Allocation
*)

let rec calcSpace t =
    match t with
    | VecType v' -> (Array.length v') * 8
    | _ -> 8

let makeVec l t  =
    let len = List.length l
    let tempIdxs = List.map (fun _ -> genSym ()) [1..len]
    let vecIdx = genSym ()
    let size = calcSpace t
    let vecSets = 
        List.foldBack (fun t e  -> 
            P1LetExp (-1, 
                    P1VectorSet (P1Id vecIdx, t, tempIdxs.[t] |> P1Id),
                    e))
            [0..(len - 1)]
            (P1Id vecIdx)
    let allocAndSet = P1LetExp (vecIdx, P1Allocate (size, t), vecSets)
    let test = 
        P1IfExp (
            P1OpExp (ExprOp.IL, 
                     P1OpExp (ExprOp.Add, P1Global freePtr, int32ToInt64 size |> P1Int),
                     P1Global fromEnd),
            P1Void (),
            P1Collect size
        )
    let testAndSet = P1LetExp (-1, test, allocAndSet)
    let allExp =
        List.foldBack
            (fun (id, e') e -> P1LetExp (id, e', e))
            (List.zip tempIdxs l)
            testAndSet
    allExp

let rec exposeAllocation exp =
    match exp with
    | P1Bool _ 
    | P1Int _ 
    | P1Id _ 
    | P1Void _ -> exp
    | P1LetExp (i, e1, e2) -> 
        P1LetExp (i, exposeAllocation e1, exposeAllocation e2)
    | P1OpExp (op, e1, e2) ->
        P1OpExp (op, exposeAllocation e1, exposeAllocation e2)
    | P1UOpExp (op, e1) ->
        P1UOpExp (op, exposeAllocation e1)
    | P1VectorRef (e, i) -> P1VectorRef (exposeAllocation e, i)
    | P1VectorSet (e1, i, e2) -> P1VectorSet (exposeAllocation e1, i, e2)
    | P1IfExp (e1, e2, e3) -> 
        P1IfExp ( exposeAllocation e1,
                  exposeAllocation e2,
                  exposeAllocation e3 )
    | P1Allocate _ 
    | P1Global _ 
    | P1Collect _ -> Impossible () |> raise
    | P1Vector (l, t) -> makeVec (List.map exposeAllocation l) t
    

let pass1 x = result {
    let! x = lexicalAddress x
    let! (x, _) = typeCheck x
    let x = exposeAllocation x
    return x
}

(*
    Approach 1 : Pass 2 Administrative Normal Form
*)

let isAtomPass1Out p1o = 
    match p1o with
    | P1Id _ -> true
    | P1Int _ -> true
    | P1Global _ -> true
    | _ -> false

let listToTuple1 l =
    match l with
    | [e1;] -> e1
    | _ -> Impossible () |> raise
let listToTuple2 l =
    match l with
    | [e1; e2] -> (e1, e2)
    | _ -> Impossible () |> raise
let listToTuple1f f l =
    listToTuple1 l |> f
let listToTuple2f f l =
    listToTuple2 l |> fun (e1, e2) -> f e1 e2
   
    
let anf exp = 
    let rec loop exp = 
        match exp with 
        | P1Int i -> P2Int i |> P2Atm 
        | P1Id i -> P2Var i |> P2Atm
        | P1Bool b -> P2Bool b |> P2Atm
        | P1Global g -> P2Global g |> P2Atm
        | P1Void _ -> P2Void ()
        | P1Collect bytes -> P2Collect bytes
        | P1Allocate (bytes, t) -> P2Allocate (bytes, t)
        | P1LetExp (id, exp1, exp2) -> 
            P2LetExp (id, loop exp1, loop exp2)
        | P1OpExp (op, expr1, expr2) -> 
            anfList ((fun e1 e2 -> P2OpExp (op, e1, e2)) |> listToTuple2f) [expr1; expr2]
        | P1UOpExp (op, expr1) ->
            anfList ((fun e1 -> P2UOpExp (op, e1)) |> listToTuple1f) [expr1]
        | P1IfExp (exp1, exp2, exp3) ->
            let exp1' = loop exp1
            let exp2' = loop exp2
            let exp3' = loop exp3
            P2IfExp (exp1', exp2', exp3')
        | P1Vector (l, t) -> Impossible () |> raise
        | P1VectorRef (v, i) ->
            let f x = match x with
                      | [ P2Var i' ] -> P2VectorRef( i', i)
                      | _ -> Impossible () |> raise 
            anfList f [v]
        | P1VectorSet (v, i, value) ->
            let f x = match x with
                      | [ P2Var v'; value' ] -> P2VectorSet (v', i, value')
                      | _ -> Impossible () |> raise
            anfList f [v; value]
    and anfList func expl =
        let rec handleExpl expl ids = 
            match expl with
            | [] -> List.rev ids |> func 
            | hd :: tl -> 
                match hd with
                | P1Id i -> handleExpl tl ((P2Var i) :: ids)
                | P1Int i -> handleExpl tl ((P2Int i) :: ids)
                | P1Bool b -> handleExpl tl ((P2Bool b) :: ids)
                | P1Global g -> handleExpl tl ((P2Global g) :: ids)
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

let transformP2 exp =
    match exp with
    | P2Atm atm -> let p3Atm = p2AtmToP3Atm atm in P3Atm p3Atm 
    | P2OpExp (op, atm1, atm2) -> let p3Opbp = p2OpExpToP3OpExp op atm1 atm2 in p3Opbp
    | P2UOpExp (op, atm1) -> p2UOpExpToP3 op atm1
    | P2Allocate (size, t) -> P3Allocate (size, t) 
    | P2VectorSet (v, idx, value) -> P3VectorSet (v, idx, p2AtmToP3Atm value) 
    | P2VectorRef (v, idx) -> P3VectorRef (v, idx)
    | _ -> Impossible () |> raise
let explicitControl exp =
    let mutable acc = []
    let addBlock instrs label = 
        acc <- (label, instrs) :: acc
    let addBlock' instrs = 
        acc <- (genBlockLabel (), instrs) :: acc
    let rec explicitTail exp = 
        match exp with
        | P2LetExp (idx, rhs, e) -> let cont = explicitTail e in explicitAssign idx rhs cont
        | P2IfExp (cond, ifTrue, ifFalse) -> 
            let ifTrue' = lazy explicitTail ifTrue
            let ifFalse' = lazy explicitTail ifFalse
            explicitCond cond ifTrue' ifFalse'
        | _ -> transformP2 exp |> P3Return
    and explicitAssign idx rhs cont = 
        match rhs with
        | P2LetExp (idx2, rhs2, e) -> 
            let contE = explicitAssign idx e cont
            explicitAssign idx2 rhs2 contE
        | P2IfExp (cond, ifTrue, ifFalse) ->
            let contLabel = genBlockLabel ()
            let ifCont = P3Goto contLabel |> P3TailGoto
            let ifTrue' = lazy explicitAssign idx ifTrue ifCont
            let ifFalse' = lazy explicitAssign idx ifFalse ifCont
            addBlock cont contLabel
            explicitCond cond ifTrue' ifFalse'
        | _ -> let rhs' = transformP2 rhs in P3Seq (P3Assign (idx, rhs'), cont)
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
        | P2Atm (P2Bool b) -> if b then ifTrue.Force () else ifFalse.Force ()
        | P2Atm (P2Var i) -> simpleExp (P3Var i |> P3Atm) ifTrue ifFalse
        | P2OpExp _  | P2UOpExp _ | P2VectorRef _ ->  simpleExp (transformP2 cond) ifTrue ifFalse
        | P2LetExp (var, value, exp) ->
            let cont = explicitCond exp ifTrue ifFalse
            explicitAssign var value cont
        | P2IfExp (cond', ifTrue', ifFalse') ->
            let gotoIfTrue = lazy ((makeGoto ifTrue).Force () |> P3TailGoto)
            let gotoIfFalse = lazy ((makeGoto ifFalse).Force () |> P3TailGoto)
            let ifTrue'' = lazy explicitCond ifTrue' gotoIfTrue gotoIfFalse
            let ifFalse'' = lazy explicitCond ifFalse' gotoIfTrue gotoIfFalse
            explicitCond cond' ifTrue'' ifFalse''
        | _ -> Impossible () |> raise
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

let makeVecRef idx =
    P4DeRef (Reg.Rax, 8 * (idx + 1))
let genVectorRef v idx leftAtm =
    [
        P4BOp (InstrBOp.Mov, P4Var v, P4Reg Reg.Rax)
        P4BOp (InstrBOp.Mov, makeVecRef idx, leftAtm)
    ]

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
            | P3VectorRef (v, idx') ->
                let thisCode = genVectorRef v idx' (P4Var idx)
                handleTail tail ( (List.rev thisCode) @ acc)
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