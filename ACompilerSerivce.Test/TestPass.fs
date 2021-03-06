module TestPass

open System
open Xunit
open ACompilerService.Pass
open ACompilerService.Ast
open ACompilerService.Parser
open ACompilerService.Utils

let toPass1 x = parseToAst x |> pass1
let testPass1 x = stateRun (toPass1 x) (emptyCompileState ()) 
[<Fact>]
let ``Pass 1 test 1`` () = 
    let prg = "(let ([a 1] [b 2]) (+ a b))"
    let wanted = 
        Pass1Out.P1LetExp ([(0, Pass1Out.P1Int 1L); (1, Pass1Out.P1Int 2L)],
            Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 1 ))
    let (res, _) = testPass1 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 1 test 2`` () = 
    let prg = "(let ([a (let ([c 1]) (+ c 1))] [b 1]) (+ a b))"
    let wanted = 
        Pass1Out.P1LetExp ([(0, 
                             (Pass1Out.P1LetExp 
                                ([(1, Pass1Out.P1Int 1L)], 
                                 (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 1, Pass1Out.P1Int 1L)))));
                            (2, Pass1Out.P1Int 1L)], (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 2)))
    let (res, _) = testPass1 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 1 test 3`` () =
   let prg = "(+ a b)" 
   Assert.Throws(typeof<VarNotBound>, 
       Action(fun () -> toPass1 prg |> ignore))

let toPass2 x = stateComb (toPass1 x) (fun x -> x |> pass2)
let testPass2 x = stateRun (toPass2 x) (emptyCompileState ())

let prgList = 
    [|
        "(let ([a 1] [b 2]) (+ a b))"
        "(let ([a 1]) (/ (+ a 3) 4))" 
        "(let ([a 1]) (let ([b 2]) b))"
        "(let ([a 1]) (/ (+ (- a 10) 3) 4))" 
        "(+ (* 10 1) 1)"
    |]

[<Fact>]
let ``Pass 2 test 1`` () =
    let prg = prgList.[0]
    let wanted = 
        P2LetExp (0, P2Int 1L |> P2Atm
                   , P2LetExp (1, P2Int 2L |> P2Atm, P2OpExp (ExprOp.Add ,(P2Var 0), (P2Var 1))))
    let (res, _) = testPass2 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 2 test 2`` () =
    let prg = prgList.[1]
    let wanted = 
        P2LetExp (0
                 ,P2IntAtm 1L
                 ,P2LetExp (1
                           ,P2OpExp (ExprOp.Add, P2Var 0, P2Int 3L)
                           ,P2OpExp (ExprOp.Div, P2Var 1, P2Int 4L)))
    let (res, _) = testPass2 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 2 test 3`` () =
    let prg = prgList.[2]
    let wanted =
        P2LetExp (0
                 ,P2IntAtm 1L
                 ,P2LetExp (1, P2IntAtm 2L, P2VarAtm 1))
    let (res, _) = testPass2 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 2 test 4`` () =
    let prg = prgList.[3] 
    let wanted = 
        P2LetExp (0
                 ,P2IntAtm 1L
                 ,P2LetExp (1
                           ,P2LetExp (2
                                    ,P2OpExp (ExprOp.Sub, P2Var 0, P2Int 10L)
                                    ,P2OpExp (ExprOp.Add, P2Var 2, P2Int 3L))
                           ,P2OpExp (ExprOp.Div, P2Var 1, P2Int 4L)))
    let (res, _) = testPass2 prg
    Assert.Equal(wanted, res)
    
let toPass3 x = stateComb (toPass2 x) (fun x -> x |> pass3)
let testPass3 x = stateRun (toPass3 x) (emptyCompileState ())
[<Fact>]
let ``Pass 3 test 1`` () =
    let prg = prgList.[0]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq(P3Assign (1, p3IntAtm 2L)
                         ,P3Return (P3BPrim (ExprOp.Add, P3Var 0, P3Var 1))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    let (res, _) = testPass3 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 3 test 2`` () =
    let prg = prgList.[1]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (1, P3BPrim (ExprOp.Add, P3Var 0, P3Int 3L))
                          ,P3Return (P3BPrim (ExprOp.Div, P3Var 1, P3Int 4L))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    let (res, _) = testPass3 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 3 test 3`` () =
    let prg = prgList.[2]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (1, p3IntAtm 2L)
                          ,P3Return (p3VarAtm 1)))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    let (res, _) = testPass3 prg
    Assert.Equal(wanted, res)
[<Fact>]
let ``Pass 3 test 4 `` () =
    let prg = prgList.[3]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (2, P3BPrim (ExprOp.Sub, P3Var 0, P3Int 10L))
                          ,P3Seq (P3Assign (1, P3BPrim (ExprOp.Add, P3Var 2, P3Int 3L))
                                 ,P3Return (P3BPrim (ExprOp.Div, P3Var 1, P3Int 4L)))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    let (res, _) =testPass3 prg 
    Assert.Equal(wanted, res)

let toPass4 x = state {
    let! a = toPass3 x
    return! (pass4 a)
}
let testPass4 x = stateRun (toPass4 x) (emptyCompileState ())
[<Fact>]
let ``Pass 4 test 1 `` () =
    let prg = prgList.[0]
    let p4 =
        [ 
            P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 0)
            P4BOp (InstrBOp.Mov, P4Int 2L, P4Var 1)
            P4BOp (InstrBOp.Mov, P4Var 1, P4Reg Reg.Rax)
            P4BOp (InstrBOp.Add, P4Var 0, P4Reg Reg.Rax)
            P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
        ]
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ])
    let (res, _) = testPass4 prg 
    Assert.Equal(wanted, res)
[<Fact>]
let ``Pass 4 test 2 `` () =
    let prg = prgList.[1]
    let p4 =
        [ 
            P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 0)
            P4BOp (InstrBOp.Mov, P4Var 0, P4Var 1)
            P4BOp (InstrBOp.Add, P4Int 3L, P4Var 1)
            P4BOp (InstrBOp.Mov, P4Var 1, P4Reg Reg.Rax)
            P4UOp (InstrUOp.IDiv, P4Int 4L )
            P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
        ]
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ])
    let (res, _) = testPass4 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 4 test 3 `` () =
    let prg = prgList.[2]
    let p4 =
        [ 
            P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 0)
            P4BOp (InstrBOp.Mov, P4Int 2L, P4Var 1)
            P4BOp (InstrBOp.Mov, P4Var 1, P4Reg Reg.Rax)
            P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
        ]
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ])
    let (res, _) = testPass4 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 4 test 4 `` () =
    let prg = prgList.[3]
    let p4 =
        [ 
            P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 0)
            P4BOp (InstrBOp.Mov, P4Var 0, P4Var 2)
            P4BOp (InstrBOp.Sub, P4Int 10L, P4Var 2)
            P4BOp (InstrBOp.Mov, P4Var 2, P4Var 1)
            P4BOp (InstrBOp.Add, P4Int 3L, P4Var 1)
            P4BOp (InstrBOp.Mov, P4Var 1, P4Reg Reg.Rax)
            P4UOp (InstrUOp.IDiv, P4Int 4L)
            P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
        ]
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ])
    let (res, _) = testPass4 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 4 test 5`` () = 
    let prg = prgList.[4]
    let p4 = 
        [
            P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Var 1)
            P4BOp (InstrBOp.Mov, P4Int 10L, P4Reg Reg.Rax)
            P4UOp (InstrUOp.IMul, P4Int 1L)
            P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Var 0)
            P4BOp (InstrBOp.Mov, P4Var 1, P4Reg Reg.Rax)
            P4BOp (InstrBOp.Mov, P4Var 0, P4Reg Reg.Rax)
            P4BOp (InstrBOp.Add, P4Int 1L, P4Reg Reg.Rax)
            P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
        ]
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ])
    let (res, _) = testPass4 prg 
    Assert.Equal(wanted, res)
    
let regAllocSTestCase = [
    P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 0)
    P4BOp (InstrBOp.Mov, P4Int 42L, P4Var 1)
    P4BOp (InstrBOp.Mov, P4Var 0, P4Var 2)
    P4BOp (InstrBOp.Add, P4Int 7L, P4Var 2)
    P4BOp (InstrBOp.Mov, P4Var 2, P4Var 3)
    P4BOp (InstrBOp.Mov, P4Var 2, P4Var 4)
    P4BOp (InstrBOp.Add, P4Var 1, P4Var 4)
    P4BOp (InstrBOp.Mov, P4Var 3, P4Var 5)
    P4UOp (InstrUOp.Neg, P4Var 5)
    P4BOp (InstrBOp.Mov, P4Var 4, P4Reg Reg.Rax)
    P4BOp (InstrBOp.Add, P4Var 5, P4Reg Reg.Rax)
]
let regAllocTestCaseRemoveTemp = [
    P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 0)
    P4BOp (InstrBOp.Mov, P4Int 42L, P4Var 1)
    P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 2)
    P4BOp (InstrBOp.Add, P4Int 7L, P4Var 2)
    P4BOp (InstrBOp.Mov, P4Var 2, P4Var 3)
    P4BOp (InstrBOp.Mov, P4Var 2, P4Var 4)
    P4BOp (InstrBOp.Add, P4Int 42L, P4Var 4)
    P4BOp (InstrBOp.Mov, P4Var 2, P4Var 5)
    P4UOp (InstrUOp.Neg, P4Var 5)
    P4BOp (InstrBOp.Mov, P4Var 4, P4Reg Reg.Rax)
    P4BOp (InstrBOp.Add, P4Var 5, P4Reg Reg.Rax)
]
let regAllocTestCaseInfGraph = createGraph [|
    (P4Reg Reg.Rax, [| P4Var 5 |])
    (P4Var 4, [| P4Var 5 ; P4Var 2|])
    (P4Var 2, [| P4Var 4 |])
    (P4Var 5, [| P4Reg Reg.Rax ; P4Var 4 |])
|]

let testCreateInfGraph x = removeTemp x |> createInfGraph

[<Fact>]
let ``Create InfGraph Test 1`` () =
    let p4 = [
        P4BOp (InstrBOp.Mov, P4Int 10L, P4Var 1)
        P4BOp (InstrBOp.Mov, P4Var 1, P4Var 0)
        P4BOp (InstrBOp.Add, P4Var 1, P4Var 2)
        P4BOp (InstrBOp.Sub, P4Var 0, P4Var 1)
    ]
    let wanted = createGraph [|
        (P4Var 1, [|P4Var 2|])
        (P4Var 2, [|P4Var 1|])
    |]
    let res = createInfGraph (removeTemp p4)
    Assert.Equal(wanted, res)

[<Fact>]
let ``create InfGraph Test 2`` () =
    let res = testCreateInfGraph regAllocTestCaseRemoveTemp
    let wanted = regAllocTestCaseInfGraph
    Assert.Equal(wanted, res)
    
[<Fact>]
let ``remove Temp Test 1`` () =
    let p4 = [
        P4BOp (InstrBOp.Mov, P4Var 0, P4Var 1)
        P4BOp (InstrBOp.Mov, P4Var 1, P4Var 2)
        P4BOp (InstrBOp.Mov, P4Var 2, P4Var 3)
    ]
    let wanted = [
         P4BOp (InstrBOp.Mov, P4Var 0, P4Var 1)
         P4BOp (InstrBOp.Mov, P4Var 0, P4Var 2)
         P4BOp (InstrBOp.Mov, P4Var 0, P4Var 3)
    ]
    let res = removeTemp p4
    Assert.Equal<Pass4Instr list>(res, wanted)

[<Fact>]
let  ``remove Temp Test 2`` () =
    let p4 = [
        P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Var 1)
        P4BOp (InstrBOp.Mov, P4Int 10L, P4Reg Reg.Rax)
        P4UOp (InstrUOp.IMul, P4Int 1L)
        P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Var 0)
        P4BOp (InstrBOp.Mov, P4Var 1, P4Reg Reg.Rax)
        P4BOp (InstrBOp.Mov, P4Var 0, P4Reg Reg.Rax)
        P4BOp (InstrBOp.Add, P4Int 1L, P4Reg Reg.Rax)
        P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
    ]
    let wanted = [
        P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Var 1)
        P4BOp (InstrBOp.Mov, P4Int 10L, P4Reg Reg.Rax)
        P4UOp (InstrUOp.IMul, P4Int 1L)
        P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Var 0)
        P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Reg Reg.Rax)
        P4BOp (InstrBOp.Mov, P4Reg Reg.Rax, P4Reg Reg.Rax)
        P4BOp (InstrBOp.Add, P4Int 1L, P4Reg Reg.Rax)
        P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
    ]
    let res = removeTemp wanted
    Assert.Equal<Pass4Instr list>(wanted, res)

[<Fact>]
let ``remove Temp test 3`` () =
    let wanted = regAllocTestCaseRemoveTemp
    let res = removeTemp regAllocSTestCase
    Assert.Equal<Pass4Instr list>(wanted, res)
        
let pass5 = regAlloc
let toPass5 x = state {
    let! t = toPass4 x
    return! pass5 t}
let testPass5 x = stateRun (toPass5 x) (emptyCompileState ()) |> fst

[<Fact>]
let ``reg Alloc Test 1`` () =
    let prg = prgList.[0]
    let p5 = [ 
        P5BOp (InstrBOp.Mov, P5Int 2L, P5Reg Reg.Rax)
        P5BOp (InstrBOp.Add, P5Int 1L, P5Reg Reg.Rax)
        P5CtrOp (InstrCtrOp.Jmp, conclusionLabel)
    ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ])
    let res = testPass5 prg
    Assert.Equal(wanted, res)
    
[<Fact>]
let ``reg Alloc Test 2`` () =
    let prg = prgList.[1]
    let p5 = 
        [ 
            P5BOp (InstrBOp.Mov, P5Int 1L, P5Reg Reg.Rax)
            P5BOp (InstrBOp.Add, P5Int 3L, P5Reg Reg.Rax)
            P5UOp (InstrUOp.IDiv, P5Int 4L )
            P5CtrOp (InstrCtrOp.Jmp, conclusionLabel)
        ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ])
    let res = testPass5 prg
    Assert.Equal(wanted, res)
    

[<Fact>]
let ``reg Alloc Test 3`` () =
    let prg = prgList.[2]
    let p5 = 
         [ 
             P5BOp (InstrBOp.Mov, P5Int 2L, P5Reg Reg.Rax)
             P5CtrOp (InstrCtrOp.Jmp, conclusionLabel)
         ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ])
    let res = testPass5 prg
    Assert.Equal(wanted, res)
    
[<Fact>]
let ``reg Alloc Test 4`` () =
    let prg = prgList.[3]
    let p5 =
         [ 
             P5BOp (InstrBOp.Mov, P5Int 1L, P5Reg Reg.Rax)
             P5BOp (InstrBOp.Sub, P5Int 10L, P5Reg Reg.Rax)
             P5BOp (InstrBOp.Add, P5Int 3L, P5Reg Reg.Rax)
             P5UOp (InstrUOp.IDiv, P5Int 4L)
             P5CtrOp (InstrCtrOp.Jmp, conclusionLabel)
         ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ])
    let res = testPass5 prg
    Assert.Equal(wanted, res)
    
[<Fact>]
let ``reg Alloc Test 5`` () =
    let prg = prgList.[4]
    let p5 = [
         P5BOp (InstrBOp.Mov, P5Int 10L, P5Reg Reg.Rax)
         P5UOp (InstrUOp.IMul, P5Int 1L)
         P5BOp (InstrBOp.Add, P5Int 1L, P5Reg Reg.Rax)
         P5CtrOp (InstrCtrOp.Jmp, conclusionLabel)
     ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ])
    let res = testPass5 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``reg Alloc Test 6`` () =
    let p4 = P4Program (emptyInfo , [ (startLabel, emptyInfo, regAllocTestCaseRemoveTemp)  ]) |> stateRet
    let res = stateRun (stateComb p4 regAlloc) (emptyCompileState ()) |> fst
    let p5 = [
       P5BOp (InstrBOp.Mov, P5Int 1L, P5Reg Reg.Rcx)
       P5BOp (InstrBOp.Add, P5Int 7L, P5Reg Reg.Rcx)
       P5BOp (InstrBOp.Mov, P5Reg Reg.Rcx, P5Reg Reg.Rax)
       P5BOp (InstrBOp.Add, P5Int 42L, P5Reg Reg.Rax)
       P5UOp (InstrUOp.Neg, P5Reg Reg.Rcx)
       P5BOp (InstrBOp.Add, P5Reg Reg.Rcx, P5Reg Reg.Rax)
    ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ])
    Assert.Equal(wanted, res)