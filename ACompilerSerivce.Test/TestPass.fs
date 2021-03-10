module TestPass

open Xunit
open ACompilerService.Pass
open ACompilerService.Ast
open ACompilerService.Parser
open ACompilerService.Utils
open ACompilerService.IrParser

let printResult r =
    match r with
    | Result.Ok t -> printfn "%A" t
    | Result.Error e -> printfn "%A" e
let prgList = 
    [|
        "(let ([a 1] [b 2]) (+ a b))"                // 0
        "(let ([a 1]) (/ (+ a 3) 4))"                // 1
        "(let ([a 1]) (let ([b 2]) b))"              // 2
        "(let ([a 1]) (/ (+ (- a 10) 3) 4))"         // 3
        "(+ (* 10 1) 1)"                             // 4
        "(if (let [(a #t)] a) 1 2)"                  // 5
        "(+ (if #t 1 2) 3)"                          // 6
        "(eq? 1 #t)"                                 // 7
        "(if (if (< 1 2) (< 3 4) #t)                 
             (let ([a 1])
                  a)
             2)"                                     // 8
        "(if (and (< 3 4) (>= 5 7))
             1
             2)"                                     // 9
        "(if (< 1 2) 1 2)"                           // 10
        "(if (<= 1 2) 1 2)"                          // 11
        "(if (= 1 2) 1 2)"                           // 12
        "(if (> 1 2) 1 2)"                           // 13
        "(if (>= 1 2) 1 2)"                          // 14
        "(< 1 2)"                                    // 15
        "(<= 1 2)"                                   // 16
        "(= 1 2)"                                    // 17
        "(> 1 2)"                                    // 18
        "(>= 1 2)"                                   // 19
    |]

let toChecked x =
    let x' = parseToAst x
    renewCompileState ()
    result {
        let! x'' = lexicalAddress x'
        let! x''' = typeCheck x''
        return x''' |> snd
    }

[<Fact>]
let ``typeCheck Test 1`` () =
    let prg = "(let ([a 1]) a)"
    let wanted = Result.Ok ExprValueType.IntType
    Assert.Equal(wanted, toChecked prg)
    
[<Fact>]
let ``typeCheck Test 2`` () =
    let prg = "(let ([t #t]) t)"
    let wanted = Result.Ok ExprValueType.BoolType
    Assert.Equal(wanted, toChecked prg)
    
[<Fact>]
let ``typeCheck Test 3`` () =
    let prg = "(if 1 #t #t)"
    match (toChecked prg) with
    | Result.Error (TypeError _) -> Assert.True
    | _ -> Assert.False
    
[<Fact>]
let ``typeCheck Test 4`` () =
    let prg = "(if #t 1 #f)"
    match (toChecked prg) with
    | Result.Error (TypeError _) -> Assert.True
    | _ -> Assert.False
    
[<Fact>]
let ``typeCheck Test 5`` () =
    let prg = "(+ 1 #t)"
    match (toChecked prg) with
    | Result.Error (TypeError _) -> Assert.True
    | _ -> Assert.False
    
[<Fact>]
let ``typeCheck Test 6`` () =
    let prg = "(eq? 1 #t)"
    let res = ExprValueType.BoolType |> Result.Ok
    Assert.Equal(res, toChecked prg)
 
let toPass1 x =
    renewCompileState ()
    parseToAst x |> pass1
let testPass1 x = toPass1 x
let makeRes x = Result.Ok x
[<Fact>]
let ``Pass 1 test 1`` () = 
    let prg = "(let ([a 1] [b 2]) (+ a b))"
    let wanted = 
        Pass1Out.P1LetExp ([(0, Pass1Out.P1Int 1L); (1, Pass1Out.P1Int 2L)],
            Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 1 )) |> makeRes
    let res = testPass1 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 1 test 2`` () = 
    let prg = "(let ([a (let ([c 1]) (+ c 1))] [b 1]) (+ a b))"
    let wanted = 
        Pass1Out.P1LetExp ([(0, 
                             (Pass1Out.P1LetExp 
                                ([(1, Pass1Out.P1Int 1L)], 
                                 (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 1, Pass1Out.P1Int 1L)))));
                            (2, Pass1Out.P1Int 1L)], 
                           (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 2)))
        |> makeRes
    let res = testPass1 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 1 test 3`` () =
   let prg = "(+ a b)"
   match (testPass1 prg) with
   | Result.Error (VarNotBoundError _) -> Assert.True
   | _ -> Assert.False
   
[<Fact>]
let ``Pass 1 test 4`` () =
    let prg = prgList.[5]
    let wanted =
        P1IfExp (P1LetExp([(0, P1Bool true)], P1Id 0)
                ,P1Int 1L
                ,P1Int 2L
                ) |> makeRes
    let res = testPass1 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 1 test 5`` () =
    let prg = prgList.[7]
    let wanted = P1Bool false |> makeRes
    let res = testPass1 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 1 test 6`` () =
    let prg = prgList.[9]
    let wanted = 
        P1IfExp (P1IfExp (P1OpExp (ExprOp.IL, P1Int 3L, P1Int 4L)
                         ,P1OpExp (ExprOp.IEqB,P1Int 5L, P1Int 7L)
                         ,P1Bool false)
                ,P1Int 1L
                ,P1Int 2L) |> makeRes
    let res = testPass1 prg
    Assert.Equal(wanted, res)
let toPass2 x = Result.bind pass2 (toPass1 x) 
let testPass2 x = toPass2 x


[<Fact>]
let ``Pass 2 test 1`` () =
    let prg = prgList.[0]
    let wanted = 
        P2LetExp (0, P2Int 1L |> P2Atm
                   , P2LetExp (1, P2Int 2L |> P2Atm, P2OpExp (ExprOp.Add ,(P2Var 0), (P2Var 1))))
        |> makeRes
    let res = testPass2 prg
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
        |> makeRes
    let res = testPass2 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 2 test 3`` () =
    let prg = prgList.[2]
    let wanted =
        P2LetExp (0
                 ,P2IntAtm 1L
                 ,P2LetExp (1, P2IntAtm 2L, P2VarAtm 1))
        |> makeRes 
    let res = testPass2 prg
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
       |> makeRes
    let res = testPass2 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 2 test 5`` () =
    let prg = prgList.[6]
    let wanted =
        P2LetExp (0
                 ,P2IfExp (P2Atm (P2Bool true), P2IntAtm 1L, P2IntAtm 2L)
                 ,P2OpExp (ExprOp.Add, P2Var 0, P2Int 3L))
        |> makeRes
    Assert.Equal(wanted, testPass2 prg)
    
let toPass3 x = result {
    let! x' = toPass2 x 
    return! (pass3 x')
}
let testPass3 x = toPass3 x
[<Fact>]
let ``Pass 3 test 1`` () =
    let prg = prgList.[0]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq(P3Assign (1, p3IntAtm 2L)
                         ,P3Return (P3BPrim (ExprOp.Add, P3Var 0, P3Var 1))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ]) 
    let wanted' = wanted|> makeRes
    let p3Str = "
    _start:
        (var 0) = 1
        (var 1) = 2
        return +((var 0), (var 1))
    "
    let parseRes = parseP3 p3Str
    Assert.Equal(wanted, parseRes)
    let res = testPass3 prg
    Assert.Equal(wanted', res)

[<Fact>]
let ``Pass 3 test 2`` () =
    let prg = prgList.[1]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (1, P3BPrim (ExprOp.Add, P3Var 0, P3Int 3L))
                          ,P3Return (P3BPrim (ExprOp.Div, P3Var 1, P3Int 4L))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ]) 
    let wanted' = wanted|> makeRes
    let p3Str = "
    _start:
        (var 0) = 1
        (var 1) = +((var 0), 3)
        return /((var 1), 4)
    "
    let parseRes = parseP3 p3Str
    Assert.Equal(wanted, parseRes)
 
    let res = testPass3 prg
    Assert.Equal(wanted', res)

[<Fact>]
let ``Pass 3 test 3`` () =
    let prg = prgList.[2]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (1, p3IntAtm 2L)
                          ,P3Return (p3VarAtm 1)))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ]) |> makeRes
    let res = testPass3 prg
    Assert.Equal(wanted, res)
[<Fact>]
let ``Pass 3 test 4 `` () =
    let prg = prgList.[3]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (2, P3BPrim (ExprOp.Sub, P3Var 0, P3Int 10L))
                          ,P3Seq (P3Assign (1, P3BPrim (ExprOp.Add, P3Var 2, P3Int 3L))
                                 ,P3Return (P3BPrim (ExprOp.Div, P3Var 1, P3Int 4L)))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ]) |> makeRes
    let res =testPass3 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 3 test 5`` () =
    let prg = prgList.[5]
    let p3 = parseP3 "
    _start:
        (var 0) = #t
        if (var 0) goto label(block-0)
        goto label(block-1)
    block-1:
        return 2
    block-0:
        return 1
    "
    let wanted = p3 |> makeRes
    let res = testPass3 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 3 test 6`` () =
    let prg = prgList.[6]
    let p3 = parseP3 "
    _start:
        (var 0) = 1
        goto label(block-0)
    block-0:
        return +((var 0), 3)
    "
    let wanted = p3 |> makeRes
    let res = testPass3 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 3 test 7`` () =
    let prg = prgList.[8]
    let p3 = parseP3 "
    _start:
        if <(1, 2) goto label(block-2)
        goto label(block-0)
    block-2:
        if <(3, 4) goto label(block-0)
        goto label(block-1)
    block-1:
        return 2
    block-0:
        (var 0) = 1
        return (var 0)
   "
    let wanted = p3 |> makeRes
    let res = testPass3 prg
    Assert.Equal(wanted, res)
    
let toPass4 x = Result.bind pass4 (toPass3 x)
let testPass4 x = (toPass4 x) 
[<Fact>]
let ``Pass 4 test 1 `` () =
    let prg = prgList.[0]
    let p4 =
        [ 
            P4BOp (InstrBOp.Mov, P4Int 1L, P4Var 0)
            P4BOp (InstrBOp.Mov, P4Int 2L, P4Var 1)
            P4BOp (InstrBOp.Mov, P4Var 0, P4Reg Reg.Rax)
            P4BOp (InstrBOp.Add, P4Var 1, P4Reg Reg.Rax)
            P4CtrOp (InstrCtrOp.Jmp, conclusionLabel)
        ]
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ]) 
    let p4' = parseP4 "
        _start:
            mov 1, (var 0)
            mov 2, (var 1)
            mov (var 0), rax
            add (var 1), rax
            jmp conclusion
    "
    Assert.Equal(wanted, p4')
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)
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
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ]) |> makeRes
    let res = testPass4 prg 
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
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ]) |> makeRes
    let res = testPass4 prg 
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
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ]) |> makeRes
    let res = testPass4 prg 
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
    let wanted = P4Program (emptyInfo, [ (startLabel, emptyP4BlockInfo, p4) ]) |> makeRes
    let res = testPass4 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 4 test 6`` () =
    let prg = prgList.[5]
    let wanted = parseP4 "
    _start:
        mov 0, (var 0)
        test (var 0), (var 0)
        jnz block-0
        jmp block-1
    block-1:
        mov 2, rax
        jmp conclusion
    block-0:
        mov 1, rax 
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 7`` () =
    let prg = prgList.[10]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        jb block-0
        jmp block-1
    block-1:
        mov 2, rax
        jmp conclusion
    block-0:
        mov 1, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 8`` () =
    let prg = prgList.[11]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        jbe block-0
        jmp block-1
    block-1:
        mov 2, rax
        jmp conclusion
    block-0:
        mov 1, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 9`` () =
    let prg = prgList.[12]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        jz block-0
        jmp block-1
    block-1:
        mov 2, rax
        jmp conclusion
    block-0:
        mov 1, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 10`` () =
    let prg = prgList.[13]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        jg block-0
        jmp block-1
    block-1:
        mov 2, rax
        jmp conclusion
    block-0:
        mov 1, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 11`` () =
    let prg = prgList.[14]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        jge block-0
        jmp block-1
    block-1:
        mov 2, rax
        jmp conclusion
    block-0:
        mov 1, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 12`` () =
    let prg = prgList.[15]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        setb rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 13`` () =
    let prg = prgList.[16]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        setbe rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 14`` () =
    let prg = prgList.[17]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        sete rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 15`` () =
    let prg = prgList.[18]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        setg rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 16`` () =
    let prg = prgList.[19]
    let wanted = parseP4 "
    _start:
        cmp 1, 2
        setge rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

[<Fact>]
let ``Pass 4 test 17`` () =
    let prg = prgList.[9]
    let wanted = parseP4 "
    _start:
        cmp 3, 4
        jb block-2
        jmp block-1
    block-2:
        cmp 5, 7
        jge block-0
        jmp block-1
    block-1:
        mov 2, rax
        jmp conclusion
    block-0:
        mov 1, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted |> makeRes, res)

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
    let p4' = (removeTemp p4)
    let res = createInfGraph p4'
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
        
let testCtrFlow x = result {
    let! res = toPass4 x
    return (makeCtrFlowGraph res)
}

[<Fact>]
let ``CtrFlow test 1`` () =
    let prg = prgList.[1]
    let target =
        (createGraph [|
            ("_start", [|"conclusion"|])
        |] ) |> makeRes
    Assert.Equal(target, testCtrFlow prg)

[<Fact>]
let ``CtrFlow test 2`` () =
    let prg = prgList.[5]
    let target =
        createGraph [|
            ("_start", [|"block-0"; "block-1"|])
            ("block-0", [|"conclusion"|])
            ("block-1", [|"conclusion"|])
        |] |> makeRes
    let res = testCtrFlow prg
    Assert.Equal(target, res)

[<Fact>]
let ``CtrFlow test 3`` () =
    let prg = prgList.[9]
    let target =
        createGraph [|
            ("_start", [|"block-1"; "block-2"|])
            ("block-2", [|"block-0"; "block-1"|])
            ("block-1", [|"conclusion"|])
            ("block-0", [|"conclusion"|])
        |] |> makeRes
    let res = testCtrFlow prg
    Assert.Equal(target, res)

let pass5 = regAlloc
let toPass5 x = Result.bind pass5 (toPass4 x)
let testPass5 x = toPass5 x

[<Fact>]
let ``reg Alloc Test 1`` () =
    let prg = prgList.[0]
    let p5 = [ 
        P5BOp (InstrBOp.Mov, P5Int 1L, P5Reg Reg.Rax)
        P5BOp (InstrBOp.Add, P5Int 2L, P5Reg Reg.Rax)
        P5CtrOp (InstrCtrOp.Jmp, conclusionLabel)
    ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ]) |> makeRes
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
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ]) |> makeRes
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
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ]) |> makeRes
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
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ]) |> makeRes
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
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ]) |> makeRes
    let res = testPass5 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``reg Alloc Test 6`` () =
    let p4 = P4Program (emptyInfo , [ (startLabel, emptyInfo, regAllocTestCaseRemoveTemp)  ])
    let res = regAlloc p4
    let p5 = [
       P5BOp (InstrBOp.Mov, P5Int 1L, P5Reg Reg.Rcx)
       P5BOp (InstrBOp.Add, P5Int 7L, P5Reg Reg.Rcx)
       P5BOp (InstrBOp.Mov, P5Reg Reg.Rcx, P5Reg Reg.Rax)
       P5BOp (InstrBOp.Add, P5Int 42L, P5Reg Reg.Rax)
       P5UOp (InstrUOp.Neg, P5Reg Reg.Rcx)
       P5BOp (InstrBOp.Add, P5Reg Reg.Rcx, P5Reg Reg.Rax)
    ]
    let wanted = P5Program (emptyInfo , [ (startLabel, emptyInfo, p5) ]) |> makeRes
    Assert.Equal(wanted, res)