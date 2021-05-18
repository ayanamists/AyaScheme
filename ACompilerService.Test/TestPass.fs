module TestPass

open System.Reflection.Metadata
open ACompilerService
open Xunit
open ACompilerService.Pass
open ACompilerService.Ast
open ACompilerService.Parser
open ACompilerService.Utils
open ACompilerService.IrParser
open ACompilerService.Asm

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
        "(vector (vector 1 2 3 4) 2 3 4)"            // 20
        "(vector-ref (vector 1 2 3 4) 1)"            // 21
        "(vector-set! (vector 1 2 3 4) 1 10)"        // 22
    |]

let toChecked x =
    renewCompileState ()
    result {
        let! x' = parseToAst x
        let! x'' = lexicalAddress x'
        let! x''' = typeCheck x''
        return x''' |> snd
    }

[<Fact>]
let ``typeCheck Test 1`` () =
    let prg = "(let ([a 1]) a)"
    let wanted = Result.Ok (ExprValueType.IntType ())
    Assert.Equal(wanted, toChecked prg)
    
[<Fact>]
let ``typeCheck Test 2`` () =
    let prg = "(let ([t #t]) t)"
    let wanted = Result.Ok (ExprValueType.BoolType ())
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
    let res = ExprValueType.BoolType () |> Result.Ok
    Assert.Equal(res, toChecked prg)
 
[<Fact>]
let ``typeCheck Test 7`` () =
    let prg = "(vector 1 2 3 4)"
    let res = ExprValueType.VecType [| intType; intType; intType; intType |]
    Assert.Equal(res, toChecked prg |> getResult)
    
[<Fact>]
let ``typeCheck Test 8`` () =
    let prg = "
        (let ([a (vector 1 2 3 4)])
          (let ([b (vector-ref a 1)])
            b))
    "
    let res = intType
    Assert.Equal(res, toChecked prg |> getResult)
    
[<Fact>]
let ``typeCheck Test 9`` () =
     let prg = "
         (let ([a (vector 1 2 3 4)])
           (let ([_ (vector-set! a 1 #t)])
             (let ([b (vector-ref a 1)])
               b)))
     "
     let res = boolType
     Assert.Equal(res, toChecked prg |> getResult)   
let toPass1 x =
    renewCompileState ()
    Result.bind pass1 (parseToAst x) 
let testPass1 x = toPass1 x |> getResult
let makeRes x = x
let parseP1T x = parseP1 x |> getResult
[<Fact>]
let ``Pass 1 test 1`` () = 
    let prg = "(let ([a 1] [b 2]) (+ a b))"
    let wanted = parseP1T "
        (let ([$0 1])
          (let ([$1 2])
            (+ $0 $1)))
    "
    let res = testPass1 prg
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 1 test 2`` () = 
    let prg = "(let ([a (let ([c 1]) (+ c 1))] [b 1]) (+ a b))"
    let wanted = "
        (let ([$0 (let ([$1 1]) (+ $1 1))])
          (let ([$2 1])
            (+ $0 $2)))
    "
    let res = testPass1 prg
    Assert.Equal(wanted |> parseP1T, res)

[<Fact>]
let ``Pass 1 test 3`` () =
   let prg = "(+ a b)"
   match (toPass1 prg) with
   | Result.Error (VarNotBoundError _) -> Assert.True
   | _ -> Assert.False
   
[<Fact>]
let ``Pass 1 test 4`` () =
    let prg = prgList.[5]
    let wanted =
        P1IfExp (P1LetExp(0, P1Bool true, P1Id 0)
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


[<Fact>]
let ``Pass 1 test 7`` () = 
    let prg = prgList.[20]
    let wanted = parseP1T "
(let ([$5 (let ([$0 1]) (let ([$1 2]) (let ([$2 3]) (let ([$3 4])
                    (let ([_ (if (< (+ (global free_ptr) 32)
                                    (global fromspace_end))
                                 (void)
                                 (collect 32))])
                      (let ([$4 (allocate 32 (int int int int))])
                        (let ([_ (vector-set! $4 0 $0)])
                          (let ([_ (vector-set! $4 1 $1)])
                            (let ([_ (vector-set! $4 2 $2)])
                              (let ([_ (vector-set! $4 3 $3)])
                                $4))))))))))])
  (let ([$6 2])
    (let ([$7 3])
      (let ([$8 4])
        (let ([_ (if (< (+ (global free_ptr) 32)
                        (global fromspace_end))
                     (void)
                     (collect 32))])
          (let ([$9 (allocate 32 ((int int int int) int int int))])
            (let ([_ (vector-set! $9 0 $5)])
              (let ([_ (vector-set! $9 1 $6)])
                (let ([_ (vector-set! $9 2 $7)])
                  (let ([_ (vector-set! $9 3 $8)])
                    $9))))))))))
    "
    Assert.Equal(wanted, testPass1 prg)

let toPass2 x = Result.bind pass2 (toPass1 x) 
let testPass2 x = toPass2 x |> getResult
let parseP2T x = parseP2 x |> getResult
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
    
[<Fact>]
let ``Pass 2 test 6`` () = 
    let prg = prgList.[21]
    let wanted = parseP2T "
(let ([$5 (let ([$0 1])
            (let ([$1 2])
              (let ([$2 3])
                (let ([$3 4])
                  (let ([_ (if (let ([$6 (+ (global free_ptr) 32)])
                                 (< $6 (global fromspace_end)))
                               (void)
                               (collect 32))])
                    (let ([$4 (allocate 32 (int int int int))])
                      (let ([_ (vector-set! $4 0 $0)])
                        (let ([_ (vector-set! $4 1 $1)])
                          (let ([_ (vector-set! $4 2 $2)])
                            (let ([_ (vector-set! $4 3 $3)])
                              $4))))))))))])
  (vector-ref $5 1))
    "
    Assert.Equal(wanted, testPass2 prg)


let toPass3 x = result {
    let! x' = toPass2 x 
    return! (pass3 x')
}
let testPass3 x = toPass3 x |> getResult
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
let testPass4 x = (toPass4 x) |> getResult
[<Fact>]
let ``Pass 4 test 1 `` () =
    let prg = prgList.[0]
    let p4' = parseP4 "
        conclusion:
        _start:
            mov 1, (var 0)
            mov 2, (var 1)
            mov (var 0), rax
            add (var 1), rax
            jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(p4' , res)
[<Fact>]
let ``Pass 4 test 2 `` () =
    let prg = prgList.[1]
    let wanted = parseP4 "
        conclusion:
        _start:
            mov 1, (var 0)
            mov (var 0), (var 1)
            add 3, (var 1)
            mov (var 1), rax
            cqto rdx
            idiv 4
            jmp conclusion
            
    "
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
    let wanted = parseP4 "
        conclusion:
        _start:
            mov 1, (var 0)
            mov 2, (var 1)
            mov (var 1), rax
            jmp conclusion
    "        
    let res = testPass4 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 4 test 4 `` () =
    let prg = prgList.[3]
    let wanted = parseP4 "
    conclusion:
    _start:
        mov 1, (var 0)
        mov (var 0), (var 2)
        sub 10, (var 2)
        mov (var 2), (var 1)
        add 3, (var 1)
        mov (var 1), rax
        cqto rdx
        idiv 4
        jmp conclusion 
    "
    let res = testPass4 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 4 test 5`` () = 
    let prg = prgList.[4]
    let wanted = parseP4 "
    conclusion:
    _start:
        mov 10, rax
        imul 1
        mov rax, (var 0)
        mov (var 0), rax
        add 1, rax
        jmp conclusion
    "
    let res = testPass4 prg 
    Assert.Equal(wanted, res)

[<Fact>]
let ``Pass 4 test 6`` () =
    let prg = prgList.[5]
    let wanted = parseP4 "
    conclusion:
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
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 7`` () =
    let prg = prgList.[10]
    let wanted = parseP4 "
    conclusion:
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
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 8`` () =
    let prg = prgList.[11]
    let wanted = parseP4 "
    conclusion:
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
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 9`` () =
    let prg = prgList.[12]
    let wanted = parseP4 "
    conclusion:
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
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 10`` () =
    let prg = prgList.[13]
    let wanted = parseP4 "
    conclusion:
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
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 11`` () =
    let prg = prgList.[14]
    let wanted = parseP4 "
    conclusion:
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
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 12`` () =
    let prg = prgList.[15]
    let wanted = parseP4 "
    conclusion:
    _start:
        cmp 1, 2
        setg rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 13`` () =
    let prg = prgList.[16]
    let wanted = parseP4 "
    conclusion:
    _start:
        cmp 1, 2
        setge rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 14`` () =
    let prg = prgList.[17]
    let wanted = parseP4 "
    conclusion:
    _start:
        cmp 1, 2
        sete rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 15`` () =
    let prg = prgList.[18]
    let wanted = parseP4 "
    conclusion:
    _start:
        cmp 1, 2
        setb rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 16`` () =
    let prg = prgList.[19]
    let wanted = parseP4 "
    conclusion:
    _start:
        cmp 1, 2
        setbe rax
        movzb rax, rax
        jmp conclusion
    "
    let res = testPass4 prg
    Assert.Equal(wanted , res)

[<Fact>]
let ``Pass 4 test 17`` () =
    let prg = prgList.[9]
    let wanted = parseP4 "
    conclusion:
    _start:
        cmp 3, 4
        jg block-2
        jmp block-1
    block-2:
        cmp 5, 7
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
    Assert.Equal(wanted , res)
        
let testCtrFlow' x = result {
    let! res = toPass4 x
    return (makeCtrFlowGraph res)
}

let testCtrFlow x = testCtrFlow' x |> getResult

[<Fact>]
let ``CtrFlow test 1`` () =
    let prg = prgList.[1]
    let target =
        (createGraph [|
            ("_start", [|"conclusion"|])
            ("conclusion", [||])
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
            ("conclusion", [||])
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
            ("conclusion", [||])
        |] |> makeRes
    let res = testCtrFlow prg
    Assert.Equal(target, res)

let testMakeLiveSets x = makeLiveSets x

let regAllocTestCase1 = parseP4 "
                            conclusion:
                            _start:
                                mov 1, (var 0)
                                mov 2, (var 1)
                                add (var 0), (var 1)
                                mov (var 1), (var 2)
                                sub (var 2), (var 0)
                                mov (var 1), (var 3)
                                mov (var 1), (var 4)
                                cmp (var 1), rax
                                jz block-0
                                jmp block-1
                            block-0:
                                mov (var 3), rax
                                jmp conclusion
                            block-1:
                                mov (var 4), rax
                                jmp conclusion
                            "
[<Fact>]
let ``make live Test 1`` () = Assert.Equal(true, true)

let testCreateInfGraph' x = result {
    let! x = toPass4 x
    return pass4ToInfGraph x
}

let testCreateInfGraph x = testCreateInfGraph' x |> getResult
[<Fact>]
let ``create Inf Graph Test 1`` () =
    let prg = prgList.[0]
    let g = createGraph [|
        (P4Var 0, [|P4Var 1|])
        (P4Var 1, [|P4Var 0; P4Reg Reg.Rax|])
        (P4Reg Reg.Rax, [|P4Var 1|])
    |]
    Assert.Equal(g, testCreateInfGraph prg)

[<Fact>]
let ``Create Inf Graph Test 2`` () =
    let prg = prgList.[5]
    let g = createGraph [||]
    Assert.Equal(g, testCreateInfGraph prg)

[<Fact>]
let ``Create Inf Graph Test 3`` () =
    let prg = regAllocTestCase1
    let g = createGraph [|
        (P4Var 0, [|P4Var 1; P4Var 2; P4Reg Reg.Rax|])
        (P4Var 1, [|P4Var 0; P4Reg Reg.Rax|])
        (P4Var 2, [|P4Var 0; P4Reg Reg.Rax|])
        (P4Var 3, [|P4Var 4; P4Reg Reg.Rax|])
        (P4Var 4, [|P4Var 3; P4Reg Reg.Rax|])
        (P4Reg Reg.Rax, [|P4Var 0; P4Var 1; P4Var 2; P4Var 3; P4Var 4|])
    |]
    Assert.Equal(g, pass4ToInfGraph prg)
    
    
let pass5 = regAlloc
let toPass5 x = Result.bind pass5 (toPass4 x)
let testPass5 x = toPass5 x |> getResult

[<Fact>]
let ``reg Alloc Test 1`` () =
    let prg = prgList.[0]
    let p5 = parseP5 "
    conclusion:
    _start:
        mov 1, rax
        mov 2, rcx
        add rcx, rax
        jmp conclusion
    " 
    let res = testPass5 prg
    Assert.Equal(p5 , res)
    
[<Fact>]
let ``reg Alloc Test 2`` () =
    let prg = prgList.[1]
    let wanted = parseP5 "
    conclusion:
    _start:
        mov 1, rax
        add 3, rax
        cqto rdx
        idiv 4
        jmp conclusion
    "
    Assert.Equal(wanted, testPass5 prg)
    

[<Fact>]
let ``reg Alloc Test 3`` () =
    let prg = prgList.[3]
    let p5 = parseP5 "
    conclusion:
    _start:
        mov 1, rax
        sub 10, rax
        add 3, rax
        cqto rdx
        idiv 4
        jmp conclusion
    "
    let res = testPass5 prg
    Assert.Equal(p5, res)
    
[<Fact>]
let ``reg Alloc Test 4`` () =
    let prg = regAllocTestCase1
    let res = pass5 prg |> getResult
    Assert.True
    
(*
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
*)

let testPass6 x = patchInstructions x |> getResult
[<Fact>]
let ``patchInstr test 1`` () =
    let prg = parseP5 "
    _start:
        add mem(rbp, -8), mem(rbp, -16)
    "
    let wanted = parseP5 "
    _start:
        mov mem(rbp, -8), r8
        add r8, mem(rbp, -16)
    "
    Assert.Equal(wanted, testPass6 prg)
    
[<Fact>]
let ``patchInstr test 2`` () =
    let prg = parseP5 "
    _start:
        cmp 1, 2
        jz block-0
        jmp block-1
    "
    let wanted = parseP5 "
    _start:
        mov 2, r8
        cmp 1, r8
        jz block-0
        jmp block-1
    "
    Assert.Equal(wanted, testPass6 prg)
    
[<Fact>]
let ``patchInstr test 3`` () =
    let prg = parseP5 "
    _start:
        cmp 11111111111111, 10000000000000
        jz block-0
        jmp block-1
    "
    let wanted = parseP5 "
    _start:
        mov 10000000000000, r8
        mov 11111111111111, r9
        cmp r9, r8
        jz block-0
        jmp block-1
    "
    Assert.Equal(wanted, testPass6 prg)
    
let pass6 = patchInstructions
let toPass6 x = result {
    let! x' = toPass5 x
    return! pass6 x'
}
let testPass6' x = toPass6 x |> getResult
[<Fact>]
let ``Asm test 1`` () =
    let prg = prgList.[10]
    let res = assemble (testPass6' prg)
    let asmStr = printAsm res
    Assert.True
    
[<Fact>]
let ``Asm test 2`` () =
    let prg =
        parseP5'' "
          conclusion:
          _start:
          mov -1, mem(rbp, -8)
          mov mem(rbp, -8), rax
          jmp conclusion " {stackSize = 8}
    let res = assemble prg
    let asmStr = printAsm res
    Assert.True