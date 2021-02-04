module TestPass

open System
open Xunit
open Pass
open Ast
open Parser

let toPass1 x = parseToAst x |> pass1
[<Fact>]
let ``Pass 1 test 1`` () = 
    let prg = "(let ([a 1] [b 2]) (+ a b))"
    let wanted = (
        Pass1Out.P1LetExp ([(0, Pass1Out.P1Int 1L); (1, Pass1Out.P1Int 2L)],
            Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 1 )),
        2)
    Assert.Equal(wanted, toPass1 prg)

[<Fact>]
let ``Pass 1 test 2`` () = 
    let prg = "(let ([a (let ([c 1]) (+ c 1))] [b 1]) (+ a b))"
    let wanted = (
        Pass1Out.P1LetExp ([(0, 
                             (Pass1Out.P1LetExp 
                                ([(1, Pass1Out.P1Int 1L)], 
                                 (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 1, Pass1Out.P1Int 1L)))));
                            (2, Pass1Out.P1Int 1L)], (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 2))),
        3)
    Assert.Equal(wanted, toPass1 prg)

[<Fact>]
let ``Pass 1 test 3`` () =
   let prg = "(+ a b)" 
   Assert.Throws(typeof<VarNotBound>, 
       Action(fun () -> toPass1 prg |> ignore))

let toPass2 x = 
    let (exp, idx) = toPass1 x
    pass2 exp idx

let prgList = 
    [|
        "(let ([a 1] [b 2]) (+ a b))"
        "(let ([a 1]) (/ (+ a 3) 4))" 
        "(let ([a 1]) (let ([b 2]) b))"
        "(let ([a 1]) (/ (+ (- a 10) 3) 4))" 
    |]

[<Fact>]
let ``Pass 2 test 1`` () =
    let prg = prgList.[0]
    let wanted = 
        P2LetExp (0, P2Int 1L |> P2Atm
                   , P2LetExp (1, P2Int 2L |> P2Atm, P2OpExp (ExprOp.Add ,(P2Var 0), (P2Var 1))))
    Assert.Equal(wanted, prg |> toPass2)

[<Fact>]
let ``Pass 2 test 2`` () =
    let prg = prgList.[1]
    let wanted = 
        P2LetExp (0
                 ,P2IntAtm 1L
                 ,P2LetExp (1
                           ,P2OpExp (ExprOp.Add, P2Var 0, P2Int 3L)
                           ,P2OpExp (ExprOp.Div, P2Var 1, P2Int 4L)))
    Assert.Equal(wanted, prg |> toPass2)

[<Fact>]
let ``Pass 2 test 3`` () =
    let prg = prgList.[2]
    let wanted =
        P2LetExp (0
                 ,P2IntAtm 1L
                 ,P2LetExp (1, P2IntAtm 2L, P2VarAtm 1))
    Assert.Equal(wanted, prg |> toPass2)

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
    Assert.Equal(wanted, prg |> toPass2)

let toPass3 x = toPass2 x |> pass3
[<Fact>]
let ``Pass 3 test 1`` () =
    let prg = prgList.[0]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq(P3Assign (1, p3IntAtm 2L)
                         ,P3Return (P3BPrim (ExprOp.Add, P3Var 0, P3Var 1))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    Assert.Equal(wanted, toPass3 prg)

[<Fact>]
let ``Pass 3 test 2`` () =
    let prg = prgList.[1]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (1, P3BPrim (ExprOp.Add, P3Var 0, P3Int 3L))
                          ,P3Return (P3BPrim (ExprOp.Div, P3Var 1, P3Int 4L))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    Assert.Equal(wanted, toPass3 prg)

[<Fact>]
let ``Pass 3 test 3`` () =
    let prg = prgList.[2]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (1, p3IntAtm 2L)
                          ,P3Return (p3VarAtm 1)))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    Assert.Equal(wanted, toPass3 prg)

[<Fact>]
let ``Pass 3 test 4 `` () =
    let prg = prgList.[3]
    let p3 = P3Seq (P3Assign (0, p3IntAtm 1L)
                   ,P3Seq (P3Assign (2, P3BPrim (ExprOp.Sub, P3Var 0, P3Int 10L))
                          ,P3Seq (P3Assign (1, P3BPrim (ExprOp.Add, P3Var 2, P3Int 3L))
                                 ,P3Return (P3BPrim (ExprOp.Div, P3Var 1, P3Int 4L)))))
    let wanted = P3Program (emptyInfo, [ (startLabel, p3) ])
    Assert.Equal(wanted, toPass3 prg)




