module TestPass

open System
open Xunit
open Pass
open Ast
open Parser

let toPass1 x = parseToAst x |> lexicalAddress
[<Fact>]
let ``Pass 1 test 1`` () = 
    let prg = "(let ([a 1] [b 2]) (+ a b))"
    let wanted = 
        Pass1Out.P1LetExp ([(0, Pass1Out.P1Int 1L); (1, Pass1Out.P1Int 2L)],
            Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 1 ))
    Assert.Equal(wanted, toPass1 prg)

[<Fact>]
let ``Pass 1 test 2`` () = 
    let prg = "(let ([a (let ([c 1]) (+ c 1))] [b 1]) (+ a b))"
    let wanted = 
        Pass1Out.P1LetExp ([(0, 
                             (Pass1Out.P1LetExp 
                                ([(0, Pass1Out.P1Int 1L)], 
                                 (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Int 1L)))));
                            (1, Pass1Out.P1Int 1L)], (Pass1Out.P1OpExp (ExprOp.Add, Pass1Out.P1Id 0, Pass1Out.P1Id 1)))
    Assert.Equal(wanted, toPass1 prg)

[<Fact>]
let ``Pass 1 test 3`` () =
   let prg = "(+ a b)" 
   Assert.Throws(typeof<VarNotBound>, 
       Action(fun () -> toPass1 prg |> ignore))
