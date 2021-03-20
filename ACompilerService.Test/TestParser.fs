module TestParser

open System
open Xunit
open ACompilerService.Parser
open ACompilerService.Ast
open ACompilerService.Utils

let testFunc data wanted = 
   match wanted , (parse data) with
   | Error _, Error _ -> Assert.True(true)
   | Ok res1, Ok res2 -> Assert.Equal(res1, res2) 
   | _ , Error y -> printfn "Should be %A, but occur error : %A" wanted y; Assert.True(false)
   | Error x, Ok y -> printfn "Should occur error, but is %A" y; Assert.True(false)

[<Fact>]
let ``test 1`` () = testFunc "()" ( Error "")

[<Fact>]
let ``test 2`` () = testFunc "1" (Ok (SInt 1L))

[<Fact>]
let ``test 3`` () = testFunc "s-exp" (Ok (SId "s-exp"))

[<Fact>]
let ``test 4`` () = testFunc "(+ 1 2)" (Ok (SExp [(SId "+" ); (SInt 1L); (SInt 2L)]))

[<Fact>]
let ``test 5`` () = 
    testFunc 
        "(let \n ((x 10) (y 20)) (+ x y)\n)" 
        (Ok (SExp [(SId "let"); (SExp [(SExp [(SId "x") ; (SInt 10L)]);
            (SExp [(SId "y");(SInt 20L)])]); (SExp [(SId "+"); (SId "x"); (SId "y")])]))


[<Fact>]
let ``test 6`` () =
    testFunc
        "(if #t 1 2)"
        (Ok (SExp [(SId "if"); (SBool true); (SInt 1L); (SInt 2L)]))

[<Fact>]
let ``test 7`` () =
    testFunc
        "(if (not (and (>= 1 2) (or (< 1 2) (= 1 2)))) 1 2)"
        (Ok (SExp [(SId "if")
                   SExp [(SId "not")
                         SExp [
                             SId "and"
                             SExp [SId ">="; SInt 1L; SInt 2L]
                             SExp [
                                 SId "or"
                                 SExp [SId "<"; SInt 1L; SInt 2L]
                                 SExp [SId "="; SInt 1L; SInt 2L]
                             ]
                         ]
                   ]
                   SInt 1L
                   SInt 2L
             ]))

[<Fact>]
let ``test 8`` () =
    let tprg = "(int, int, bool, int)"
    let t = runParser pType tprg |> getResult
    Assert.Equal(t, VecType [|intType; intType; boolType; intType|])

[<Fact>]
let ``post parser test 1`` () = 
       let res = parseToAst "(let \n ((x 10) (y 20)) (+ x y))"
       match res with
       | Ok t ->
           Assert.Equal(
               LetExp ([("x", (Int 10L)); ("y", (Int 20L))],(OpExp (ExprOp.Add, (Id "x"), (Id "y")))),
               t
           )
       | Error r -> Assert.True(false)

[<Fact>]
let ``post parser test 2`` () = 
        let res = parseToAst "(let (let []))"
        match res with
        | Error (SyntaxError e) -> Assert.True(true)
        | _ -> Assert.True(false)

[<Fact>]
let ``post parser test 3`` () =
        let res = parseToAst "(let \n ((x 10) (y (- 10 20)) (z 30)) (+ x y z))"
        match res with
        | Ok t -> 
            Assert.Equal(
                LetExp ([("x", Int 10L); ("y", OpExp (ExprOp.Sub, Int 10L, Int 20L)); 
                         ("z", Int 30L)], 
                        (OpExp (ExprOp.Add, Id "x", (OpExp (ExprOp.Add , Id "y", Id "z"))))),
                t
            )
        | _ -> Assert.True(false)

[<Fact>]
let ``post parser test 4`` () =
        let res = parseToAst "(let \n [(x 20) (y (let {[t 20]} t))] (/ x y))" |> getResult
        Assert.Equal(
            LetExp ([("x", Int 20L); ("y", LetExp ([("t", Int 20L)], Id "t"))], 
                OpExp (ExprOp.Div, Id "x", Id "y")),
            res
        )
    
[<Fact>]
let ``post parser test 5`` () =
            let res = parseToAst "(if (>= 1 2) 1 2)" |> getResult
            Assert.Equal(
                IfExp (OpExp (ExprOp.IEqB, Int 1L, Int 2L), Int 1L, Int 2L), 
                res
            )

[<Fact>]
let ``post parser test 6`` () =
       let res = parseToAst "(if (not (and (>= 1 2) (or (< 1 2) (= 1 2)))) 1 2)" |> getResult
       Assert.Equal(
           IfExp (
               UOpExp (ExprUOp.Not,
                       OpExp (ExprOp.And,
                             OpExp (ExprOp.IEqB, Int 1L, Int 2L),
                             OpExp (ExprOp.Or,
                                    OpExp (ExprOp.IL, Int 1L, Int 2L ),
                                    OpExp (ExprOp.IEq, Int 1L, Int 2L)))),
               Int 1L,
               Int 2L),
           res
       )
       
[<Fact>]
let ``post parser test 7`` () =
    let res = parseToAst "(vector 1 2 3 4)" |> getResult
    Assert.Equal(
        Vector [ (Int 1L); (Int 2L) ;(Int 3L); (Int 4L) ], res
        )
    
[<Fact>]
let ``post parser test 8`` () =
    let res = parseToAst "(vector-length (vector 1 2 3 4))" |> getResult
    Assert.Equal(
        UOpExp(ExprUOp.VecLen, Vector [ (Int 1L); (Int 2L) ;(Int 3L); (Int 4L) ]), res
        )
    
[<Fact>]
let ``post parser test 9`` () =
    let res = parseToAst "(vector-ref (vector 1 2 3 4) 1)" |> getResult
    Assert.Equal(
        VectorRef(Vector [ (Int 1L); (Int 2L) ;(Int 3L); (Int 4L) ], 1), res
        )

[<Fact>]
let ``post parser test 10`` () =
    let res = parseToAst "(vector-set! (vector 1 2 3 4) 1 10)" |> getResult
    Assert.Equal(
        VectorSet(Vector [ (Int 1L); (Int 2L) ;(Int 3L); (Int 4L) ], 1, (Int 10L)), res
        )
    