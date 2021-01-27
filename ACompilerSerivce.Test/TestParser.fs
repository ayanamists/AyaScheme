module TestParser

open System
open Xunit
open Parser
open Ast

let testFunc data wanted = 
   match wanted , (Parser.parse data) with
   | Error, Error -> Assert.True(true)
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
let ``post parser test 1`` () = 
   try
       let res = parseToAst "(let \n ((x 10) (y 20)) (+ x y))"
       Assert.Equal(
           LetExp ([("x", (Int 10L)); ("y", (Int 20L))],(OpExp (ExprOp.Add, (Id "x"), (Id "y")))),
           res
       )
   with 
   | _ -> Assert.True(false)

[<Fact>]
let ``post parser test 2`` () = 
    try 
        let res = parseToAst "(let (let []))"
        Assert.True(false)
    with 
    | :? ExcepOfExpToAst -> Assert.True(true)
    | _ -> Assert.True(false)

[<Fact>]
let ``post parser test 3`` () =
    try 
        let res = parseToAst "(let \n ((x 10) (y (- 10 20)) (z 30)) (+ x y z))"
        Assert.Equal(
            LetExp ([("x", Int 10L); ("y", OpExp (ExprOp.Sub, Int 10L, Int 20L)); 
                     ("z", Int 30L)], 
                    (OpExp (ExprOp.Add, Id "x", (OpExp (ExprOp.Add , Id "y", Id "z"))))),
            res
        )
    with 
    | _ -> Assert.True(false)
