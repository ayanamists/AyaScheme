module TestInterpreter

open ACompilerService.Parser
open ACompilerService.Ast
open ACompilerService.Interpreter
open Xunit
open System

let parseAndEval code = parseToAst code |> eval

[<Fact>]
let ``Interpreter test 1`` () = 
    let prg = "1"
    let wanted = IntValue 1L
    Assert.Equal(wanted, parseAndEval prg)

[<Fact>]
let ``Interpreter test 2`` () =
    let prg = "(let ([a 10] [b 20]) (+ a b))"
    let wanted = IntValue 30L
    Assert.Equal(wanted, parseAndEval prg)

[<Fact>]
let ``Interpreter test 3`` () =
    let prg = "(let ([a 10] [b 20]) \n (let ([a 30] [c 20]) (* a b)))"
    let wanted = IntValue 600L
    Assert.Equal(wanted, parseAndEval prg)

[<Fact>]
let ``Interpreter test 4`` () =
    let prg = "(let ([a (let ([a 10]) a)]) (/ a 2))"
    let wanted = IntValue 5L
    Assert.Equal(wanted, parseAndEval prg)

[<Fact>]
let ``Interpreter test 5`` () =
    let prg = "(- 10000000 30)"
    let wanted = IntValue 9999970L
    Assert.Equal(wanted, parseAndEval prg)

[<Fact>]
let ``Interpreter test 6`` () =
    let prg = "(let ([a 1])
                 (if (= a 1)
                      1
                      2))"
    let wanted = IntValue 1L
    Assert.Equal(wanted, parseAndEval prg)
    
[<Fact>]
let ``Interpreter test 7`` () =
    let prg = "(let ([a 10])
                 (>= a 11))"
    let wanted = BoolValue false
    Assert.Equal(wanted, parseAndEval prg)
    
[<Fact>]
let ``Interpreter test 8`` () =
    let prg = "(if (not (and (>= 1 2) (or (< 1 2) (= 1 2)))) 1 2)"
    let wanted = IntValue 1L
    Assert.Equal(wanted, parseAndEval prg)
    
[<Fact>]
let ``Interpreter test 9`` () =
    let prg = "(< 10 11)"
    let wanted = BoolValue true
    Assert.Equal(wanted, parseAndEval prg)
    
[<Fact>]
let ``Interpreter test 10`` () =
    let prg = "(eq? 10 #t)"
    let wanted = BoolValue false
    Assert.Equal(wanted, parseAndEval prg)
    
[<Fact>]
let ``Interpreter test 11`` () =
    let prg = "(eq? 10 10)"
    let wanted = BoolValue true
    Assert.Equal(wanted, parseAndEval prg)
    
[<Fact>]
let ``Interpreter test 12`` () =
    let prg = "(eq? #t #t)"
    let wanted = BoolValue true
    Assert.Equal(wanted, parseAndEval prg)
 
 