module ACompilerService.Test.TestUtils

open Xunit
open ACompilerService.Utils
open TestGenerator

[<Fact>]
let ``Graph Illegal Test 1`` () =
    let g = createGraph [|
        (1, [|0; 2|])
        (2, [|0; 3; 1|])
        (0, [|1; 2|])
        (3, [|2|])
    |]
    Assert.Equal(true, isIllegalGraph g)
    
[<Fact>]
let ``Graph Illegal Test 2`` () =
    let g = createGraph [|
        (2, [|3; 4|])
    |]
    Assert.Equal(false, isIllegalGraph g)

