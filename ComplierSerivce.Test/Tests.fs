module Tests

open System
open Xunit

[<Fact>]
let ``My test`` () =
    Assert.True(true)

[<Fact>]
let ``Test 1`` () = 
   let res = ComplierService.Parser.parseAll "1111" = "1111"
   Assert.True(res)
