module ACompilerService.Test.TestUtils


open Xunit
open FsCheck
open FsCheck.Xunit
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
    
let ``topoSort res is in topological order`` (g:Graph<int>) =
    let existsSuccessor x l =
        let successors = getNeighbor g x
        (List.map (fun x-> List.contains x l) successors)
        |> (fun x -> if List.isEmpty x then true
                     else List.reduce (&&) x )
    let rec test l =
        match l with
        | [] -> true
        | x :: tl -> (existsSuccessor x tl) && (test tl)
    test (topoSort g)
[<Fact>]
let ``TopoSort test 1`` () =
    let g = createGraph [|
        (1, [|2;3;4|])
        (2, [|3|])
        (3, [|4|])
        (4, [||])
    |]
    Assert.Equal<int list>([1; 2; 3; 4], topoSort g)

[<Fact>]
let ``TopoSort test 2`` () =
    let g = createGraph [|
        (2, [|1;3|])
        (1, [|7;4|])
        (3, [|6|])
        (4, [|3; 5|])
        (5, [|3; 6|])
        (6, [|7|])
        (7, [||])
    |]
    Assert.True(``topoSort res is in topological order`` g)
    
    
[<Property(Arbitrary=[|typeof<DGraphGenerators>|])>]
let ``Every node exists in topoSort Res`` (g:Graph<int>) =
    let count = getAllVex g |> List.length
    let res = topoSort g |> List.length
    res = count
    
