module ACompilerSerivce.Test.TestColoring

open System
open System.Runtime.Intrinsics.X86
open FSharpx.Collections.Tagged
open Xunit
open FsCheck
open FsCheck.Xunit
open ACompilerService.Coloring
open ACompilerService.Utils

let CanUse x n = x >= 0 && x < n
let fix x y n =
    if CanUse (x - 1) n
    then
        if CanUse (y + 1) n then (x - 1, y + 1) else (x - 1, y)
    else
        if CanUse (y - 1) n then (x + 1, y - 1) else (x + 1 , y)

let genPairGraph n = gen {
    let i = Gen.choose (0, n - 1)
    let j = Gen.choose (0, n - 1)
    let eCount' = Gen.choose (1, n * n)
    let! eCount = Gen.map ((( * )) 2) eCount'
    let pair = Gen.map2 (fun x y -> if x = y then fix x y n else (x, y)) i j
    return Gen.sample 0 eCount pair
}

let genGraph = gen {
    let! n = Gen.choose (0, 30)
    let! i = genPairGraph n
    return List.fold (fun g (v1, v2) -> addEdge g v1 v2) (createGraph [||]) i
}

type GraphGenerators =
    static member Graph() =
        {new Arbitrary<Graph<int>>() with
            override x.Generator = genGraph
            override x.Shrinker t = Seq.empty}
        
let maxColor m =     
    let c = Map.toList m |> List.map (fun (_, c) -> c)
    List.sortDescending c |> List.head |> (+) 1

[<Fact>]
let ``maxColor Test 1`` () =
    let g = createGraph [|
        (1, [|0; 2|])
        (0, [|1; 2|])
        (2, [|1; 0|])
    |]
    let m = coloringGraph g
    Assert.Equal(3, maxColor m)

[<Fact>]
let ``maxColor Test 2`` () =
    let g = createGraph [|
        (0, [|1|])
        (1, [|0; 2; 3; 4;|])
        (2, [|1|])
        (3, [|1|])
        (4, [|1|])
    |]
    let m = coloringGraph g
    Assert.Equal(2, maxColor m)
    
[<Fact>]
let ``maxColor Test 3`` () =
    let g = createGraph [|
        (0, [|1; 5|])
        (1, [|0; 2|])
        (2, [|1; 3|])
        (3, [|2; 4|])
        (4, [|3; 5|])
        (5, [|4; 0|])
    |]
    let m = coloringGraph g
    Assert.Equal(2, maxColor m)
    
[<Property>]
let ``complete graph color is n`` (n:int) =
    n > 0 ==> lazy 
    let g = createGraph [|
        for i in [0 .. n - 1] ->
        (i
        ,[| for j in ([0 .. n - 1] |> List.filter (fun x -> not (x = i))) -> j |])
    |]
    let m = coloringGraph g
    n = maxColor m


[<Property(Arbitrary=[|typeof<GraphGenerators>|])>]
let ``All Vex Has Color`` (g:Graph<int>) =
    not (isEmptyGraph g) ==> lazy
    let m = coloringGraph g
    Map.count m = (getAllVex g |> List.length)
    
[<Property(Arbitrary=[|typeof<GraphGenerators>|])>]
let ``All Color Exists`` (g:Graph<int>) =
    not (isEmptyGraph g) ==> lazy
    let m = coloringGraph g
    let s = Set.ofList [ for KeyValue(_, c) in m -> c ]
    let max = maxColor m
    let rec test l =
        match l with
        | [] -> true
        | now :: tl -> if Set.contains now s then test tl else false
    test [0 .. max - 1]
    
[<Property(Arbitrary=[|typeof<GraphGenerators>|])>]
let ``Vex Color Requirement`` (g:Graph<int>) =
    not (isEmptyGraph g) ==> lazy
    let m = coloringGraph g
    let vexs = getAllVex g
    let rec test l =
        match l with
        | [] -> true
        | now :: tl ->
            let neighbors = getNeighbor g now
            let myColor = Map.find now m
            let colors = List.map (fun x -> Map.find x m) neighbors
            (not (List.contains myColor colors)) && test tl
    test vexs