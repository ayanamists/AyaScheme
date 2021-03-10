module ACompilerService.Test.TestColoring

open Xunit
open FsCheck
open FsCheck.Xunit
open ACompilerService.Coloring
open ACompilerService.Utils
open TestGenerator

        
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