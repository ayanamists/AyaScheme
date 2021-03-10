module ACompilerService.Test.TestGenerator

open FsCheck
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

(*
    no circle
*)
let genDGraph = gen {
   let! n = Gen.choose (0, 5)
   let! i = genPairGraph n
   return List.fold (fun g (v1, v2) ->
               if existEdge g v2 v1 then g else
               addEdgeD g v1 v2)
           (createGraph [||]) i
}

type GraphGenerators =
    static member Graph() =
        {new Arbitrary<Graph<int>>() with
            override x.Generator = genGraph
            override x.Shrinker t = Seq.empty}

type DGraphGenerators =
    static member Graph() =
        {new Arbitrary<Graph<int>>() with
            override x.Generator = genDGraph
            override x.Shrinker t = Seq.empty}
