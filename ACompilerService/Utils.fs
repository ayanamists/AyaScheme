module ACompilerService.Utils

open System
open FSharpx.Collections


exception VarNotBound of string
exception Impossible of unit

let getResult res =
    match res with
    | Result.Ok t -> t
    | Result.Error r ->
        printfn "%A" r 
        Impossible () |> raise
        
type Index = int
type CompileError =
    | TypeError of string
    | VarNotBoundError of string
    | SyntaxError of string
    | VecIdxOutBound of string
    
let makeVecOutBound idx v =
    sprintf "length of vec is %A, but ref pos %A" (Array.length v) idx |> VecIdxOutBound
    
let makeTypeError tNeed tReal =
    sprintf "should be type %A, but is %A" tNeed tReal |> TypeError
 
type Env<'A, 'B when 'A : comparison> = BEnv of Map<'A, 'B>
let rec searchEnv (env:Env<'A, 'B>) var =
    match env with 
    | BEnv hd -> hd.TryFind var
    
let rec addEnv (env:Env<'A, 'B>) var val' =
    match env with
    | BEnv hd -> hd.Add (var, val') |> BEnv

let emptyEnv<'A, 'B when 'A : comparison > : Env<'A, 'B> = Map [] |> BEnv
type State<'s, 'a> = St of ('s -> 'a * 's)

let stateRet a = St (fun x -> (a, x))

let stateComb (St m) (f:'b -> State<'s, 'c>) = St (fun x ->
    let (a1, s1) = m x
    match (f a1) with
    | St f' -> f' s1 )

let stateGet = St (fun x -> (x, x))

let statePut f = St (fun x -> ( (), f x ))

let stateRun m s = match m with
                   | St f -> f s

type StateBuilder () =
    member x.Return(a) = stateRet a
    member x.Bind(m, f) = stateComb m f
    member x.ReturnFrom(m) = x.Bind(m, stateRet)
    member x.Combine(m1, m2) = x.Bind(m1, fun _ -> m2)
    member x.Zero () = stateRet ()
    member x.Delay f = f ()

let state = StateBuilder ()

let stateMap f l =
    let rec loop acc l =
        match l with
        | [] -> List.rev acc |> stateRet
        | hd :: tl ->
            state {
                let! hd' = f hd
                return! loop (hd' :: acc) tl
            }
    loop [] l
    
(*
    this result builder is written by Yuriy Habarov,
    see http://www.fssnip.net/7UJ/title/ResultBuilder-Computational-Expression
    for more info
*)
let ofOption error = function Some s -> Ok s | None -> Error error
type ResultBuilder() =
    member __.Return(x) = Ok x
    member __.ReturnFrom(m: Result<_, _>) = m
    member __.Bind(m, f) = Result.bind f m
    member __.Bind((m, error): (Option<'T> * 'E), f) = m |> ofOption error |> Result.bind f
    member __.Zero() = None
    member __.Combine(m, f) = Result.bind f m
    member __.Delay(f: unit -> _) = f
    member __.Run(f) = f()
    member __.TryWith(m, h) =
        try __.ReturnFrom(m)
        with e -> h e
    member __.TryFinally(m, compensation) =
        try __.ReturnFrom(m)
        finally compensation()
    member __.Using(res:#IDisposable, body) =
        __.TryFinally(body res, fun () -> match res with null -> () | disp -> disp.Dispose())
    member __.While(guard, f) =
        if not (guard()) then Ok () else
        do f() |> ignore
        __.While(guard, f)
    member __.For(sequence:seq<_>, body) =
        __.Using(sequence.GetEnumerator(), fun enum -> __.While(enum.MoveNext, __.Delay(fun () -> body enum.Current)))

let result = new ResultBuilder()
let result1 (eval1:'a->Result<'b,'c>) exp1 f = result {
    let! exp1' = eval1 exp1
    return (f exp1')
}

let result2 (eval1:'a->Result<'b,'c>) exp1
            (eval2:'d->Result<'b,'c>) exp2 f = result {
    let! exp1' = eval1 exp1
    let! exp2' = eval2 exp2
    return (f exp1' exp2')
}

let result3 (eval1:'a->Result<'b,'c>) exp1
            (eval2:'d->Result<'b,'c>) exp2
            (eval3:'e->Result<'b,'c>) exp3 f = result {
                let! exp1' = eval1 exp1
                let! exp2' = eval2 exp2
                let! exp3' = eval3 exp3
                return (f exp1' exp2' exp3')
            }
            
let result2' (eval1:'a->Result<'b,'c>) exp1  exp2 f = result2 eval1 exp1 eval1 exp2 f
let result3' eval1 exp1 exp2 exp3 f = result3 eval1 exp1 eval1 exp2 eval1 exp3 f
 
let resultMap (f:'a->Result<'b,'c>) l =
    let rec build l acc =
        match l with
        | [] -> acc |> List.rev |> Result.Ok
        | hd :: tl ->
            result {
               let! hd' = f hd
               return! build tl (hd' :: acc)
            }
    build l []
    
type Graph<'s when 's : comparison > = G of Map<'s, Set<'s>>

let createGraph (seq:('T * 'T array) array) =
    Map ([ for (i, t) in seq -> (i, Set t) ]) |> G
    
let addEdgeD (G vg) v1 v2 =
    let changeV1 (o:Set<'a> option) =
        match o with
        | Some(s) -> Some (s.Add(v2))
        | None -> Some (Set([v2]))
    vg.Change(v1, changeV1)
    |> (fun x -> if x.ContainsKey(v2) then x else x.Add(v2, Set []) )
    |> G
    
let addEdge (G vg) v1 v2 =
    addEdgeD (addEdgeD (G vg) v1 v2) v2 v1

let addEdges g l = 
    List.fold (fun now (v1, v2) -> addEdge now v1 v2 ) g l

let addEdgesD g l =
    List.fold (fun now (v1, v2) -> addEdgeD now v1 v2) g l

let getNeighbor (G vg) v1 =
    let s = vg.TryFind(v1)
    match s with
    | Some s -> [ for i in s -> i  ]
    | None   -> []

let getAllVex (G vg) =
    [ for (KeyValue(v, _)) in vg -> v ]

let existVex (G vg) v =
    vg.ContainsKey(v)

let existEdge (G vg) v1 v2  =
    vg.ContainsKey(v1) && vg.ContainsKey(v2) &&
    match vg.TryFind(v1) with
    | Some(l) -> l.Contains(v2)
    | None -> Impossible () |> raise

let allEdges (G vg) =
    let foldF res (v, s) =
        Set.union res (Set [for i in s -> (v, i)])
    List.fold foldF (Set []) [for KeyValue(i, j) in vg -> (i, j)]

let addVex (G vg) v =
    match Map.containsKey v vg with
    | true  -> (G vg)
    | false -> 
        Map.add v (Set []) vg |> G

let isIllegalGraph (G vg) =
    let vexs = getAllVex (G vg) |> Set
    let allE = allEdges (G vg)
    let rec edgeIllegal1 l =
        match l with
        | [] -> true
        | (_, s) :: tl -> Set.isSubset s vexs && edgeIllegal1 tl
    let rec edgeIllegal2 l=
        match l with
        | [] -> true
        | (i, j) :: tl -> Set.contains (j, i) allE && edgeIllegal2 tl
    edgeIllegal1 [for KeyValue(i, j) in vg -> (i, j)] &&
    edgeIllegal2 [for i in allE -> i]

let isEmptyGraph (G vg) =
    Map.isEmpty vg
    
let topoSort g =
    let vexs = (getAllVex g)
    let mutable visit = Map [ for i in vexs -> (i, false) ]
    let mutable res = []
    let rec traverse node =
        if visit.[node] = true then () else
        visit <- visit.Change (node, (fun _ -> Some true))
        let neighbors = getNeighbor g node
        for i in neighbors do
            traverse i
        res <- node :: res
    for i in vexs do
        traverse i
    res
    
let graphArrowReverse (G vg) =
    if vg.Count = 0 then createGraph [||] else
    [for KeyValue(i, j) in vg -> (i, j)]
    |> List.map (fun (i, j) -> List.map (fun i' -> (i', i)) [ for i' in j -> i' ])
    |> List.reduce (@)
    |> addEdgesD (createGraph [||])

let mapMerge (a:Map<'a, 'b>) (b:Map<'a, 'b>) f =
    Map.fold (fun s k v ->
        match Map.tryFind k s with
        | Some v' -> Map.change k (f k (v, v')) s
        | None -> Map.add k v s) a b

let mapIntersection (a:Map<'a, 'b>) (b:Map<'a,'b>) =
    Set.intersect (Set [| for KeyValue(i, j) in a -> (i, j) |])
                  (Set [| for KeyValue(i, j) in b -> (i, j) |])
    |> Set.toArray
    |> Map.ofArray

let graphUnion (G g1) (G g2) =
    let v1 = getAllVex (G g1) |> Set.ofList
    let v2 = getAllVex (G g2) |> Set.ofList
    let v = Set.union v1 v2 |> Set.toList
    List.map (fun x -> (x, Set.union (Map.find x g1) (Map.find x g2))) v
    |> Map.ofList
    |> G
    
let listToTuple1 l =
    match l with
    | [e1;] -> e1
    | _ -> Impossible () |> raise
let listToTuple2 l =
    match l with
    | [e1; e2] -> (e1, e2)
    | _ -> Impossible () |> raise
let listToTuple1f f l =
    listToTuple1 l |> f
let listToTuple2f f l =
    listToTuple2 l |> fun (e1, e2) -> f e1 e2

let int32ToInt64 (i:int32) = System.Convert.ToInt64(i)