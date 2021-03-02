module ACompilerService.Utils

open System

exception VarNotBound of string
exception Impossible of unit

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
    
type Graph<'s when 's : comparison > = G of Map<'s, Set<'s>>

let createGraph (seq:seq<'T * seq<'T>>) =
    Map ([ for (i, t) in seq -> (i, Set t) ]) |> G
    
let addEdge (G vg) v1 v2 =
    let changeV1 (o:Set<'a> option) =
        match o with
        | Some(s) -> Some (s.Add(v2))
        | None -> Some (Set([v2]))
    let changeV2 (o:Set<'a> option) =
        match o with
        | Some(l) -> Some (l.Add(v1))
        | None -> Set ([v1]) |> Some
    let vg1 = vg.Change(v1, changeV1)
    vg1.Change(v2, changeV2) |> G

let addEdges g l = 
    List.fold (fun now (v1, v2) -> addEdge now v1 v2 ) g l

let getNeighbor (G vg) v1 =
    vg.TryFind(v1)

let getAllVex (G vg) =
    [ for (KeyValue(v, _)) in vg -> v ]

let existVex (G vg) v =
    vg.ContainsKey(v)

let existEdge (G vg) v1 v2  =
    vg.ContainsKey(v1) && vg.ContainsKey(v2) &&
    match vg.TryFind(v1) with
    | Some(l) -> l.Contains(v2)
    | None -> Impossible () |> raise