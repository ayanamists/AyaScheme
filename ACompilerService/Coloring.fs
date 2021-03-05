module ACompilerService.Coloring

open System
open FSharpx.Collections
open Utils

[<CustomComparison; CustomEquality; Struct>]
type PriorityEle<'T> =
    | PE of 'T * int
    interface IComparable with
        member x.CompareTo obj =
            match obj with
            | :? PriorityEle<'T> as another ->
                match another, x with
                | PE (_, a') , PE (_, x') -> x'.CompareTo(a')
            | _ -> Impossible () |> raise
    interface IEquatable<PriorityEle<'T>> with    
        member x.Equals another =
            match another, x with
            | PE (_, a'), PE (_, x') -> x'.Equals a'

let coloringGraph g =
    let findMin l =
        let len = List.length l
        let rec makeArr arr l =
            match l with
            | [] -> arr
            | hd :: tl -> if hd >= Array.length arr then makeArr arr tl
                          else
                              arr.[hd] <- true
                              makeArr arr tl
        makeArr (Array.create len false) l |>
            fun arr -> List.find (fun x -> x = len || arr.[x] = false) [0 .. len + 1]
    let rec loop pq res =
        if PriorityQueue.isEmpty pq
        then res
        else
            let (PE (now, _), pq') = PriorityQueue.pop pq
            match (Map.tryFind now res) with
            | Some c -> loop pq' res
            | None -> assignNew now res pq'
    and assignNew now res pq =
        let neigh = getNeighbor g now
        let colorToAssign =
            List.fold (fun l x ->
                match Map.tryFind x res with
                | Some t -> t :: l
                | None -> l) [] neigh |> findMin
        let res' = Map.add now colorToAssign res
        let foldF pq' x = PriorityQueue.insert ((x, colorToAssign) |> PE) pq'
        let pq' = List.fold foldF pq neigh
        loop pq' res'
    let vexs = getAllVex g
    let foldF m vex =
        match (Map.tryFind vex m) with
        | Some t -> m
        | None -> loop (PriorityQueue.insert (PE (vex, 0)) (PriorityQueue.empty true)) m
    List.fold foldF (Map []) vexs