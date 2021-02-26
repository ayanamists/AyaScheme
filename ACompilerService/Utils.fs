module ACompilerService.Utils

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
    