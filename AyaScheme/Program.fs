// Learn more about F# at http://fsharp.org

open System
open Iced.Intel
open ACompilerLoader
open ACompilerService.Compile
open ACompilerService.Asm

let run prg =
    let asm = compileToBin prg
    match asm with
    | Ok (a, t) ->
        printAsm a |> printfn "%A"
        let loader = Loader()
        loader.Load(a)
        let t = (loader.Exec ())
        printfn "%A" t
    | Error e -> 
        printfn "%A" e

let rec loop () =
    Console.Write("> ")
    let str = Console.ReadLine()
    if str = null
    then
        Console.WriteLine("goodbye")
    else
        run str
        loop ()
    
[<EntryPoint>]
let main _ =
    loop ()
    0
    
    
