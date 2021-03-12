// Learn more about F# at http://fsharp.org

open System
open Iced.Intel
open ACompilerLoader

[<EntryPoint>]
let main _ =
    let a = Assembler(64)
    a.mov(AssemblerRegisters.rax, 1000000L)
    a.ret()
    let t = Loader(a)
    t.Load() |> ignore
    0 // return an integer exit code
