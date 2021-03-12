module ACompilerService.Asm

open Iced.Intel
open Ast


(*
    pass 7: assemble asm code to machine code
*)    

let assembleAtm atm =
    match atm with
    | P5Int i -> i
    | _ -> 0L
let assembleInstr assembler instr =
    ()
    
let assemble p5Prg =
    match p5Prg with
    | P5Program (info, blocks) ->
        let assembler = Assembler(64)
        ()

