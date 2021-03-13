module ACompilerService.Compile

open ACompilerService
open Utils
open Pass
open Parser
open Asm
let compile x = result {
    let! x' = parseToAst x
    let! x1 = lexicalAddress x'
    let! (x1', t) = typeCheck x1
    let! x2 = pass2 x1'
    let! x3 = pass3 x2
    let! x4 = pass4 x3
    let! x5 = pass5 x4
    let! x6 = pass6 x5
    return (x6, t)
}

let compileToBin x = result {
    let! (x', t) =  compile x
    return (assemble x', t)
}