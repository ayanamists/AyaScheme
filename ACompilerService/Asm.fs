module ACompilerService.Asm

open System.IO
open Iced.Intel
open Utils
open Iced.Intel
open Ast


(*
    pass 7: assemble asm code to machine code
*)    

let memToIced' (offset:int64) (r:AssemblerRegister64) =
    AssemblerRegisters.__qword_ptr.[r] + (int)offset
let regToIced r =
    match r with
    | Reg.Rax -> AssemblerRegisters.rax
    | Reg.Rbx -> AssemblerRegisters.rbx
    | Reg.Rcx -> AssemblerRegisters.rcx
    | Reg.Rdx -> AssemblerRegisters.rdx
    | Reg.Rbp -> AssemblerRegisters.rbp
    | Reg.Rsp -> AssemblerRegisters.rsp
    | Reg.Rdi -> AssemblerRegisters.rdi
    | Reg.Rsi -> AssemblerRegisters.rsi
    | Reg.R8 -> AssemblerRegisters.r8
    | Reg.R9 -> AssemblerRegisters.r9
    | Reg.R10 -> AssemblerRegisters.r10
    | Reg.R11 -> AssemblerRegisters.r11
    | Reg.R12 -> AssemblerRegisters.r12
    | Reg.R13 -> AssemblerRegisters.r13
    | Reg.R14 -> AssemblerRegisters.r14
    | Reg.R15 -> AssemblerRegisters.r15
    | _ -> Impossible () |> raise

let memToIced offset r =
    let r' = regToIced r
    AssemblerRegisters.__qword_ptr.[r'] + (int) offset
    


// case1 for (Int, Reg)
let case1 (asm:Assembler) op (i:int) (r:AssemblerRegister64) =
    match op with
    | InstrBOp.Add -> asm.add(r, i)
    | InstrBOp.Sub -> asm.sub(r, i)
    | InstrBOp.Cmp -> asm.cmp(r, i)
    | InstrBOp.Test -> asm.test(r, i)
    | InstrBOp.And -> asm.``and``(r, i)
    | InstrBOp.Or -> asm.``or``(r, i)
    | InstrBOp.Xor -> asm.``xor``(r, i)
    | _ -> Impossible () |> raise
    
// case 2 for (Reg, Reg)
let case2 (asm:Assembler) op (r1:AssemblerRegister64) (r2:AssemblerRegister64) =
    match op with
    | InstrBOp.Add -> asm.add(r2, r1)
    | InstrBOp.Sub -> asm.sub(r2, r1)
    | InstrBOp.Cmp -> asm.cmp(r2, r1)
    | InstrBOp.Test -> asm.test(r2, r1)
    | InstrBOp.And -> asm.``and``(r2, r1)
    | InstrBOp.Or -> asm.``or``(r2, r1)
    | InstrBOp.Mov -> asm.mov(r2, r1)
    | InstrBOp.MovZb -> asm.movzx(r2, AssemblerRegisters.al)
    | InstrBOp.Xor -> asm.xor(r2, r1)
    | _ -> Impossible () |> raise
    
// case 3 for (Mem, Reg)
let case3 (asm:Assembler) op (r1:AssemblerMemoryOperand) (r2:AssemblerRegister64) =
    match op with
    | InstrBOp.Add -> asm.add(r2, r1)
    | InstrBOp.Sub -> asm.sub(r2, r1)
    | InstrBOp.Cmp -> asm.cmp(r2, r1)
    | InstrBOp.Test -> asm.test(r1, r2)
    | InstrBOp.And -> asm.``and``(r2, r1)
    | InstrBOp.Or -> asm.``or``(r2, r1)
    | InstrBOp.Mov -> asm.mov(r2, r1)
    | InstrBOp.MovZb -> asm.movzx(r2, AssemblerRegisters.al)
    | InstrBOp.Xor -> asm.xor(r2, r1)
    | _ -> Impossible () |> raise
    
// case 4 for (Int, mem)
let case4 (asm:Assembler) op (i:int) (r:AssemblerMemoryOperand) =
    match op with
    | InstrBOp.Mov -> asm.mov(r, i)
    | InstrBOp.Add -> asm.add(r, i)
    | InstrBOp.Sub -> asm.sub(r, i)
    | InstrBOp.Cmp -> asm.cmp(r, i)
    | InstrBOp.Test -> asm.test(r, i)
    | InstrBOp.And -> asm.``and``(r, i)
    | InstrBOp.Or -> asm.``or``(r, i)
    | InstrBOp.Xor -> asm.``xor``(r, i)
    | _ -> Impossible () |> raise

// case 5 for (Reg, Mem)
let case5 (asm:Assembler) op (i:AssemblerRegister64) (r:AssemblerMemoryOperand) =
    match op with
    | InstrBOp.Mov -> asm.mov(r, i)
    | InstrBOp.Add -> asm.add(r, i)
    | InstrBOp.Sub -> asm.sub(r, i)
    | InstrBOp.Cmp -> asm.cmp(r, i)
    | InstrBOp.Test -> asm.test(r, i)
    | InstrBOp.And -> asm.``and``(r, i)
    | InstrBOp.Or -> asm.``or``(r, i)
    | InstrBOp.Xor -> asm.``xor``(r, i)
    | _ -> Impossible () |> raise
    
let assembleBOpInstr (assembler:Assembler) op atm1 atm2 =
    match atm1, atm2 with
    | P5Int i, P5Reg r ->
        match op with
        | InstrBOp.Mov -> assembler.mov(regToIced r, i)
        | _ -> case1 assembler op ((int32)i) (regToIced r) 
    | P5Reg r1, P5Reg r2 -> case2 assembler op (regToIced r1) (regToIced r2)
    | P5Stack (off, r1), P5Reg r2 -> case3 assembler op (memToIced off r1) (regToIced r2)
    | P5Int i, P5Stack (off, r1) -> case4 assembler op ((int32)i) (memToIced off r1)
    | P5Reg r1, P5Stack (off, r2) -> case5 assembler op (regToIced r1) (memToIced off r2)
    | _ -> Impossible () |> raise
    
// ucase1 for Int
let ucase1 (assembler:Assembler) op (i:int32) = Impossible () |> raise
// ucase2 for reg
let ucase2 (assembler:Assembler) op (r:AssemblerRegister64) =
    match op with
    | InstrUOp.Mul -> assembler.mul(r)
    | InstrUOp.IMul -> assembler.imul(r)
    | InstrUOp.Neg -> assembler.neg(r)
    | InstrUOp.IDiv -> assembler.idiv(r)
    | InstrUOp.SetB -> assembler.setl(AssemblerRegisters.al)
    | InstrUOp.SetG -> assembler.setg(AssemblerRegisters.al)
    | InstrUOp.SetGe -> assembler.setge(AssemblerRegisters.al)
    | InstrUOp.SetBe -> assembler.setle(AssemblerRegisters.al)
    | InstrUOp.SetE -> assembler.sete(AssemblerRegisters.al)
    | InstrUOp.Cqto -> assembler.cqo()
    | _ -> Impossible () |> raise

let ucase3 (assembler:Assembler) op (r:AssemblerMemoryOperand) =
     match op with
     | InstrUOp.Mul -> assembler.mul(r)
     | InstrUOp.IMul -> assembler.imul(r)
     | InstrUOp.Neg -> assembler.neg(r)
     | InstrUOp.IDiv -> assembler.idiv(r)
     | InstrUOp.SetB -> assembler.setl(AssemblerRegisters.al)
     | InstrUOp.SetG -> assembler.setg(AssemblerRegisters.al)
     | InstrUOp.SetGe -> assembler.setge(AssemblerRegisters.al)
     | InstrUOp.SetBe -> assembler.setle(AssemblerRegisters.al)
     | InstrUOp.SetE -> assembler.sete(AssemblerRegisters.al)
     | InstrUOp.Cqto -> assembler.cqo()
     | _ -> Impossible () |> raise

let assembleUOpInstr (assembler:Assembler) op atm1 =
    match atm1 with
    | P5Int i -> ucase1 assembler op ((int32)i)
    | P5Reg r -> ucase2 assembler op (regToIced r)
    | P5Stack (off, r) -> ucase3 assembler op (memToIced off r)
    
let assembleCtrOpInstr (assembler:Assembler) op (label:Iced.Intel.Label) =
    match op with
    | InstrCtrOp.Jmp -> assembler.jmp(label)
    | InstrCtrOp.Call -> assembler.call(label)
    | InstrCtrOp.Jz -> assembler.je(label)
    | InstrCtrOp.Jnz -> assembler.jne(label)
    | InstrCtrOp.Jb -> assembler.jl(label)
    | InstrCtrOp.Jbe -> assembler.jle(label)
    | InstrCtrOp.Jg -> assembler.jg(label)
    | InstrCtrOp.Jge -> assembler.jge(label)
    | InstrCtrOp.Ret -> assembler.ret()
    | _ -> Impossible () |> raise
    
    
let makeLabelMap (assembler:Assembler) labels =
    List.fold (fun m l ->
        let l' = assembler.CreateLabel(l)
        Map.add l l' m) (Map []) labels
    
let addBeginAndConclusion (assembler:Assembler) stackSize
                          (m:Map<Label, Iced.Intel.Label>) =
    if stackSize = 0
    then
        assembler.jmp(m.[startLabel])
        assembler.Label(ref m.[conclusionLabel])
        assembler.ret()
    else
        assembler.push(AssemblerRegisters.rbp)
        assembler.mov(AssemblerRegisters.rbp, AssemblerRegisters.rsp)
        assembler.sub(AssemblerRegisters.rsp, stackSize)
        assembler.jmp(m.[startLabel])
        assembler.Label(ref m.[conclusionLabel])
        assembler.add(AssemblerRegisters.rsp, stackSize)
        assembler.pop(AssemblerRegisters.rbp)
        assembler.ret()
let assemble p5Prg =
    match p5Prg with
    | P5Program (info, blocks) ->
        let assembler = Assembler(64)
        let labels = [ for (l, b) in blocks -> l]
        let m = makeLabelMap assembler labels
        addBeginAndConclusion assembler (info.stackSize) m
        for (label, instrL) in blocks.Tail do
            assembler.Label(ref (m.[label]))
            for instr in instrL do
                match instr with
                | P5BOp (op, atm1, atm2) -> assembleBOpInstr assembler op atm1 atm2
                | P5UOp (op, atm1) -> assembleUOpInstr assembler op atm1
                | P5CtrOp (op, label') ->
                    let label'' = Map.tryFind label' m
                    match label'' with
                    | Some t -> 
                        assembleCtrOpInstr assembler op t
                    | None -> assembler.ret()
        assembler
        
let printAsm (assembler:Assembler) =
    let rip = 0x1234567810001000UL
    let stream = new MemoryStream()
    assembler.Assemble(StreamCodeWriter (stream), rip) |> ignore
    stream.Position <- 0L
    let reader = StreamCodeReader (stream)
    let decoder = Decoder.Create(64, reader)
    decoder.IP <- rip
    let mutable str = ""
    while (stream.Position < stream.Length) do
        let instr = decoder.Decode()
        str <- String.concat "\n" [ str; (sprintf "%X=%A" instr.IP instr) ]
    str