#r "nuget: FParsec, 1.1.1"

open System.Reflection
open FSharp.Reflection
open FSharp.Collections
open FParsec

type Ast =
    | Int of int64
    | Add of Ast * Ast

type SExpression =
    | SId of string
    | SExp of SExpression list

type SParser<'T> = Parser<'T, unit>

let typeToStr (x:System.Type) = x.Name

let makeTypeMap (parsers: (System.Type * 'a) list) =
    let types, parsersOfT = List.unzip parsers
    let typeNames = List.map typeToStr types
    List.zip typeNames parsersOfT |> Map.ofList

type ParseInfo<'T> = (System.Type * string * SParser<'T>) list
let parseS (t: System.Type) (parses: ParseInfo<'T>) (x: SExpression) =
    let ut = FSharpType.GetUnionCases(t.GetType())
    match x with
    | _ -> ()

printf
    "%A"
    (typeof<Ast>
     |> FSharpType.GetUnionCases
     |> fun x -> x.[1].Name)

parseS typeof<Ast> [ (typeof<string>, "string", pstring "a")
                     (typeof<int>, "int", pint64) ]