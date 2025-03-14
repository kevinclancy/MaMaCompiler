open System
open System.IO
open FSharp.Text.Lexing
open GenComputation
open Syntax
open Environment
open GenCode
open AddressResolution
open VirtualMachine
open TargetCode
open Utils

let range_string ((start, fin) : Range) =
  $"line {start.Line + 1} column {start.Column + 1}"

[<EntryPoint>]
let main (args : string array) : int =
  let prog =
    try
      let reader = new StreamReader(args[0])
      let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(reader.ReadToEnd())
      let src = (new StreamReader(args[0])).ReadToEnd()
      try
        Parser.prog (Lexer.token) lexbuffer
      with
      | e ->
        let message = e.Message
        printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column)
        exit 1
    with
    | :? IndexOutOfRangeException ->
      printfn "provide the name of a text file as the command line argument"
      exit 1
    | :? FileNotFoundException ->
      printfn "file not found"
      exit 1
  let { typedefs = typedefs ; expr = e } = prog
  let ctxt =
      match run (Context.Empty.WithTypedefs typedefs) with
      | Result(ctxt', _) ->
          ctxt'
      | Error(msg, rng) ->
          printf $"code generation failed: {msg} at {range_string rng}"
          exit 1
  let ty, code =
      match run (codeV ctxt e 0) with
      | Result(code, _) ->
          code
      | Error(msg, rng) ->
          printf $"code generation failed: {msg} at {range_string rng}"
          exit 1
  let code' = resolve <| List.concat [code ; [Halt]]
  let result = execute code'
  printfn "Result Computed: %s" (result.ToString())
  0