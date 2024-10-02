module TestVirtualMachine

open NUnit.Framework

open Syntax
open TargetCode
open AddressResolution
open GenComputation
open GenCode
open Utils
open Environment
open VirtualMachine

[<TestFixture>]
type Fixture () =

    [<SetUp>]
    member this.setup () =
        ()

    [<Test>]
    member this.someTwoInts () =
        let e = parseExpr "3 + 2"
        let ty, code =
            match run (codeV Context.Empty e 0) with
            | Result(code, _) ->
                code
            | Error(msg, _) ->
                failwith $"code generation failed: {msg}"
        match ty with
        | IntTy(_) ->
            ()
        | _ ->
            failwith "expected type of '3 + 2' to be int"
        let code' = List.concat [code ; [Halt]]
        let code'' = resolve code'
        let result = execute code''
        match result with
        | Basic(5) ->
            ()
        | _ ->
            failwith "expected result 5"
        ()

// ((fun (x : int) (y : int) -> x + y) 3 2)
    [<Test>]
    member this.testApply () =
        let e = parseExpr "((fun (x : int) (y : int) -> x + y) 3 2)"
        let ty, code =
            match run (codeV Context.Empty e 0) with
            | Result(code, _) ->
                code
            | Error(msg, _) ->
                failwith $"code generation failed: {msg}"
        match ty with
        | IntTy(_) ->
            ()
        | _ ->
            failwith "expected output of type 'Int'"
        let code' = resolve <| List.concat [code ; [Halt]]
        let result = execute code'

        Assert.That( (result = Basic(5)) )