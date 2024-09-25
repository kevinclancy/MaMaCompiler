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
    member this.durrr () =
        let e = parseExpr "3 + 2"
        let ty, code =
            match run (codeV Context.Empty e 0) with
            | Result(code, _) ->
                code
            | Error(_, _) ->
                failwith "code generation failed"
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

    // [<Test>]
    // member this.testApply () =
    //     let e = parseExpr "((fun x y -> x + y) 3 2)"
    //     let ty, code =
    //         match run (codeV Context.Empty e 0) with
    //         | Result(code, _) ->
    //             code
    //         | Error(_, _) ->
    //             failwith "code generation failed"

    //     match ty with
    //     | IntTy(_) ->
    //         ()
    //     | _ ->
    //         failwith "expected output of type 'Int'"
    //     let code' = resolve code
    //     let result = execute code'

    //     Assert.That( (result = 5) )