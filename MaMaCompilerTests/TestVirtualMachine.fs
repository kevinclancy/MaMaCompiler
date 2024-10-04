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
    member this.sumTwoInts () =
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

    [<Test>]

    member this.testLet () =
        let e = parseExpr """
        let a = (fun (x : int) (y : int) -> x + y) in
        (a 3 2)
        """
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

    [<Test>]

    member this.testCallAndUse () =
        let e = parseExpr """
        let a = (fun (x : int) (y : int) -> x + y) in
        ((a 3 2) + 1)
        """
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

        Assert.That( (result = Basic(6)) )

    [<Test>]

    member this.testMultiCall () =
        let e = parseExpr """
        let a = (fun (x : int) (y : int) -> x + y) in
        (a (3 + 2) 1)
        """
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

        Assert.That( (result = Basic(6)) )

    [<Test>]
    member this.testTwoCalls () =
        let e = parseExpr """
        let a = (fun (x : int) (y : int) -> x + y) in
        ((a 3 2) + (a 1 4))
        """
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

        Assert.That( (result = Basic(10)) )

    [<Test>]
    member this.testCallArg () =
        let e = parseExpr """
        let a = (fun (x : int) (y : int) -> x + y) in
        (a (a 3 2) 1)
        """
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

        Assert.That( (result = Basic(6)) )

    [<Test>]
    member this.testCallArg2 () =
        let e = parseExpr """
        let a = (fun (x : int) (y : int) -> x + y) in
        (a 1 (a 3 2))
        """
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

        Assert.That( (result = Basic(6)) )

    [<Test>]
    member this.testIfThenElse () =
        let e = parseExpr """
        if 6 then 1 else (3 + 2)
        """
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

        Assert.That( (result = Basic(1)) )

    [<Test>]
    member this.testFactorial () =
        let e = parseExpr """
        let rec fact : (int -> int) =
            (fun (x : int) -> if x == 0 then 1 else (x * (fact (x - 1))))
        in
        (fact 4)
        """
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

        Assert.That( (result = Basic(24)) )