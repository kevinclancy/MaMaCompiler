module TestVirtualMachine

open NUnit.Framework

[<TestFixture>]
type Fixture () =

    [<Test>]
    member this.setup () =
        ()

    member this.testApply () =
        let e = "((fun x y -> x + y) 3 2)"
        let ty, code =
            match run (genExpr Context.empty e) with
            | Result(code, _) ->
                code
            | Error(_, _) ->
                failwith "code generation failed"

        match ty with
        | Int(_) ->
            ()
        | _ ->
            failwith "expected output of type 'Int'"
        let code' = resolve code
        let result = execute code'

        Assert.That( (result = 5) )