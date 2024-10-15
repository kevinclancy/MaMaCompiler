module GenCode

open Syntax
open GenComputation
open TargetCode
open Environment

/// Generates code to push the value corresponding to a variable onto the stack,
/// evaluating a closure if necessary
///
/// ## Parameters
///
/// * ctxt - The context the variable occurrence appears under
/// * varName - The name of the variable
/// * varRng - The source-code range the variable appears in
/// * stackLevel - SP-SP0, where SP0 is the SP value at the time the current function was initially entered
///
/// ## Returns
///
/// * The type of the variable
/// * Code to push the variable and possibly evaluate a closure if it's bound to one
let getVar (ctxt : Context) (varName : string) (varRng : Range) (stackLevel : int) : Gen<Ty * Instruction> =
    match ctxt.varCtxt.TryFind(varName) with
    | Some { ty = ty ; address = Local(offset) } ->
        gen {
            return (ty, PushLoc <| stackLevel - offset)
        }
    | Some { ty = ty ; address = Global(addr) } ->
        gen {
            return (ty, PushGlob addr)
        }
    | None ->
        error $"identifier '{varName}' unknown" varRng

/// For a binary operation `e1 binOp e2`, generate code to push the result's raw basic value
/// (not heap reference) onto the stack
///
/// ## Parameters
///
/// * ctxt - The context the binary operation occurs under
/// * e1 - The left operand
/// * e2 - The right operand
/// * instr - The instruction that pops the top two stack elements `v1` and `v2` and
///           pushes the result of `v1 binOp v2` onto the stack
/// * stackLevel - SP1-SP0, where SP0 is the SP value at the time the current function was initially
///                entered and SP1 is the SP value at the time the returned code begins executing
///
/// ## Returns
///
/// * The type of the result of the binary operation
/// * Code that pushes the value of `e1 binOp e2`
let rec binOpB (ctxt : Context) (e1 : Expr) (e2 : Expr) (instr : Instruction) (stackLevel : int) : Gen<Ty * List<Instruction>> =
    gen {
        let! ty1, code1 = codeB ctxt e1 stackLevel
        let! ty2, code2 = codeB ctxt e2 (stackLevel + 1)
        do!
            match ty1 with
            | IntTy(_) ->
                pass
            | _ ->
                error $"expected lhs to have type 'int'" e1.Range
        do!
            match ty2 with
            | IntTy(_) ->
                pass
            | _ ->
                error $"expected rhs to have type 'int'" e2.Range
        return (
            IntTy(noRange),
            List.concat [code1; code2 ; [instr]]
        )
    }

/// For a binary operation `e1 binOp e2`, generate code to push the result's B-object
/// onto the stack
///
/// ## Parameters
///
/// * ctxt - The context the binary operation occurs under
/// * e1 - The left operand
/// * e2 - The right operand
/// * instr - The instruction that pops the top two stack elements `v1` and `v2` and
///           pushes the result of `v1 binOp v2` onto the stack
/// * stackLevel - SP1-SP0, where SP0 is the SP value at the time the current function was initially
///                entered and SP1 is the SP value at the time the returned code begins executing
///
/// ## Returns
///
/// * The type of the result of the binary operation
/// * Code that pushes the value of `e1 binOp e2`
and binOpV (ctxt : Context) (e1 : Expr) (e2 : Expr) (instr : Instruction) (stackLevel : int) : Gen<Ty * List<Instruction>> =
    gen {
        let! ty, code = binOpB ctxt e1 e2 instr stackLevel
        return (
            ty,
            List.concat [code; [MkBasic]]
        )
    }

/// Generates code that pushes a closure of an expression onto the stack
///
/// ## Parameters
/// * ctxt - The context that `expr` occurs under
/// * expr - The expression whose closure our code pushes onto the stack
/// * stackLevel - SP1-SP0, where SP0 is the SP value at the time the current function was initially
///                entered and SP1 is the SP value at the time the returned code begins executing
///
/// ## Returns
///
/// * The type of the expression
/// * Code that pushes the closure of `expr` onto the stack
and codeC (ctxt : Context) (expr : Expr) (stackLevel : int) : Gen<Ty * List<Instruction>> =
    gen {
            let freeVarList = Set.toList expr.FreeVars
            let! globalVars =
                letAll <| List.mapi (fun i varName -> getVar ctxt varName noRange (stackLevel + i)) freeVarList
            let pushGlobals = List.map snd globalVars
            let foldFreeVar (ctxt : Context) ((v, (ty, _)) : string * (Ty * Instruction)) (i : int) : Context =
                { ctxt with varCtxt = ctxt.varCtxt.Add(v, { ty = ty ; address = Global(i) }) }
            let ctxt' = List.fold2 foldFreeVar ctxt (List.zip freeVarList globalVars) [0 .. freeVarList.Length-1]
            let! tyExpr, codeExpr = codeV ctxt' expr 0
            let! executeClosureAddr = getFreshSymbolicAddr
            let! afterAddr = getFreshSymbolicAddr
            return (
                tyExpr,
                List.concat [
                    pushGlobals
                    [MkVec globalVars.Length]
                    [MkClos executeClosureAddr]
                    [Jump afterAddr]
                    [SymbolicAddress executeClosureAddr]
                    codeExpr
                    [Update]
                    [SymbolicAddress afterAddr]
                ]
            )
    }

/// Generates code that evaluates the expression `expr` and pushes its result's raw basic value
/// (not heap reference) onto the stack
///
/// ## Parameters
///
/// * ctxt - The context that expr occurs under
/// * expr - The expression to generate code for
/// * stackLevel - SP1-SP0, where SP0 is the SP value at the time the current function was initially
///                entered and SP1 is the SP value at the time the returned code begins executing
///
/// ## Returns
///
/// * The type of the expression, which should be a basic type like `IntTy`
/// * Code to evaluate `expr` and push its result onto the stack
and codeB (ctxt : Context) (expr : Expr) (stackLevel : int) : Gen<Ty * List<Instruction>> =
    match expr with
    | Expr.Int(n, _) ->
        gen {
            return (IntTy(noRange), [LoadC n])
        }
    | Expr.Plus(e1, e2, _) ->
        binOpB ctxt e1 e2 Add stackLevel
    | Expr.Minus(e1, e2, _) ->
        binOpB ctxt e1 e2 Sub stackLevel
    | Expr.Times(e1, e2, _) ->
        binOpB ctxt e1 e2 Mul stackLevel
    | Expr.Eq(e1, e2, _) ->
        binOpB ctxt e1 e2 Eq stackLevel
    | Expr.Leq(e1, e2, _) ->
        binOpB ctxt e1 e2 Leq stackLevel
    | Expr.Geq(e1, e2, _) ->
        binOpB ctxt e1 e2 Geq stackLevel
    | Expr.Lt(e1, e2, _) ->
        binOpB ctxt e1 e2 Lt stackLevel
    | Expr.Gt(e1, e2, _) ->
        binOpB ctxt e1 e2 Gt stackLevel
    | Expr.IfThenElse(cond, thenExpr, elseExpr, rng) ->
        gen {
            let! tyCond, codeCond = codeB ctxt cond stackLevel
            let! tyThen, codeThen = codeB ctxt thenExpr stackLevel
            let! tyElse, codeElse = codeB ctxt elseExpr stackLevel
            do!
                match tyCond with
                | IntTy(_) ->
                    pass
                | _ ->
                    error $"expected condition to have type 'int'" cond.Range
            do!
                match Ty.IsEqual tyThen tyElse with
                | true ->
                    pass
                | false ->
                    error $"expected 'then' and 'else' branch to have equal types" rng
            let! elseAddr = getFreshSymbolicAddr
            let! afterAddr = getFreshSymbolicAddr
            return (
                tyThen,
                List.concat [
                    codeCond
                    [JumpZ elseAddr]
                    codeThen
                    [Jump afterAddr]
                    [SymbolicAddress elseAddr]
                    codeElse
                    [SymbolicAddress afterAddr]
                ]
            )
        }
    | FunAbstraction(_, _, _) ->
        failwith "functions do not produce basic values"
    | _ ->
        gen {
            let! ty, code = codeV ctxt expr stackLevel
            return (
                ty,
                List.concat [code ; [GetBasic]]
            )
        }

/// Generates code that evaluates the expression `expr` and pushes a reference to its result's heap object
/// onto the stack.
///
/// ## Parameters
///
/// * ctxt - The context `expr` occurs under
/// * expr - The expression to generate code for
/// * stackLevel - SP1-SP0, where SP0 is the SP value at the time the current function was initially
///                entered and SP1 is the SP value at the time the returned code begins executing
///
/// ## Return
///
/// * The type of `expr`
/// * Code to evaluate `expr` and push its result onto the stack
and codeV (ctxt : Context) (expr : Expr) (stackLevel : int) : Gen<Ty * List<Instruction>> =
    match expr with
    | Expr.Int(n, _) ->
        gen {
            return (IntTy(noRange), [LoadC n ; MkBasic])
        }
    | Expr.Plus(e1, e2, rng) ->
        binOpV ctxt e1 e2 Add stackLevel
    | Expr.Minus(e1, e2, _) ->
        binOpV ctxt e1 e2 Sub stackLevel
    | Expr.Times(e1, e2, _) ->
        binOpV ctxt e1 e2 Mul stackLevel
    | Expr.Eq(e1, e2, _) ->
        binOpV ctxt e1 e2 Eq stackLevel
    | Expr.Leq(e1, e2, _) ->
        binOpV ctxt e1 e2 Leq stackLevel
    | Expr.Geq(e1, e2, _) ->
        binOpV ctxt e1 e2 Geq stackLevel
    | Expr.Lt(e1, e2, _) ->
        binOpV ctxt e1 e2 Lt stackLevel
    | Expr.Gt(e1, e2, _) ->
        binOpV ctxt e1 e2 Gt stackLevel
    | Expr.IfThenElse(cond, thenExpr, elseExpr, rng) ->
        gen {
            let! tyCond, codeCond = codeB ctxt cond stackLevel
            let! tyThen, codeThen = codeV ctxt thenExpr stackLevel
            let! tyElse, codeElse = codeV ctxt elseExpr stackLevel
            do!
                match tyCond with
                | IntTy(_) ->
                    pass
                | _ ->
                    error $"expected condition to have type 'int'" cond.Range
            do!
                match Ty.IsEqual tyThen tyElse with
                | true ->
                    pass
                | false ->
                    error $"expected 'then' and 'else' branch to have equal types" rng
            let! elseAddr = getFreshSymbolicAddr
            let! afterAddr = getFreshSymbolicAddr
            return (
                tyThen,
                List.concat [
                    codeCond
                    [JumpZ elseAddr]
                    codeThen
                    [Jump afterAddr]
                    [SymbolicAddress elseAddr]
                    codeElse
                    [SymbolicAddress afterAddr]
                ]
            )
        }
    | Var(name, rng) ->
        gen {
            let! ty, instr = getVar ctxt name rng stackLevel
            return (ty, [instr ; Eval])
        }
    | Let(varName, boundExpr, bodyExpr, rng) ->
        gen {
            let! tyBound, codeBound = codeC ctxt boundExpr stackLevel
            let varEntry = { address = Local(stackLevel + 1); ty = tyBound }
            let ctxt' = { ctxt with varCtxt = ctxt.varCtxt.Add(varName, varEntry) }
            let! tyBody, codeBody = codeV ctxt' bodyExpr (stackLevel + 1)
            return (tyBody, List.concat [codeBound ; codeBody ; [Slide 1]])
        }
    | LetTuple(varNames, boundExpr, body, rng) ->
        gen {
            let! tyBound, codeBound = codeV ctxt boundExpr stackLevel
            let! componentNameTys, n =
                match tyBound with
                | ProdTy(components, _) when components.Length = varNames.Length ->
                    gen {
                        return (List.zip varNames components), varNames.Length
                    }
                | _ ->
                    error $"expected bound expression to have a tuple type of length {varNames.Length}" rng
            let foldComponent (ctxt : Context) (i : int) ((name, ty) : string * Ty) : Context =
                { ctxt with varCtxt = ctxt.varCtxt.Add(name, { address = Local(stackLevel + i); ty = ty }) }
            let ctxt' = List.fold2 foldComponent ctxt [1 .. n] componentNameTys
            let! tyBody, codeBody = codeV ctxt' body (stackLevel + n)
            return (
                tyBody,
                List.concat [
                    codeBound
                    [GetVec]
                    codeBody
                    [Slide n]
                ]
            )
        }
    | LetRec(bindings, body , rng) ->
        gen {
            let n = bindings.Length
            let addVarToContext (ctxt : Context) ((name, ty, _) : string * Ty * Expr) (i : int) : Context =
                { ctxt with varCtxt = ctxt.varCtxt.Add(name, { ty = ty ; address = Local(stackLevel + i)})}
            let ctxt' = List.fold2 addVarToContext ctxt bindings [1 .. n]
            let! bindingClosures =
                letAll <| List.map (fun (_,_,e) -> codeC ctxt' e (stackLevel + n)) bindings
            let boundExprTys,pushClosureBlocks = List.unzip bindingClosures
            let rewriteClosureBlocks =
                List.map2
                    (fun block i -> List.concat [block ; [Rewrite i]])
                    pushClosureBlocks
                    [n .. -1 .. 1]
            let checkBindingTy (synthesizedTy : Ty) ((_, ascribedTy, _) : string * Ty * Expr) : Gen<Unit> =
                if Ty.IsEqual synthesizedTy ascribedTy then
                    gen {
                        return ()
                    }
                else
                    error $"ascribed type {ascribedTy} does not match synthesized type {synthesizedTy}" ascribedTy.Range
            do!
                doAll <| List.map2 checkBindingTy boundExprTys bindings
            let! bodyTy, bodyCode = codeV ctxt' body (stackLevel + n)
            return (
                bodyTy,
                List.concat [
                    [Alloc n]
                    List.concat rewriteClosureBlocks
                    bodyCode
                    [Slide n]
                ]
            )
        }
    | FunAbstraction(formals, body, rng) ->
        gen {
            let freeVarList = Set.toList expr.FreeVars
            let! globalVars =
                letAll <| List.mapi (fun i varName -> getVar ctxt varName rng (stackLevel + i)) freeVarList
            let pushGlobals = List.map snd globalVars
            let! callStartAddr = getFreshSymbolicAddr
            let! afterAddr = getFreshSymbolicAddr
            let addFormalToContext (ctxt : Context) (i : int)  (f : Formal) : Context =
                let entry = {
                    address = Local(-i)
                    ty = f.ty
                }
                { ctxt with varCtxt = ctxt.varCtxt.Add(f.name, entry) }
            let addGlobalToContext (ctxt : Context)
                                   (i : int)
                                   ((name, (ty,instr)) : string * (Ty * Instruction)) : Context =
                let entry = {
                    address = Global(i)
                    ty = ty
                }
                { ctxt with varCtxt = ctxt.varCtxt.Add(name, entry) }
            let ctxt' =
                List.fold2 addFormalToContext ctxt [0..formals.Length-1] formals
            let ctxt'' =
                List.fold2 addGlobalToContext ctxt' [0..freeVarList.Length-1] (List.zip freeVarList globalVars)
            let! bodyTy, bodyCode = codeV ctxt'' body 0
            let funTy = List.fold (fun (ty : Ty) (f : Formal) -> FunTy(f.ty, ty, noRange)) bodyTy formals
            return (
                funTy,
                List.concat [
                    pushGlobals
                    [MkVec <| List.length freeVarList]
                    [MkFunVal callStartAddr]
                    [Jump afterAddr]
                    [SymbolicAddress callStartAddr]
                    [TArg <| formals.Length]
                    bodyCode
                    [Return <| formals.Length]
                    [SymbolicAddress afterAddr]
                ]
            )
        }
    | Application(fnExpr, args, _) ->
        gen {
            let! tyFun, codeFun = codeV ctxt fnExpr (stackLevel + args.Length + 3)
            let! tyCodeArgs = letAll <| List.mapi (fun i e -> codeC ctxt e (stackLevel + (args.Length - 1 - i) + 3)) args
            let formalTys = tyFun.DomTyList
            do!
                if formalTys.Length < tyCodeArgs.Length then
                    error $"expected applied expression to have function type" fnExpr.Range
                else
                    pass
            let usedFormalTys = List.take tyCodeArgs.Length formalTys
            let checkEq (actual : Expr) ((tyActual, _) : Ty * List<Instruction>) (tyFormal : Ty) : Gen<Unit> =
                gen {
                    do!
                        if Ty.IsEqual tyActual tyFormal then
                            pass
                        else
                            error $"expected type of actual argument to match type of formal argument" actual.Range
                    return ()
                }
            do!
                doAll <| List.map3 checkEq args tyCodeArgs usedFormalTys
            let pushArgs = tyCodeArgs |> List.rev |> (List.map snd) |> List.concat
            let! afterAddr = getFreshSymbolicAddr
            return (
                tyFun.Apply args.Length,
                List.concat [
                    [Mark afterAddr]
                    pushArgs
                    codeFun
                    [Apply]
                    [SymbolicAddress afterAddr]
                ]
            )
        }
    | Tuple(elems, rng) ->
        gen {
            let! elemTyCodes = letAll <| List.mapi (fun i e -> codeC ctxt e (stackLevel + i)) elems
            let elemTys, elemCodes = List.unzip elemTyCodes
            return (
                ProdTy(elemTys, noRange),
                List.concat [
                    List.concat elemCodes
                    [MkVec elemCodes.Length]
                ]
            )
        }
    | RefConstructor(initExpr, _) ->
        gen {
            let! initExprTy, initExprCode = codeV ctxt initExpr stackLevel
            return (
                RefTy(initExprTy, noRange),
                List.concat [
                    initExprCode
                    [MkRef]
                ]
            )
        }
    | Deref(refExpr, rng) ->
        gen {
            let! refExprTy, refExprCode = codeV ctxt refExpr stackLevel
            let! elemTy =
                match refExprTy with
                | RefTy(elemTy, _) ->
                    gen {
                        return elemTy
                    }
                | _ ->
                    error $"Expected {refExpr} to have a reference type but instead found {refExprTy}" rng
            return (
                elemTy,
                List.concat [
                    refExprCode
                    [GetRef]
                ]
            )
        }
    | Assign(refExpr, newValExpr, _) ->
        failwith "todo"
    | Sequence(firstExpr, secondExpr, rng) ->
        gen {
            let! firstExprTy, firstExprCode = codeV ctxt firstExpr stackLevel
            let! secondExprTy, secondExprCode = codeV ctxt secondExpr stackLevel
            do!
                match firstExprTy with
                | ProdTy([], _) ->
                    gen {
                        return ()
                    }
                | _ ->
                    error $"expected {firstExpr} to have unit type." firstExpr.Range
            return (
                secondExprTy,
                List.concat [
                    firstExprCode
                    [Pop]
                    secondExprCode
                ]
            )
        }