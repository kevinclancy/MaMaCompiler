module GenCode

open Syntax
open GenComputation
open TargetCode
open Environment

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

and binOpV (ctxt : Context) (e1 : Expr) (e2 : Expr) (instr : Instruction) (stackLevel : int) : Gen<Ty * List<Instruction>> =
    gen {
        let! ty, code = binOpB ctxt e1 e2 instr stackLevel
        return (
            ty,
            List.concat [code; [MkBasic]]
        )
    }

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
            /// TODO: check that boundExprTys match the types of bindings
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