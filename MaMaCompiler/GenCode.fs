module GenCode

open Syntax
open GenComputation
open TargetCode
open Environment
open Utils

/// Generates code to push the value corresponding to a variable onto the stack
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
/// * Code to push the variable onto the stack
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
/// (not heap reference) onto the basic stack
///
/// ## Parameters
///
/// * ctxt - The context the binary operation occurs under
/// * e1 - The left operand
/// * e2 - The right operand
/// * instr - The instruction that pops the top two stack elements `v1` and `v2` and
///           pushes the result of `v1 binOp v2` onto the basic stack
/// * stackLevel - SP1-SP0, where SP0 is the SP value at the time the current function was initially
///                entered and SP1 is the SP value at the time the returned code begins executing
///
/// ## Returns
///
/// * The type of the result of the binary operation
/// * Code that pushes the value of `e1 binOp e2`
let rec binOpB (ctxt : Context) (e1 : Expr) (e2 : Expr) (instr : Instruction) (stackLevel : int) : Gen<Ty * List<Instruction>> =
    gen {
        let! ty1, code1 = codeB { ctxt with tailPos = None } e1 stackLevel
        let! ty2, code2 = codeB { ctxt with tailPos = None } e2 stackLevel
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
/// * instr - The instruction that pops the top two basic stack elements `v1` and `v2` and
///           pushes the result of `v1 binOp v2` onto the basic stack
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
    match expr with
    | Int(n, _) ->
        gen {
            return (
                IntTy(noRange),
                [LoadC n ; MkBasic]
            )
        }
    | Var(name, rng) ->
        gen {
            let! varTy, varInstr = getVar ctxt name rng stackLevel
            return (
                varTy,
                [varInstr]
            )
        }
    | FunAbstraction(_,_,_) as funAbs ->
        codeV ctxt funAbs stackLevel
    | _ ->
      gen {
        let freeVarList = Set.toList expr.FreeVars
        let! globalVars =
            letAll <| List.mapi (fun i varName -> getVar ctxt varName noRange (stackLevel + i)) freeVarList
        let pushGlobals = List.map snd globalVars
        let foldFreeVar (ctxt : Context) ((v, (ty, _)) : string * (Ty * Instruction)) (i : int) : Context =
            { ctxt with varCtxt = ctxt.varCtxt.Add(v, { ty = ty ; address = Global(i) }) }
        let ctxt' = List.fold2 foldFreeVar ctxt (List.zip freeVarList globalVars) [0 .. freeVarList.Length-1]
        let! tyExpr, codeExpr = codeV { ctxt' with tailPos = None } expr 0
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
            let! tyCond, codeCond = codeB { ctxt with tailPos = None } cond stackLevel
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
            let! tyCond, codeCond = codeB { ctxt with tailPos = None } cond stackLevel
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
    | Match(scrutinee, cases, _) ->
        gen {
            let! scrutTy, scrutCode = codeV { ctxt with tailPos = None } scrutinee stackLevel

            // The address directly after the match expression
            let! afterAddr = getFreshSymbolicAddr

            let! scrutTyVariants =
                match scrutTy with
                | IdTy(name,_) ->
                    match ctxt.tyCtxt.TryFind name with
                    | Some(SumTy(variants, _)) ->
                        gen {
                            return variants
                        }
                    | _ ->
                        error $"Match scrutinee expected to have sum type, but found '{scrutTy}'" scrutinee.Range
                | _ ->
                    error $"Match scrutinee expected to have sum type, but found '{scrutTy}'" scrutinee.Range

            /// Add *case* to the list whose key is its constructorName
            /// Or to the list whose key is "catchAll" if it is a CatchAll case
            let foldCase (m : Map<string, List<MatchCase>>) (case : MatchCase) : Map<string, List<MatchCase>> =
                let constructorName = case.ConstructorName
                if m.ContainsKey constructorName then
                    m.Add(constructorName, case :: m[constructorName])
                else
                    m.Add(constructorName, [case])

            let caseMap = List.fold foldCase Map.empty cases

            // defaultTys - The types of the 'default' case bodies
            // code - Code that pattern matches and evaluates guards, and then jumps to the appropriate body and evaluates it
            // defualtAddr - The address of *defaultCode*
            let! (defaultTyCases : List<Ty * MatchCase>, defaultCode : List<Instruction>, defaultAddr : int) =
                match caseMap.TryFind "catchAll" with
                | Some(cases) ->
                    let foldCases ((tys, prevBodyCode, prevGuardCode) : List<Ty * MatchCase> * List<Instruction> * List<Instruction>)
                                  (m : MatchCase) : Gen<List<Ty * MatchCase> * List<Instruction> * List<Instruction>> =
                        match m with
                        | CatchAllCase(varName, None, body, _) ->
                            gen {
                                let ctxt' = {
                                    ctxt with
                                        varCtxt = ctxt.varCtxt.Add(varName, { ty = scrutTy ; address = Local(stackLevel + 1) })
                                }
                                let! bodyTy, bodyCode = codeV ctxt' body (stackLevel + 1)
                                return (
                                    (bodyTy, m) :: tys,
                                    prevBodyCode,
                                    List.concat [
                                        prevGuardCode
                                        bodyCode
                                        [Slide(1, 1)]
                                        [Jump afterAddr]
                                    ]
                                )
                            }
                        | CatchAllCase(varName, Some(whenCond), body, _) ->
                            gen {
                                let ctxt' = {
                                    ctxt with
                                        varCtxt = ctxt.varCtxt.Add(varName, { ty = scrutTy ; address = Local(stackLevel + 1) })
                                }
                                let! guardTy, guardCode = codeV { ctxt' with tailPos = None } whenCond (stackLevel + 1)
                                do!
                                    if not (Ty.IsEqual guardTy (IntTy(noRange))) then
                                        error $"Expeceted type 'int' as guard expression type, but found '{guardTy}'" whenCond.Range
                                    else
                                        pass
                                let! bodyTy, bodyCode = codeV ctxt' body stackLevel
                                let! bodyAddr = getFreshSymbolicAddr
                                return (
                                    (bodyTy, m) :: tys,
                                    List.concat [
                                        prevBodyCode
                                        [SymbolicAddress bodyAddr]
                                        bodyCode
                                        [Slide(1, 1)]
                                        [Jump afterAddr]
                                    ],
                                    List.concat [
                                        prevGuardCode
                                        guardCode
                                        [JumpNZ bodyAddr]
                                    ]
                                )
                            }
                        | _ ->
                            failwith "impossible"
                    gen {
                        let! defaultCasesAddr = getFreshSymbolicAddr
                        let! (tys, bodyCode, guardCode) = foldM ([], [], []) foldCases (List.rev cases)
                        return (
                            tys,
                            List.concat [[SymbolicAddress defaultCasesAddr] ; guardCode ; [Halt] ; bodyCode],
                            defaultCasesAddr
                        )
                    }
                | None ->
                    gen {
                        let! defaultCasesAddr = getFreshSymbolicAddr
                        return (
                            [],
                            [SymbolicAddress defaultCasesAddr ; Slide(1, 1) ; Halt],
                            defaultCasesAddr
                        )
                    }

            let caseMap = Map.remove "catchAll" caseMap

            /// Returns (ty, guardCode, bodyCode), where *ty* is the list of type of the body,
            /// *guardCode* is a sequence of instructions that performs pattern matching and guard evaluation and jumps to the corresponding
            /// body if it succeeds.
            /// *bodyCode* is a labelled sequence of instructions that evaluates the case's body and
            /// pushes its value onto the stack, then jumps to after the match
            let genCase (case : MatchCase) : Gen<Ty * List<Instruction> * List<Instruction>> =
                match case with
                | ConstructorCase(constructorName, argVar, Some(whenCond), body, caseRng) ->
                    gen {
                        let! argTy =
                            match scrutTyVariants.TryFind constructorName with
                            | Some(ty) ->
                                gen {
                                    return ty
                                }
                            | None ->
                                error $"The type '{scrutTy.ToString()}' does not have a variant called '{constructorName}'" caseRng
                        let ctxt' = {
                            ctxt with
                                varCtxt = ctxt.varCtxt.Add(argVar, { ty = argTy ; address = Local(stackLevel + 1) })
                        }
                        let! guardTy, guardCode = codeV { ctxt' with tailPos = None } whenCond (stackLevel + 1)
                        do!
                            if not (Ty.IsEqual guardTy (IntTy(noRange))) then
                                error $"Expeceted type 'int' as guard expression type, but found '{guardTy}'" whenCond.Range
                            else
                                pass
                        let! bodyTy, bodyCode = codeV ctxt' body (stackLevel + 1)
                        let! bodyAddr = getFreshSymbolicAddr
                        return (
                            bodyTy,
                            List.concat [
                                [TGetConstructorArg]
                                guardCode
                                [JumpNZ bodyAddr]
                                [Pop]
                            ],
                            List.concat [
                                [SymbolicAddress bodyAddr]
                                bodyCode
                                [Slide(2, 1)]
                                [Jump afterAddr]
                            ]
                        )
                    }
                | ConstructorCase(constructorName, argVar, None, body, caseRng) ->
                    gen {
                        let! argTy =
                            match scrutTyVariants.TryFind constructorName with
                            | Some(ty) ->
                                gen {
                                    return ty
                                }
                            | None ->
                                error $"The type '{scrutTy.ToString()}' does not have a variant called '{constructorName}'" caseRng
                        let ctxt' = {
                            ctxt with
                                varCtxt = ctxt.varCtxt.Add(argVar, { ty = argTy ; address = Local(stackLevel + 1) })
                        }
                        let! bodyTy, bodyCode = codeV ctxt' body (stackLevel + 1)
                        return (
                            bodyTy,
                            List.concat [
                                [TGetConstructorArg]
                                bodyCode
                                [Slide(2, 1)]
                                [Jump afterAddr]
                            ],
                            []
                        )
                    }
                | _ ->
                    failwith "impossible"

            /// Returns (tyCases, code, addr) for all guard and body code for all cases of a specific variant constructor
            ///
            /// * *tyCases* is a list of the type/matchCase pairs of all bodies for this constructor
            ///
            /// * *code* contains the "guard" code used to match cases and dispatch to their bodies,
            /// followed by labelled body blocks for each case body
            ///
            /// * *nameAddr* is a pair (name, addr) of the constructor name and the address of *code*
            let mapCaseMapEntry ((constructorName, cases) : string * List<MatchCase>)
                : Gen<List<Ty * MatchCase> * List<Instruction> * (string * int)> =

                gen {
                    let! constructorCasesAddr = getFreshSymbolicAddr
                    let! mappedCases = letAll (List.map genCase (List.rev cases))
                    let (caseTys, caseGuardCodes, caseBodyCodes) = List.unzip3 mappedCases
                    return (
                        List.zip caseTys cases,
                        List.concat [
                            [SymbolicAddress constructorCasesAddr]
                            List.concat caseGuardCodes
                            [Jump defaultAddr]
                            List.concat caseBodyCodes
                        ],
                        (constructorName, constructorCasesAddr)
                    )
                }

            let! caseResults = letAll <| List.map mapCaseMapEntry (Map.toList caseMap)
            let (constructorCaseTys, constructorCodes, constructorAddrs) = List.unzip3 caseResults
            let allTyCases = List.append defaultTyCases (List.concat constructorCaseTys)

            let (ty0, _) = allTyCases[0]
            let checkTy ((ty, case) : Ty * MatchCase) : Gen<unit> =
                if Ty.IsEqual ty ty0 then
                    pass
                else
                    error
                        $"Expected case to have type '{ty0.ToString()}' but instead found '{ty.ToString()}'"
                        case.Range

            do! doAll (List.map checkTy allTyCases)

            let constructorAddrMap = Map.ofList constructorAddrs
            let constructorNameToJump (name : string) : Instruction =
                match constructorAddrMap.TryFind name with
                | Some(addr) ->
                    Jump addr
                | None ->
                    Jump defaultAddr

            let! jumpTableAddr = getFreshSymbolicAddr
            let jumpTable = List.map (fun (name, _) -> constructorNameToJump name) (Map.toList scrutTyVariants)

            return (
                ty0,
                List.concat [
                    scrutCode
                    [TSum jumpTableAddr]
                    [SymbolicAddress jumpTableAddr]
                    jumpTable
                    defaultCode
                    List.concat constructorCodes
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
            let! tyBound, codeBound = codeV { ctxt with tailPos = None } boundExpr stackLevel
            let varEntry = { address = Local(stackLevel + 1); ty = tyBound }
            let ctxt' = { ctxt with varCtxt = ctxt.varCtxt.Add(varName, varEntry) }
            let! tyBody, codeBody = codeV ctxt' bodyExpr (stackLevel + 1)
            return (tyBody, List.concat [codeBound ; codeBody ; [Slide(1, 1)]])
        }
    | LetTuple(varNames, boundExpr, body, rng) ->
        gen {
            let! tyBound, codeBound = codeV { ctxt with tailPos = None } boundExpr stackLevel
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
                    [GetTuple]
                    codeBody
                    [Slide(n, 1)]
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
                letAll <| List.map (fun (_,_,e) -> codeV { ctxt' with tailPos = None } e (stackLevel + n)) bindings
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
                    [Slide(n, 1)]
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
            let! bodyTy, bodyCode = codeV { ctxt'' with tailPos = Some(formals.Length) } body 0
            let funTy = List.fold (fun (ty : Ty) (f : Formal) -> FunTy(f.ty, ty, noRange)) bodyTy formals
            return (
                funTy,
                List.concat [
                    pushGlobals
                    [MkVec <| List.length freeVarList]
                    [MkFunVal callStartAddr]
                    [Jump afterAddr]
                    [SymbolicAddress callStartAddr]
                    [TArg formals.Length]
                    bodyCode
                    [Return formals.Length]
                    [SymbolicAddress afterAddr]
                ]
            )
        }
    | Application(fnExpr, args, _) ->
        gen {
            let numAdminElems = match ctxt.tailPos with | Some(_) -> 0 | None -> 1
            let! tyFun, codeFun = codeV { ctxt with tailPos = None } fnExpr (stackLevel + args.Length + numAdminElems)
            let! tyCodeArgs = letAll <| List.mapi (fun i e -> codeV { ctxt with tailPos = None } e (stackLevel + (args.Length - 1 - i) + numAdminElems)) args
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
                match ctxt.tailPos with
                | Some(numOuterArgs) ->
                    List.concat [
                        pushArgs
                        codeFun
                        [Slide(stackLevel + numOuterArgs, args.Length + 1)]
                        [Apply]
                    ]
                | None ->
                    List.concat [
                        [Mark afterAddr]
                        pushArgs
                        codeFun
                        [Apply]
                        [SymbolicAddress afterAddr]
                    ]
            )
        }
    | ConstructorApplication(name, arg, _) ->
        gen {
            let! argTy, argCode = codeV { ctxt with tailPos = None } arg stackLevel
            let constructor = ctxt.constructorCtxt[name]
            do!
                if Ty.IsEqual argTy constructor.contentTy then
                    pass
                else
                    error $"Expected expression of type '{constructor.contentTy}', but found '{argTy}'" arg.Range
            return (
                IdTy(constructor.sumTyName, noRange),
                List.concat [
                    argCode
                    [MkSum constructor.index]
                ]
            )
        }
    | Tuple(elems, rng) ->
        gen {
            let! elemTyCodes = letAll <| List.mapi (fun i e -> codeV { ctxt with tailPos = None } e (stackLevel + i)) elems
            let elemTys, elemCodes = List.unzip elemTyCodes
            return (
                ProdTy(elemTys, noRange),
                List.concat [
                    List.concat elemCodes
                    [MkVec elemCodes.Length]
                    [MkTuple]
                ]
            )
        }
    | RefConstructor(initExpr, _) ->
        gen {
            let! initExprTy, initExprCode = codeV { ctxt with tailPos = None } initExpr stackLevel
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
            let! refExprTy, refExprCode = codeV { ctxt with tailPos = None } refExpr stackLevel
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
        gen {
            let! newValTy, newValCode = codeV { ctxt with tailPos = None } newValExpr stackLevel
            let! refExprTy, refExprCode = codeV { ctxt with tailPos = None } refExpr (stackLevel + 1)
            do!
                match refExprTy with
                | RefTy(innerTy, _) ->
                    if Ty.IsEqual innerTy newValTy then
                        gen {
                            return ()
                        }
                    else
                        error $"expected lhs to have type Ref {newValTy} but instead had type {refExprTy}" refExpr.Range
                | _ ->
                    error $"expected lhs to have reference type but instead it had type {refExprTy}" refExpr.Range
            return (
                ProdTy([], noRange),
                List.concat [
                    newValCode
                    refExprCode
                    [RefAssign]
                ]
            )
        }
    | Sequence(firstExpr, secondExpr, rng) ->
        gen {
            let! firstExprTy, firstExprCode = codeV { ctxt with tailPos = None } firstExpr stackLevel
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