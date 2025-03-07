module Syntax

open Utils

/// Variant(constructorName, type)
type Variant = string * Ty

and Ty =
    | IntTy of Range
    | FunTy of dom:Ty * cod:Ty * Range
    | ProdTy of components:List<Ty> * Range
    | RefTy of containedTy:Ty * Range
    /// SumTy(variants, rng) - A sum type, where *variants* maps each constructor name to the type of
    /// the constructor argument
    | SumTy of variants:Map<string, Ty> * Range
    | IdTy of name:string * Range

    with
        member this.Range : Range =
            match this with
            | IntTy(rng)
            | IdTy(_, rng)
            | FunTy(_,_,rng)
            | ProdTy(_,rng)
            | RefTy(_,rng)
            | SumTy(_, rng) ->
                rng

        member this.Apply (n : int) : Ty =
            match (n, this) with
            | (0, _) ->
                this
            | (_, FunTy(dom, cod, _)) ->
                cod.Apply (n - 1)
            | _ ->
                failwith "applied function type to too many args"

        member this.DomTyList : List<Ty> =
            match this with
            | FunTy(dom, cod, _) ->
                dom :: cod.DomTyList
            | _ ->
                []

        static member IsEqual (tyA : Ty) (tyB : Ty) : bool =
            match (tyA, tyB) with
            | SumTy(variantsA, _), SumTy(variantsB, _) ->
                false
            | IdTy(n,_), IdTy(m,_) when n = m ->
                true
            | IntTy(_), IntTy(_) ->
                true
            | FunTy(domA, codA, _), FunTy(domB, codB, _) ->
                (Ty.IsEqual domA domB) && (Ty.IsEqual codA codB)
            | ProdTy(componentsL, _), ProdTy(componentsR, _) ->
                if componentsL.Length <> componentsR.Length then
                    false
                else
                    List.forall (fun (l,r) -> Ty.IsEqual l r) (List.zip componentsL componentsR)
            | RefTy(containedTyA, _), RefTy(containedTyB, _) ->
                Ty.IsEqual containedTyA containedTyB
            | _ ->
                false

type Typedef =
    | Typedef of typename:string * variants:List<Variant> * Range

type Formal = {
    name : string
    ty : Ty
}

type MatchCase =
    | ConstructorCase of name:string * argVar:string * whenCond:Option<Expr> * body:Expr * Range
    | CatchAllCase of varName:string * whenCond:Option<Expr> * body:Expr * Range

    with
        /// Returns the name of the outer-level constructor for this case,
        /// or "catchAll" if the cases has a catch-all pattern
        member this.ConstructorName : string =
            match this with
            | ConstructorCase(name, _, _, _, _) ->
                name
            | CatchAllCase(_, _, _, _) ->
                "catchAll"

        member this.FreeVars : Set<string> =
            match this with
            | ConstructorCase(name, argVar, whenCond, body, _) ->
                let whenCondVars = match whenCond with | Some(x) -> x.FreeVars | None -> Set.empty
                Set.remove argVar (Set.union whenCondVars body.FreeVars)
            | CatchAllCase(varName, whenCond, body, _) ->
                let whenCondVars = match whenCond with | Some(x) -> x.FreeVars | None -> Set.empty
                Set.remove varName (Set.union whenCondVars body.FreeVars)

        member this.Range : Range =
            match this with
            | ConstructorCase(_, _, _, _, rng)
            | CatchAllCase(_, _, _, rng) ->
                rng

and Expr =
    | Plus of Expr * Expr * Range
    | Minus of Expr * Expr * Range
    | Times of Expr * Expr * Range
    | Eq of Expr * Expr * Range
    | Leq of Expr * Expr * Range
    | Geq of Expr * Expr * Range
    | Lt of Expr * Expr * Range
    | Gt of Expr * Expr * Range
    | FunAbstraction of formals:List<Formal> * body:Expr * Range
    | Var of string * Range
    | Let of bound_var:string * bindTo:Expr * body:Expr * Range
    | LetRec of bindings:List<string * Ty * Expr> * body:Expr * Range
    | Application of fnExpr:Expr * args:List<Expr> * Range
    | ConstructorApplication of name:string * arg:Expr * Range
    | Match of scrutinee:Expr * cases:List<MatchCase> * Range
    | IfThenElse of cond:Expr * thenExpr:Expr * elseExpr:Expr * Range
    | Int of int * Range
    | Tuple of List<Expr> * Range
    | LetTuple of componentVars:List<string> * bindTo:Expr * body:Expr * Range
    | RefConstructor of init:Expr * Range
    | Deref of ref:Expr * Range
    | Assign of ref:Expr * newVal:Expr * Range
    | Sequence of first:Expr * second:Expr * Range

    with
        member this.FreeVars : Set<string> =
            match this with
            | Plus(e0, e1, _)
            | Minus(e0, e1, _)
            | Times(e0, e1, _)
            | Eq(e0, e1, _)
            | Leq(e0, e1, _)
            | Geq(e0, e1, _)
            | Lt(e0, e1, _)
            | Gt(e0, e1, _) ->
                Set.union e0.FreeVars e1.FreeVars
            | FunAbstraction(formals, body, _) ->
                let formalNames = Set.ofList <| List.map (fun f -> f.name) formals
                Set.difference body.FreeVars formalNames
            | Var(name, _) ->
                Set.singleton name
            | Let(varName, boundExpr, bodyExpr, _) ->
                Set.union boundExpr.FreeVars (bodyExpr.FreeVars.Remove(varName))
            | LetRec(bindings, body, _) ->
                let boundVars = List.fold (fun vars (nm, _, _) -> Set.add nm vars) Set.empty bindings
                let bindingFreeVars =
                    Set.unionMany <| List.map (fun (_, _, expr : Expr) -> expr.FreeVars) bindings
                Set.difference (Set.union bindingFreeVars body.FreeVars) boundVars
            | Application(fnExpr, argExprs, _) ->
                let argFreeVars = Set.unionMany <| List.map (fun (x : Expr) -> x.FreeVars) argExprs
                Set.union fnExpr.FreeVars argFreeVars
            | ConstructorApplication(name, arg, _) ->
                arg.FreeVars
            | Match(scrutinee, matchCases, _) ->
                Set.union
                    scrutinee.FreeVars
                    (Set.unionMany <| List.map (fun (x : MatchCase) -> x.FreeVars) matchCases)
            | IfThenElse(condExpr, thenExpr, elseExpr, _) ->
                Set.unionMany [
                    condExpr.FreeVars
                    thenExpr.FreeVars
                    elseExpr.FreeVars
                ]
            | Int(_, _) ->
                Set.empty
            | Tuple(elems, _) ->
                Set.unionMany (List.map (fun (e : Expr) -> e.FreeVars) elems)
            | LetTuple(componentVars, bindTo, body, _) ->
                Set.union
                    bindTo.FreeVars
                    (Set.difference body.FreeVars (Set.ofList componentVars))
            | RefConstructor(initExpr, _) ->
                initExpr.FreeVars
            | Deref(refExpr, _) ->
                refExpr.FreeVars
            | Assign(refExpr, newValExpr, _) ->
                Set.union refExpr.FreeVars newValExpr.FreeVars
            | Sequence(firstExpr, secondExpr, _) ->
                Set.union firstExpr.FreeVars secondExpr.FreeVars

        member this.Range : Range =
            match this with
            | Plus(_,_,rng)
            | Minus(_,_,rng)
            | Times(_,_,rng)
            | Eq(_,_,rng)
            | Leq(_,_,rng)
            | Geq(_,_,rng)
            | Lt(_,_,rng)
            | Gt(_,_,rng)
            | FunAbstraction(_,_,rng)
            | Var(_, rng)
            | Let(_,_,_,rng)
            | LetRec(_,_,rng)
            | Application(_,_,rng)
            | ConstructorApplication(_,_,rng)
            | IfThenElse(_,_,_,rng)
            | Match(_,_,rng)
            | Int(_,rng)
            | Tuple(_, rng)
            | LetTuple(_,_,_,rng)
            | RefConstructor(_, rng)
            | Deref(_, rng)
            | Assign(_, _, rng)
            | Sequence(_, _, rng) ->
                rng

type Prog = { typedefs : List<Typedef> ; expr : Expr }