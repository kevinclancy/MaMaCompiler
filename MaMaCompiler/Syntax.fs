module Syntax

open Utils

type Ty =
    | IntTy of Range
    | FunTy of dom:Ty * cod:Ty * Range
    | ProdTy of components:List<Ty> * Range

    with
        member this.Range : Range =
            match this with
            | IntTy(rng)
            | FunTy(_,_,rng)
            | ProdTy(_,rng) ->
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
            | IntTy(_), IntTy(_) ->
                true
            | FunTy(domA, codA, _), FunTy(domB, codB, _) ->
                (Ty.IsEqual domA domB) && (Ty.IsEqual codA codB)
            | ProdTy(componentsL, _), ProdTy(componentsR, _) ->
                if componentsL.Length <> componentsR.Length then
                    false
                else
                    List.forall (fun (l,r) -> Ty.IsEqual l r) (List.zip componentsL componentsR)
            | _ ->
                false

type Formal = {
    name : string
    ty : Ty
}

type Expr =
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
    | IfThenElse of cond:Expr * thenExpr:Expr * elseExpr:Expr * Range
    | Int of int * Range
    | Tuple of List<Expr> * Range
    | LetTuple of componentVars:List<string> * bindTo:Expr * body:Expr * Range

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
            | IfThenElse(_,_,_,rng)
            | Int(_,rng)
            | Tuple(_, rng)
            | LetTuple(_,_,_,rng) ->
                rng