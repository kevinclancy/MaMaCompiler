module Syntax

open Utils

type Ty =
    | IntTy of Range
    | FunTy of dom:Ty * cod:Ty * Range

    with
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
    | Let of bound_var:string * bind_to:Expr * body:Expr * Range
    | Application of fnExpr:Expr * args:List<Expr> * Range
    | IfThenElse of cond:Expr * thenExpr:Expr * elseExpr:Expr * Range
    | Int of int * Range

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
            | Application(_,_,rng)
            | IfThenElse(_,_,_,rng)
            | Int(_,rng) ->
                rng