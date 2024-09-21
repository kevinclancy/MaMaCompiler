module Syntax

open Utils

type Ty =
    | IntTy of Range
    | FunTy of dom:Ty * cod:Ty * Range

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
    | IfThenElse of cond:Expr * thenExpr:Expr * elseExpr:Expr