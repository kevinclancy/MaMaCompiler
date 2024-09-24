module Environment

open Syntax

type Address =
    | Local of offset : int
    | Global of absolute : int

type VarContextEntry = {
    address : Address
    ty : Ty
}

type Context = {
    varCtxt : Map<string, VarContextEntry>
}