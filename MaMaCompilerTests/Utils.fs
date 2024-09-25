module Utils

open FSharp.Text.Lexing
open Syntax

let parseExpr (s : string) : Expr =
    let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(s)
    Parser.expr (Lexer.token) lexbuffer