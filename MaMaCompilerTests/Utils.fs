module Utils

open FSharp.Text.Lexing
open Syntax

let parseExpr (s : string) : Expr =
    let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(s)
    Parser.expr (Lexer.token) lexbuffer

let parseProg (s : string) : Prog =
    let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(s)
    Parser.prog (Lexer.token) lexbuffer