// Implementation file for parser generated by fsyacc
module Parser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open FSharp.Text.Lexing
open FSharp.Text.Parsing.ParseHelpers
# 1 "Parser.fsy"


open Syntax


# 12 "Parser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | NEW
  | AMPERSAND
  | RIGHTARROW
  | DELETE
  | RETURN
  | VOID
  | EOF
  | FUN
  | TYPEDEF
  | TO
  | WHILE
  | FOR
  | SWITCH
  | CASE
  | DEFAULT
  | COLON
  | STRUCT
  | BREAK
  | COMMA
  | PERIOD
  | PLUS
  | MINUS
  | TIMES
  | LEQ
  | GEQ
  | LT
  | GT
  | GETS
  | SEMICOLON
  | IF
  | ELSE
  | THEN
  | EQ
  | IN
  | LET
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | LSQUAREBRACK
  | RSQUAREBRACK
  | TYPEINT
  | INT of (int)
  | ID of (string)
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_NEW
    | TOKEN_AMPERSAND
    | TOKEN_RIGHTARROW
    | TOKEN_DELETE
    | TOKEN_RETURN
    | TOKEN_VOID
    | TOKEN_EOF
    | TOKEN_FUN
    | TOKEN_TYPEDEF
    | TOKEN_TO
    | TOKEN_WHILE
    | TOKEN_FOR
    | TOKEN_SWITCH
    | TOKEN_CASE
    | TOKEN_DEFAULT
    | TOKEN_COLON
    | TOKEN_STRUCT
    | TOKEN_BREAK
    | TOKEN_COMMA
    | TOKEN_PERIOD
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_TIMES
    | TOKEN_LEQ
    | TOKEN_GEQ
    | TOKEN_LT
    | TOKEN_GT
    | TOKEN_GETS
    | TOKEN_SEMICOLON
    | TOKEN_IF
    | TOKEN_ELSE
    | TOKEN_THEN
    | TOKEN_EQ
    | TOKEN_IN
    | TOKEN_LET
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_LSQUAREBRACK
    | TOKEN_RSQUAREBRACK
    | TOKEN_TYPEINT
    | TOKEN_INT
    | TOKEN_ID
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startexpr
    | NONTERM__startprog
    | NONTERM_expr
    | NONTERM_Expr
    | NONTERM_Formal
    | NONTERM_FormalList
    | NONTERM_ExprList
    | NONTERM_Type
    | NONTERM_prog

// This function maps tokens to integer indexes
let tagOfToken (t:token) = 
  match t with
  | NEW  -> 0 
  | AMPERSAND  -> 1 
  | RIGHTARROW  -> 2 
  | DELETE  -> 3 
  | RETURN  -> 4 
  | VOID  -> 5 
  | EOF  -> 6 
  | FUN  -> 7 
  | TYPEDEF  -> 8 
  | TO  -> 9 
  | WHILE  -> 10 
  | FOR  -> 11 
  | SWITCH  -> 12 
  | CASE  -> 13 
  | DEFAULT  -> 14 
  | COLON  -> 15 
  | STRUCT  -> 16 
  | BREAK  -> 17 
  | COMMA  -> 18 
  | PERIOD  -> 19 
  | PLUS  -> 20 
  | MINUS  -> 21 
  | TIMES  -> 22 
  | LEQ  -> 23 
  | GEQ  -> 24 
  | LT  -> 25 
  | GT  -> 26 
  | GETS  -> 27 
  | SEMICOLON  -> 28 
  | IF  -> 29 
  | ELSE  -> 30 
  | THEN  -> 31 
  | EQ  -> 32 
  | IN  -> 33 
  | LET  -> 34 
  | LPAREN  -> 35 
  | RPAREN  -> 36 
  | LBRACK  -> 37 
  | RBRACK  -> 38 
  | LSQUAREBRACK  -> 39 
  | RSQUAREBRACK  -> 40 
  | TYPEINT  -> 41 
  | INT _ -> 42 
  | ID _ -> 43 

// This function maps integer indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_NEW 
  | 1 -> TOKEN_AMPERSAND 
  | 2 -> TOKEN_RIGHTARROW 
  | 3 -> TOKEN_DELETE 
  | 4 -> TOKEN_RETURN 
  | 5 -> TOKEN_VOID 
  | 6 -> TOKEN_EOF 
  | 7 -> TOKEN_FUN 
  | 8 -> TOKEN_TYPEDEF 
  | 9 -> TOKEN_TO 
  | 10 -> TOKEN_WHILE 
  | 11 -> TOKEN_FOR 
  | 12 -> TOKEN_SWITCH 
  | 13 -> TOKEN_CASE 
  | 14 -> TOKEN_DEFAULT 
  | 15 -> TOKEN_COLON 
  | 16 -> TOKEN_STRUCT 
  | 17 -> TOKEN_BREAK 
  | 18 -> TOKEN_COMMA 
  | 19 -> TOKEN_PERIOD 
  | 20 -> TOKEN_PLUS 
  | 21 -> TOKEN_MINUS 
  | 22 -> TOKEN_TIMES 
  | 23 -> TOKEN_LEQ 
  | 24 -> TOKEN_GEQ 
  | 25 -> TOKEN_LT 
  | 26 -> TOKEN_GT 
  | 27 -> TOKEN_GETS 
  | 28 -> TOKEN_SEMICOLON 
  | 29 -> TOKEN_IF 
  | 30 -> TOKEN_ELSE 
  | 31 -> TOKEN_THEN 
  | 32 -> TOKEN_EQ 
  | 33 -> TOKEN_IN 
  | 34 -> TOKEN_LET 
  | 35 -> TOKEN_LPAREN 
  | 36 -> TOKEN_RPAREN 
  | 37 -> TOKEN_LBRACK 
  | 38 -> TOKEN_RBRACK 
  | 39 -> TOKEN_LSQUAREBRACK 
  | 40 -> TOKEN_RSQUAREBRACK 
  | 41 -> TOKEN_TYPEINT 
  | 42 -> TOKEN_INT 
  | 43 -> TOKEN_ID 
  | 46 -> TOKEN_end_of_input
  | 44 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startexpr 
    | 1 -> NONTERM__startprog 
    | 2 -> NONTERM_expr 
    | 3 -> NONTERM_Expr 
    | 4 -> NONTERM_Expr 
    | 5 -> NONTERM_Expr 
    | 6 -> NONTERM_Expr 
    | 7 -> NONTERM_Expr 
    | 8 -> NONTERM_Expr 
    | 9 -> NONTERM_Expr 
    | 10 -> NONTERM_Expr 
    | 11 -> NONTERM_Expr 
    | 12 -> NONTERM_Expr 
    | 13 -> NONTERM_Expr 
    | 14 -> NONTERM_Expr 
    | 15 -> NONTERM_Expr 
    | 16 -> NONTERM_Expr 
    | 17 -> NONTERM_Expr 
    | 18 -> NONTERM_Formal 
    | 19 -> NONTERM_FormalList 
    | 20 -> NONTERM_FormalList 
    | 21 -> NONTERM_ExprList 
    | 22 -> NONTERM_ExprList 
    | 23 -> NONTERM_Type 
    | 24 -> NONTERM_Type 
    | 25 -> NONTERM_prog 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 46 
let _fsyacc_tagOfErrorTerminal = 44

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | NEW  -> "NEW" 
  | AMPERSAND  -> "AMPERSAND" 
  | RIGHTARROW  -> "RIGHTARROW" 
  | DELETE  -> "DELETE" 
  | RETURN  -> "RETURN" 
  | VOID  -> "VOID" 
  | EOF  -> "EOF" 
  | FUN  -> "FUN" 
  | TYPEDEF  -> "TYPEDEF" 
  | TO  -> "TO" 
  | WHILE  -> "WHILE" 
  | FOR  -> "FOR" 
  | SWITCH  -> "SWITCH" 
  | CASE  -> "CASE" 
  | DEFAULT  -> "DEFAULT" 
  | COLON  -> "COLON" 
  | STRUCT  -> "STRUCT" 
  | BREAK  -> "BREAK" 
  | COMMA  -> "COMMA" 
  | PERIOD  -> "PERIOD" 
  | PLUS  -> "PLUS" 
  | MINUS  -> "MINUS" 
  | TIMES  -> "TIMES" 
  | LEQ  -> "LEQ" 
  | GEQ  -> "GEQ" 
  | LT  -> "LT" 
  | GT  -> "GT" 
  | GETS  -> "GETS" 
  | SEMICOLON  -> "SEMICOLON" 
  | IF  -> "IF" 
  | ELSE  -> "ELSE" 
  | THEN  -> "THEN" 
  | EQ  -> "EQ" 
  | IN  -> "IN" 
  | LET  -> "LET" 
  | LPAREN  -> "LPAREN" 
  | RPAREN  -> "RPAREN" 
  | LBRACK  -> "LBRACK" 
  | RBRACK  -> "RBRACK" 
  | LSQUAREBRACK  -> "LSQUAREBRACK" 
  | RSQUAREBRACK  -> "RSQUAREBRACK" 
  | TYPEINT  -> "TYPEINT" 
  | INT _ -> "INT" 
  | ID _ -> "ID" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | NEW  -> (null : System.Object) 
  | AMPERSAND  -> (null : System.Object) 
  | RIGHTARROW  -> (null : System.Object) 
  | DELETE  -> (null : System.Object) 
  | RETURN  -> (null : System.Object) 
  | VOID  -> (null : System.Object) 
  | EOF  -> (null : System.Object) 
  | FUN  -> (null : System.Object) 
  | TYPEDEF  -> (null : System.Object) 
  | TO  -> (null : System.Object) 
  | WHILE  -> (null : System.Object) 
  | FOR  -> (null : System.Object) 
  | SWITCH  -> (null : System.Object) 
  | CASE  -> (null : System.Object) 
  | DEFAULT  -> (null : System.Object) 
  | COLON  -> (null : System.Object) 
  | STRUCT  -> (null : System.Object) 
  | BREAK  -> (null : System.Object) 
  | COMMA  -> (null : System.Object) 
  | PERIOD  -> (null : System.Object) 
  | PLUS  -> (null : System.Object) 
  | MINUS  -> (null : System.Object) 
  | TIMES  -> (null : System.Object) 
  | LEQ  -> (null : System.Object) 
  | GEQ  -> (null : System.Object) 
  | LT  -> (null : System.Object) 
  | GT  -> (null : System.Object) 
  | GETS  -> (null : System.Object) 
  | SEMICOLON  -> (null : System.Object) 
  | IF  -> (null : System.Object) 
  | ELSE  -> (null : System.Object) 
  | THEN  -> (null : System.Object) 
  | EQ  -> (null : System.Object) 
  | IN  -> (null : System.Object) 
  | LET  -> (null : System.Object) 
  | LPAREN  -> (null : System.Object) 
  | RPAREN  -> (null : System.Object) 
  | LBRACK  -> (null : System.Object) 
  | RBRACK  -> (null : System.Object) 
  | LSQUAREBRACK  -> (null : System.Object) 
  | RSQUAREBRACK  -> (null : System.Object) 
  | TYPEINT  -> (null : System.Object) 
  | INT _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | ID _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
let _fsyacc_gotos = [| 0us;65535us;0us;65535us;1us;65535us;0us;1us;19us;65535us;0us;4us;2us;22us;14us;21us;21us;21us;23us;6us;24us;7us;25us;8us;26us;9us;27us;10us;28us;11us;29us;12us;30us;13us;33us;14us;37us;15us;41us;16us;42us;17us;45us;18us;46us;19us;47us;20us;2us;65535us;35us;53us;54us;53us;2us;65535us;35us;36us;54us;55us;2us;65535us;14us;43us;21us;56us;2us;65535us;50us;51us;59us;58us;1us;65535us;2us;3us;|]
let _fsyacc_sparseGotoTableRowOffsets = [|0us;1us;2us;4us;24us;27us;30us;33us;36us;|]
let _fsyacc_stateToProdIdxsTableElements = [| 1us;0us;1us;0us;1us;1us;1us;1us;9us;2us;3us;4us;5us;6us;7us;8us;9us;10us;1us;2us;9us;3us;3us;4us;5us;6us;7us;8us;9us;10us;9us;3us;4us;4us;5us;6us;7us;8us;9us;10us;9us;3us;4us;5us;5us;6us;7us;8us;9us;10us;9us;3us;4us;5us;6us;6us;7us;8us;9us;10us;9us;3us;4us;5us;6us;7us;7us;8us;9us;10us;9us;3us;4us;5us;6us;7us;8us;8us;9us;10us;9us;3us;4us;5us;6us;7us;8us;9us;9us;10us;9us;3us;4us;5us;6us;7us;8us;9us;10us;10us;10us;3us;4us;5us;6us;7us;8us;9us;10us;13us;16us;9us;3us;4us;5us;6us;7us;8us;9us;10us;14us;9us;3us;4us;5us;6us;7us;8us;9us;10us;15us;9us;3us;4us;5us;6us;7us;8us;9us;10us;15us;9us;3us;4us;5us;6us;7us;8us;9us;10us;17us;9us;3us;4us;5us;6us;7us;8us;9us;10us;17us;9us;3us;4us;5us;6us;7us;8us;9us;10us;17us;10us;3us;4us;5us;6us;7us;8us;9us;10us;21us;22us;9us;3us;4us;5us;6us;7us;8us;9us;10us;25us;1us;3us;1us;4us;1us;5us;1us;6us;1us;7us;1us;8us;1us;9us;1us;10us;1us;11us;1us;12us;3us;13us;14us;16us;1us;13us;1us;14us;1us;14us;1us;14us;1us;14us;1us;15us;1us;15us;1us;15us;1us;15us;1us;16us;1us;16us;1us;17us;1us;17us;1us;17us;1us;18us;1us;18us;1us;18us;2us;18us;24us;1us;18us;2us;19us;20us;1us;19us;1us;19us;1us;22us;1us;23us;2us;24us;24us;1us;24us;1us;25us;|]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us;2us;4us;6us;8us;18us;20us;30us;40us;50us;60us;70us;80us;90us;100us;111us;121us;131us;141us;151us;161us;171us;182us;192us;194us;196us;198us;200us;202us;204us;206us;208us;210us;212us;216us;218us;220us;222us;224us;226us;228us;230us;232us;234us;236us;238us;240us;242us;244us;246us;248us;250us;253us;255us;258us;260us;262us;264us;266us;269us;271us;|]
let _fsyacc_action_rows = 61
let _fsyacc_actionTableElements = [|5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;0us;49152us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;0us;49152us;9us;32768us;6us;5us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;32us;26us;0us;16386us;5us;16387us;23us;27us;24us;28us;25us;29us;26us;30us;32us;26us;5us;16388us;23us;27us;24us;28us;25us;29us;26us;30us;32us;26us;7us;16389us;20us;23us;21us;24us;23us;27us;24us;28us;25us;29us;26us;30us;32us;26us;0us;16390us;0us;16391us;0us;16392us;0us;16393us;0us;16394us;14us;32768us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;29us;45us;32us;26us;34us;39us;35us;33us;36us;34us;42us;31us;43us;32us;9us;32768us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;32us;26us;36us;38us;9us;32768us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;32us;26us;33us;42us;0us;16399us;9us;32768us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;31us;46us;32us;26us;9us;32768us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;30us;47us;32us;26us;0us;16401us;13us;16405us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;29us;45us;32us;26us;34us;39us;35us;33us;42us;31us;43us;32us;9us;32768us;6us;60us;20us;23us;21us;24us;22us;25us;23us;27us;24us;28us;25us;29us;26us;30us;32us;26us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;0us;16395us;0us;16396us;6us;32768us;7us;35us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;0us;16397us;1us;32768us;35us;48us;1us;32768us;9us;37us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;0us;16398us;1us;32768us;43us;40us;1us;32768us;32us;41us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;1us;32768us;36us;44us;0us;16400us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;5us;32768us;29us;45us;34us;39us;35us;33us;42us;31us;43us;32us;1us;32768us;43us;49us;1us;32768us;15us;50us;1us;32768us;41us;57us;2us;32768us;9us;59us;36us;52us;0us;16402us;1us;16404us;18us;54us;1us;32768us;35us;48us;0us;16403us;0us;16406us;0us;16407us;1us;16408us;9us;59us;1us;32768us;41us;57us;0us;16409us;|]
let _fsyacc_actionTableRowOffsets = [|0us;6us;7us;13us;14us;24us;25us;31us;37us;45us;46us;47us;48us;49us;50us;65us;75us;85us;86us;96us;106us;107us;121us;131us;137us;143us;149us;155us;161us;167us;173us;179us;180us;181us;188us;189us;191us;193us;199us;200us;202us;204us;210us;216us;218us;219us;225us;231us;237us;239us;241us;243us;246us;247us;249us;251us;252us;253us;254us;256us;258us;|]
let _fsyacc_reductionSymbolCounts = [|1us;1us;2us;3us;3us;3us;3us;3us;3us;3us;3us;1us;1us;3us;6us;6us;4us;6us;5us;3us;1us;1us;2us;1us;3us;2us;|]
let _fsyacc_productionToNonTerminalTable = [|0us;1us;2us;3us;3us;3us;3us;3us;3us;3us;3us;3us;3us;3us;3us;3us;3us;3us;4us;5us;5us;6us;6us;7us;7us;8us;|]
let _fsyacc_immediateActions = [|65535us;49152us;65535us;49152us;65535us;16386us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;16395us;16396us;65535us;16397us;65535us;65535us;65535us;16398us;65535us;65535us;65535us;65535us;65535us;16400us;65535us;65535us;65535us;65535us;65535us;65535us;65535us;16402us;65535us;65535us;16403us;16406us;16407us;65535us;65535us;16409us;|]
let _fsyacc_reductions = lazy [|
# 358 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : 'gentype__startexpr));
# 367 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> Prog in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : 'gentype__startprog));
# 376 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 37 "Parser.fsy"
                                       _1 
                   )
# 37 "Parser.fsy"
                 : Expr));
# 387 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 38 "Parser.fsy"
                                                          Plus(_1, _3, parseState.ResultRange) 
                   )
# 38 "Parser.fsy"
                 : 'gentype_Expr));
# 399 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 39 "Parser.fsy"
                                                          Minus(_1, _3, parseState.ResultRange) 
                   )
# 39 "Parser.fsy"
                 : 'gentype_Expr));
# 411 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 40 "Parser.fsy"
                                                          Times(_1, _3, parseState.ResultRange) 
                   )
# 40 "Parser.fsy"
                 : 'gentype_Expr));
# 423 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 41 "Parser.fsy"
                                                          Eq(_1, _3, parseState.ResultRange) 
                   )
# 41 "Parser.fsy"
                 : 'gentype_Expr));
# 435 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 42 "Parser.fsy"
                                                          Leq(_1, _3, parseState.ResultRange) 
                   )
# 42 "Parser.fsy"
                 : 'gentype_Expr));
# 447 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 43 "Parser.fsy"
                                                          Geq(_1, _3, parseState.ResultRange) 
                   )
# 43 "Parser.fsy"
                 : 'gentype_Expr));
# 459 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 44 "Parser.fsy"
                                                          Lt(_1, _3, parseState.ResultRange) 
                   )
# 44 "Parser.fsy"
                 : 'gentype_Expr));
# 471 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 45 "Parser.fsy"
                                                          Gt(_1, _3, parseState.ResultRange) 
                   )
# 45 "Parser.fsy"
                 : 'gentype_Expr));
# 483 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> int in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 46 "Parser.fsy"
                                  IntLiteral(_1, parseState.ResultRange) 
                   )
# 46 "Parser.fsy"
                 : 'gentype_Expr));
# 494 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> string in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 47 "Parser.fsy"
                                 Var(_1, parseState.ResultRange) 
                   )
# 47 "Parser.fsy"
                 : 'gentype_Expr));
# 505 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 48 "Parser.fsy"
                                                 _2 
                   )
# 48 "Parser.fsy"
                 : 'gentype_Expr));
# 516 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _3 = parseState.GetInput(3) :?> 'gentype_FormalList in
            let _5 = parseState.GetInput(5) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 49 "Parser.fsy"
                                                                   FunAbstraction(_3, _5, parseState.ResultRange) 
                   )
# 49 "Parser.fsy"
                 : 'gentype_Expr));
# 528 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> string in
            let _4 = parseState.GetInput(4) :?> 'gentype_Expr in
            let _6 = parseState.GetInput(6) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 50 "Parser.fsy"
                                                               Let(_2, _4, _6, parseState.ResultRange) 
                   )
# 50 "Parser.fsy"
                 : 'gentype_Expr));
# 541 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_Expr in
            let _3 = parseState.GetInput(3) :?> 'gentype_ExprList in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 51 "Parser.fsy"
                                                          Application(_2, _3, parseState.ResultRange) 
                   )
# 51 "Parser.fsy"
                 : 'gentype_Expr));
# 553 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> 'gentype_Expr in
            let _4 = parseState.GetInput(4) :?> 'gentype_Expr in
            let _6 = parseState.GetInput(6) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 52 "Parser.fsy"
                                                                   IfThenElse(_2, _4, _6) 
                   )
# 52 "Parser.fsy"
                 : 'gentype_Expr));
# 566 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = parseState.GetInput(2) :?> string in
            let _4 = parseState.GetInput(4) :?> 'gentype_Type in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 54 "Parser.fsy"
                                                            { name = _1 ; ty = _3 } 
                   )
# 54 "Parser.fsy"
                 : 'gentype_Formal));
# 578 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Formal in
            let _3 = parseState.GetInput(3) :?> 'gentype_FormalList in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 56 "Parser.fsy"
                                                            _1 :: _3 
                   )
# 56 "Parser.fsy"
                 : 'gentype_FormalList));
# 590 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Formal in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 57 "Parser.fsy"
                                                            [_1] 
                   )
# 57 "Parser.fsy"
                 : 'gentype_FormalList));
# 601 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 59 "Parser.fsy"
                                       [_1] 
                   )
# 59 "Parser.fsy"
                 : 'gentype_ExprList));
# 612 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            let _2 = parseState.GetInput(2) :?> 'gentype_ExprList in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 60 "Parser.fsy"
                                                _1 :: _2 
                   )
# 60 "Parser.fsy"
                 : 'gentype_ExprList));
# 624 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 62 "Parser.fsy"
                                      Int(parseState.ResultRange) 
                   )
# 62 "Parser.fsy"
                 : 'gentype_Type));
# 634 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Type in
            let _3 = parseState.GetInput(3) :?> 'gentype_Type in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 63 "Parser.fsy"
                                           FunTy(_1, _3, parseState.ResultRange) 
                   )
# 63 "Parser.fsy"
                 : 'gentype_Type));
# 646 "Parser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = parseState.GetInput(1) :?> 'gentype_Expr in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 65 "Parser.fsy"
                                       _1 
                   )
# 65 "Parser.fsy"
                 : Prog));
|]
# 658 "Parser.fs"
let tables : FSharp.Text.Parsing.Tables<_> = 
  { reductions = _fsyacc_reductions.Value;
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken; 
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt:FSharp.Text.Parsing.ParseErrorContext<_>) -> 
                              match parse_error_rich with 
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 47;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = tables.Interpret(lexer, lexbuf, startState)
let expr lexer lexbuf : Expr =
    engine lexer lexbuf 0 :?> _
let prog lexer lexbuf : Prog =
    engine lexer lexbuf 2 :?> _
