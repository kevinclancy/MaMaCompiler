module VirtualMachine

open TargetCode

let maxStackMem = 10000
let maxHeapMem = 10000

type HeapObject =
    | Basic of int
    | Closure of code_addr:int * global_vec:int
    | Function of code_addr:int * argument_vec:int * global_vec:int
    | Vector of length:int * elems:int array
let execute (code : Instruction []) : int =
    let mutable PC = 0
    let mutable SP = 0
    let mutable GP = 0
    let mutable FP = 1
    let S = Array.create maxStackMem 0
    let H = new ResizeArray<HeapObject>()
    // add empty global vector
    H.Add(Vector(0, Array.create 0 0))

    // executes the next instruction
    // return - false if the instruction was HALT, and true otherwise
    let step () : bool =
        match code[PC] with
        | Update ->
            failwith "todo"
        | TArg(n) ->
            failwith "todo"
        | Rewrite(n) ->
            failwith "todo"
        | PushLoc(n) ->
            S[SP + 1] <- S[SP - n]
            SP <- SP + 1
            true
        | PushGlob(n) ->
            match H[GP] with
            | Vector(m, elems) when n < m ->
                S[SP + 1] <- elems[n]
                SP <- SP + 1
                true
            | Vector(_, _) ->
                failwith $"fewer than {n} globals"
            | _ ->
                failwith "GP references a non-vector"
        | MkVec(n) ->
            let array = Array.create n 0
            H.Add(Vector(n, array))
            SP <- SP - n + 1
            for i in 0 .. n do
                array[i] <- S[SP + i]
            S[SP] <- H.Count - 1
            true
        | MkFunVal(addr) ->
            failwith "todo"
        | MkClos(addr) ->
            failwith "todo"
        | MkBasic ->
            H.Add(Basic(S[SP]))
            S[SP] <- H.Count-1
            true
        | GetBasic ->
            match H[S[SP]] with
            | Basic(n) ->
                S[SP] <- n
                true
            | _ ->
                failwith "not basic"
        | Eval ->
            failwith "todo"
        | Apply ->
            failwith "todo"
        | Halt ->
            false
        | Mul ->
            S[SP - 1] <- S[SP - 1] * S[SP]
            SP <- SP - 1
            PC <- PC + 1
            true
        | Add ->
            S[SP - 1] <- S[SP - 1] + S[SP]
            SP <- SP - 1
            PC <- PC + 1
            true
        | Sub ->
            S[SP - 1] <- S[SP - 1] - S[SP]
            SP <- SP - 1
            PC <- PC + 1
            true
        | Leq ->
            S[SP - 1] <- if S[SP - 1] <= S[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Eq ->
            S[SP - 1] <- if S[SP - 1] = S[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Geq ->
            S[SP - 1] <- if S[SP - 1] >= S[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Gt ->
            S[SP - 1] <- if S[SP - 1] > S[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Lt ->
            S[SP - 1] <- if S[SP - 1] < S[SP] then 1 else 0
            SP <- SP - 1
            PC <- PC + 1
            true
        | Neg ->
            S[SP] <- -S[SP]
            PC <- PC + 1
            true
        | LoadC(constantToLoad) ->
            SP <- SP + 1
            S[SP] <- constantToLoad
            PC <- PC + 1
            true
        | Load(numWordsToLoad) ->
            for i in (numWordsToLoad - 1) .. -1 .. 0 do
                S[SP + i] <- S[S[SP] + i]
            SP <- SP + numWordsToLoad - 1
            PC <- PC + 1
            true
        | Jump(dest) ->
            PC <- dest
            true
        | JumpZ(dest) ->
            PC <- if S[SP] = 0 then dest else (PC + 1)
            SP <- SP - 1
            true
        | JumpI(jumpOffset) ->
            PC <- S[SP] + jumpOffset
            SP <- SP - 1
            true
        | LoadRC(frameOffset) ->
            SP <- SP + 1
            S[SP] <- FP + frameOffset
            PC <- PC + 1
            true
        | LoadR(loadFromFPOffset, numWordsToLoad) ->
            SP <- SP + 1
            let addrToLoadFrom = FP + loadFromFPOffset
            for i in (numWordsToLoad - 1) .. -1 .. 0 do
                S[SP + i] <- S[addrToLoadFrom + i]
            SP <- SP + numWordsToLoad - 1
            PC <- PC + 1
            true
        | Mark(addr) ->
            failwith "todo"
        | Slide(n) ->
            S[SP - n] <- S[SP]
            SP <- SP - n
            true
        | Alloc(n) ->
            failwith "todo"
        | Return(n) ->
            failwith "todo"
        | LoadCAddr(addr) ->
            failwith "The 'LoadCAddr' instruction should be resolved before executing code"
        | SymbolicAddress(_) ->
            failwith "symbolic addresses must be resolved before code execution"

    while step() do
        ()

    mem[1]