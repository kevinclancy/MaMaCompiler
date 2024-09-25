module VirtualMachine

open TargetCode

let maxStackMem = 10000
let maxHeapMem = 10000

type HeapObject =
    | Basic of int
    | Closure of code_addr:int * global_vec:int
    | Function of code_addr:int * argument_vec:int * global_vec:int
    | Vector of length:int * elems:int array



let execute (code : Instruction []) : HeapObject =
    let mutable PC = 0
    let mutable SP = 0
    let mutable GP = 0
    let mutable FP = 1
    let S = Array.create maxStackMem 0
    let H = new ResizeArray<HeapObject>()
    // add empty global vector
    H.Add(Vector(0, Array.create 0 0))

    /// Returns heap address of new vector
    let new_vector (length : int) (elems : int array) : int =
        H.Add(Vector(length, elems))
        H.Count - 1

    let new_function (code_addr : int) (argument_vec_addr : int) (global_vec_addr : int) : int =
        H.Add(Function(code_addr, argument_vec_addr, global_vec_addr))
        H.Count - 1

    let new_closure (code_addr : int) (global_vec_addr : int) : int =
        H.Add(Closure(code_addr, global_vec_addr))
        H.Count - 1

    let new_basic (n : int) : int =
        H.Add(Basic(n))
        H.Count - 1

    let (|ExpectFunction|) (fn : HeapObject) : int * int * int =
        match fn with
        | Function(code_addr, argument_vec, global_vec) ->
            (code_addr, argument_vec, global_vec)
        | _ ->
            failwith "expected function"

    let (|ExpectClosure|) (closure : HeapObject) : int * int =
        match closure with
        | Closure(code_addr, global_vec_addr) ->
            (code_addr, global_vec_addr)
        | _ ->
            failwith "expected closure"

    let (|ExpectVector|) (vector : HeapObject) : int * (int array) =
        match vector with
        | Vector(length, elems) ->
            (length, elems)
        | _ ->
            failwith "expected vector"

    let (|ExpectBasic|) (basic : HeapObject) : int =
        match basic with
        | Basic(n) ->
            n
        | _ ->
            failwith "expected basic"

    let mkvec0 () : unit =
        let n = SP - FP
        let array = Array.create n 0
        SP <- FP + 1
        for i in 0 .. n do
            array[i] <- S[SP + i]
        H.Add(Vector(n, array))
        S[SP] <- H.Count - 1

    let wrap () : unit =
        H.Add(Function(PC - 1, S[SP], GP))
        S[SP] <- H.Count - 1

    let popenv () : unit =
        GP <- S[FP - 2]
        PC <- S[FP]
        S[FP - 2] <- S[SP]
        SP <- FP - 2
        FP <- S[FP - 1]

    let mark (return_addr : int) : unit =
        S[SP + 1] <- GP
        S[SP + 2] <- FP
        S[SP + 3] <- return_addr
        FP <- SP + 3
        SP <- SP + 3

    let apply () : unit =
        let (ExpectFunction(code_addr, args_addr, globals_addr)) = H[S[SP]]
        let (ExpectVector(n_args, array_args)) = H[args_addr]
        for i in 0 .. (n_args-1) do
            S[SP + i] <- array_args[i]
        SP <- SP + n_args - 1
        GP <- globals_addr
        PC <- code_addr

    let apply0 () : unit =
        let (ExpectClosure(code_addr, globals_vec_addr)) = H[S[SP]]
        GP <- globals_vec_addr
        PC <- code_addr
        SP <- SP - 1

    let slide (n : int) : unit =
        S[SP - n] <- S[SP]
        SP <- SP - n

    let rewrite (n : int) : unit =
        H[S[SP - n]] <- H[S[SP]]
        SP <- SP - 1

    let pushloc (n : int) : unit =
        S[SP + 1] <- S[SP - n]
        SP <- SP + 1

    // executes the next instruction
    // return - false if the instruction was HALT, and true otherwise
    let step () : bool =
        match code[PC] with
        | Update ->
            popenv ()
            rewrite 1
            PC <- PC + 1
            true
        | TArg(n) ->
            if SP - FP < n then
                mkvec0 ()
                wrap ()
                popenv ()
            PC <- PC + 1
            true
        | Rewrite(n) ->
            H[S[SP - n]] <- H[S[SP]]
            SP <- SP - 1
            PC <- PC + 1
            true
        | PushLoc(n) ->
            pushloc n
            PC <- PC + 1
            true
        | PushGlob(n) ->
            let (ExpectVector(m, elems)) = H[GP]
            if n < m then
                S[SP + 1] <- elems[n]
                SP <- SP + 1
                PC <- PC + 1
                true
            else
                failwith $"fewer than {n} globals"
        | MkVec(n) ->
            let array = Array.create n 0
            let vec_addr = new_vector n array
            SP <- SP - n + 1
            for i in 0 .. (n - 1) do
                array[i] <- S[SP + i]
            S[SP] <- vec_addr
            PC <- PC + 1
            true
        | MkFunVal(code_addr) ->
            let vec_addr = new_vector 0 (Array.create 0 0)
            S[SP] <- new_function code_addr vec_addr S[SP]
            PC <- PC + 1
            true
        | MkClos(code_addr) ->
            S[SP] <- new_closure code_addr S[SP]
            PC <- PC + 1
            true
        | MkBasic ->
            S[SP] <- new_basic S[SP]
            PC <- PC + 1
            true
        | GetBasic ->
            let (ExpectBasic n) = H[S[SP]]
            S[SP] <- n
            PC <- PC + 1
            true
        | Eval ->
            match H[S[SP]] with
            | Closure(_, _) ->
                mark PC
                pushloc 3
                apply0 ()
                true
            | _ ->
                PC <- PC + 1
                true
        | Apply ->
            apply ()
            true
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
        | Mark(return_addr) ->
            mark return_addr
            PC <- PC + 1
            true
        | Slide(n) ->
            slide n
            PC <- PC + 1
            true
        | Alloc(n) ->
            for i in 0 .. (n - 1) do
                S[SP] <- (new_closure (- 1) (- 1))
            SP <- SP + n
            PC <- PC + 1
            true
        | Return(n) ->
            if SP - FP - 1 = n then
                popenv ()
                true
            else
                slide n
                apply ()
                true
        | LoadCAddr(addr) ->
            failwith "The 'LoadCAddr' instruction should be resolved before executing code"
        | SymbolicAddress(_) ->
            failwith "symbolic addresses must be resolved before code execution"

    while step() do
        ()

    H[1]
