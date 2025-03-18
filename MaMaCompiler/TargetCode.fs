module TargetCode

type Instruction =
    // not a real instruction.
    /// SymbolicAddress(n) means that the following instruction is located at symbolic address n
    | SymbolicAddress of int
    /// LoadCAddr(symbolicAddr) resolves to LoadC(addr), where addr is the physical address mapped to
    /// by symbolicAddr
    | LoadCAddr of int
    // real instructions below
    | Halt
    | Mul
    | Add
    | Sub
    | Leq
    | Eq
    | Geq
    | Gt
    | Lt
    | Neg
    /// MkSum(n) Pops value v from top of stack. Pushes a value of a sum datatype onto the stack with variant index n
    /// and argument v
    | MkSum of n:int
    /// TSum(addr) Pops an address of a sum value off the stack, pushes the variant constructor argument onto the stack,
    /// and jumps to (addr + n), where n is the variant index of the sum value
    /// (the instruction at addr + n is supposed to jump somewhere else, i.e. it's part of a "jump table")
    | TSum of addr:int
    /// Assuming a sum value (Constructor v) on the top of the stack, pushes the constructor argument *v* onto the stack.
    | TGetConstructorArg
    /// Remove the top value on the stack
    | Pop
    /// Replace the address of a "reference" item on top of the stack
    /// with the address of whatever the "reference" item refers to
    | GetRef
    /// Pop an address of a heap object `h` off of the stack.
    /// Then, create a new R-object referring to `h`, pushing its address onto the stack.
    | MkRef
    /// Assume a heap address of an R-object is on top of the stack and an address of another
    /// heap object `h` directly below it.
    ///
    /// This instruction reassigns the R-object's reference to refer to `h`, pops both off the stack,
    /// and then pushes an empty tuple onto the stack.
    | RefAssign
    /// Replace a reference to a "basic" item on top of the
    /// stack with the value stored in the "basic" item
    | GetBasic
    /// Replace the value x on top of the stack with a reference to
    /// a new "basic" item whose value is x
    | MkBasic
    /// Push S[SP - n] onto the stack
    | PushLoc of n:int
    /// Push the n-th value of the (0-indexed) global vector onto the stack
    | PushGlob of n:int
    /// Remove the n values below the top element of the stack,
    /// but leave the top element on the stack
    | Slide of n:int
    /// Assuming a V-object on top of the stack, pop the V-object and then
    /// push its elements from left-to-right.
    | GetVec
    /// Pop the n top elements from the stack, where v_{n-1} is the top element, v_{n-2} is
    /// the second-to-top element, etc. Push a reference to a length-n vector
    /// whose first element is v_0, second element is v_1, etc.
    | MkVec of n:int
    /// Make a new function whose code address is `addr`, whose argument vector is empty,
    /// and whose global vector is the vector currently on top of the stack.
    /// Pop the global vector from the stack and push a reference to the new function in its place.
    | MkFunVal of addr:int
    /// Assume a reference to a vector `V` is at the top of the stack. Then
    /// `MkClos addr` creates a now C-Object whose GP component references `V` and whose CP component
    /// is `addr`.
    | MkClos of addr:int
    /// Push the global vector, then the frame pointer, then the address `addr`.
    /// Finally, set the FP to the value of the SP.
    | Mark of addr:int
    /// Assume as function F(CP, AP, GP') is on top of the stack.
    /// Reassigns the PC to CP.
    /// Pushes the values of the vector AP onto the stack from left (index 0) to right.
    /// Reassigns the GP register to GP'.
    | Apply
    /// Upon entering a function `f` of `n` arguments, let `ap` be the supplied arguments, which
    /// should be on the stack between the SP and FP.
    ///
    /// If the supplied argument vector `ap` have fewer than `n` arguments then TArg `n`
    /// returns from `f` prematurely, producing a new F-object whose argument vector is `ap` as a result.
    /// Otherwise, when `ap` contains at least `n` elements, TArg `n` does nothing.
    | TArg of n:int
    /// Suppose we have finished evaluating the body of a function `f` of `n` formal arguments.
    /// Let `ap` be the vector of arguments `f` was applied to, which should be on the stack between SP and FP.
    ///
    /// If the supplied argument vector `ap` has more than `n` arguments then the body of `f` should evaluate to
    /// a function. The instruction Ret `n` then removes the first `n` of the supplied arguments off of the stack
    /// and applies the function returned by `f` (at the top of the stack) to the remaining arguments.
    /// Otherwise, when `ap` has exactly `n` elements, we return to the caller of `f` using the organizational
    /// data (PC, GP, FP) stored at indices FP, FP-1, and FP-2 on the stack.
    | Return of n:int
    /// Push `n` references to fresh C-objects to the top of the stack; the CP and GP components of the
    /// C-objects are -1 because we expect to write over them
    | Alloc of n:int
    /// Assume the value `v` is the value referenced by the top of the stack and the
    /// value `w` is referenced by stack index SP-n.
    ///
    /// `Rewrite n` mutates `w` to equal `v` without changing the address of `w`.
    /// Then it pops the reference to `v` from the stack.
    | Rewrite of n:int
    /// If a reference to a C-object is at the top of the stack then the `Eval` instruction pops the C-Object,
    /// and evaluates it so that the closures value is placed on the top of the stack.
    ///
    /// If the top of the stack is not a reference to a C-Object then `Eval` does nothing.
    | Eval
    /// Assume the top of the stack contains the value produced from evaluating a closure,
    /// directly below that are organizational cells, and below that is the closure we just evaluated.
    ///
    /// `Update` pops the top value and organizational cells, using the organizational cells to return
    /// to the context that triggered closure evaluation. It then mutates the closure to the value the closure produced,
    /// without changing its address.
    | Update
    /// Pops the address n off the stack and pushes the words (integers and addresses) stored at n,n+1,...,n+(numWords-1)
    | Load of numWords : int
    /// pushes constantToLoad onto the stack
    | LoadC of constantToLoad : int
    // jump to destAddr
    | Jump of destAddr : int
    // jump to destAddr if top of stack is 0, pop top of stack
    | JumpZ of destAddr : int
    // jump to destAddr if top of stack is non-0, pop top of stack
    | JumpNZ of destAddr : int
    // pop an index off the top of the stack. then jump to (baseAddr + index).
    | JumpI of baseAddr : int

    with
        /// The instruction's 32-bit binary representation
        member this.Serialization : uint =
            match this with
            | SymbolicAddress(_)
            | LoadCAddr(_) ->
                failwith "can only serialize code with resolved addresses"
            | Halt ->
                0x00000000u
            | Mul ->
                0x00000001u
            | Add ->
                0x00000002u
            | Sub ->
                0x00000003u
            | Leq ->
                0x00000004u
            | Eq ->
                0x00000005u
            | Geq ->
                0x00000006u
            | Gt ->
                0x00000007u
            | Lt ->
                0x00000008u
            | Neg ->
                0x00000009u
            | MkSum(n) ->
                let opId = 0x0Au
                let variantId = uint n
                opId ||| (variantId <<< 8)
            | TSum(jumpTableAddr) ->
                assert (jumpTableAddr < (1 <<< 16))
                let opId = 0x0Bu
                let addr = uint jumpTableAddr
                opId ||| (addr <<< 8)
            | TGetConstructorArg ->
                0x0000000Cu
            | Pop ->
                0x0000000Du
            | GetRef ->
                0x0000000Eu
            | MkRef ->
                0x0000000Fu
            | RefAssign ->
                0x00000010u
            | GetBasic ->
                0x00000011u
            | MkBasic ->
                0x00000012u
            | PushLoc(n) ->
                let opId = 0x13u
                // NOTE: this could be 1 byte instead of 2
                let loc = (uint n) &&& 0x00001111u
                opId ||| (loc <<< 8)
            | PushGlob(n) ->
                let opId = 0x14u
                /// NOTE: this could be 1 byte instead of 2
                let loc = (uint n) &&& 0x00001111u
                opId ||| (loc <<< 8)
            | Slide(n) ->
                let opId = 0x15u
                /// NOTE: this could be one byte instead of 2
                let slideDistance = (uint n) &&& 0x00001111u
                opId ||| (slideDistance <<< 8)
            | GetVec ->
                0x00000016u
            | MkVec(n) ->
                assert (n < (1 <<< 16))
                let opId = 0x16u
                let vecLen = uint n
                opId ||| (vecLen <<< 8)
            | MkFunVal(addr) ->
                assert (addr < (1 <<< 16))
                let opId = 0x17u
                opId ||| (uint addr <<< 8)
            | MkClos(addr) ->
                assert (addr < (1 <<< 16))
                let opId = 0x18u
                opId ||| (uint addr <<< 8)
            | Mark(addr) ->
                // NOTE: addr could be one byte since we're returning to address that is a few instructions ahead
                assert (addr < (1 <<< 16))
                let opId = 0x19u
                opId ||| (uint addr <<< 8)
            | Apply ->
                0x1Au
            | TArg(numFormals) ->
                assert (numFormals < (1 <<< 8) && numFormals >= 0)
                let opId = 0x1Bu
                opId ||| (uint numFormals <<< 8)
            | Return(numFormals) ->
                assert (numFormals < (1 <<< 8) && numFormals >= 0)
                let opId = 0x1Cu
                opId ||| (uint numFormals <<< 8)
            | Alloc(n) ->
                assert (n < (1 <<< 8) && n >= 0)
                let opId = 0x1Du
                opId ||| (uint n <<< 8)
            | Rewrite(n) ->
                assert (n < (1 <<< 8) && n >= 0)
                let opId = 0x1Eu
                opId ||| (uint n <<< 8)
            | Eval ->
                0x0000001Fu
            | Update ->
                0x00000020u
            | Load(numWords) ->
                assert (numWords < (1 <<< 8) && numWords >= 0)
                let opId = 0x21u
                opId ||| (uint numWords <<< 8)
            | LoadC(constantToLoad) ->
                assert (constantToLoad < (1 <<< 20) && constantToLoad > -(1 <<< 20))
                let opId = 0x22u
                let maskedConstant = (uint constantToLoad) &&& 0x00111111u
                opId ||| (maskedConstant <<< 8)
            | Jump(destAddr) ->
                assert (destAddr < (1 <<< 16) && destAddr >= 0)
                let opId = 0x23u
                opId ||| (uint destAddr <<< 8)
            | JumpZ(destAddr) ->
                assert (destAddr < (1 <<< 16) && destAddr >= 0)
                let opId = 0x24u
                opId ||| (uint destAddr <<< 8)
             | JumpNZ(destAddr) ->
                assert (destAddr < (1 <<< 16) && destAddr >= 0)
                let opId = 0x25u
                opId ||| (uint destAddr <<< 8)
            | JumpI(baseAddr) ->
                assert (baseAddr < (1 <<< 16) && baseAddr >= 0)
                let opId = 0x26u
                opId ||| (uint baseAddr <<< 8)
