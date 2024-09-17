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
    /// Pops the address n off the stack and pushes the words stored at n,n+1,...,n+(numWords-1)
    | Load of numWords : int
    /// pushes constantToLoad onto the stack
    | LoadC of constantToLoad : int
    /// pushes (*FP + offset) onto the stack
    | LoadRC of offset : int
    /// "loadrc offset" followed by "load numWords"
    | LoadR of offset : int * numWords : int
    // jump to destAddr
    | Jump of destAddr : int
    // jump to destAddr if top of stack is 0, pop top of stack
    | JumpZ of destAddr : int
    // pop an index off the top of the stack. then jump to (baseAddr + index).
    | JumpI of baseAddr : int