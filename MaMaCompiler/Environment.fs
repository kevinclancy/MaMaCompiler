module Environment

open Syntax
open Utils
open GenComputation

type Address =
    | Local of offset : int
    | Global of absolute : int

type VarContextEntry = {
    address : Address
    ty : Ty
}

type Constructor = {
    /// The name of the sum typedef this constructor belongs to
    sumTyName : string
    /// The index in which this constructor's variant occurs inside its sum typedef
    index : int
    /// The argument, or "content", of this constructor
    contentTy : Ty
}

type Context = {
    /// Maps the name of each bound constructor to its variant index and content type
    constructorCtxt : Map<string, Constructor>
    varCtxt : Map<string, VarContextEntry>
    tyCtxt : Map<string, Ty>
}
    with
        static member Empty =
            {
                varCtxt = Map.empty
                constructorCtxt = Map.empty
                tyCtxt = Map.empty
            }

        /// Add typedefs to context, or produce an error if any typedef is not well-formed
        member this.WithTypedefs (typedefs : List<Typedef>) : Gen<Context> =
            let foldTypeDef (ctxt : Context) (typedef : Typedef) : Gen<Context> =
                match typedef with
                | Typedef(typename, variants, rng) ->
                    gen {
                        let foldVariant (m : Map<string, Ty>) (constructorName, ty) : Gen<Map<string,Ty>> =
                            if m.ContainsKey constructorName then
                                error $"Constructor name '{constructorName}' appears twice in typedef" rng
                            else
                                gen {
                                    return m.Add(constructorName, ty)
                                }

                        let! variants' = foldM Map.empty foldVariant variants
                        let sumTy = SumTy(variants', noRange)
                        let foldVariant (ctxt : Context) (((varName, varTy), index) : Variant * int) : Context =
                            let constructor = {
                                sumTyName = typename
                                index = index
                                contentTy = varTy
                            }
                            {
                                ctxt with
                                    constructorCtxt = ctxt.constructorCtxt.Add(varName, constructor)
                            }
                        let ctxt' =
                            {
                                ctxt with
                                    tyCtxt = ctxt.tyCtxt.Add(typename, sumTy)
                            }
                        return List.fold foldVariant ctxt' (List.zip (Map.toList variants') [0..variants.Length-1])
                    }
            foldM this foldTypeDef typedefs