namespace VisualProof.Theory

abbrev RelCtx := List Nat

structure RelVar (ctx : RelCtx) (arity : Nat) where
  index : Fin ctx.length
  hasArity : ctx.get index = arity

structure NamedRel (signature : List Nat) (arity : Nat) where
  index : Fin signature.length
  hasArity : signature.get index = arity

end VisualProof.Theory
