namespace VisualProof.Theory

abbrev RelCtx := List Nat

structure RelVar (ctx : RelCtx) (arity : Nat) where
  index : Fin ctx.length
  hasArity : ctx.get index = arity

end VisualProof.Theory
