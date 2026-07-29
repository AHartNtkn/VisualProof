import VisualProof.Diagram.Context

namespace VisualProof

namespace DiagramContext

/--
Embed the variables visible outside a one-hole context into the context's
hole. Intervening binders contribute only local variables.
-/
def liftOuter :
    {holeCtx outerCtx : List Sig} →
      DiagramContext definitions holeCtx outerCtx →
      WireRenaming outerCtx holeCtx
  | _, _, .hole => fun value => value
  | _, _, .surround _ inner _ => liftOuter inner
  | _, _, .cut inner => liftOuter inner
  | _, _, .bind _ inner => fun value => liftOuter inner (.there value)

/--
A hole environment preserves a fixed enclosing environment when it agrees on
every retained ancestor variable. Descendant binder values remain unrestricted.
-/
def PreservesOuter
    (context : DiagramContext definitions holeCtx outerCtx)
    (fixed : Env pre outerCtx)
    (descendant : Env pre holeCtx) : Prop :=
  Env.comp descendant (liftOuter context) = fixed

end DiagramContext

end VisualProof
