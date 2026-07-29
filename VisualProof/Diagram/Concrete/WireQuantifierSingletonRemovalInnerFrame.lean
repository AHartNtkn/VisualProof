import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemoval

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace SingletonRemovalSemantics

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

/-- The paired contexts immediately inside one enclosing region's binders. -/
structure PairedInnerFrame
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter)) where
  sourceInner :
    DiagramContext definitions sourceFrame.visible.sigs
      (sourceOuter.extend region).sigs
  targetInner :
    DiagramContext definitions targetFrame.visible.sigs
      ((targetContext source removed sourceOuter).extend
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          source removed region)).sigs
  sourceDecomposition :
    sourceFrame.context =
      bindContextFor source.val sourceOuter.ids
        (source.val.wiresAt region) sourceInner
  targetDecomposition :
    targetFrame.context =
      bindContextFor
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter).ids
        ((ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed).wiresAt
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            source removed region))
        targetInner

/-- Pointwise replacement law in one canonical target visible environment. -/
def LocalReplacementAt
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (sourceVisible : ConcreteElaboration.WireContext source.val)
    (targetVisible :
      ConcreteElaboration.WireContext
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed))
    (visibleExact :
      targetVisible = targetContext source removed sourceVisible)
    (replacement : Region definitions targetVisible.sigs)
    (removedItem : Item definitions sourceVisible.sigs)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetVisible.sigs) : Prop :=
  denoteRegion pre definitionEnv targetEnv replacement ↔
    denoteItem pre definitionEnv
      (Env.comp
        (congrArg ConcreteElaboration.WireContext.sigs visibleExact ▸
          targetEnv)
        (contextRenaming source removed sourceVisible))
      removedItem

/--
The fixed-ancestor eliminator carried by paired pre-binder contexts. Each use
chooses one enclosing environment and requires the pointwise replacement law
only in descendants preserving it.
-/
def PairedInnerFrame.ReplacementDenotation
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removed : source.val.NodeId}
    {region : source.val.RegionId}
    {sourceOuter : ConcreteElaboration.WireContext source.val}
    {sourceFrame : RegionFrame definitions source.val sourceOuter}
    {targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        (targetContext source removed sourceOuter)}
    (paired :
      PairedInnerFrame source removed region sourceOuter sourceFrame
        targetFrame)
    (visibleExact :
      targetFrame.visible =
        targetContext source removed sourceFrame.visible)
    (replacement : Region definitions targetFrame.visible.sigs)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) : Prop :=
  ∀ fixedTargetEnv :
      Env pre
        ((targetContext source removed sourceOuter).extend
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            source removed region)).sigs,
    (∀ descendant : Env pre targetFrame.visible.sigs,
      DiagramContext.PreservesOuter paired.targetInner fixedTargetEnv
          descendant →
        LocalReplacementAt source removed sourceFrame.visible
          targetFrame.visible visibleExact replacement removedItem pre
          definitionEnv descendant) →
    (denoteRegion pre definitionEnv fixedTargetEnv
          (paired.targetInner.fill
            (replacement.conjoin targetFrame.siteBody)) ↔
      denoteRegion pre definitionEnv
        (Env.comp fixedTargetEnv
          (extendedContextRenaming source removed sourceOuter region))
        (paired.sourceInner.fill sourceFrame.siteBody))

end SingletonRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
