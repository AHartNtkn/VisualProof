import VisualProof.Concrete.Step
import VisualProof.Concrete.Elaboration.SpliceElaboration
import VisualProof.Refinement.Step.Core

namespace VisualProof.Refinement.Erasure

open VisualProof.Diagram

private theorem spliceLocal
    {arity : Nat} {source : Concrete.State arity}
    (normalized : Concrete.Splice.Input.SourceNormalized source)
    (layout : Concrete.Splice.Input.PlugLayout normalized.toInput)
    (admissible : normalized.toInput.Admissible)
    (host : Concrete.CompiledSite source normalized.site)
    (material : Concrete.CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer) :
    Rule.Erasure.Local
      (host.spliceBody normalized layout admissible material)
      host.siteBody := by
  let evidence := Rule.Erasure.Local.erase
    host.siteLocals.length
    (host.siteBody.itemsCast host.siteBody_localCount)
    material.siteBody
    (Fin.cast List.length_append ∘
      material.spliceWireMap normalized.toInput layout admissible
        (host.siteContext ++ host.siteLocals) host.completeContext_exact)
    (fun relation => material.spliceRelationMap normalized.toInput admissible
      host.siteBinders host.binder_covers relation)
  have hostBody :
      Diagram.Region.mk host.siteLocals.length
          (host.siteBody.itemsCast host.siteBody_localCount) =
        host.siteBody :=
    Diagram.Region.mk_itemsCast host.siteBody host.siteBody_localCount
  rw [← hostBody]
  exact evidence

private theorem directedErasure
    {orientation : Concrete.Orientation}
    {source target : OpenDiagram arity}
    (replacement : Diagram.ContextReplacement source target)
    (localEvidence : Rule.Erasure.Local replacement.before replacement.after)
    (depthEq : replacement.context.cutDepth = depth)
    (guard : Concrete.erasurePolarity orientation depth) :
    DirectedStep orientation source target := by
  have polarity := contextPolarity_of_erasurePolarity replacement.context
    depthEq guard
  cases orientation with
  | forward =>
      exact Rule.Step.erasure (replacement.lift (by
        simpa only [polarity, Rule.atPolarity] using localEvidence))
  | backward =>
      apply Rule.Step.erasure
      apply replacement.symm.lift
      change Rule.atPolarity replacement.context.polarity
        Rule.Erasure.Local replacement.after replacement.before
      simpa only [polarity, Rule.atPolarity, Rule.converse] using
        localEvidence

private theorem directedSpawn
    {orientation : Concrete.Orientation}
    {source target : OpenDiagram arity}
    (replacement : Diagram.ContextReplacement source target)
    (localEvidence : Rule.Erasure.Local replacement.after replacement.before)
    (depthEq : replacement.context.cutDepth = depth)
    (guard : Concrete.spawnPolarity orientation depth) :
    DirectedStep orientation source target := by
  have polarity := contextPolarity_of_spawnPolarity replacement.context
    depthEq guard
  cases orientation with
  | forward =>
      exact Rule.Step.erasure (replacement.lift (by
        simpa only [polarity, Rule.atPolarity, Rule.converse] using
          localEvidence))
  | backward =>
      apply Rule.Step.erasure
      apply replacement.symm.lift
      change Rule.atPolarity replacement.context.polarity
        Rule.Erasure.Local replacement.after replacement.before
      simpa only [polarity, Rule.atPolarity] using localEvidence

theorem erasure
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (selection : Concrete.CheckedSelection source.checked.val.diagram)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source (.erasure selection) =
      .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  sorry

theorem boundRelationSpawn
    {arity : Nat}
    {source : Concrete.State arity}
    {orientation : Concrete.Orientation}
    (insertion : Concrete.Insertion source)
    {receipt : Concrete.Receipt source}
    (success : Concrete.execute orientation source
      (.boundRelationSpawn insertion) = .ok receipt) :
    DirectedStep orientation (canonicalDiagram source)
      (canonicalDiagram receipt.target) := by
  sorry

end VisualProof.Refinement.Erasure
