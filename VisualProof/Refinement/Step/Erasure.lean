import VisualProof.Concrete.Step
import VisualProof.Concrete.Elaboration.SpliceElaboration
import VisualProof.Refinement.Step.Core

namespace VisualProof.Refinement.Erasure

open VisualProof.Diagram

private noncomputable def normalizeCastIso
    (diagram : OpenDiagram sourceArity)
    (first : sourceArity = middleArity)
    (second : middleArity = targetArity)
    (direct : sourceArity = targetArity) :
    OpenDiagramIso ((diagram.castArity first).castArity second)
      (diagram.castArity direct) := by
  subst middleArity
  subst targetArity
  exact OpenDiagramIso.refl _

private theorem spliceLocal
    {arity : Nat} {source : Concrete.State arity}
    (normalized : Concrete.Splice.Input.SourceNormalized source)
    (layout : Concrete.Splice.Input.PlugLayout normalized.toInput)
    (admissible : normalized.toInput.Admissible)
    (host : Concrete.CompiledSite source normalized.site)
    (material : Concrete.Splice.Input.CompiledMaterial normalized.toInput) :
    Rule.Erasure.Local
      (host.spliceBody normalized layout admissible material)
      host.siteBody := by
  let evidence := Rule.Erasure.Local.erase
    host.siteLocals.length
    (host.siteBody.itemsCast host.siteBody_localCount)
    material.siteBody
    (Fin.cast List.length_append ∘
      material.spliceWireMap normalized.toInput layout admissible
        (host.siteContext ++ host.siteLocals)
          host.local.completeContext_exact)
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
  obtain ⟨guard, operation, rawSuccess, packed⟩ :=
    Concrete.execute_success_composition success
  rcases insertion with ⟨input, frameEq, _, consistent⟩
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  let normalized : Concrete.Splice.Input.SourceNormalized source := {
    pattern := pattern
    site := site
    attachment := attachment
    binderSpine := binderSpine
    binderTarget := binderTarget
  }
  have consistent' : normalized.toInput.AttachmentConsistent := by
    simpa [normalized, Concrete.Splice.Input.SourceNormalized.toInput] using
      consistent
  have rawSuccess' : Concrete.spliceRaw normalized.toInput = .ok operation := by
    simpa [normalized, Concrete.Splice.Input.SourceNormalized.toInput] using
      rawSuccess
  have packed' : operation.toReceipt source = some receipt := by
    simpa using packed
  let layout : Concrete.Splice.Input.PlugLayout normalized.toInput := {}
  let admissible : normalized.toInput.Admissible :=
    Concrete.spliceRaw_admissible normalized.toInput operation rawSuccess'
  let host : Concrete.CompiledSite source normalized.site :=
    Concrete.CompiledSite.ofSource source normalized.site
  let materialSource : Concrete.CompiledSite
      normalized.toInput.patternState normalized.binderSpine.bodyContainer :=
    Concrete.CompiledSite.ofSource normalized.toInput.patternState
      normalized.binderSpine.bodyContainer
  let material : Concrete.Splice.Input.CompiledMaterial normalized.toInput :=
    Concrete.Splice.Input.CompiledMaterial.ofCompiledSite normalized.toInput
      admissible.terminal_body materialSource
  let result : Concrete.CompiledSite.SpliceResult normalized layout admissible
      host material receipt :=
    Concrete.CompiledSite.spliceResult source normalized consistent' operation
      receipt rawSuccess' packed' host material
  let replacement := result.rawReplacement
  have localEvidence :
      Rule.Erasure.Local replacement.after replacement.before := by
    simpa only [Concrete.CompiledSite.SpliceResult.rawReplacement_after,
      Concrete.CompiledSite.SpliceResult.rawReplacement_before] using
        spliceLocal normalized layout admissible host material
  have depthEq : replacement.context.cutDepth =
      Concrete.concreteCutDepth source.checked.val.diagram normalized.site := by
    simpa only [Concrete.CompiledSite.SpliceResult.rawReplacement_context] using
      host.siteOccurrence_cutDepth
  let rawStep := directedSpawn replacement localEvidence depthEq guard
  let casted := rawStep.castArity source.boundary_length
  let targetNormalization : OpenDiagramIso
      ((receipt.target.checked.elaborate.castArity
        (receipt.target.boundary_length.trans source.boundary_length.symm)
          ).castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) :=
    normalizeCastIso receipt.target.checked.elaborate
      (receipt.target.boundary_length.trans source.boundary_length.symm)
      source.boundary_length receipt.target.boundary_length
  simpa only [canonicalDiagram] using
    casted.iso (OpenDiagramIso.refl _) targetNormalization

end VisualProof.Refinement.Erasure
