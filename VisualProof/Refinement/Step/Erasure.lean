import VisualProof.Concrete.Step
import VisualProof.Concrete.Elaboration.SpliceRootCompilation
import VisualProof.Refinement.Step.Core

namespace VisualProof.Refinement.Erasure

open VisualProof.Diagram

private theorem splice_local_erasure
    {arity : Nat} {source : Concrete.State arity}
    (input : Concrete.Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : Concrete.OperationReceipt input.frame}
    (raw : Concrete.spliceRaw input = .ok operation)
    {receipt : Concrete.Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    Rule.Erasure.Local
      (Concrete.Elaboration.CompiledSite.splice input frameEq raw packed
        consistent).after
      (Concrete.Elaboration.CompiledSite.splice input frameEq raw packed
        consistent).before := by
  rw [Concrete.Elaboration.CompiledSite.splice_after,
    Concrete.Elaboration.CompiledSite.splice_before]
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  unfold Concrete.Elaboration.CompiledSite.spliceAfterBody
    Concrete.Elaboration.CompiledSite.spliceBefore
  dsimp only
  simp only [Concrete.Elaboration.CompiledSite.spliceSite,
    Concrete.Elaboration.CompiledSite.castRegionIndex]
  unfold Concrete.Elaboration.CompiledSite.spliceAfter
  rw [Concrete.Elaboration.CompiledSite.body_eq_finish source site]
  simp only [Concrete.Elaboration.CompiledSite.directItems]
  simpa only using (Rule.Erasure.Local.erase _ _ _ _ _)

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
  obtain ⟨guard, operation, raw, packed⟩ :=
    Concrete.execute_success_composition success
  rcases insertion with ⟨input, frameEq, _admissible, consistent⟩
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  let input : Concrete.Splice.Input := {
    frame := source.diagram
    pattern := pattern
    site := site
    attachment := attachment
    binderSpine := binderSpine
    binderTarget := binderTarget
  }
  let replacement := Concrete.Elaboration.CompiledSite.splice input rfl raw
    packed consistent
  have localEvidence :
      Rule.Erasure.Local replacement.after replacement.before := by
    exact splice_local_erasure input rfl raw packed consistent
  have polarity := contextPolarity_of_spawnPolarity replacement.context
    (by
      simpa [replacement] using
        Concrete.Elaboration.CompiledSite.splice_context_cutDepth input rfl
          raw packed consistent)
    (by simpa using guard)
  cases orientation with
  | forward =>
      exact .erasure (replacement.lift (by
        simpa [Rule.atPolarity, polarity] using localEvidence))
  | backward =>
      exact .erasure (replacement.symm.lift (by
        change Rule.atPolarity replacement.context.polarity
          Rule.Erasure.Local replacement.after replacement.before
        simpa [Rule.atPolarity, polarity] using localEvidence))

end VisualProof.Refinement.Erasure
