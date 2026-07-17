import VisualProof.Rule.Soundness.Iteration.KeptRoute

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- A zero-local-wire region is exactly an item block in the ambient wire
environment.  This form is what lets the selected block remain an ancestor
resource while the retained block supplies the route to the insertion site. -/
theorem denoteRegion_mk_zero_iff
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin wires → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (items : ItemSeq signature wires rels) :
    denoteRegion model named env relEnv (Region.mk 0 items) ↔
      denoteItemSeq model named env relEnv items := by
  simp only [denoteRegion_mk]
  constructor
  · rintro ⟨localEnv, hitems⟩
    simpa [extendWireEnv] using hitems
  · intro hitems
    refine ⟨Fin.elim0, ?_⟩
    simpa [extendWireEnv] using hitems

/-- The authoritative anchor compiler factors semantically into the retained
route block and the selected ancestor resource, with no fresh wire witnesses
introduced by either factor. -/
theorem compilerLeaf_selection_factor
    {signature : List Nat}
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    (leaf : Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here body)) :
    ∃ (keptItems selectedItems : ItemSeq signature
        (leaf.inheritedWires.extend selection.val.anchor).length rels),
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (keptOccurrences input.val selection) = some keptItems ∧
        ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (selectedOccurrences input.val selection) = some selectedItems ∧
        ∀ (model : Lambda.LambdaModel)
          (named : NamedEnv model.Carrier signature)
          (env : Fin (leaf.inheritedWires.extend
            selection.val.anchor).length → model.Carrier)
          (relEnv : RelEnv model.Carrier rels),
          denoteItemSeq model named env relEnv leaf.items ↔
            denoteRegion model named env relEnv (Region.mk 0 selectedItems) ∧
            denoteRegion model named env relEnv (Region.mk 0 keptItems) := by
  obtain ⟨keptItems, selectedItems, keptCompiled, selectedCompiled,
      partition⟩ := compilerLeaf_selection_partition input selection leaf
  refine ⟨keptItems, selectedItems, keptCompiled, selectedCompiled, ?_⟩
  intro model named env relEnv
  rw [partition, denoteItemSeq_append]
  simp only [denoteRegion_mk_zero_iff]
  exact and_comm

end VisualProof.Rule.IterationSoundness
