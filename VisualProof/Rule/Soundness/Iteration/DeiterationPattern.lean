import VisualProof.Rule.Soundness.Iteration.DeiterationReinsert

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

/-- The survivor extraction is an exact renaming of the original justifier
extraction.  Keeping this equality separate lets the independently checked
justifier-to-selected certificates remain the only beta-eta authority. -/
theorem deiterationRetainedOccurrence_nodes_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : Fin
      (selectedFragment
        ⟨input.val.removeRaw selection (deiterationDomains input selection),
          ConcreteDiagram.removeRaw_wellFormed input selection
            (deiterationDomains input selection)⟩
        (deiterationRetainedSelection input selection witness)).diagram.nodeCount) :
    ((selectedFragment
        ⟨input.val.removeRaw selection (deiterationDomains input selection),
          ConcreteDiagram.removeRaw_wellFormed input selection
            (deiterationDomains input selection)⟩
        (deiterationRetainedSelection input selection witness)).diagram.nodes
          node).rename
      (deiterationRetainedOccurrenceEquiv input selection witness).diagram.regions =
    (selectedFragment input witness.justifier).diagram.nodes
      ((deiterationRetainedOccurrenceEquiv input selection witness).diagram.nodes
        node) := by
  change ((deiterationRetainedExtract input selection witness).diagram.nodes
      node).rename (deiterationExtractRegionEquiv input selection witness) =
    (deiterationOriginalExtract input selection witness).diagram.nodes
      (deiterationExtractNodeEquiv input selection witness node)
  exact deiterationExtract_nodes_eq input selection witness node

/-- Direct certified occurrence from the survivor copy to the removed
selection.  The exact extraction transport is composed without manufacturing
a certificate; the witness certificates are reused verbatim. -/
def deiterationPatternOccurrenceEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    OpenOccurrenceEquiv
      (selectedFragment
        ⟨input.val.removeRaw selection (deiterationDomains input selection),
          ConcreteDiagram.removeRaw_wellFormed input selection
            (deiterationDomains input selection)⟩
        (deiterationRetainedSelection input selection witness))
      (selectedFragment input selection) :=
  (deiterationRetainedOccurrenceEquiv input selection witness).transOfRenameEq
    witness.occurrence
    (deiterationRetainedOccurrence_nodes_eq input selection witness)

theorem deiterationPattern_proxyCount_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationReinsertInput input selection witness).binderSpine.proxyCount =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).binderSpine.proxyCount := by
  change (deiterationRetainedLayout input selection witness).proxyCount =
    (deiterationExtraction input selection).raw.layout.proxyCount
  exact deiterationExternalLengthEq input selection witness |>.trans
    (congrArg List.length witness.sameExternalBinders)

/-- The composed occurrence sends every survivor proxy to the corresponding
selected proxy in the same ordered external-binder position. -/
theorem deiterationPattern_proxy_alignment
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin
      (deiterationReinsertInput input selection witness).binderSpine.proxyCount) :
    (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
        ((deiterationReinsertInput input selection witness).binderSpine.proxy
          index) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).binderSpine.proxy
          (Fin.cast
            (deiterationPattern_proxyCount_eq input selection witness) index) := by
  let sourceLayout := deiterationRetainedLayout input selection witness
  let justifierLayout := deiterationOriginalLayout input selection witness
  let targetLayout : FragmentLayout input.val selection := {}
  let justifierIndex : Fin justifierLayout.proxyCount :=
    Fin.cast (deiterationExternalLengthEq input selection witness) index
  have first := deiterationExtractRegionEquiv_proxy input selection witness index
  have second := witness.proxy_alignment justifierIndex
  change witness.occurrence.diagram.regions
      (deiterationExtractRegionEquiv input selection witness
        (sourceLayout.proxy index)) =
    targetLayout.proxy
      (Fin.cast (deiterationPattern_proxyCount_eq input selection witness) index)
  rw [first]
  exact second

theorem deiterationPattern_bodyContainer_alignment
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
        (deiterationReinsertInput input selection witness).binderSpine.bodyContainer =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).binderSpine.bodyContainer := by
  let source := (deiterationReinsertInput input selection witness).binderSpine
  let target := (Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)).binderSpine
  have countEq := deiterationPattern_proxyCount_eq input selection witness
  have countEq' : source.proxyCount = target.proxyCount := by
    simpa [source, target] using countEq
  by_cases empty : source.proxyCount = 0
  · have targetEmpty : target.proxyCount = 0 := by omega
    rw [source.body_eq_root_of_empty empty,
      target.body_eq_root_of_empty targetEmpty]
    exact (deiterationPatternOccurrenceEquiv input selection witness).diagram.root_eq
  · have targetNonempty : target.proxyCount ≠ 0 := by omega
    rw [source.body_eq_terminal_of_nonempty empty,
      target.body_eq_terminal_of_nonempty targetNonempty]
    let sourceLast : Fin source.proxyCount :=
      ⟨source.proxyCount - 1, by omega⟩
    let targetLast : Fin target.proxyCount :=
      ⟨target.proxyCount - 1, by omega⟩
    have aligned := deiterationPattern_proxy_alignment input selection witness
      sourceLast
    have aligned' :
        (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
            (source.proxy sourceLast) =
          target.proxy (Fin.cast countEq' sourceLast) := by
      simpa [source, target] using aligned
    have lastEq : Fin.cast countEq' sourceLast = targetLast := by
      apply Fin.ext
      simp only [Fin.val_cast, sourceLast, targetLast]
      omega
    exact aligned'.trans (congrArg target.proxy lastEq)

end VisualProof.Rule.IterationSoundness
