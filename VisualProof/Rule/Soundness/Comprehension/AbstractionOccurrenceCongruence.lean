import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrenceFamily

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- A compiled selected occurrence depends on its anchor valuation only
through the occurrence's internal and touching wires. -/
theorem selectedOccurrence_denote_congr
    (input : Concrete.Checked )
    (occurrence : OperationAbstractionOccurrence input)
    (witness : OperationAbstractionWitness input comprehension occurrence)
    (model : Model)
    (hostFuel : Nat)
    (hostContext : Concrete.Elaboration.WireContext input.val)
    (hostBinders : Concrete.Elaboration.BinderContext input.val hostRels)
    (hostEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val hostBinders occurrence.selection.val.anchor)
    (hostCover : hostBinders.Covers occurrence.selection.val.anchor)
    (hostExact : hostContext.Exact occurrence.selection.val.anchor)
    (hostItems : ItemSeq  hostContext.length hostRels)
    (hostCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  input.val
        (Concrete.Elaboration.compileRegion?  input.val hostFuel)
        hostContext hostBinders
        (VisualProof.Rule.ModalSoundness.selectedOccurrences input.val occurrence.selection) =
          some hostItems)
    (first second : Fin hostContext.length → model.Carrier)
    (relations : RelEnv model.Carrier hostRels)
    (agree : ∀ index,
      hostContext.get index ∈ occurrence.selection.internalWires ∨
        hostContext.get index ∈ occurrence.selection.touchingWires →
      first index = second index) :
    denoteItemSeq model  first relations hostItems ↔
      denoteItemSeq model  second relations hostItems := by
  let layout := occurrenceLayout input occurrence
  let fragment := input.val.extractOpenRaw occurrence.selection layout
  let checkedFragment : Concrete.CheckedOpen  :=
    ⟨fragment, occurrenceFragment_wellFormed input occurrence⟩
  let compiled := Concrete.Splice.Input.compiledSpliceOpenRootItems checkedFragment
  have bodyEq : layout.bodyContainer = fragment.diagram.root :=
    (occurrenceLayout input occurrence).bodyContainer_eq_root_of_proxyCount_eq_zero
      (occurrenceLayout_proxyCount_zero input occurrence witness)
  let fragmentEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration fragment.diagram
        Concrete.Elaboration.BinderContext.empty layout.bodyContainer :=
    bodyEq.symm ▸ Concrete.Elaboration.BinderContext.Enumeration.empty
      fragment.diagram
  have fragmentExact : Concrete.Elaboration.WireContext.Exact
      fragment.rootWires layout.bodyContainer := by
    rw [bodyEq]
    exact Concrete.Elaboration.openRootWires_exact
      (occurrenceFragment_wellFormed input occurrence)
  have fragmentCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  fragment.diagram
        (Concrete.Elaboration.compileRegion?  fragment.diagram
          fragment.diagram.regionCount)
        fragment.rootWires Concrete.Elaboration.BinderContext.empty
        (Concrete.Elaboration.localOccurrences fragment.diagram
          layout.bodyContainer) = some compiled.items := by
    simpa [fragment, checkedFragment, bodyEq] using compiled.computation
  have backward := VisualProof.Rule.IterationSoundness.extractionCompileSelectedItems_denote
    input occurrence.selection layout model  .backward
    fragment.diagram.regionCount hostFuel fragment.rootWires hostContext
    Concrete.Elaboration.BinderContext.empty hostBinders fragmentEnumeration
    hostEnumeration hostCover fragmentExact hostExact compiled.items hostItems
    fragmentCompiled hostCompiled
  have forward := VisualProof.Rule.IterationSoundness.extractionCompileSelectedItems_denote
    input occurrence.selection layout model  .forward
    fragment.diagram.regionCount hostFuel fragment.rootWires hostContext
    Concrete.Elaboration.BinderContext.empty hostBinders fragmentEnumeration
    hostEnumeration hostCover fragmentExact hostExact compiled.items hostItems
    fragmentCompiled hostCompiled
  let fragmentMap := VisualProof.Rule.IterationSoundness.extractionContextIndexMap input
    occurrence.selection layout fragment.rootWires hostContext fragmentExact
      hostExact
  let fragmentEnvironment : Fin fragment.rootWires.length → model.Carrier :=
    first ∘ fragmentMap
  have firstAgreement :=
    VisualProof.Rule.IterationSoundness.extractionContextEnvironmentsAgree input
      occurrence.selection layout fragment.rootWires hostContext fragmentExact
      hostExact first
  have secondAgreement :
      (VisualProof.Rule.IterationSoundness.extractionContextRelation input occurrence.selection
        layout fragment.rootWires hostContext).EnvironmentsAgree
          fragmentEnvironment second := by
    intro fragmentIndex hostIndex related
    have firstValue := firstAgreement fragmentIndex hostIndex related
    calc
      fragmentEnvironment fragmentIndex = first hostIndex := by
        simpa [fragmentEnvironment, fragmentMap] using firstValue
      _ = second hostIndex := by
        apply agree hostIndex
        have originClosure := occurrenceFragmentWire_origin_mem_closure input
          occurrence (fragment.rootWires.get fragmentIndex)
        unfold VisualProof.Rule.IterationSoundness.extractionContextRelation at related
        dsimp only [layout] at related
        rcases originClosure with internal | touching
        · exact Or.inl (related ▸ internal)
        · exact Or.inr (related ▸ touching)
  constructor
  · intro firstDenotes
    exact forward fragmentEnvironment second relations secondAgreement
      (backward fragmentEnvironment first relations firstAgreement firstDenotes)
  · intro secondDenotes
    exact forward fragmentEnvironment first relations firstAgreement
      (backward fragmentEnvironment second relations secondAgreement secondDenotes)

end AbstractionRawTrace

end VisualProof.Concrete
