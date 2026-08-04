import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrenceFamily

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- A compiled selected occurrence depends on its anchor valuation only
through the occurrence's internal and touching wires. -/
theorem selectedOccurrence_denote_congr
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (hostFuel : Nat)
    (hostContext : ConcreteElaboration.WireContext input.val)
    (hostBinders : ConcreteElaboration.BinderContext input.val hostRels)
    (hostEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val hostBinders occurrence.selection.val.anchor)
    (hostCover : hostBinders.Covers occurrence.selection.val.anchor)
    (hostExact : hostContext.Exact occurrence.selection.val.anchor)
    (hostItems : ItemSeq signature hostContext.length hostRels)
    (hostCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val hostFuel)
        hostContext hostBinders
        (ModalSoundness.selectedOccurrences input.val occurrence.selection) =
          some hostItems)
    (first second : Fin hostContext.length → model.Carrier)
    (relations : RelEnv model.Carrier hostRels)
    (agree : ∀ index,
      hostContext.get index ∈ occurrence.selection.internalWires ∨
        hostContext.get index ∈ occurrence.selection.touchingWires →
      first index = second index) :
    denoteItemSeq model named first relations hostItems ↔
      denoteItemSeq model named second relations hostItems := by
  let layout := occurrenceLayout input occurrence
  let fragment := input.val.extractOpenRaw occurrence.selection layout
  let checkedFragment : CheckedOpenDiagram signature :=
    ⟨fragment, occurrenceFragment_wellFormed input occurrence⟩
  let compiled := Splice.Input.compiledSpliceOpenRootItems checkedFragment
  have bodyEq : layout.bodyContainer = fragment.diagram.root :=
    (occurrenceLayout input occurrence).bodyContainer_eq_root_of_proxyCount_eq_zero
      (occurrenceLayout_proxyCount_zero input occurrence witness)
  let fragmentEnumeration :
      ConcreteElaboration.BinderContext.Enumeration fragment.diagram
        ConcreteElaboration.BinderContext.empty layout.bodyContainer :=
    bodyEq.symm ▸ ConcreteElaboration.BinderContext.Enumeration.empty
      fragment.diagram
  have fragmentExact : ConcreteElaboration.WireContext.Exact
      fragment.rootWires layout.bodyContainer := by
    rw [bodyEq]
    exact ConcreteElaboration.openRootWires_exact
      (occurrenceFragment_wellFormed input occurrence)
  have fragmentCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature fragment.diagram
        (ConcreteElaboration.compileRegion? signature fragment.diagram
          fragment.diagram.regionCount)
        fragment.rootWires ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences fragment.diagram
          layout.bodyContainer) = some compiled.items := by
    simpa [fragment, checkedFragment, bodyEq] using compiled.computation
  have backward := IterationSoundness.extractionCompileSelectedItems_denote
    input occurrence.selection layout model named .backward
    fragment.diagram.regionCount hostFuel fragment.rootWires hostContext
    ConcreteElaboration.BinderContext.empty hostBinders fragmentEnumeration
    hostEnumeration hostCover fragmentExact hostExact compiled.items hostItems
    fragmentCompiled hostCompiled
  have forward := IterationSoundness.extractionCompileSelectedItems_denote
    input occurrence.selection layout model named .forward
    fragment.diagram.regionCount hostFuel fragment.rootWires hostContext
    ConcreteElaboration.BinderContext.empty hostBinders fragmentEnumeration
    hostEnumeration hostCover fragmentExact hostExact compiled.items hostItems
    fragmentCompiled hostCompiled
  let fragmentMap := IterationSoundness.extractionContextIndexMap input
    occurrence.selection layout fragment.rootWires hostContext fragmentExact
      hostExact
  let fragmentEnvironment : Fin fragment.rootWires.length → model.Carrier :=
    first ∘ fragmentMap
  have firstAgreement :=
    IterationSoundness.extractionContextEnvironmentsAgree input
      occurrence.selection layout fragment.rootWires hostContext fragmentExact
      hostExact first
  have secondAgreement :
      (IterationSoundness.extractionContextRelation input occurrence.selection
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
        unfold IterationSoundness.extractionContextRelation at related
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

end VisualProof.Rule
