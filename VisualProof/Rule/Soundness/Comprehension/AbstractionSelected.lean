import VisualProof.Rule.Comprehension.Semantics
import VisualProof.Rule.Soundness.Comprehension.AbstractionEnvironment
import VisualProof.Rule.Soundness.Iteration.ExtractionTerminalSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

def occurrenceLayout
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input) :
    FragmentLayout input.val occurrence.selection := {}

theorem occurrenceLayout_proxyCount_zero
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence) :
    (occurrenceLayout input occurrence).proxyCount = 0 := by
  change occurrence.selection.externalBinders.length = 0
  rw [witness.externalBinders_empty]
  rfl

theorem occurrenceFragment_eq_selectedFragment
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input) :
    input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence) =
      selectedFragment input occurrence.selection := by
  unfold selectedFragment
  congr 1

theorem occurrenceFragment_wellFormed
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input) :
    (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)).WellFormed signature :=
  ConcreteDiagram.extractOpenRaw_wellFormed input occurrence.selection
    (occurrenceLayout input occurrence)

noncomputable def touchingIndex
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor)
    (position : Fin occurrence.selection.touchingWires.length) :
    Fin context.length :=
  Classical.choose (indexOf?_complete ((exact.mem_iff _).2
    (ConcreteDiagram.touchingWire_scope_encloses_anchor input
      occurrence.selection position)))

theorem touchingIndex_get
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor)
    (position : Fin occurrence.selection.touchingWires.length) :
    context.get (touchingIndex input occurrence context exact position) =
      occurrence.selection.touchingWires.get position := by
  unfold touchingIndex
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((exact.mem_iff _).2
      (ConcreteDiagram.touchingWire_scope_encloses_anchor input
        occurrence.selection position))))

noncomputable def touchingEnvironment
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor)
    (environment : Fin context.length → D) :
    Fin occurrence.selection.touchingWires.length → D :=
  environment ∘ touchingIndex input occurrence context exact

noncomputable def exposedHostIndex
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor) :
    Fin (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)).exposedWires.length →
      Fin context.length :=
  fun index => Classical.choose (indexOf?_complete ((exact.mem_iff _).2 (by
    have rootScope :=
      (occurrenceFragment_wellFormed input occurrence).exposed_root_scoped
        (List.get_mem _ index)
    change ((input.val.extractDiagramRaw occurrence.selection
      (occurrenceLayout input occurrence)).wires
        ((input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).exposedWires.get index)).scope =
      (occurrenceLayout input occurrence).root at rootScope
    have bodyEq := FragmentLayout.bodyContainer_eq_root_of_proxyCount_eq_zero
      (occurrenceLayout input occurrence)
      (occurrenceLayout_proxyCount_zero input occurrence witness)
    apply IterationSoundness.fragmentWireOrigin_scope_encloses_anchor input
      occurrence.selection (occurrenceLayout input occurrence)
      ((input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).exposedWires.get index)
    rw [rootScope, bodyEq]
    exact ConcreteDiagram.Encloses.refl _ _)))

theorem exposedHostIndex_get
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor)
    (index : Fin (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)).exposedWires.length) :
    context.get (exposedHostIndex input occurrence witness context exact index) =
      input.val.fragmentWireOrigin occurrence.selection
        (occurrenceLayout input occurrence)
        ((input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).exposedWires.get index) := by
  unfold exposedHostIndex
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((exact.mem_iff _).2 (by
      have rootScope :=
        (occurrenceFragment_wellFormed input occurrence).exposed_root_scoped
          (List.get_mem _ index)
      change ((input.val.extractDiagramRaw occurrence.selection
        (occurrenceLayout input occurrence)).wires
          ((input.val.extractOpenRaw occurrence.selection
            (occurrenceLayout input occurrence)).exposedWires.get index)).scope =
        (occurrenceLayout input occurrence).root at rootScope
      have bodyEq := FragmentLayout.bodyContainer_eq_root_of_proxyCount_eq_zero
        (occurrenceLayout input occurrence)
        (occurrenceLayout_proxyCount_zero input occurrence witness)
      apply IterationSoundness.fragmentWireOrigin_scope_encloses_anchor input
        occurrence.selection (occurrenceLayout input occurrence)
        ((input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).exposedWires.get index)
      rw [rootScope, bodyEq]
      exact ConcreteDiagram.Encloses.refl _ _))))

noncomputable def fragmentOuterEnvironment
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor)
    (environment : Fin context.length → D) :
    Fin (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)).exposedWires.length → D :=
  environment ∘ exposedHostIndex input occurrence witness context exact

theorem fragmentOuterEnvironment_boundary
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor)
    (environment : Fin context.length → D)
    (position : Fin occurrence.selection.touchingWires.length) :
    fragmentOuterEnvironment input occurrence witness context exact environment
        ((input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).boundaryClass
            (Fin.cast (ConcreteDiagram.extractBoundaryRaw_length input.val
              occurrence.selection (occurrenceLayout input occurrence)).symm
              position)) =
      touchingEnvironment input occurrence context exact environment position := by
  simp only [fragmentOuterEnvironment, touchingEnvironment, Function.comp_apply]
  apply congrArg environment
  apply Fin.ext
  apply (List.getElem_inj exact.nodup).mp
  change context.get (exposedHostIndex input occurrence witness context exact
      ((input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).boundaryClass
          (Fin.cast (ConcreteDiagram.extractBoundaryRaw_length input.val
            occurrence.selection (occurrenceLayout input occurrence)).symm
            position))) =
    context.get (touchingIndex input occurrence context exact position)
  rw [exposedHostIndex_get, touchingIndex_get]
  have boundarySound := OpenConcreteDiagram.boundaryClass_sound
    (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence))
    (Fin.cast (ConcreteDiagram.extractBoundaryRaw_length input.val
      occurrence.selection (occurrenceLayout input occurrence)).symm position)
  rw [boundarySound]
  simpa [ConcreteDiagram.extractOpenRaw, ConcreteDiagram.extractBoundaryRaw,
    ConcreteDiagram.fragmentWireOrigin, FragmentLayout.boundaryWire]

theorem fragmentOuterEnvironment_agrees
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (context : ConcreteElaboration.WireContext input.val)
    (exact : context.Exact occurrence.selection.val.anchor)
    (environment : Fin context.length → D) :
    (IterationSoundness.extractionContextRelation input occurrence.selection
      (occurrenceLayout input occurrence)
      (input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).exposedWires context
    ).EnvironmentsAgree
      (fragmentOuterEnvironment input occurrence witness context exact
        environment) environment := by
  intro fragmentIndex hostIndex related
  simp only [fragmentOuterEnvironment, Function.comp_apply]
  apply congrArg environment
  apply Fin.ext
  apply (List.getElem_inj exact.nodup).mp
  change context.get (exposedHostIndex input occurrence witness context exact
      fragmentIndex) = context.get hostIndex
  rw [exposedHostIndex_get]
  exact related

theorem occurrenceFragment_denote_iff_relation
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin occurrence.selection.touchingWires.length →
      model.Carrier) :
    (input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).denote
        (occurrenceFragment_wellFormed input occurrence) model named
        (environment ∘ Fin.cast
          (ConcreteDiagram.extractBoundaryRaw_length input.val
            occurrence.selection (occurrenceLayout input occurrence))) ↔
      abstractionRelation (signature := signature) comprehension model named
        (environment ∘ witness.assignment.args) := by
  let fragment := input.val.extractOpenRaw occurrence.selection
    (occurrenceLayout input occurrence)
  let occurrenceIso : OpenConcreteIso fragment witness.diagonal.val := by
    dsimp only [fragment]
    rw [occurrenceFragment_eq_selectedFragment input occurrence]
    exact witness.exactOccurrence
  let sourceArgs : Fin fragment.boundary.length → model.Carrier :=
    environment ∘ Fin.cast
      (ConcreteDiagram.extractBoundaryRaw_length input.val
        occurrence.selection (occurrenceLayout input occurrence))
  have argsEq :
      sourceArgs ∘ Fin.cast occurrenceIso.boundary_length_eq.symm =
        ((environment ∘ Fin.cast witness.diagonal_externalClasses) ∘
          witness.diagonal.elaborate.boundary) := by
    funext position
    apply congrArg environment
    apply Fin.ext
    have identity := witness.diagonal_boundary_identity
      (Fin.cast witness.diagonal_boundary_length position)
    have values := congrArg Fin.val identity
    simpa [sourceArgs, fragment, occurrenceIso, Function.comp_apply] using values.symm
  have isoSemantic := occurrenceIso.denote_iff
    (occurrenceFragment_wellFormed input occurrence) witness.diagonal.property
    model named sourceArgs
  rw [argsEq] at isoSemantic
  exact isoSemantic.trans
    (witness.diagonal_denote_iff_relation model named environment)

/-- Truth of one executor-certified selected occurrence entails application
of the single comprehension relation to that occurrence's ordered host wires.
The theorem consumes the actual selected compiler block, including hidden
root-wire witnesses, rather than an intrinsic replacement surrogate. -/
theorem selectedOccurrence_denote_relation
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
    (hostEnvironment : Fin hostContext.length → model.Carrier)
    (relationEnvironment : RelEnv model.Carrier hostRels)
    (hostDenotes : denoteRegion model named hostEnvironment relationEnvironment
      (Region.mk 0 hostItems)) :
    abstractionRelation (signature := signature) comprehension model named
      (touchingEnvironment input occurrence hostContext hostExact
        hostEnvironment ∘ witness.assignment.args) := by
  let fragment := input.val.extractOpenRaw occurrence.selection
    (occurrenceLayout input occurrence)
  let checkedFragment : CheckedOpenDiagram signature :=
    ⟨fragment, occurrenceFragment_wellFormed input occurrence⟩
  let compiled := Splice.Input.compiledSpliceOpenRootItems checkedFragment
  have selectedSimulation :=
    IterationSoundness.extractionCompileRoot_selected_denote input
      occurrence.selection (occurrenceLayout input occurrence)
      (occurrenceLayout_proxyCount_zero input occurrence witness)
      model named hostFuel hostContext hostBinders hostEnumeration hostCover
      hostExact compiled.items hostItems (by
        simpa [checkedFragment, fragment] using compiled.computation)
      hostCompiled
  let fragmentOuter := fragmentOuterEnvironment input occurrence witness
    hostContext hostExact hostEnvironment
  have fragmentRenamedDenotes := selectedSimulation fragmentOuter
    hostEnvironment relationEnvironment
    (fragmentOuterEnvironment_agrees input occurrence witness hostContext
      hostExact hostEnvironment) hostDenotes
  let relationMap : RelationRenaming [] hostRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming hostRels
  have fragmentBodyDenotes : denoteRegion (relCtx := []) model named fragmentOuter
      (PUnit.unit : RelEnv model.Carrier [])
      (ConcreteElaboration.finishRoot fragment.exposedWires
        fragment.hiddenWires compiled.items) := by
    exact (denoteRegion_renameRelations model named relationMap
      (PUnit.unit : RelEnv model.Carrier []) relationEnvironment
      (RelEnv.pullback_agrees relationMap relationEnvironment)
      fragmentOuter
      (ConcreteElaboration.finishRoot fragment.exposedWires
        fragment.hiddenWires compiled.items)).mp (by
          simpa [relationMap] using fragmentRenamedDenotes)
  let touching := touchingEnvironment input occurrence hostContext hostExact
    hostEnvironment
  have fragmentDenotes : fragment.denote
      (occurrenceFragment_wellFormed input occurrence) model named
      (touching ∘ Fin.cast
        (ConcreteDiagram.extractBoundaryRaw_length input.val
          occurrence.selection (occurrenceLayout input occurrence))) := by
    change checkedFragment.denote model named _
    rw [CheckedOpenDiagram.denote_eq_intrinsic]
    unfold denoteOpen
    refine ⟨{
      args := touching ∘ Fin.cast
        (ConcreteDiagram.extractBoundaryRaw_length input.val
          occurrence.selection (occurrenceLayout input occurrence))
      classes := fragmentOuter
      agrees := ?_
    }, rfl, ?_⟩
    · intro position
      have boundary := fragmentOuterEnvironment_boundary input occurrence
        witness hostContext hostExact hostEnvironment
        (Fin.cast (ConcreteDiagram.extractBoundaryRaw_length input.val
          occurrence.selection (occurrenceLayout input occurrence)) position)
      simpa [checkedFragment, fragment, touching, Function.comp_apply] using
        boundary
    · rw [compiled.elaborate_body]
      exact fragmentBodyDenotes
  exact (occurrenceFragment_denote_iff_relation input occurrence witness model
    named touching).mp fragmentDenotes

end AbstractionRawTrace

end VisualProof.Rule
