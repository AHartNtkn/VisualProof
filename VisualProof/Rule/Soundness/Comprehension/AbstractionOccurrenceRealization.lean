import VisualProof.Rule.Soundness.Comprehension.AbstractionFixedRelation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- A true application of the comprehension relation supplies the exact
open-root compiler witnesses for one certified occurrence.  Its exposed
classes are forced to be the ordered touching-wire valuation; only hidden
root wires remain freely chosen. -/
theorem relation_occurrence_openRoot_realization
    {signature : List Nat}
    (input : CheckedDiagram signature)
    (comprehension : CheckedOpenDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (hostContext : ConcreteElaboration.WireContext input.val)
    (hostExact : hostContext.Exact occurrence.selection.val.anchor)
    (hostEnvironment : Fin hostContext.length → model.Carrier)
    (relationDenotes : abstractionRelation (signature := signature)
      comprehension model named
        (touchingEnvironment input occurrence hostContext hostExact
          hostEnvironment ∘ witness.assignment.args)) :
    let fragment := input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)
    let checkedFragment : CheckedOpenDiagram signature :=
      ⟨fragment, occurrenceFragment_wellFormed input occurrence⟩
    let compiled := Splice.Input.compiledSpliceOpenRootItems checkedFragment
    ∃ assignment : BoundaryAssignment checkedFragment.elaborate model.Carrier,
      assignment.classes = fragmentOuterEnvironment input occurrence witness
        hostContext hostExact hostEnvironment ∧
      ∃ hiddenEnvironment : Fin fragment.hiddenWires.length → model.Carrier,
        denoteItemSeq (relCtx := []) model named
          (ConcreteElaboration.rootEnvironment fragment.exposedWires
            fragment.hiddenWires assignment.classes hiddenEnvironment)
          (PUnit.unit : RelEnv model.Carrier []) compiled.items := by
  dsimp only
  let fragment := input.val.extractOpenRaw occurrence.selection
    (occurrenceLayout input occurrence)
  let checkedFragment : CheckedOpenDiagram signature :=
    ⟨fragment, occurrenceFragment_wellFormed input occurrence⟩
  let compiled := Splice.Input.compiledSpliceOpenRootItems checkedFragment
  let touching := touchingEnvironment input occurrence hostContext hostExact
    hostEnvironment
  let fragmentArguments : Fin fragment.boundary.length → model.Carrier :=
    touching ∘ Fin.cast (ConcreteDiagram.extractBoundaryRaw_length input.val
      occurrence.selection (occurrenceLayout input occurrence))
  have fragmentDenotes : checkedFragment.denote model named fragmentArguments := by
    exact (occurrenceFragment_denote_iff_relation input occurrence witness model
      named touching).2 (by
        simpa [fragmentArguments, touching, Function.comp_def] using
          relationDenotes)
  obtain ⟨assignment, assignmentArgs, hiddenEnvironment, itemsDenote⟩ :=
    (compiled.denote_iff model named fragmentArguments).1 fragmentDenotes
  refine ⟨assignment, ?_, hiddenEnvironment, itemsDenote⟩
  funext external
  obtain ⟨position, positionClass⟩ :=
    checkedFragment.val.boundaryClass_surjective external
  have assignmentAt := assignment.agrees position
  change assignment.classes (checkedFragment.val.boundaryClass position) =
    assignment.args position at assignmentAt
  rw [positionClass] at assignmentAt
  calc
    assignment.classes external = assignment.args position := assignmentAt
    _ = fragmentArguments position := congrFun assignmentArgs position
    _ = touching
        (Fin.cast (ConcreteDiagram.extractBoundaryRaw_length input.val
          occurrence.selection (occurrenceLayout input occurrence))
          position) := rfl
    _ = fragmentOuterEnvironment input occurrence witness hostContext
        hostExact hostEnvironment external := by
      rw [← positionClass]
      symm
      exact fragmentOuterEnvironment_boundary input occurrence witness
        hostContext hostExact hostEnvironment
          (Fin.cast (ConcreteDiagram.extractBoundaryRaw_length input.val
            occurrence.selection (occurrenceLayout input occurrence)) position)

/-- Extend one fragment-root valuation to the host anchor context, using the
fragment value exactly on wires represented by the occurrence and retaining a
caller-supplied fallback everywhere else. -/
noncomputable def occurrenceHostEnvironment
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (hostContext : ConcreteElaboration.WireContext input.val)
    (hostExact : hostContext.Exact occurrence.selection.val.anchor)
    (fragmentEnvironment : Fin (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)).rootWires.length → D)
    (fallback : Fin hostContext.length → D) :
    Fin hostContext.length → D := by
  classical
  exact fun hostIndex =>
    if represented : ∃ fragmentIndex,
        (IterationSoundness.extractionContextRelation input occurrence.selection
          (occurrenceLayout input occurrence)
          (input.val.extractOpenRaw occurrence.selection
            (occurrenceLayout input occurrence)).rootWires hostContext).Rel
              fragmentIndex hostIndex
    then fragmentEnvironment (Classical.choose represented)
    else fallback hostIndex

theorem occurrenceHostEnvironment_agrees
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (hostContext : ConcreteElaboration.WireContext input.val)
    (hostExact : hostContext.Exact occurrence.selection.val.anchor)
    (fragmentEnvironment : Fin (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)).rootWires.length → D)
    (fallback : Fin hostContext.length → D) :
    (IterationSoundness.extractionContextRelation input occurrence.selection
      (occurrenceLayout input occurrence)
      (input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).rootWires hostContext
    ).EnvironmentsAgree fragmentEnvironment
      (occurrenceHostEnvironment input occurrence witness hostContext hostExact
        fragmentEnvironment fallback) := by
  intro fragmentIndex hostIndex related
  unfold occurrenceHostEnvironment
  rw [dif_pos ⟨fragmentIndex, related⟩]
  let chosen := Classical.choose
    (show ∃ candidate,
      (IterationSoundness.extractionContextRelation input occurrence.selection
        (occurrenceLayout input occurrence)
        (input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).rootWires hostContext).Rel
            candidate hostIndex from ⟨fragmentIndex, related⟩)
  have chosenRelated := Classical.choose_spec
    (show ∃ candidate,
      (IterationSoundness.extractionContextRelation input occurrence.selection
        (occurrenceLayout input occurrence)
        (input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).rootWires hostContext).Rel
            candidate hostIndex from ⟨fragmentIndex, related⟩)
  have wireEq :
      (input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).rootWires.get chosen =
      (input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).rootWires.get fragmentIndex := by
    apply input.val.fragmentWireOrigin_injective occurrence.selection
      (occurrenceLayout input occurrence)
    exact chosenRelated.trans related.symm
  have indexEq : chosen = fragmentIndex := by
    apply Fin.ext
    exact (List.getElem_inj
      (input.val.extractOpenRaw occurrence.selection
        (occurrenceLayout input occurrence)).rootWires_nodup).mp wireEq
  exact congrArg fragmentEnvironment indexEq.symm

/-- Root environments produced by the open compiler take the assignment's
class value on every exposed root wire. -/
theorem rootEnvironment_exposed
    (fragment : OpenConcreteDiagram)
    (classes : Fin fragment.exposedWires.length → D)
    (hidden : Fin fragment.hiddenWires.length → D)
    (rootIndex : Fin fragment.rootWires.length)
    (exposedIndex : Fin fragment.exposedWires.length)
    (wireEq : fragment.rootWires.get rootIndex =
      fragment.exposedWires.get exposedIndex) :
    ConcreteElaboration.rootEnvironment fragment.exposedWires
        fragment.hiddenWires classes hidden rootIndex = classes exposedIndex := by
  let lengthEq : fragment.exposedWires.length + fragment.hiddenWires.length =
      fragment.rootWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let canonical : Fin fragment.rootWires.length :=
    Fin.cast lengthEq (Fin.castAdd fragment.hiddenWires.length exposedIndex)
  have canonicalWire : fragment.rootWires.get canonical =
      fragment.exposedWires.get exposedIndex := by
    simp [canonical, lengthEq, OpenConcreteDiagram.rootWires]
  have indexEq : rootIndex = canonical := by
    apply Fin.ext
    exact (List.getElem_inj fragment.rootWires_nodup).mp
      (wireEq.trans canonicalWire.symm)
  subst rootIndex
  simp [canonical, lengthEq, ConcreteElaboration.rootEnvironment,
    OpenConcreteDiagram.rootWires, extendWireEnv]

/-- The host extension changes only wires internal to this occurrence.  On a
boundary/exposed fragment wire, the open assignment is already forced to the
fallback touching-wire value. -/
theorem occurrenceHostEnvironment_eq_fallback_of_not_internal
    (input : CheckedDiagram signature)
    (occurrence : AbstractionOccurrence input)
    (witness : AbstractionWitness input comprehension occurrence)
    (hostContext : ConcreteElaboration.WireContext input.val)
    (hostExact : hostContext.Exact occurrence.selection.val.anchor)
    (fragmentEnvironment : Fin (input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)).rootWires.length → D)
    (fallback : Fin hostContext.length → D)
    (exposedValues : ∀ rootIndex exposedIndex,
      (input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).rootWires.get rootIndex =
        (input.val.extractOpenRaw occurrence.selection
          (occurrenceLayout input occurrence)).exposedWires.get exposedIndex →
      fragmentEnvironment rootIndex =
        fragmentOuterEnvironment input occurrence witness hostContext hostExact
          fallback exposedIndex)
    (hostIndex : Fin hostContext.length)
    (notInternal : hostContext.get hostIndex ∉
      occurrence.selection.internalWires) :
    occurrenceHostEnvironment input occurrence witness hostContext hostExact
        fragmentEnvironment fallback hostIndex = fallback hostIndex := by
  classical
  unfold occurrenceHostEnvironment
  split
  · rename_i represented
    let fragment := input.val.extractOpenRaw occurrence.selection
      (occurrenceLayout input occurrence)
    let fragmentIndex := Classical.choose represented
    have related := Classical.choose_spec represented
    have originNotInternal : input.val.fragmentWireOrigin occurrence.selection
        (occurrenceLayout input occurrence)
        (fragment.rootWires.get fragmentIndex) ∉
          occurrence.selection.internalWires := by
      intro internal
      apply notInternal
      unfold IterationSoundness.extractionContextRelation at related
      exact related ▸ internal
    have boundaryMember : fragment.rootWires.get fragmentIndex ∈
        fragment.boundary := by
      let fragmentWire := fragment.rootWires.get fragmentIndex
      change fragmentWire ∈ fragment.boundary
      have originNotInternal' :
          input.val.fragmentWireOrigin occurrence.selection
              (occurrenceLayout input occurrence) fragmentWire ∉
            occurrence.selection.internalWires := by
        exact originNotInternal
      revert originNotInternal'
      refine Fin.addCases (m := (occurrenceLayout input occurrence).internalWireCount)
        (n := (occurrenceLayout input occurrence).boundaryWireCount)
        (fun internal notInternal => ?_)
        (fun boundary _ => ?_) fragmentWire
      · apply False.elim
        apply notInternal
        simpa only [ConcreteDiagram.fragmentWireOrigin,
          Fin.addCases_left] using
            (List.get_mem occurrence.selection.internalWires internal)
      · change Fin.natAdd (occurrenceLayout input occurrence).internalWireCount
            boundary ∈
          List.ofFn (occurrenceLayout input occurrence).boundaryWire
        exact List.mem_ofFn.mpr ⟨boundary, rfl⟩
    have exposedMember : fragment.rootWires.get fragmentIndex ∈
        fragment.exposedWires :=
      (OpenConcreteDiagram.mem_exposedWires fragment _).2 boundaryMember
    obtain ⟨exposedIndex, exposedGet⟩ := List.mem_iff_get.mp exposedMember
    have fragmentValue := exposedValues fragmentIndex exposedIndex exposedGet.symm
    have hostIndexEq : exposedHostIndex input occurrence witness hostContext
        hostExact exposedIndex = hostIndex := by
      apply Fin.ext
      apply (List.getElem_inj hostExact.nodup).mp
      have exposedOrigin := exposedHostIndex_get input occurrence witness
        hostContext hostExact exposedIndex
      unfold IterationSoundness.extractionContextRelation at related
      simpa only [List.get_eq_getElem] using exposedOrigin.trans
        ((congrArg (input.val.fragmentWireOrigin occurrence.selection
          (occurrenceLayout input occurrence)) exposedGet).trans related)
    calc
      fragmentEnvironment (Classical.choose represented) =
          fragmentOuterEnvironment input occurrence witness hostContext
            hostExact fallback exposedIndex := fragmentValue
      _ = fallback hostIndex := by
        simp [fragmentOuterEnvironment, Function.comp_apply, hostIndexEq]
  · rfl

/-- Converse of `selectedOccurrence_denote_relation` at the correct semantic
level: a true comprehension application chooses the occurrence's deleted
root-wire witnesses and makes the authoritative selected compiler block true.
The chosen host valuation is unchanged outside the occurrence's internal-wire
set, which is the composition law needed for several disjoint occurrences. -/
theorem relation_selectedOccurrence_environment
    (input : CheckedDiagram signature)
    (comprehension : CheckedOpenDiagram signature)
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
    (fallback : Fin hostContext.length → model.Carrier)
    (relationEnvironment : RelEnv model.Carrier hostRels)
    (relationDenotes : abstractionRelation (signature := signature)
      comprehension model named
        (touchingEnvironment input occurrence hostContext hostExact fallback ∘
          witness.assignment.args)) :
    ∃ hostEnvironment : Fin hostContext.length → model.Carrier,
      (∀ index, hostContext.get index ∉ occurrence.selection.internalWires →
        hostEnvironment index = fallback index) ∧
      denoteItemSeq model named hostEnvironment relationEnvironment hostItems := by
  let fragment := input.val.extractOpenRaw occurrence.selection
    (occurrenceLayout input occurrence)
  let checkedFragment : CheckedOpenDiagram signature :=
    ⟨fragment, occurrenceFragment_wellFormed input occurrence⟩
  let compiled := Splice.Input.compiledSpliceOpenRootItems checkedFragment
  obtain ⟨assignment, classesEq, hiddenEnvironment, fragmentItemsDenote⟩ :=
    relation_occurrence_openRoot_realization input comprehension occurrence
      witness model named hostContext hostExact fallback relationDenotes
  let fragmentEnvironment := ConcreteElaboration.rootEnvironment
    fragment.exposedWires fragment.hiddenWires assignment.classes
      hiddenEnvironment
  let hostEnvironment := occurrenceHostEnvironment input occurrence witness
    hostContext hostExact fragmentEnvironment fallback
  have exposedValues : ∀ rootIndex exposedIndex,
      fragment.rootWires.get rootIndex =
          fragment.exposedWires.get exposedIndex →
        fragmentEnvironment rootIndex =
          fragmentOuterEnvironment input occurrence witness hostContext
            hostExact fallback exposedIndex := by
    intro rootIndex exposedIndex wireEq
    change ConcreteElaboration.rootEnvironment fragment.exposedWires
        fragment.hiddenWires assignment.classes hiddenEnvironment rootIndex = _
    rw [rootEnvironment_exposed fragment assignment.classes hiddenEnvironment
      rootIndex exposedIndex wireEq, classesEq]
  have preserves : ∀ index,
      hostContext.get index ∉ occurrence.selection.internalWires →
        hostEnvironment index = fallback index := by
    intro index notInternal
    exact occurrenceHostEnvironment_eq_fallback_of_not_internal input occurrence
      witness hostContext hostExact fragmentEnvironment fallback exposedValues
      index notInternal
  have environmentsAgree :
      (IterationSoundness.extractionContextRelation input occurrence.selection
        (occurrenceLayout input occurrence) fragment.rootWires hostContext
      ).EnvironmentsAgree fragmentEnvironment hostEnvironment := by
    exact occurrenceHostEnvironment_agrees input occurrence witness hostContext
      hostExact fragmentEnvironment fallback
  have bodyEq : (occurrenceLayout input occurrence).bodyContainer =
      fragment.diagram.root :=
    (occurrenceLayout input occurrence).bodyContainer_eq_root_of_proxyCount_eq_zero
      (occurrenceLayout_proxyCount_zero input occurrence witness)
  let fragmentEnumeration :
      ConcreteElaboration.BinderContext.Enumeration fragment.diagram
        ConcreteElaboration.BinderContext.empty
          (occurrenceLayout input occurrence).bodyContainer :=
    bodyEq.symm ▸ ConcreteElaboration.BinderContext.Enumeration.empty
      fragment.diagram
  have fragmentExact : ConcreteElaboration.WireContext.Exact
      fragment.rootWires (occurrenceLayout input occurrence).bodyContainer := by
    rw [bodyEq]
    exact ConcreteElaboration.openRootWires_exact
      (occurrenceFragment_wellFormed input occurrence)
  let binderWitness := IterationSoundness.ExtractionBinderWitness.terminal input
    occurrence.selection (occurrenceLayout input occurrence)
    ConcreteElaboration.BinderContext.empty fragmentEnumeration hostBinders
      hostCover
  have itemsSimulation :=
    IterationSoundness.extractionCompileSelectedItems_denote input
      occurrence.selection (occurrenceLayout input occurrence) model named
      .forward fragment.diagram.regionCount hostFuel fragment.rootWires
      hostContext ConcreteElaboration.BinderContext.empty hostBinders
      fragmentEnumeration hostEnumeration hostCover fragmentExact hostExact
      compiled.items hostItems (by
        simpa [fragment, checkedFragment, bodyEq] using compiled.computation)
      hostCompiled
  have fragmentRenamedDenotes : denoteItemSeq model named fragmentEnvironment
      relationEnvironment
      (compiled.items.renameRelations binderWitness.relationMap) := by
    exact (denoteItemSeq_renameRelations model named binderWitness.relationMap
      (PUnit.unit : RelEnv model.Carrier []) relationEnvironment
      (RelEnv.pullback_agrees binderWitness.relationMap relationEnvironment)
      fragmentEnvironment compiled.items).2 (by
        simpa [fragmentEnvironment] using fragmentItemsDenote)
  refine ⟨hostEnvironment, preserves, ?_⟩
  exact itemsSimulation fragmentEnvironment hostEnvironment relationEnvironment
    environmentsAgree (by
      simpa [binderWitness] using fragmentRenamedDenotes)

end AbstractionRawTrace

end VisualProof.Rule
