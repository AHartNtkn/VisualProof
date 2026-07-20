import VisualProof.Rule.Soundness.Comprehension.AbstractionReachability

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace AbstractionRawTrace

def extendedOuterIndex
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount) (index : Fin context.length) :
    Fin (context.extend region).length :=
  Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
    (Fin.castAdd
      (ConcreteElaboration.exactScopeWires d region).length index)

def extendedLocalIndex
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires d region).length) :
    Fin (context.extend region).length :=
  Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
    (Fin.natAdd context.length index)

def localEnvironmentPart
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (environment : Fin (context.extend region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires d region).length → D :=
  fun index => environment (extendedLocalIndex context region index)

theorem extendedEnvironment_of_parts
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (outerEnvironment : Fin context.length → D)
    (environment : Fin (context.extend region).length → D)
    (outerValues : ∀ index,
      environment (extendedOuterIndex context region index) =
        outerEnvironment index) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        (localEnvironmentPart context region environment) = environment := by
  funext index
  let splitIndex := Fin.cast
    (ConcreteElaboration.WireContext.length_extend context region) index
  change extendWireEnv outerEnvironment
      (localEnvironmentPart context region environment) splitIndex =
    environment (Fin.cast
      (ConcreteElaboration.WireContext.length_extend context region).symm
      splitIndex)
  refine Fin.addCases ?_ ?_ splitIndex
  · intro outerIndex
    rw [extendWireEnv, Fin.addCases_left]
    exact (outerValues outerIndex).symm
  · intro localIndex
    rw [extendWireEnv, Fin.addCases_right]
    rfl

@[simp] theorem extendedEnvironment_outer
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (outerEnvironment : Fin context.length → D)
    (localEnvironment :
      Fin (ConcreteElaboration.exactScopeWires d region).length → D)
    (index : Fin context.length) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        localEnvironment (extendedOuterIndex context region index) =
      outerEnvironment index := by
  simp [ConcreteElaboration.extendedEnvironment, extendedOuterIndex,
    extendWireEnv, Fin.addCases_left]

@[simp] theorem extendedEnvironment_local
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (outerEnvironment : Fin context.length → D)
    (localEnvironment :
      Fin (ConcreteElaboration.exactScopeWires d region).length → D)
    (index :
      Fin (ConcreteElaboration.exactScopeWires d region).length) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        localEnvironment (extendedLocalIndex context region index) =
      localEnvironment index := by
  simp [ConcreteElaboration.extendedEnvironment, extendedLocalIndex,
    extendWireEnv, Fin.addCases_right]

@[simp] theorem extendedOuterIndex_get
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount) (index : Fin context.length) :
    (context.extend region).get (extendedOuterIndex context region index) =
      context.get index := by
  simpa [extendedOuterIndex, ConcreteElaboration.WireContext.outerIndex] using
    ConcreteElaboration.WireContext.extend_outer context region index

@[simp] theorem extendedLocalIndex_get
    (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (index :
      Fin (ConcreteElaboration.exactScopeWires d region).length) :
    (context.extend region).get (extendedLocalIndex context region index) =
    (ConcreteElaboration.exactScopeWires d region).get index := by
  simpa [extendedLocalIndex] using
    ConcreteElaboration.WireContext.extend_local context region index

noncomputable def localSourceIndex
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true)
    (targetIndex : Fin
      (ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).length) :
    Fin (ConcreteElaboration.exactScopeWires input.val region).length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete (by
    let targetWire :=
      (ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).get targetIndex
    have targetScope :=
      (ConcreteElaboration.mem_exactScopeWires trace.diagram
        (trace.regionMap region) targetWire).1 (List.get_mem _ _)
    let original := trace.domains.wires.origin targetWire
    have originalSurvives := trace.domains.wires.origin_survives targetWire
    have scopeTransport := trace.targetWire_scope original originalSurvives
    rw [trace.targetWire_origin_index targetWire, targetScope,
      trace.regionMap_of_survives region survives] at scopeTransport
    exact (ConcreteElaboration.mem_exactScopeWires input.val region original).2
      (trace.targetRegion_injective scopeTransport.symm)))

theorem localSourceIndex_get
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true)
    (targetIndex : Fin
      (ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).length) :
    (ConcreteElaboration.exactScopeWires input.val region).get
        (trace.localSourceIndex region survives targetIndex) =
      trace.domains.wires.origin
        ((ConcreteElaboration.exactScopeWires trace.diagram
          (trace.regionMap region)).get targetIndex) :=
  ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete (by
      let targetWire :=
        (ConcreteElaboration.exactScopeWires trace.diagram
          (trace.regionMap region)).get targetIndex
      have targetScope :=
        (ConcreteElaboration.mem_exactScopeWires trace.diagram
          (trace.regionMap region) targetWire).1 (List.get_mem _ _)
      let original := trace.domains.wires.origin targetWire
      have originalSurvives := trace.domains.wires.origin_survives targetWire
      have scopeTransport := trace.targetWire_scope original originalSurvives
      rw [trace.targetWire_origin_index targetWire, targetScope,
        trace.regionMap_of_survives region survives] at scopeTransport
      exact (ConcreteElaboration.mem_exactScopeWires input.val region original).2
        (trace.targetRegion_injective scopeTransport.symm))))

theorem localSourceIndex_injective
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true) :
    Function.Injective (trace.localSourceIndex region survives) := by
  intro first second equal
  have originEq : trace.domains.wires.origin
      ((ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).get first) =
      trace.domains.wires.origin
      ((ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).get second) := by
    rw [← trace.localSourceIndex_get region survives first,
      ← trace.localSourceIndex_get region survives second, equal]
  have wireEq := trace.domains.wires.origin_injective originEq
  apply Fin.ext
  exact (List.getElem_inj
    (ConcreteElaboration.exactScopeWires_nodup trace.diagram
      (trace.regionMap region))).mp wireEq

noncomputable def sourceLocalOfTarget [Nonempty D]
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true)
    (targetLocal : Fin
      (ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).length → D) :
    Fin (ConcreteElaboration.exactScopeWires input.val region).length → D :=
  fun sourceIndex =>
    if member : ∃ targetIndex,
        trace.localSourceIndex region survives targetIndex = sourceIndex
    then targetLocal (Classical.choose member)
    else Classical.choice inferInstance

@[simp] theorem sourceLocalOfTarget_image [Nonempty D]
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true)
    (targetLocal : Fin
      (ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).length → D)
    (targetIndex : Fin
      (ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).length) :
    trace.sourceLocalOfTarget targetWellFormed region survives targetLocal
        (trace.localSourceIndex region survives targetIndex) =
      targetLocal targetIndex := by
  unfold sourceLocalOfTarget
  rw [dif_pos ⟨targetIndex, rfl⟩]
  apply congrArg targetLocal
  exact trace.localSourceIndex_injective targetWellFormed region survives
    (Classical.choose_spec
      (show ∃ candidate,
        trace.localSourceIndex region survives candidate =
          trace.localSourceIndex region survives targetIndex from
        ⟨targetIndex, rfl⟩))

theorem targetEnvironment_outer
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true)
    (sourceExact : (sourceContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgreement : context.indexRelation.EnvironmentsAgree sourceOuter
      targetOuter)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input.val region).length → D)
    (targetIndex : Fin targetContext.length) :
    let extended := context.extend region survives
    extended.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal)
        (extendedOuterIndex targetContext (trace.regionMap region)
          targetIndex) = targetOuter targetIndex := by
  dsimp only
  let extended := context.extend region survives
  let sourceIndex := context.sourceIndex targetIndex
  let sourceExtendedIndex := extendedOuterIndex sourceContext region sourceIndex
  let targetExtendedIndex := extendedOuterIndex targetContext
    (trace.regionMap region) targetIndex
  have corresponding :
      (sourceContext.extend region).get sourceExtendedIndex =
        trace.domains.wires.origin
          ((targetContext.extend (trace.regionMap region)).get
            targetExtendedIndex) := by
    rw [extendedOuterIndex_get, extendedOuterIndex_get]
    exact context.sourceIndex_get targetIndex
  have sourceExtendedEq : sourceExtendedIndex =
      extended.sourceIndex targetExtendedIndex := by
    apply Fin.ext
    exact (List.getElem_inj sourceExact.nodup).mp (by
      simpa only [List.get_eq_getElem] using
        corresponding.trans (extended.sourceIndex_get _).symm)
  unfold ContextWitness.targetEnvironment
  change ConcreteElaboration.extendedEnvironment sourceContext region
      sourceOuter sourceLocal (extended.sourceIndex targetExtendedIndex) = _
  rw [← sourceExtendedEq]
  rw [extendedEnvironment_outer]
  exact outerAgreement sourceIndex targetIndex rfl

theorem targetEnvironment_local
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (region : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives region = true)
    (sourceExact : (sourceContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input.val region).length → D)
    (targetIndex : Fin
      (ConcreteElaboration.exactScopeWires trace.diagram
        (trace.regionMap region)).length) :
    let extended := context.extend region survives
    extended.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal)
        (extendedLocalIndex targetContext (trace.regionMap region)
          targetIndex) =
      sourceLocal (trace.localSourceIndex region survives targetIndex) := by
  dsimp only
  let extended := context.extend region survives
  let sourceIndex := trace.localSourceIndex region survives targetIndex
  let sourceExtendedIndex := extendedLocalIndex sourceContext region sourceIndex
  let targetExtendedIndex := extendedLocalIndex targetContext
    (trace.regionMap region) targetIndex
  have corresponding :
      (sourceContext.extend region).get sourceExtendedIndex =
        trace.domains.wires.origin
          ((targetContext.extend (trace.regionMap region)).get
            targetExtendedIndex) := by
    rw [extendedLocalIndex_get, extendedLocalIndex_get]
    exact trace.localSourceIndex_get region survives targetIndex
  have sourceExtendedEq : sourceExtendedIndex =
      extended.sourceIndex targetExtendedIndex := by
    apply Fin.ext
    exact (List.getElem_inj sourceExact.nodup).mp (by
      simpa only [List.get_eq_getElem] using
        corresponding.trans (extended.sourceIndex_get _).symm)
  unfold ContextWitness.targetEnvironment
  change ConcreteElaboration.extendedEnvironment sourceContext region
      sourceOuter sourceLocal (extended.sourceIndex targetExtendedIndex) = _
  rw [← sourceExtendedEq]
  exact extendedEnvironment_local sourceContext region sourceOuter sourceLocal
    sourceIndex

/-- Exact survivor contexts admit valuation selection in both semantic
directions. Deleted source-local wires are irrelevant to the backward index
relation and receive an arbitrary carrier value. -/
theorem regularEnvironmentSelection
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (region : Fin input.val.regionCount)
    (regular : trace.FrameRegular region)
    (sourceExact : (sourceContext.extend region).Exact region)
    [Nonempty D] :
    let extended := context.extend region regular.1
    ∀ (sourceOuter : Fin sourceContext.length → D)
      (targetOuter : Fin targetContext.length → D),
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              extended.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (trace.regionMap region) targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              extended.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (trace.regionMap region) targetOuter targetLocal) := by
  dsimp only
  let extended := context.extend region regular.1
  intro sourceOuter targetOuter outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let sourceEnvironment := ConcreteElaboration.extendedEnvironment
        sourceContext region sourceOuter sourceLocal
      let targetEnvironment := extended.targetEnvironment sourceEnvironment
      let targetLocal := localEnvironmentPart targetContext
        (trace.regionMap region) targetEnvironment
      refine ⟨targetLocal, ?_⟩
      have outerValues : ∀ index,
          targetEnvironment
              (extendedOuterIndex targetContext (trace.regionMap region)
                index) = targetOuter index := by
        intro index
        exact trace.targetEnvironment_outer sourceContext targetContext context
          region regular.1 sourceExact sourceOuter targetOuter outerAgreement
          sourceLocal index
      have environmentEq := extendedEnvironment_of_parts targetContext
        (trace.regionMap region) targetOuter targetEnvironment outerValues
      rw [environmentEq]
      exact extended.targetEnvironment_agrees sourceEnvironment
  | backward =>
      intro targetLocal
      let sourceLocal := trace.sourceLocalOfTarget targetWellFormed region
        regular.1 targetLocal
      let sourceEnvironment := ConcreteElaboration.extendedEnvironment
        sourceContext region sourceOuter sourceLocal
      let targetEnvironment := extended.targetEnvironment sourceEnvironment
      refine ⟨sourceLocal, ?_⟩
      have outerValues : ∀ index,
          targetEnvironment
              (extendedOuterIndex targetContext (trace.regionMap region)
                index) = targetOuter index := by
        intro index
        exact trace.targetEnvironment_outer sourceContext targetContext context
          region regular.1 sourceExact sourceOuter targetOuter outerAgreement
          sourceLocal index
      have localValues : localEnvironmentPart targetContext
          (trace.regionMap region) targetEnvironment = targetLocal := by
        funext index
        exact (trace.targetEnvironment_local sourceContext targetContext
          context region regular.1 sourceExact sourceOuter sourceLocal index).trans
            (trace.sourceLocalOfTarget_image targetWellFormed region regular.1
              targetLocal index)
      have environmentEq := extendedEnvironment_of_parts targetContext
        (trace.regionMap region) targetOuter targetEnvironment outerValues
      rw [localValues] at environmentEq
      rw [environmentEq]
      exact extended.targetEnvironment_agrees sourceEnvironment

end AbstractionRawTrace

end VisualProof.Rule
