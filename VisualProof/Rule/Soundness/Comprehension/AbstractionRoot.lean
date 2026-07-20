import VisualProof.Rule.Soundness.Comprehension.AbstractionSimulation
import VisualProof.Rule.Soundness.Modal.EliminationRoot

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open DoubleCutElimTrace

namespace AbstractionRawTrace

namespace ContextWitness

theorem sourceIndex_injective
    (witness : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup) :
    Function.Injective witness.sourceIndex := by
  intro first second equal
  have originEq : trace.domains.wires.origin (targetContext.get first) =
      trace.domains.wires.origin (targetContext.get second) := by
    rw [← witness.sourceIndex_get first, ← witness.sourceIndex_get second,
      equal]
  have wireEq := trace.domains.wires.origin_injective originEq
  apply Fin.ext
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using wireEq)

noncomputable def sourceEnvironment
    (witness : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (fallback : D)
    (targetEnvironment : Fin targetContext.length → D) :
    Fin sourceContext.length → D :=
  fun sourceIndex =>
    if preimage : ∃ targetIndex, witness.sourceIndex targetIndex = sourceIndex then
      targetEnvironment (Classical.choose preimage)
    else fallback

theorem sourceEnvironment_sourceIndex
    (witness : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (fallback : D)
    (targetEnvironment : Fin targetContext.length → D)
    (targetIndex : Fin targetContext.length) :
    witness.sourceEnvironment sourceNodup targetNodup fallback
        targetEnvironment (witness.sourceIndex targetIndex) =
      targetEnvironment targetIndex := by
  let preimage : ∃ candidate,
      witness.sourceIndex candidate = witness.sourceIndex targetIndex :=
    ⟨targetIndex, rfl⟩
  rw [sourceEnvironment, dif_pos preimage]
  exact congrArg targetEnvironment
    (witness.sourceIndex_injective sourceNodup targetNodup
      (Classical.choose_spec preimage))

theorem sourceEnvironment_agrees
    (witness : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (fallback : D)
    (targetEnvironment : Fin targetContext.length → D) :
    witness.indexRelation.EnvironmentsAgree
      (witness.sourceEnvironment sourceNodup targetNodup fallback
        targetEnvironment)
      targetEnvironment := by
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
    _ _ _).2
  funext targetIndex
  exact witness.sourceEnvironment_sourceIndex sourceNodup targetNodup fallback
    targetEnvironment targetIndex

end ContextWitness

/-- The ordered semantic boundary selected by a successful abstraction
interface transport. Repeated source positions remain repeated. -/
def targetBoundary
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    List (Fin trace.diagram.wireCount) :=
  List.ofFn fun position =>
    trace.targetWire (boundary.get position)
      (trace.transportedWire_survives hraw boundary mapped transport position)

@[simp] theorem targetBoundary_length
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    (trace.targetBoundary hraw boundary mapped transport).length =
      boundary.length := by
  simp [targetBoundary]

theorem targetBoundary_get
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped)
    (position : Fin (trace.targetBoundary hraw boundary mapped transport).length) :
    (trace.targetBoundary hraw boundary mapped transport).get position =
      trace.targetWire
        (boundary.get (Fin.cast
          (trace.targetBoundary_length hraw boundary mapped transport) position))
        (trace.transportedWire_survives hraw boundary mapped transport
          (Fin.cast (trace.targetBoundary_length hraw boundary mapped transport)
            position)) := by
  simp [targetBoundary]

def sourceOpen
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram := {
  diagram := input.val
  boundary := boundary
}

def targetOpen
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    OpenConcreteDiagram := {
  diagram := trace.diagram
  boundary := trace.targetBoundary hraw boundary mapped transport
}

theorem targetBoundary_root_scoped
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    ∀ wire, wire ∈ trace.targetBoundary hraw boundary mapped transport →
      (trace.diagram.wires wire).scope = trace.diagram.root := by
  intro wire member
  obtain ⟨position, positionEq⟩ := List.mem_iff_get.mp member
  subst wire
  let sourcePosition : Fin boundary.length := Fin.cast
    (trace.targetBoundary_length hraw boundary mapped transport) position
  rw [trace.targetBoundary_get hraw boundary mapped transport position,
    trace.targetWire_scope]
  have rootScope := sourceRoot (boundary.get sourcePosition)
    (List.get_mem boundary sourcePosition)
  calc
    trace.targetRegion (input.val.wires (boundary.get sourcePosition)).scope _ =
        trace.targetRegion input.val.root trace.root_survives := by
      congr 1
    _ = trace.diagram.root := trace.targetRegion_root

theorem sourceOpen_wellFormed
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    (trace.sourceOpen boundary).WellFormed signature :=
  by
    unfold sourceOpen
    constructor
    · change input.val.WellFormed signature
      exact input.property
    · change ∀ wire, wire ∈ boundary →
        (input.val.wires wire).scope = input.val.root
      exact sourceRoot

theorem targetOpen_wellFormed
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    (trace.targetOpen hraw boundary mapped transport).WellFormed signature :=
  ⟨targetWellFormed,
    trace.targetBoundary_root_scoped payload hraw boundary sourceRoot mapped
      transport⟩

/-- The exposed target classes have exactly the exposed source classes that
survive the certified ordered interface transport as their origins. -/
def rootOuterContextWitness
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    ContextWitness trace
      (trace.sourceOpen boundary).exposedWires
      (trace.targetOpen hraw boundary mapped transport).exposedWires where
  origin_mem := by
    intro targetWire targetMember
    have boundaryMember : targetWire ∈
        trace.targetBoundary hraw boundary mapped transport :=
      by
        simpa only [targetOpen] using
          (OpenConcreteDiagram.mem_exposedWires
            (trace.targetOpen hraw boundary mapped transport) targetWire).1
              targetMember
    obtain ⟨position, positionEq⟩ := List.mem_iff_get.mp boundaryMember
    have targetEq := trace.targetBoundary_get hraw boundary mapped transport
      position
    rw [positionEq] at targetEq
    let sourcePosition : Fin boundary.length := Fin.cast
      (trace.targetBoundary_length hraw boundary mapped transport) position
    have originEq : trace.domains.wires.origin targetWire =
        boundary.get sourcePosition := by
      rw [targetEq]
      exact trace.targetWire_origin _ _
    apply (OpenConcreteDiagram.mem_exposedWires _ _).2
    rw [originEq]
    exact List.get_mem boundary sourcePosition

theorem rootOuterContextWitness_sourceIndex_surjective
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    Function.Surjective
      (trace.rootOuterContextWitness hraw boundary mapped transport).sourceIndex := by
  let source := trace.sourceOpen boundary
  let target := trace.targetOpen hraw boundary mapped transport
  let outer := trace.rootOuterContextWitness hraw boundary mapped transport
  intro sourceIndex
  have sourceBoundaryMember : source.exposedWires.get sourceIndex ∈ boundary :=
    (OpenConcreteDiagram.mem_exposedWires source _).1
      (List.get_mem source.exposedWires sourceIndex)
  obtain ⟨sourcePosition, sourcePositionEq⟩ :=
    List.mem_iff_get.mp sourceBoundaryMember
  let targetPosition : Fin
      (trace.targetBoundary hraw boundary mapped transport).length :=
    Fin.cast (trace.targetBoundary_length hraw boundary mapped transport).symm
      sourcePosition
  let targetWire :=
    (trace.targetBoundary hraw boundary mapped transport).get targetPosition
  have targetExposed : targetWire ∈ target.exposedWires := by
    apply (OpenConcreteDiagram.mem_exposedWires target targetWire).2
    exact List.get_mem _ targetPosition
  obtain ⟨targetIndex, targetLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete targetExposed
  refine ⟨targetIndex, ?_⟩
  symm
  apply ConcreteElaboration.WireContext.lookup?_unique source.exposedWires_nodup
    (outer.sourceIndex_lookup targetIndex)
  have targetGet : target.exposedWires.get targetIndex = targetWire :=
    ConcreteElaboration.WireContext.lookup?_sound targetLookup
  change source.exposedWires.get sourceIndex =
    trace.domains.wires.origin (target.exposedWires.get targetIndex)
  rw [targetGet]
  have targetBoundaryGet := trace.targetBoundary_get hraw boundary mapped
    transport targetPosition
  have sourcePositionCast : Fin.cast
      (trace.targetBoundary_length hraw boundary mapped transport)
        targetPosition = sourcePosition := by
    apply Fin.ext
    rfl
  dsimp only [targetWire]
  rw [targetBoundaryGet]
  calc
    source.exposedWires.get sourceIndex = boundary.get sourcePosition :=
      sourcePositionEq.symm
    _ = boundary.get (Fin.cast
        (trace.targetBoundary_length hraw boundary mapped transport)
          targetPosition) := congrArg boundary.get sourcePositionCast.symm
    _ = trace.domains.wires.origin
        (trace.targetWire (boundary.get (Fin.cast
          (trace.targetBoundary_length hraw boundary mapped transport)
            targetPosition)) _) :=
      (trace.targetWire_origin _ _).symm

/-- The complete root contexts are related by survivor origin. Deleted source
root wires may remain hidden on the source side, while every target root wire
has one unique source origin. -/
def rootContextWitness
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    ContextWitness trace
      (trace.sourceOpen boundary).rootWires
      (trace.targetOpen hraw boundary mapped transport).rootWires where
  origin_mem := by
    intro targetWire targetMember
    let source := trace.sourceOpen boundary
    let target := trace.targetOpen hraw boundary mapped transport
    have targetOpenWellFormed := trace.targetOpen_wellFormed payload
      targetWellFormed hraw boundary sourceRoot mapped transport
    have targetScope : (trace.diagram.wires targetWire).scope =
        trace.diagram.root :=
      (OpenConcreteDiagram.mem_rootWires_iff target targetOpenWellFormed
        targetWire).1 targetMember
    let original := trace.domains.wires.origin targetWire
    have originalSurvives := trace.domains.wires.origin_survives targetWire
    have scopeTransport := trace.targetWire_scope original originalSurvives
    rw [trace.targetWire_origin_index targetWire, targetScope] at scopeTransport
    have originalRoot : (input.val.wires original).scope = input.val.root := by
      apply trace.targetRegion_injective
        (rightSurvives := trace.root_survives)
      simpa only [trace.targetRegion_root] using scopeTransport.symm
    apply (OpenConcreteDiagram.mem_rootWires_iff source
      (trace.sourceOpen_wellFormed boundary sourceRoot) original).2
    exact originalRoot

/-- Select complete root valuations while preserving the ordered exposed
classes. Source-only hidden wires receive an arbitrary value only in the
backward direction. -/
theorem rootEnvironmentSelection
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped)
    (direction : ConcreteElaboration.SimulationDirection)
    [Nonempty D] :
    let source : CheckedOpenDiagram signature :=
      ⟨trace.sourceOpen boundary,
        trace.sourceOpen_wellFormed boundary sourceRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨trace.targetOpen hraw boundary mapped transport,
        trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
          sourceRoot mapped transport⟩
    let outer := trace.rootOuterContextWitness hraw boundary mapped transport
    let combined := trace.rootContextWitness payload targetWellFormed hraw
      boundary sourceRoot mapped transport
    ∀ (sourceOuter : Fin source.val.exposedWires.length → D)
      (targetOuter : Fin target.val.exposedWires.length → D),
      outer.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              combined.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.rootEnvironment source.val.exposedWires
                  source.val.hiddenWires sourceOuter sourceLocal)
                (ConcreteElaboration.rootEnvironment target.val.exposedWires
                  target.val.hiddenWires targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              combined.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.rootEnvironment source.val.exposedWires
                  source.val.hiddenWires sourceOuter sourceLocal)
                (ConcreteElaboration.rootEnvironment target.val.exposedWires
                  target.val.hiddenWires targetOuter targetLocal) := by
  dsimp only
  let source : CheckedOpenDiagram signature :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed boundary sourceRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨trace.targetOpen hraw boundary mapped transport,
      trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
        sourceRoot mapped transport⟩
  let outer := trace.rootOuterContextWitness hraw boundary mapped transport
  let combined := trace.rootContextWitness payload targetWellFormed hraw
    boundary sourceRoot mapped transport
  have sourceRootExact : ConcreteElaboration.WireContext.Exact
      source.val.rootWires source.val.diagram.root :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      source
  have targetRootExact : ConcreteElaboration.WireContext.Exact
      target.val.rootWires target.val.diagram.root :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      target
  have outerGet (targetIndex : Fin target.val.exposedWires.length) :
      combined.sourceIndex
          (rootOuterIndex target.val.exposedWires target.val.hiddenWires
            targetIndex) =
        rootOuterIndex source.val.exposedWires source.val.hiddenWires
          (outer.sourceIndex targetIndex) := by
    symm
    apply ConcreteElaboration.WireContext.lookup?_unique sourceRootExact.nodup
      (combined.sourceIndex_lookup
        (rootOuterIndex target.val.exposedWires target.val.hiddenWires
          targetIndex))
    calc
      source.val.rootWires.get
          (rootOuterIndex source.val.exposedWires source.val.hiddenWires
            (outer.sourceIndex targetIndex)) =
          source.val.exposedWires.get (outer.sourceIndex targetIndex) :=
        rootOuterIndex_get _ _ _
      _ = trace.domains.wires.origin
          (target.val.exposedWires.get targetIndex) :=
        outer.sourceIndex_get targetIndex
      _ = trace.domains.wires.origin
          (target.val.rootWires.get
            (rootOuterIndex target.val.exposedWires target.val.hiddenWires
              targetIndex)) := congrArg trace.domains.wires.origin
        (rootOuterIndex_get _ _ _).symm
  intro sourceOuter targetOuter outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let sourceEnvironment := ConcreteElaboration.rootEnvironment
        source.val.exposedWires source.val.hiddenWires sourceOuter sourceLocal
      let targetEnvironment := combined.targetEnvironment sourceEnvironment
      let targetLocal := rootLocalPart target.val.exposedWires
        target.val.hiddenWires targetEnvironment
      refine ⟨targetLocal, ?_⟩
      have targetEnvironmentEq :
          ConcreteElaboration.rootEnvironment target.val.exposedWires
              target.val.hiddenWires targetOuter targetLocal =
            targetEnvironment := by
        apply rootEnvironment_of_parts
        intro targetIndex
        change sourceEnvironment
            (combined.sourceIndex
              (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                targetIndex)) = targetOuter targetIndex
        rw [outerGet targetIndex]
        dsimp only [sourceEnvironment]
        rw [rootEnvironment_outer]
        exact outerAgreement (outer.sourceIndex targetIndex) targetIndex rfl
      rw [targetEnvironmentEq]
      exact combined.targetEnvironment_agrees sourceEnvironment
  | backward =>
      intro targetLocal
      let targetEnvironment := ConcreteElaboration.rootEnvironment
        target.val.exposedWires target.val.hiddenWires targetOuter targetLocal
      let fallback : D := Classical.choice inferInstance
      let sourceEnvironment := combined.sourceEnvironment sourceRootExact.nodup
        targetRootExact.nodup fallback targetEnvironment
      let sourceLocal := rootLocalPart source.val.exposedWires
        source.val.hiddenWires sourceEnvironment
      refine ⟨sourceLocal, ?_⟩
      have sourceEnvironmentEq :
          ConcreteElaboration.rootEnvironment source.val.exposedWires
              source.val.hiddenWires sourceOuter sourceLocal =
            sourceEnvironment := by
        apply rootEnvironment_of_parts
        intro sourceIndex
        obtain ⟨targetIndex, targetIndexEq⟩ :=
          trace.rootOuterContextWitness_sourceIndex_surjective hraw boundary
            mapped transport sourceIndex
        have combinedIndex : combined.sourceIndex
              (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                targetIndex) =
            rootOuterIndex source.val.exposedWires source.val.hiddenWires
              sourceIndex := by
          rw [outerGet targetIndex, targetIndexEq]
        change sourceEnvironment
            (rootOuterIndex source.val.exposedWires source.val.hiddenWires
              sourceIndex) = sourceOuter sourceIndex
        rw [← combinedIndex]
        calc
          sourceEnvironment
              (combined.sourceIndex
                (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                  targetIndex)) =
              targetEnvironment
                (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                  targetIndex) :=
            combined.sourceEnvironment_sourceIndex sourceRootExact.nodup
              targetRootExact.nodup fallback targetEnvironment _
          _ = targetOuter targetIndex := rootEnvironment_outer _ _ _ _ _
          _ = sourceOuter (outer.sourceIndex targetIndex) :=
            (outerAgreement (outer.sourceIndex targetIndex) targetIndex rfl).symm
          _ = sourceOuter sourceIndex := congrArg sourceOuter targetIndexEq
      rw [sourceEnvironmentEq]
      exact combined.sourceEnvironment_agrees sourceRootExact.nodup
        targetRootExact.nodup fallback targetEnvironment

noncomputable def rootContextSimulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    let source : CheckedOpenDiagram signature :=
      ⟨trace.sourceOpen boundary,
        trace.sourceOpen_wellFormed boundary sourceRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨trace.targetOpen hraw boundary mapped transport,
        trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
          sourceRoot mapped transport⟩
    let simulation := trace.semanticSimulation payload targetWellFormed model named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires := by
  let source : CheckedOpenDiagram signature :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed boundary sourceRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨trace.targetOpen hraw boundary mapped transport,
      trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
        sourceRoot mapped transport⟩
  let simulation := trace.semanticSimulation payload targetWellFormed model named
  let outer := trace.rootOuterContextWitness hraw boundary mapped transport
  let combined := trace.rootContextWitness payload targetWellFormed hraw
    boundary sourceRoot mapped transport
  have sourceRootExact : ConcreteElaboration.WireContext.Exact
      source.val.rootWires source.val.diagram.root :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      source
  have targetRootExact : ConcreteElaboration.WireContext.Exact
      target.val.rootWires target.val.diagram.root :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      target
  refine {
    outer := outer.indexRelation
    context := PLift.up combined
    atRoot := trace.outerReachable_root payload
    atRootChild := ?_
    atFocusedRootChild := ?_
    transport := ?_
    focusedRootKernel := ?_
  }
  · intro regular child childParent
    exact trace.outerReachable_child_of_regular payload input.val.root child
      (trace.outerReachable_root payload) (Classical.not_not.mp regular)
      childParent
  · intro focused child childParent targetParent
    have rootFocus : input.val.root = wrap.val.anchor :=
      trace.outerReachable_focused_eq payload input.val.root
        (trace.outerReachable_root payload) focused
    change trace.OuterReachable child
    have childParent' : (input.val.regions child).parent? =
        some wrap.val.anchor := by
      simpa only [rootFocus] using childParent
    have targetParent' :
        (trace.diagram.regions (trace.regionMap child)).parent? =
          some (trace.regionMap wrap.val.anchor) := by
      simpa only [rootFocus] using targetParent
    have childSurvives := trace.reachable_child_of_focus targetWellFormed
      wrap.val.anchor child (wrap_anchor_survives payload) targetParent'
    refine ⟨childSurvives, ?_⟩
    by_cases childEq : child = wrap.val.anchor
    · exact Or.inl childEq
    · apply Or.inr
      intro selected
      have targetDirect : child ∉ wrap.val.childRoots := by
        rw [trace.regionMap_of_survives child childSurvives,
          trace.regionMap_of_survives wrap.val.anchor
            (wrap_anchor_survives payload)] at targetParent'
        exact ((trace.targetRegion_parent_wrap_iff child childSurvives
          (wrap_anchor_survives payload)).1 targetParent').2
      obtain ⟨root, rootMember, encloses⟩ :=
        (wrap.mem_selectedRegions child).1 selected
      have rootEq : root = child := by
        have rootParent := wrap.property.childRoots_direct root rootMember
        rcases ConcreteElaboration.encloses_direct_child childParent' encloses with
          equal | enclosesParent
        · exact equal
        · exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property rootParent enclosesParent)
      exact targetDirect (rootEq ▸ rootMember)
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    apply ConcreteElaboration.directionalRootTransport_of_agreement direction
      source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outer.indexRelation
      combined.indexRelation model named
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems
    · exact trace.rootEnvironmentSelection payload targetWellFormed hraw boundary
        sourceRoot mapped transport direction
    · exact itemSemantics
  · sorry

end AbstractionRawTrace

end VisualProof.Rule
