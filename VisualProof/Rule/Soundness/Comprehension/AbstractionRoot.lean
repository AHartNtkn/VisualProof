import VisualProof.Rule.Soundness.Comprehension.AbstractionSimulation
import VisualProof.Rule.Soundness.Modal.EliminationRoot

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open DoubleCutElimTrace

namespace AbstractionRawTrace

def concreteIsoOfEq {first second : ConcreteDiagram}
    (diagramEq : first = second) : ConcreteIso first second := by
  subst second
  exact ConcreteIso.refl first

theorem concreteIsoOfEq_wires_val
    {first second : ConcreteDiagram}
    (diagramEq : first = second)
    (wire : Fin first.wireCount) :
    ((concreteIsoOfEq diagramEq).wires wire).val = wire.val := by
  subst second
  rfl

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
  ·
    intro atRoot focused allowedRoot recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    have rootFocus : input.val.root = wrap.val.anchor :=
      trace.outerReachable_focused_eq payload input.val.root atRoot focused
    rw [rootFocus] at allowedRoot
    have directionEq := abstractionAllowed_focus_forward input.val
      wrap.val.anchor direction allowedRoot
    subst direction
    have allowed : AbstractionAllowed input.val wrap.val.anchor .forward
        wrap.val.anchor := allowedRoot
    let fuelSource := input.val.regionCount
    let fuelTarget := trace.diagram.regionCount
    let sourceRels : RelCtx := []
    let targetRels : RelCtx := []
    let sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels :=
      ConcreteElaboration.BinderContext.empty
    let targetBinders :
        ConcreteElaboration.BinderContext trace.diagram targetRels :=
      ConcreteElaboration.BinderContext.empty
    let binderWitness : BinderWitness trace sourceBinders targetBinders :=
      BinderWitness.empty trace
    let sourceExtended : ConcreteElaboration.WireContext input.val :=
      source.val.rootWires
    let targetExtended : ConcreteElaboration.WireContext trace.diagram :=
      target.val.rootWires
    have targetAtFocus :
        trace.regionMap wrap.val.anchor = trace.diagram.root := by
      rw [← rootFocus, trace.regionMap_root]
    have sourceExact : ConcreteElaboration.WireContext.Exact sourceExtended
        wrap.val.anchor := by
      simpa only [sourceExtended, source, sourceOpen, rootFocus] using
        sourceRootExact
    have targetExact : ConcreteElaboration.WireContext.Exact targetExtended
        (trace.regionMap wrap.val.anchor) := by
      simpa only [targetExtended, target, targetAtFocus] using targetRootExact
    have sourceBindersCover : sourceBinders.Covers wrap.val.anchor := by
      simpa only [sourceBinders, sourceRels, rootFocus] using
        ConcreteElaboration.BinderContext.empty_covers_root input.property
    have targetBindersCover :
        targetBinders.Covers (trace.regionMap wrap.val.anchor) := by
      simpa only [targetBinders, targetRels, targetAtFocus] using
        ConcreteElaboration.BinderContext.empty_covers_root targetWellFormed
    have sourceEnumeration :
        ConcreteElaboration.BinderContext.Enumeration input.val sourceBinders
          wrap.val.anchor := by
      simpa only [sourceBinders, sourceRels, rootFocus] using
        ConcreteElaboration.BinderContext.Enumeration.empty input.val
    have targetEnumerationRoot :=
      ConcreteElaboration.BinderContext.Enumeration.empty trace.diagram
    have targetEnumeration :
        ConcreteElaboration.BinderContext.Enumeration trace.diagram
          targetBinders (trace.regionMap wrap.val.anchor) := by
      simpa only [targetBinders, targetRels, targetAtFocus] using
        targetEnumerationRoot
    have sourceCompiledFocused :
        ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuelSource)
          sourceExtended sourceBinders
          (ConcreteElaboration.localOccurrences input.val wrap.val.anchor) =
            some sourceItems := by
      simpa only [fuelSource, sourceExtended, sourceBinders, sourceRels,
        source, rootFocus] using sourceCompiled
    have targetCompiledFocused :
        ConcreteElaboration.compileOccurrencesWith? signature trace.diagram
          (ConcreteElaboration.compileRegion? signature trace.diagram fuelTarget)
          targetExtended targetBinders
          (ConcreteElaboration.localOccurrences trace.diagram
            (trace.regionMap wrap.val.anchor)) = some targetItems := by
      simpa only [fuelTarget, targetExtended, targetBinders, targetRels,
        target, OpenConcreteDiagram.rootWires, ← rootFocus] using targetCompiled
    let sourceRecurse : ∀ {rels : RelCtx},
        (region : Fin input.val.regionCount) →
        (context : ConcreteElaboration.WireContext input.val) →
        ConcreteElaboration.BinderContext input.val rels →
        Option (Region signature context.length rels) :=
      fun {rels} => ConcreteElaboration.compileRegion? signature input.val
        fuelSource
    let targetRecurse : ∀ {rels : RelCtx},
        (region : Fin trace.diagram.regionCount) →
        (context : ConcreteElaboration.WireContext trace.diagram) →
        ConcreteElaboration.BinderContext trace.diagram rels →
        Option (Region signature context.length rels) :=
      fun {rels} => ConcreteElaboration.compileRegion? signature trace.diagram
        fuelTarget
    have sourcePartition := ModalSoundness.anchorOccurrences_perm_partition
      input.val wrap
    obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
        sourceExtended sourceBinders
        (ModalSoundness.keptOccurrences input.val wrap ++
          ModalSoundness.selectedOccurrences input.val wrap) (by
            intro occurrence member
            exact ModalSoundness.compileOccurrence_success_of_mem input.val
              sourceRecurse sourceExtended sourceBinders sourceCompiledFocused
              ((sourcePartition.mem_iff).1 member))
    obtain ⟨sourceKeptItems, sourceSelectedItems, sourceKeptCompiled,
        sourceSelectedCompiled, sourcePartitionEq⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_append_split sourceRecurse
        sourceExtended sourceBinders
        (ModalSoundness.keptOccurrences input.val wrap)
        (ModalSoundness.selectedOccurrences input.val wrap)
        sourcePartitionItems sourcePartitionCompiled
    have targetPartition :
        (ConcreteElaboration.localOccurrences trace.diagram
            (trace.regionMap wrap.val.anchor)).Perm
          ((ModalSoundness.keptOccurrences input.val wrap).map
              trace.survivorOccurrence ++
            [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
              ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                trace.diagram.nodeCount)]) := by
      rw [trace.regionMap_of_survives wrap.val.anchor
        (wrap_anchor_survives payload)]
      simpa [trace.kept_filterMap_eq_map payload] using
        trace.wrapAnchorLocalOccurrences payload
    obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_complete targetRecurse
        targetExtended targetBinders
        ((ModalSoundness.keptOccurrences input.val wrap).map
            trace.survivorOccurrence ++
          [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
            ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
              trace.diagram.nodeCount)]) (by
            intro occurrence member
            exact ModalSoundness.compileOccurrence_success_of_mem trace.diagram
              targetRecurse targetExtended targetBinders targetCompiledFocused
              ((targetPartition.mem_iff).2 member))
    obtain ⟨targetKeptItems, targetBubbleItems, targetKeptCompiled,
        targetBubbleCompiled, targetPartitionEq⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_append_split targetRecurse
        targetExtended targetBinders
        ((ModalSoundness.keptOccurrences input.val wrap).map
          trace.survivorOccurrence)
        [ConcreteElaboration.LocalOccurrence.child trace.bubble]
        targetPartitionItems targetPartitionCompiled
    simp only [ConcreteElaboration.compileOccurrencesWith?]
      at targetBubbleCompiled
    dsimp only [targetRecurse] at targetBubbleCompiled
    simp only [ConcreteElaboration.compileOccurrenceWith?, trace.diagram_bubble]
      at targetBubbleCompiled
    let targetPushed := targetBinders.push trace.bubble
      comprehension.val.boundary.length
    cases bubbleResult : ConcreteElaboration.compileRegion? signature
        trace.diagram fuelTarget trace.bubble targetExtended targetPushed with
    | none => simp [targetPushed, bubbleResult] at targetBubbleCompiled
    | some bubbleBody =>
        simp [targetPushed, bubbleResult] at targetBubbleCompiled
        subst targetBubbleItems
        cases fuelTargetEq : fuelTarget with
        | zero =>
            simp [fuelTargetEq, ConcreteElaboration.compileRegion?]
              at bubbleResult
        | succ bubbleFuel =>
            simp only [fuelTargetEq, ConcreteElaboration.compileRegion?]
              at bubbleResult
            obtain ⟨bubbleItems, bubbleItemsCompiled, bubbleBodyEq⟩ :=
              Option.bind_eq_some_iff.mp bubbleResult
            have bubbleBodyEq' :
                ConcreteElaboration.finishRegion trace.diagram targetExtended
                  trace.bubble bubbleItems = bubbleBody :=
              Option.some.inj bubbleBodyEq
            subst bubbleBody
            let focusedContext := combined
            have keptPointwise : ∀ occurrence,
                occurrence ∈ ModalSoundness.keptOccurrences input.val wrap →
                ∀ sourceItem targetItem,
                ConcreteElaboration.compileOccurrenceWith? signature input.val
                    sourceRecurse sourceExtended sourceBinders occurrence =
                      some sourceItem →
                ConcreteElaboration.compileOccurrenceWith? signature
                    trace.diagram targetRecurse targetExtended targetBinders
                    (trace.survivorOccurrence occurrence) = some targetItem →
                ConcreteElaboration.ItemSimulation model named .forward
                  focusedContext.indexRelation
                  (sourceItem.renameRelations binderWitness.relationMap)
                  targetItem := by
              intro occurrence member sourceItem targetItem sourceOccurrence
                targetOccurrence
              exact trace.focusedKeptOccurrence_itemSimulation payload
                targetWellFormed model named .forward fuelSource
                (bubbleFuel + 1) sourceExtended targetExtended focusedContext
                sourceBinders targetBinders binderWitness sourceExact targetExact
                sourceBindersCover targetBindersCover sourceEnumeration
                targetEnumeration allowed
                (fun childFuelTarget childSourceContext childTargetContext
                    childContext => recurseAt childFuelTarget childSourceContext
                      childTargetContext (PLift.up childContext)) occurrence member
                sourceItem targetItem (by
                  simpa [sourceRecurse] using sourceOccurrence)
                (by simpa [targetRecurse, fuelTargetEq] using targetOccurrence)
            have keptSimulation :=
              ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                model named .forward sourceRecurse targetRecurse sourceExtended
                targetExtended sourceBinders targetBinders
                focusedContext.indexRelation binderWitness.relationMap
                trace.survivorOccurrence
                (ModalSoundness.keptOccurrences input.val wrap) keptPointwise
                sourceKeptItems targetKeptItems sourceKeptCompiled
                targetKeptCompiled
            let selectedSurvivors := trace.survivingSources
              (ModalSoundness.selectedOccurrences input.val wrap)
            let selectedAtWrap := selectedAt input occurrences wrap.val.anchor
            let targetSelectedSurvivors :=
              selectedSurvivors.map trace.survivorOccurrence
            let indices := anchorIndices occurrences wrap.val.anchor
            let targetAtoms : List (ConcreteElaboration.LocalOccurrence
                trace.diagram.regionCount trace.diagram.nodeCount) :=
              indices.map fun index =>
                ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index)
            have sourceSelectedPartition :
                (selectedSurvivors ++ selectedAtWrap).Perm
                  (ModalSoundness.selectedOccurrences input.val wrap) := by
              simpa [selectedSurvivors, selectedAtWrap] using
                trace.selectedOccurrences_perm_focusedPartition payload
            have targetBubblePartition :
                (ConcreteElaboration.localOccurrences trace.diagram
                    trace.bubble).Perm
                  (targetSelectedSurvivors ++ targetAtoms) := by
              simpa [targetSelectedSurvivors, selectedSurvivors, targetAtoms,
                indices, atomsAt, anchorIndices,
                trace.survivingSources_map_survivor] using
                  trace.bubbleLocalOccurrences payload
            let bubbleContext := targetExtended.extend trace.bubble
            obtain ⟨sourceSelectedPartitionItems,
                sourceSelectedPartitionCompiled⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
                sourceExtended sourceBinders
                (selectedSurvivors ++ selectedAtWrap) (by
                  intro occurrence member
                  exact ModalSoundness.compileOccurrence_success_of_mem input.val
                    sourceRecurse sourceExtended sourceBinders
                    sourceSelectedCompiled
                    ((sourceSelectedPartition.mem_iff).1 member))
            obtain ⟨sourceSurvivorItems, sourceFamilyAggregateItems,
                sourceSurvivorCompiled, sourceFamilyAggregateCompiled,
                sourceSelectedPartitionEq⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_append_split
                sourceRecurse sourceExtended sourceBinders selectedSurvivors
                selectedAtWrap sourceSelectedPartitionItems
                sourceSelectedPartitionCompiled
            let bubbleRecurse : ∀ {rels : RelCtx},
                (region : Fin trace.diagram.regionCount) →
                (context : ConcreteElaboration.WireContext trace.diagram) →
                ConcreteElaboration.BinderContext trace.diagram rels →
                Option (Region signature context.length rels) :=
              fun {rels} => ConcreteElaboration.compileRegion? signature
                trace.diagram bubbleFuel
            obtain ⟨targetBubblePartitionItems,
                targetBubblePartitionCompiled⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_complete bubbleRecurse
                bubbleContext targetPushed
                (targetSelectedSurvivors ++ targetAtoms) (by
                  intro occurrence member
                  exact ModalSoundness.compileOccurrence_success_of_mem
                    trace.diagram bubbleRecurse bubbleContext targetPushed
                    bubbleItemsCompiled
                    ((targetBubblePartition.mem_iff).2 member))
            obtain ⟨targetSurvivorItems, targetAtomItems,
                targetSurvivorCompiled, targetAtomCompiled,
                targetBubblePartitionEq⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_append_split
                bubbleRecurse bubbleContext targetPushed
                targetSelectedSurvivors targetAtoms
                targetBubblePartitionItems targetBubblePartitionCompiled
            have sourceBlockExists : ∀ index, index ∈ indices →
                ∃ items : ItemSeq signature sourceExtended.length sourceRels,
                  ConcreteElaboration.compileOccurrencesWith? signature
                    input.val sourceRecurse sourceExtended sourceBinders
                    (ModalSoundness.selectedOccurrences input.val
                      (occurrences.get index).selection) = some items := by
              intro index indexMember
              apply ConcreteElaboration.compileOccurrencesWith?_complete
              intro occurrence occurrenceMember
              apply ModalSoundness.compileOccurrence_success_of_mem input.val
                sourceRecurse sourceExtended sourceBinders
                sourceFamilyAggregateCompiled
              exact (mem_selectedAt input occurrences wrap.val.anchor
                occurrence).2 ⟨index,
                  (mem_anchorIndices occurrences wrap.val.anchor index).1
                    indexMember,
                  occurrenceMember⟩
            let sourceFamilyItems : Fin occurrences.length →
                ItemSeq signature sourceExtended.length sourceRels :=
              fun index => if member : index ∈ indices then
                Classical.choose (sourceBlockExists index member)
              else .nil
            have sourceFamilyCompiled : ∀ index, index ∈ indices →
                ConcreteElaboration.compileOccurrencesWith? signature
                  input.val sourceRecurse sourceExtended sourceBinders
                  (ModalSoundness.selectedOccurrences input.val
                    (occurrences.get index).selection) =
                      some (sourceFamilyItems index) := by
              intro index member
              dsimp only [sourceFamilyItems]
              rw [dif_pos member]
              exact Classical.choose_spec (sourceBlockExists index member)
            have sourceFamilyCompiler := compileOccurrenceFamilyItems
              sourceRecurse sourceExtended sourceBinders indices
              (fun index => ModalSoundness.selectedOccurrences input.val
                (occurrences.get index).selection)
              sourceFamilyItems sourceFamilyCompiled
            have sourceFamilyEq :
                occurrenceFamilyItems sourceFamilyItems indices =
                  sourceFamilyAggregateItems := by
              apply Option.some.inj
              exact sourceFamilyCompiler.symm.trans (by
                simpa [selectedAtWrap, selectedAt, indices] using
                  sourceFamilyAggregateCompiled)
            have targetAtomExists : ∀ index, index ∈ indices →
                ∃ item : Item signature bubbleContext.length
                    (comprehension.val.boundary.length :: targetRels),
                  ConcreteElaboration.compileNode? signature trace.diagram
                    bubbleContext targetPushed (trace.targetAtom index) =
                      some item := by
              intro index indexMember
              obtain ⟨item, compiled⟩ :=
                ModalSoundness.compileOccurrence_success_of_mem trace.diagram
                  bubbleRecurse bubbleContext targetPushed targetAtomCompiled
                  (List.mem_map.mpr ⟨index, indexMember, rfl⟩)
              exact ⟨item, by
                simpa [ConcreteElaboration.compileOccurrenceWith?] using
                  compiled⟩
            let targetFamilyItems : Fin occurrences.length →
                Item signature bubbleContext.length
                  (comprehension.val.boundary.length :: targetRels) :=
              fun index => if member : index ∈ indices then
                Classical.choose (targetAtomExists index member)
              else .cut (.mk 0 .nil)
            have targetFamilyCompiled : ∀ index, index ∈ indices →
                ConcreteElaboration.compileNode? signature trace.diagram
                  bubbleContext targetPushed (trace.targetAtom index) =
                    some (targetFamilyItems index) := by
              intro index member
              dsimp only [targetFamilyItems]
              rw [dif_pos member]
              exact Classical.choose_spec (targetAtomExists index member)
            have targetFamilyCompiler := compileOccurrenceFamilyAtomItems
              bubbleRecurse bubbleContext targetPushed indices
              (fun index => ConcreteElaboration.LocalOccurrence.node
                (trace.targetAtom index)) targetFamilyItems (by
                  intro index member
                  simpa [ConcreteElaboration.compileOccurrenceWith?] using
                    targetFamilyCompiled index member)
            have targetFamilyEq :
                occurrenceFamilyAtomItems targetFamilyItems indices =
                  targetAtomItems := by
              apply Option.some.inj
              exact targetFamilyCompiler.symm.trans (by
                simpa [targetAtoms] using targetAtomCompiled)
            have sourceSelectedCanonicalCompiled :
                ConcreteElaboration.compileOccurrencesWith? signature input.val
                  sourceRecurse sourceExtended sourceBinders
                  (selectedSurvivors ++ selectedAtWrap) =
                    some (sourceSurvivorItems.append
                      sourceFamilyAggregateItems) := by
              rw [← sourceSelectedPartitionEq]
              exact sourceSelectedPartitionCompiled
            have targetBubbleCanonicalCompiled :
                ConcreteElaboration.compileOccurrencesWith? signature
                  trace.diagram bubbleRecurse bubbleContext targetPushed
                  (targetSelectedSurvivors ++ targetAtoms) =
                    some (targetSurvivorItems.append targetAtomItems) := by
              rw [← targetBubblePartitionEq]
              exact targetBubblePartitionCompiled
            have sourceSelectedCanonicalNodup :
                (selectedSurvivors ++ selectedAtWrap).Nodup :=
              (sourceSelectedPartition.nodup_iff).2
                (selectedOccurrences_nodup input wrap)
            have targetBubbleCanonicalNodup :
                (targetSelectedSurvivors ++ targetAtoms).Nodup :=
              (targetBubblePartition.nodup_iff).1
                (ConcreteElaboration.localOccurrences_nodup trace.diagram
                  trace.bubble)
            have selectedSurvivorMembers : ∀ occurrence,
                occurrence ∈ selectedSurvivors → occurrence ∈
                  ModalSoundness.selectedOccurrences input.val wrap := by
              intro occurrence member
              exact (mem_survivingSources trace
                (ModalSoundness.selectedOccurrences input.val wrap)
                occurrence).1 member |>.1
            have selectedSurvivorMaps : ∀ occurrence,
                occurrence ∈ selectedSurvivors →
                  ∃ target,
                    trace.survivingOccurrence? occurrence = some target := by
              intro occurrence member
              exact Option.isSome_iff_exists.mp
                ((mem_survivingSources trace
                  (ModalSoundness.selectedOccurrences input.val wrap)
                  occurrence).1 member |>.2)
            have fixedRecurseAt : ∀
                (childDirection : ConcreteElaboration.SimulationDirection)
                (child : Fin input.val.regionCount),
                child ∈ wrap.selectedRegions →
                trace.domains.regions.survives child = true →
                child ≠ wrap.val.anchor →
                AbstractionAllowed input.val wrap.val.anchor childDirection
                    child →
                  FixedRegionSimulation trace model named childDirection
                    fuelSource bubbleFuel child := by
              intro childDirection child childSelected childSurvives
                childNotWrap childAllowed
              exact trace.fixedRegionSimulation payload targetWellFormed model
                named childDirection fuelSource bubbleFuel child childSurvives
                childNotWrap childSelected childAllowed
            have bubbleContextEq : bubbleContext = targetExtended := by
              exact trace.extend_bubble_eq targetExtended
            subst bubbleContext
            have selectedContext : ContextWitness trace sourceExtended
                (targetExtended.extend trace.bubble) :=
              focusedContext.castTarget (trace.extend_bubble_eq targetExtended)
            have selectedTargetExact :
                (targetExtended.extend trace.bubble).Exact
                  (trace.regionMap wrap.val.anchor) := by
              rw [trace.extend_bubble_eq]
              exact targetExact
            have selectedSimulation :=
              trace.focusedSelectedSurvivingSources_semantic payload
                targetWellFormed model named fuelSource bubbleFuel
                sourceExtended (targetExtended.extend trace.bubble)
                selectedContext sourceBinders targetBinders binderWitness
                sourceExact selectedTargetExact
                sourceBindersCover targetBindersCover sourceEnumeration
                targetEnumeration allowed fixedRecurseAt selectedSurvivors
                selectedSurvivorMembers selectedSurvivorMaps
                sourceSurvivorItems targetSurvivorItems
                sourceSurvivorCompiled (by
                  simpa [targetPushed, targetSelectedSurvivors] using
                    targetSurvivorCompiled)
            have sourceCanonicalNodup :
                (ModalSoundness.keptOccurrences input.val wrap ++
                  ModalSoundness.selectedOccurrences input.val wrap).Nodup :=
              (sourcePartition.nodup_iff).2
                (ConcreteElaboration.localOccurrences_nodup input.val
                  wrap.val.anchor)
            have targetCanonicalNodup :
                ((ModalSoundness.keptOccurrences input.val wrap).map
                    trace.survivorOccurrence ++
                  [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                    ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                      trace.diagram.nodeCount)]).Nodup :=
              (targetPartition.nodup_iff).1
                (ConcreteElaboration.localOccurrences_nodup trace.diagram
                  (trace.regionMap wrap.val.anchor))
            letI : Nonempty model.Carrier :=
              ConcreteElaboration.lambdaModel_carrier_nonempty model
            have focusedItems :
                ConcreteElaboration.ItemSeqSimulation model named .forward
                  combined.indexRelation
                  (sourceItems.renameRelations binderWitness.relationMap)
                  targetItems := by
              intro sourceLocalEnvironment targetLocalEnvironment
                targetRelations environments sourceItemsDenote
              let sourceRelations := RelEnv.pullback
                binderWitness.relationMap targetRelations
              have baseRelationAgreement := RelEnv.pullback_agrees
                binderWitness.relationMap targetRelations
              have sourceRawDenote : denoteItemSeq model named
                  sourceLocalEnvironment sourceRelations sourceItems :=
                (denoteItemSeq_renameRelations model named
                  binderWitness.relationMap sourceRelations targetRelations
                  baseRelationAgreement sourceLocalEnvironment sourceItems).1
                    sourceItemsDenote
              have sourcePermutation := compileOccurrences_perm_denote_iff
                input.val sourceRecurse sourceExtended sourceBinders
                sourcePartition sourceCanonicalNodup
                (ConcreteElaboration.localOccurrences_nodup input.val
                  wrap.val.anchor)
                sourcePartitionCompiled sourceCompiledFocused model named
                sourceLocalEnvironment sourceRelations
              have sourceCanonicalDenote := sourcePermutation.mpr sourceRawDenote
              rw [sourcePartitionEq] at sourceCanonicalDenote
              have sourceParts :=
                (denoteItemSeq_append model named sourceLocalEnvironment
                  sourceRelations sourceKeptItems sourceSelectedItems).1
                  sourceCanonicalDenote
              have sourceKeptRenamed : denoteItemSeq model named
                  sourceLocalEnvironment targetRelations
                  (sourceKeptItems.renameRelations binderWitness.relationMap) :=
                (denoteItemSeq_renameRelations model named
                  binderWitness.relationMap sourceRelations targetRelations
                  baseRelationAgreement sourceLocalEnvironment
                  sourceKeptItems).2 sourceParts.1
              have targetKeptDenote := keptSimulation sourceLocalEnvironment
                targetLocalEnvironment targetRelations environments
                sourceKeptRenamed
              have sourceSelectedPermutation :=
                compileOccurrences_perm_denote_iff input.val sourceRecurse
                  sourceExtended sourceBinders sourceSelectedPartition
                  sourceSelectedCanonicalNodup
                  (selectedOccurrences_nodup input wrap)
                  sourceSelectedCanonicalCompiled sourceSelectedCompiled model
                  named sourceLocalEnvironment sourceRelations
              have sourceSelectedCanonicalDenote :=
                sourceSelectedPermutation.mpr sourceParts.2
              have sourceSelectedParts :=
                (denoteItemSeq_append model named sourceLocalEnvironment
                  sourceRelations sourceSurvivorItems
                  sourceFamilyAggregateItems).1 sourceSelectedCanonicalDenote
              let freshRelation := abstractionRelation
                (signature := signature) comprehension model named
              let freshRelations : RelEnv model.Carrier
                  (comprehension.val.boundary.length :: targetRels) :=
                (freshRelation, targetRelations)
              let freshWitness := binderWitness.intoFreshBubble
                comprehension.val.boundary.length
              have freshRelationAgreement : RelEnv.Agrees
                  freshWitness.relationMap sourceRelations freshRelations := by
                intro arity relation
                simpa [freshWitness, BinderWitness.intoFreshBubble,
                  BinderWitness.weakenRelationMap, freshRelations,
                  RelEnv.lookup, ConcreteElaboration.BinderContext.liftVar]
                  using baseRelationAgreement arity relation
              have sourceSurvivorRenamed : denoteItemSeq model named
                  sourceLocalEnvironment freshRelations
                  (sourceSurvivorItems.renameRelations
                    freshWitness.relationMap) :=
                (denoteItemSeq_renameRelations model named
                  freshWitness.relationMap sourceRelations freshRelations
                  freshRelationAgreement sourceLocalEnvironment
                  sourceSurvivorItems).2 sourceSelectedParts.1
              let bubbleLocal := trace.emptyBubbleEnvironment model.Carrier
              let targetBubbleEnvironment : Fin
                  (targetExtended.extend trace.bubble).length → model.Carrier :=
                fun index => targetLocalEnvironment
                  (Fin.cast (congrArg List.length
                    (trace.extend_bubble_eq targetExtended)) index)
              have selectedAgreement :
                  selectedContext.indexRelation.EnvironmentsAgree
                    sourceLocalEnvironment targetBubbleEnvironment := by
                exact focusedContext.castTarget_agrees
                  (trace.extend_bubble_eq targetExtended) sourceLocalEnvironment
                  targetLocalEnvironment environments
              have fixedFresh := FixedRelationWitness.fresh trace model named
                targetBinders targetRelations
              have targetSurvivorDenote := selectedSimulation
                sourceLocalEnvironment targetBubbleEnvironment freshRelations
                selectedAgreement fixedFresh sourceSurvivorRenamed
              have anchored : ∀ index, index ∈ indices →
                  (occurrences.get index).selection.val.anchor =
                    wrap.val.anchor := by
                intro index member
                exact (mem_anchorIndices occurrences wrap.val.anchor index).1
                  member
              have sourceFamilyDenote : denoteItemSeq model named
                  sourceLocalEnvironment sourceRelations
                  (occurrenceFamilyItems sourceFamilyItems indices) := by
                rw [sourceFamilyEq]
                exact sourceSelectedParts.2
              have targetFamilyDenote := trace.occurrenceFamily_forward payload
                model named fuelSource wrap.val.anchor indices anchored
                sourceExtended (targetExtended.extend trace.bubble)
                selectedContext sourceBinders targetPushed sourceBindersCover
                sourceEnumeration sourceExact sourceFamilyItems targetFamilyItems
                sourceFamilyCompiled targetFamilyCompiled sourceLocalEnvironment
                targetBubbleEnvironment sourceRelations freshRelations fixedFresh
                selectedAgreement sourceFamilyDenote
              have targetBubbleCanonicalDenote : denoteItemSeq model named
                  targetBubbleEnvironment freshRelations
                  (targetSurvivorItems.append targetAtomItems) := by
                apply (denoteItemSeq_append model named targetBubbleEnvironment
                  freshRelations targetSurvivorItems targetAtomItems).2
                refine ⟨targetSurvivorDenote, ?_⟩
                rw [← targetFamilyEq]
                exact targetFamilyDenote
              have targetBubblePermutation :=
                compileOccurrences_perm_denote_iff trace.diagram bubbleRecurse
                  (targetExtended.extend trace.bubble) targetPushed
                  targetBubblePartition
                  (ConcreteElaboration.localOccurrences_nodup trace.diagram
                    trace.bubble) targetBubbleCanonicalNodup bubbleItemsCompiled
                  targetBubbleCanonicalCompiled model named
                  targetBubbleEnvironment freshRelations
              have bubbleItemsDenote :=
                targetBubblePermutation.mpr targetBubbleCanonicalDenote
              have bubbleItemsDenoteActual : denoteItemSeq model named
                  (ConcreteElaboration.extendedEnvironment targetExtended
                    trace.bubble targetLocalEnvironment bubbleLocal)
                  freshRelations bubbleItems := by
                rw [trace.extendedEnvironment_bubble_empty]
                exact bubbleItemsDenote
              have bubbleBodyDenote : denoteRegion model named
                  targetLocalEnvironment freshRelations
                  (ConcreteElaboration.finishRegion trace.diagram targetExtended
                    trace.bubble bubbleItems) :=
                (DoubleCutElimTrace.finishRegion_denote_iff trace.diagram
                  targetExtended trace.bubble bubbleItems model named
                  targetLocalEnvironment freshRelations).2
                    ⟨bubbleLocal, bubbleItemsDenoteActual⟩
              have targetBubbleDenote : denoteItem model named
                  targetLocalEnvironment targetRelations
                  (.bubble comprehension.val.boundary.length
                    (ConcreteElaboration.finishRegion trace.diagram targetExtended
                      trace.bubble bubbleItems)) := by
                simp only [bubble_denotes_exists]
                exact ⟨freshRelation, bubbleBodyDenote⟩
              have targetCanonicalDenote : denoteItemSeq model named
                  targetLocalEnvironment targetRelations
                  (targetKeptItems.append (.cons
                    (.bubble comprehension.val.boundary.length
                      (ConcreteElaboration.finishRegion trace.diagram
                        targetExtended trace.bubble bubbleItems)) .nil)) := by
                apply (denoteItemSeq_append model named targetLocalEnvironment
                  targetRelations targetKeptItems _).2
                exact ⟨targetKeptDenote, by simpa using targetBubbleDenote⟩
              have targetCanonicalCompiled :
                  ConcreteElaboration.compileOccurrencesWith? signature
                    trace.diagram targetRecurse targetExtended targetBinders
                    ((ModalSoundness.keptOccurrences input.val wrap).map
                        trace.survivorOccurrence ++
                      [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                        ConcreteElaboration.LocalOccurrence
                          trace.diagram.regionCount trace.diagram.nodeCount)]) =
                      some (targetKeptItems.append (.cons
                        (.bubble comprehension.val.boundary.length
                          (ConcreteElaboration.finishRegion trace.diagram
                            targetExtended trace.bubble bubbleItems)) .nil)) := by
                rw [← targetPartitionEq]
                exact targetPartitionCompiled
              have targetPermutation := compileOccurrences_perm_denote_iff
                trace.diagram targetRecurse targetExtended targetBinders
                targetPartition
                (ConcreteElaboration.localOccurrences_nodup trace.diagram
                  (trace.regionMap wrap.val.anchor)) targetCanonicalNodup
                targetCompiledFocused targetCanonicalCompiled
                model named targetLocalEnvironment targetRelations
              have targetItemsDenote := targetPermutation.mpr
                targetCanonicalDenote
              exact targetItemsDenote
            have relationMapEq :
                (simulation.relationMap simulation.binders_empty :
                  RelationRenaming [] []) =
                  (fun {arity} (relation : RelVar [] arity) => relation) := rfl
            have focusedItems' :
                ConcreteElaboration.ItemSeqSimulation model named .forward
                  combined.indexRelation sourceItems targetItems := by
              change ConcreteElaboration.ItemSeqSimulation model named .forward
                combined.indexRelation
                (sourceItems.renameRelations
                  (simulation.relationMap simulation.binders_empty)) targetItems
                at focusedItems
              rw [relationMapEq, ItemSeq.renameRelations_id] at focusedItems
              exact focusedItems
            rw [relationMapEq, Region.renameRelations_id]
            have rootTransport :=
              ConcreteElaboration.directionalRootTransport_of_agreement .forward
                source.val.exposedWires source.val.hiddenWires
                target.val.exposedWires target.val.hiddenWires
                outer.indexRelation combined.indexRelation model named
                sourceItems targetItems
                (trace.rootEnvironmentSelection payload targetWellFormed hraw
                  boundary sourceRoot mapped transport .forward)
                focusedItems'
            exact ConcreteElaboration.finishRoot_denote .forward
              source.val.exposedWires source.val.hiddenWires
              target.val.exposedWires target.val.hiddenWires
              outer.indexRelation model named
              sourceItems targetItems rootTransport

theorem boundaryClass_transport
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped)
    (sourcePosition : Fin boundary.length) :
    let source := trace.sourceOpen boundary
    let target := trace.targetOpen hraw boundary mapped transport
    let outer := trace.rootOuterContextWitness hraw boundary mapped transport
    let targetPosition : Fin target.boundary.length :=
      Fin.cast (trace.targetBoundary_length hraw boundary mapped transport).symm
        sourcePosition
    outer.sourceIndex (target.boundaryClass targetPosition) =
      source.boundaryClass sourcePosition := by
  dsimp only
  let source := trace.sourceOpen boundary
  let target := trace.targetOpen hraw boundary mapped transport
  let outer := trace.rootOuterContextWitness hraw boundary mapped transport
  let targetPosition : Fin target.boundary.length :=
    Fin.cast (trace.targetBoundary_length hraw boundary mapped transport).symm
      sourcePosition
  symm
  apply ConcreteElaboration.WireContext.lookup?_unique source.exposedWires_nodup
    (outer.sourceIndex_lookup (target.boundaryClass targetPosition))
  change source.exposedWires.get (source.boundaryClass sourcePosition) =
    trace.domains.wires.origin
      (target.exposedWires.get (target.boundaryClass targetPosition))
  rw [OpenConcreteDiagram.boundaryClass_sound source sourcePosition,
    OpenConcreteDiagram.boundaryClass_sound target targetPosition]
  change boundary.get sourcePosition = trace.domains.wires.origin
    ((trace.targetBoundary hraw boundary mapped transport).get targetPosition)
  rw [trace.targetBoundary_get hraw boundary mapped transport targetPosition]
  have castEq : Fin.cast
      (trace.targetBoundary_length hraw boundary mapped transport)
        targetPosition = sourcePosition := by
    apply Fin.ext
    rfl
  rw [castEq]
  exact (trace.targetWire_origin _ _).symm

theorem boundaryWitness
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
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    let source : CheckedOpenDiagram signature :=
      ⟨trace.sourceOpen boundary,
        trace.sourceOpen_wellFormed boundary sourceRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨trace.targetOpen hraw boundary mapped transport,
        trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
          sourceRoot mapped transport⟩
    let root := trace.rootContextSimulation payload targetWellFormed hraw
      boundary sourceRoot mapped transport model named direction
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction source.elaborate target.elaborate root.outer model named args
      (args ∘ Fin.cast
        (trace.targetBoundary_length hraw boundary mapped transport)) := by
  let source : CheckedOpenDiagram signature :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed boundary sourceRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨trace.targetOpen hraw boundary mapped transport,
      trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
        sourceRoot mapped transport⟩
  let outer := trace.rootOuterContextWitness hraw boundary mapped transport
  let root := trace.rootContextSimulation payload targetWellFormed hraw
    boundary sourceRoot mapped transport model named direction
  let targetArgs : Fin target.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast
      (trace.targetBoundary_length hraw boundary mapped transport)
  have targetPosition_cast (sourcePosition : Fin boundary.length) :
      Fin.cast (trace.targetBoundary_length hraw boundary mapped transport)
          (Fin.cast
            (trace.targetBoundary_length hraw boundary mapped transport).symm
            sourcePosition) = sourcePosition := by
    apply Fin.ext
    rfl
  dsimp only
  unfold
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
  cases direction with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      let targetAssignment : BoundaryAssignment target.elaborate model.Carrier := {
        args := targetArgs
        classes := sourceAssignment.classes ∘ outer.sourceIndex
        agrees := by
          intro targetPosition
          let sourcePosition : Fin boundary.length := Fin.cast
            (trace.targetBoundary_length hraw boundary mapped transport)
              targetPosition
          have classEq : outer.sourceIndex
              (target.val.boundaryClass targetPosition) =
              source.val.boundaryClass sourcePosition := by
            have transported := trace.boundaryClass_transport hraw boundary
              mapped transport sourcePosition
            have positionEq : Fin.cast
                (trace.targetBoundary_length hraw boundary mapped transport).symm
                  sourcePosition = targetPosition := by
              apply Fin.ext
              rfl
            simpa only [source, target, outer, positionEq] using transported
          change sourceAssignment.classes
              (outer.sourceIndex (target.val.boundaryClass targetPosition)) =
            targetArgs targetPosition
          rw [classEq]
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          simpa only [CheckedOpenDiagram.elaborate_boundary, sourceArgsEq,
            targetArgs, Function.comp_apply] using sourceAgrees
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      exact (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
        outer.sourceIndex sourceAssignment.classes targetAssignment.classes).2 rfl
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceClassTarget : Fin source.val.exposedWires.length →
          Fin target.val.exposedWires.length := fun sourceClass =>
        Classical.choose
          (trace.rootOuterContextWitness_sourceIndex_surjective hraw boundary
            mapped transport sourceClass)
      have sourceClassTarget_spec (sourceClass) :
          outer.sourceIndex (sourceClassTarget sourceClass) = sourceClass :=
        Classical.choose_spec
          (trace.rootOuterContextWitness_sourceIndex_surjective hraw boundary
            mapped transport sourceClass)
      let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
        args := args
        classes := targetAssignment.classes ∘ sourceClassTarget
        agrees := by
          intro sourcePosition
          let targetPosition : Fin target.val.boundary.length := Fin.cast
            (trace.targetBoundary_length hraw boundary mapped transport).symm
              sourcePosition
          have directClass := trace.boundaryClass_transport hraw boundary mapped
            transport sourcePosition
          have chosenEq : sourceClassTarget
              (source.val.boundaryClass sourcePosition) =
                target.val.boundaryClass targetPosition := by
            apply outer.sourceIndex_injective source.val.exposedWires_nodup
              target.val.exposedWires_nodup
            rw [sourceClassTarget_spec]
            simpa only [source, target, outer, targetPosition] using directClass.symm
          change targetAssignment.classes
              (sourceClassTarget (source.val.boundaryClass sourcePosition)) =
            args sourcePosition
          rw [chosenEq]
          have targetAgrees := targetAssignment.agrees targetPosition
          rw [targetArgsEq] at targetAgrees
          simpa only [CheckedOpenDiagram.elaborate_boundary, Function.comp_apply,
            targetPosition_cast] using targetAgrees
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
        outer.sourceIndex sourceAssignment.classes targetAssignment.classes).2
      funext targetIndex
      change targetAssignment.classes
          (sourceClassTarget (outer.sourceIndex targetIndex)) =
        targetAssignment.classes targetIndex
      apply congrArg targetAssignment.classes
      apply outer.sourceIndex_injective source.val.exposedWires_nodup
        target.val.exposedWires_nodup
      rw [sourceClassTarget_spec]

theorem allowed_root
    (input : CheckedDiagram signature)
    (focus : Fin input.val.regionCount)
    (direction : ConcreteElaboration.SimulationDirection)
    (allowedDepth : AbstractionDepthAllowed direction
      (concreteCutDepth input.val focus)) :
    AbstractionAllowed input.val focus direction input.val.root := by
  intro path depth route routeDepth
  let view := Classical.choice (Diagram.Splice.siteView_complete input focus)
  have pathEq : path = view.path :=
    Diagram.Splice.Input.RegionRoute.path_unique input.property route view.route
  subst path
  have routeEq : route = view.route := Subsingleton.elim _ _
  subst route
  have depthEq : depth = view.focus.context.cutDepth :=
    regionRoute_cutDepth_unique routeDepth view.cutDepth
  subst depth
  rw [← siteView_concreteCutDepth_eq view]
  exact allowedDepth

theorem open_denote
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
    (allowed : AbstractionAllowed input.val wrap.val.anchor direction
      input.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    let source : CheckedOpenDiagram signature :=
      ⟨trace.sourceOpen boundary,
        trace.sourceOpen_wellFormed boundary sourceRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨trace.targetOpen hraw boundary mapped transport,
        trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
          sourceRoot mapped transport⟩
    direction.Entails (source.denote model named args)
      (target.denote model named
        (args ∘ Fin.cast
          (trace.targetBoundary_length hraw boundary mapped transport))) := by
  let source : CheckedOpenDiagram signature :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed boundary sourceRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨trace.targetOpen hraw boundary mapped transport,
      trace.targetOpen_wellFormed payload targetWellFormed hraw boundary
        sourceRoot mapped transport⟩
  let simulation := trace.semanticSimulation payload targetWellFormed model named
  exact ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
    source target model named simulation direction
    (trace.rootContextSimulation payload targetWellFormed hraw boundary
      sourceRoot mapped transport model named direction)
    allowed args
    (args ∘ Fin.cast
      (trace.targetBoundary_length hraw boundary mapped transport))
    (trace.boundaryWitness payload targetWellFormed hraw boundary sourceRoot
      mapped transport direction model named args)

def targetOpenIsoRaw
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (hraw : (comprehensionAbstractRaw? input wrap comprehension occurrences).map
      Subtype.val = some raw)
    (boundary : List (Fin input.val.wireCount))
    (mapped : List (Fin raw.wireCount))
    (transport :
      (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary boundary = some mapped) :
    OpenConcreteIso (trace.targetOpen hraw boundary mapped transport)
      ({ diagram := raw, boundary := mapped } : OpenConcreteDiagram) where
  diagram := concreteIsoOfEq trace.raw_eq_diagram.symm
  boundary := by
    apply List.ext_get
    · change (List.map (concreteIsoOfEq trace.raw_eq_diagram.symm).wires
          (trace.targetBoundary hraw boundary mapped transport)).length =
        mapped.length
      rw [List.length_map,
        trace.targetBoundary_length hraw boundary mapped transport]
      exact (comprehensionAbstractInterfaceTransport input wrap comprehension
        occurrences raw hraw).transportBoundary_length transport |>.symm
    · intro index targetBound mappedBound
      have targetBound' : index <
          (trace.targetBoundary hraw boundary mapped transport).length := by
        simpa only [targetOpen, List.length_map] using targetBound
      change (List.map (concreteIsoOfEq trace.raw_eq_diagram.symm).wires
          (trace.targetBoundary hraw boundary mapped transport))[index] =
        mapped[index]
      simp only [List.getElem_map]
      let position : Fin
          (trace.targetBoundary hraw boundary mapped transport).length :=
        ⟨index, targetBound'⟩
      let sourcePosition : Fin boundary.length := Fin.cast
        (trace.targetBoundary_length hraw boundary mapped transport) position
      have targetGet := trace.targetBoundary_get hraw boundary mapped transport
        position
      have mappedGet := trace.transportedWire_eq_rawTargetWire hraw boundary
        mapped transport sourcePosition
      apply Fin.ext
      rw [concreteIsoOfEq_wires_val]
      change ((trace.targetBoundary hraw boundary mapped transport).get
        position).val = (mapped.get ⟨index, mappedBound⟩).val
      rw [targetGet]
      have mappedPositionEq : Fin.cast
          ((comprehensionAbstractInterfaceTransport input wrap comprehension
            occurrences raw hraw).transportBoundary_length transport).symm
            sourcePosition = ⟨index, mappedBound⟩ := by
        apply Fin.ext
        rfl
      rw [← mappedPositionEq, mappedGet]
      rfl


end AbstractionRawTrace

end VisualProof.Rule
