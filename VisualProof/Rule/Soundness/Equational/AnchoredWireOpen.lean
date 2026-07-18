import VisualProof.Rule.Soundness.Equational.AnchoredWireRoot

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireSoundness

/-- The old boundary position in the append-one operational result. -/
def anchoredWireSplitRawOpenBoundaryPosition
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (position : Fin
      (anchoredWireSplitSourceOpen input boundary).boundary.length) :
    Fin (anchoredWireSplitRawOpen input boundary wire endpoints target
      term).boundary.length :=
  Fin.cast (by
    simp [anchoredWireSplitSourceOpen, anchoredWireSplitRawOpen]) position

/-- Anchored splitting preserves the quotient map from ordered boundary
positions to external classes, including repeated aliases. -/
theorem anchoredWireSplitRawOpen_boundaryClass
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (position : Fin
      (anchoredWireSplitSourceOpen input boundary).boundary.length) :
    (anchoredWireSplitRawOpen input boundary wire endpoints target
        term).boundaryClass
        (anchoredWireSplitRawOpenBoundaryPosition input boundary wire endpoints
          target term position) =
      anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
        term ((anchoredWireSplitSourceOpen input boundary).boundaryClass
          position) := by
  symm
  apply OpenConcreteDiagram.boundaryClass_complete
  have exposedEq := anchoredWireSplitRawOpen_exposedWires input boundary wire
    endpoints target term
  let source := anchoredWireSplitSourceOpen input boundary
  let targetOpen := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let sourceClass := source.boundaryClass position
  let targetClass := anchoredWireSplitRawOpenExternalClass input boundary wire
    endpoints target term sourceClass
  let mappedIndex : Fin (source.exposedWires.map (Fin.castAdd 1)).length :=
    Fin.cast (List.length_map (as := source.exposedWires)
      (Fin.castAdd 1)).symm sourceClass
  have targetGet : targetOpen.exposedWires.get targetClass =
      (source.exposedWires.get sourceClass).castSucc := by
    have transported := get_of_eq exposedEq mappedIndex
    have indexEq :
        Fin.cast (congrArg List.length exposedEq).symm mappedIndex =
          targetClass := by
      apply Fin.ext
      rfl
    rw [indexEq] at transported
    exact transported.trans (by
      simpa only [List.get_eq_getElem, Fin.val_cast] using
        (List.getElem_map (l := source.exposedWires) (i := sourceClass.val)
          (Fin.castAdd 1)))
  have sourceGet : source.exposedWires.get sourceClass =
      source.boundary.get position :=
    OpenConcreteDiagram.boundaryClass_sound source position
  rw [sourceGet] at targetGet
  have boundaryGet : targetOpen.boundary.get
      (anchoredWireSplitRawOpenBoundaryPosition input boundary wire endpoints
        target term position) =
      Fin.castAdd 1 (source.boundary.get position) := by
    simp [source, targetOpen, anchoredWireSplitSourceOpen,
      anchoredWireSplitRawOpen, anchoredWireSplitRawOpenBoundaryPosition,
      List.get_eq_getElem]
  exact targetGet.trans (by
    rw [boundaryGet]
    apply Fin.ext
    rfl)

def anchoredWireSplitSourceCheckedOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root) :
    CheckedOpenDiagram signature :=
  ⟨anchoredWireSplitSourceOpen input boundary, {
    diagram_well_formed := input.property
    boundary_is_root_scoped := sourceRoot
  }⟩

def anchoredWireSplitTargetCheckedOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature) : CheckedOpenDiagram signature :=
  ⟨anchoredWireSplitRawOpen input boundary wire endpoints target term,
    anchoredWireSplitRawOpen_wellFormed input boundary sourceRoot wire endpoints
      target term targetWellFormed⟩

theorem anchoredWireSplitExpectedTransport
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitInterfaceTransport input wire endpoints target term
      ).transportBoundary boundary =
      some (boundary.map (Fin.castAdd 1)) := by
  apply InterfaceTransport.transportBoundary_eq_map
  intro old member
  simp [anchoredWireSplitInterfaceTransport, InterfaceTransport.append,
    InterfaceTransport.rootFiltered, anchoredWireSplitRaw_root]
  rw [show Fin.castAdd 1 old = old.castSucc by
    apply Fin.ext
    rfl]
  rw [anchoredWireSplitRaw_oldWire_scope]
  exact sourceRoot old member

def anchoredWireSplitOperationalOpen
    {input : CheckedDiagram signature}
    {wire : Fin input.val.wireCount}
    {endpoints : List (CEndpoint input.val.nodeCount)}
    {target : Fin input.val.regionCount} {term : Lambda.Term 0 (Fin 0)}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes
      (anchoredWireSplitRaw input wire endpoints target term)
      (anchoredWireSplitProvenance input wire endpoints target term)
      (anchoredWireSplitInterfaceTransport input wire endpoints target term))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root) :
    CheckedOpenDiagram signature :=
  anchoredWireSplitTargetCheckedOpen input boundary sourceRoot wire endpoints
    target term (realizes.result_eq ▸ receipt.result.property)

def anchoredWireSplitOperationalIso
    {input : CheckedDiagram signature}
    {wire : Fin input.val.wireCount}
    {endpoints : List (CEndpoint input.val.nodeCount)}
    {target : Fin input.val.regionCount} {term : Lambda.Term 0 (Fin 0)}
    {receipt : StepReceipt input}
    (realizes : receipt.Realizes
      (anchoredWireSplitRaw input wire endpoints target term)
      (anchoredWireSplitProvenance input wire endpoints target term)
      (anchoredWireSplitInterfaceTransport input wire endpoints target term))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    OpenConcreteIso
      (anchoredWireSplitOperationalOpen realizes boundary sourceRoot).val
      (realizes.rawResultOpen mapped) :=
  realizes.operationalIso_to_rawResultOpen htransport
    (boundary.map (Fin.castAdd 1))
    (anchoredWireSplitExpectedTransport input boundary sourceRoot wire endpoints
      target term)

/-- The complete ordered-open compiler theorem, split only on whether the
executor-certified availability region is the root. -/
theorem anchoredWireSplitRaw_compileRoot_equiv
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (wire : Fin input.val.wireCount)
    (witness : Fin input.val.nodeCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs wire
      { node := witness, port := .output })
    (witnessKept : { node := witness, port := CPort.output } ∉ endpoints)
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (availability : SplitAvailability input wire witnessRegion target)
    (sourceBody : Region signature
      (anchoredWireSplitSourceOpen input boundary).exposedWires.length [])
    (targetBody : Region signature (anchoredWireSplitRawOpen input boundary wire
      endpoints target term).exposedWires.length [])
    (sourceCompiled : ConcreteElaboration.compileRoot? signature input.val
      (anchoredWireSplitSourceOpen input boundary).exposedWires
      (anchoredWireSplitSourceOpen input boundary).hiddenWires = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRoot? signature
      (anchoredWireSplitRaw input wire endpoints target term)
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).exposedWires
      (anchoredWireSplitRawOpen input boundary wire endpoints target term).hiddenWires =
        some targetBody)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetOuter : Fin (anchoredWireSplitRawOpen input boundary wire endpoints
      target term).exposedWires.length → model.Carrier) :
    denoteRegion (relCtx := []) model named
        (targetOuter ∘ anchoredWireSplitRawOpenExternalClass input boundary wire
          endpoints target term) PUnit.unit sourceBody ↔
      denoteRegion (relCtx := []) model named targetOuter PUnit.unit targetBody := by
  rcases availability with
    ⟨available, wireEncloses, witnessInside, sameDepth, targetInside⟩
  let availability : SplitAvailability input wire witnessRegion target :=
    ⟨available, wireEncloses, witnessInside, sameDepth, targetInside⟩
  obtain ⟨witnessPath, witnessRoute, witnessZero⟩ :=
    availability.witness_zero_route
  obtain ⟨targetPath, ⟨targetRoute⟩⟩ := availability.target_route
  by_cases atRoot : available = input.val.root
  · subst available
    exact anchoredWireSplitRaw_compileRoot_from_root_witness input boundary
      sourceRoot wire witness endpoints target witnessRegion term witnessShape
      witnessOccurs witnessKept selectedOccurs targetWellFormed
      wireEncloses sameDepth witnessRoute witnessZero
      targetRoute sourceBody targetBody sourceCompiled targetCompiled model named
      targetOuter
  · obtain ⟨rootPath, ⟨rootRoute⟩⟩ :=
      Diagram.Splice.regionRoute_complete_of_encloses input.val input.val.root
        available (input.property.all_regions_reach_root available)
    have site : AnchoredAvailableKernel input wire endpoints target available
        term targetWellFormed :=
      anchoredWireSplitRaw_certified_available_kernel input wire
      witness endpoints target available witnessRegion term term
      witnessShape (fun _ => rfl) witnessOccurs witnessKept selectedOccurs
      targetWellFormed
      wireEncloses availability.wire_encloses_target witnessRoute
      witnessZero sameDepth targetRoute
    exact anchoredWireSplitRaw_compileRoot_route_to_available input boundary
      sourceRoot wire endpoints target available term selectedOccurs
      targetWellFormed availability.wire_encloses_target rootRoute
      (fun equality => atRoot equality.symm) targetRoute site sourceBody targetBody
      sourceCompiled targetCompiled model named targetOuter

/-- The compiler equivalence lifted to the exact ordered open diagrams used by
the executor.  Boundary order and repeated aliases are transported
positionwise. -/
theorem anchoredWireSplitRawOpen_denote_iff
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ old, old ∈ boundary →
      (input.val.wires old).scope = input.val.root)
    (wire : Fin input.val.wireCount)
    (witness : Fin input.val.nodeCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs wire
      { node := witness, port := .output })
    (witnessKept : { node := witness, port := CPort.output } ∉ endpoints)
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (availability : SplitAvailability input wire witnessRegion target)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    (anchoredWireSplitSourceCheckedOpen input boundary sourceRoot).denote model
        named args ↔
      (anchoredWireSplitTargetCheckedOpen input boundary sourceRoot wire endpoints
        target term targetWellFormed).denote model named
          (args ∘ Fin.cast (by
            exact List.length_map _)) := by
  let source := anchoredWireSplitSourceCheckedOpen input boundary sourceRoot
  let targetOpen := anchoredWireSplitRawOpen input boundary wire endpoints target
    term
  let targetWf := anchoredWireSplitRawOpen_wellFormed input boundary sourceRoot
    wire endpoints target term targetWellFormed
  let targetChecked : CheckedOpenDiagram signature := ⟨targetOpen, targetWf⟩
  let boundaryLength : targetOpen.boundary.length =
      source.val.boundary.length := by
    simp [targetOpen, source, anchoredWireSplitSourceCheckedOpen,
      anchoredWireSplitSourceOpen, anchoredWireSplitRawOpen]
  change source.denote model named args ↔
    targetChecked.denote model named (args ∘ Fin.cast boundaryLength)
  obtain ⟨sourceBody, sourceCompiled, sourceElaborated⟩ :=
    CheckedOpenDiagram.elaborate_body_computation source
  obtain ⟨targetBody, targetCompiled, targetElaborated⟩ :=
    CheckedOpenDiagram.elaborate_body_computation targetChecked
  have bodyEquiv := anchoredWireSplitRaw_compileRoot_equiv input boundary
    sourceRoot wire witness endpoints target witnessRegion term witnessShape
    witnessOccurs witnessKept selectedOccurs targetWellFormed availability
    sourceBody targetBody sourceCompiled targetCompiled model named
  constructor
  · intro sourceDenotes
    change denoteOpen model named source.elaborate args at sourceDenotes
    rcases sourceDenotes with ⟨sourceAssignment, sourceArgs, sourceBodyDenotes⟩
    rw [sourceElaborated] at sourceBodyDenotes
    let exposedLength : targetOpen.exposedWires.length =
        source.val.exposedWires.length := by
      rw [anchoredWireSplitRawOpen_exposedWires]
      exact List.length_map _
    let targetClasses : Fin targetOpen.exposedWires.length → model.Carrier :=
      sourceAssignment.classes ∘ Fin.cast exposedLength
    have sourceClasses : targetClasses ∘
        anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
          term = sourceAssignment.classes := by
      funext external
      apply congrArg sourceAssignment.classes
      rfl
    let targetAssignment : BoundaryAssignment targetChecked.elaborate
        model.Carrier := {
      args := args ∘ Fin.cast boundaryLength
      classes := targetClasses
      agrees := by
        intro targetPosition
        let sourcePosition : Fin source.val.boundary.length :=
          Fin.cast boundaryLength targetPosition
        have classEq := anchoredWireSplitRawOpen_boundaryClass input boundary wire
          endpoints target term sourcePosition
        have positionEq :
            anchoredWireSplitRawOpenBoundaryPosition input boundary wire endpoints
                target term sourcePosition = targetPosition := by
          apply Fin.ext
          rfl
        rw [positionEq] at classEq
        change sourceAssignment.classes
            (Fin.cast exposedLength
              (targetChecked.val.boundaryClass targetPosition)) = _
        have backClass : Fin.cast exposedLength
            (targetChecked.val.boundaryClass targetPosition) =
          source.val.boundaryClass sourcePosition := by
          rw [classEq]
          apply Fin.ext
          rfl
        calc
          sourceAssignment.classes
              (Fin.cast exposedLength
                (targetChecked.val.boundaryClass targetPosition)) =
              sourceAssignment.classes
                (source.val.boundaryClass sourcePosition) :=
            congrArg sourceAssignment.classes backClass
          _ = sourceAssignment.args sourcePosition :=
            sourceAssignment.agrees sourcePosition
          _ = args sourcePosition := congrFun sourceArgs sourcePosition
          _ = (args ∘ Fin.cast boundaryLength) targetPosition := rfl
    }
    refine ⟨targetAssignment, rfl, ?_⟩
    rw [targetElaborated]
    apply (bodyEquiv targetClasses).mp
    rw [sourceClasses]
    exact sourceBodyDenotes
  · intro targetDenotes
    change denoteOpen model named targetChecked.elaborate
        (args ∘ Fin.cast boundaryLength) at targetDenotes
    rcases targetDenotes with ⟨targetAssignment, targetArgs, targetBodyDenotes⟩
    rw [targetElaborated] at targetBodyDenotes
    let sourceClasses : Fin source.val.exposedWires.length → model.Carrier :=
      targetAssignment.classes ∘
        anchoredWireSplitRawOpenExternalClass input boundary wire endpoints target
          term
    let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
      args := args
      classes := sourceClasses
      agrees := by
        intro sourcePosition
        have classEq := anchoredWireSplitRawOpen_boundaryClass input boundary wire
          endpoints target term sourcePosition
        have agrees := targetAssignment.agrees
          (anchoredWireSplitRawOpenBoundaryPosition input boundary wire endpoints
            target term sourcePosition)
        change targetAssignment.classes
            (targetChecked.val.boundaryClass
              (anchoredWireSplitRawOpenBoundaryPosition input boundary wire
                endpoints target term sourcePosition)) = _ at agrees
        rw [classEq] at agrees
        rw [targetArgs] at agrees
        simpa [boundaryLength, anchoredWireSplitRawOpenBoundaryPosition] using
          agrees
    }
    refine ⟨sourceAssignment, rfl, ?_⟩
    rw [sourceElaborated]
    exact (bodyEquiv targetAssignment.classes).mpr targetBodyDenotes

end AnchoredWireSoundness

/-- Every successful anchored-wire split receipt is semantically equivalent
on its exact ordered operational boundary. -/
theorem applyAnchoredWireSplit_sound
    (context : ProofContext signature) (orientation : Orientation)
    (input : Diagram.CheckedDiagram signature)
    (wire : Fin input.val.wireCount) (witness : Fin input.val.nodeCount)
    (endpoints : List (Diagram.CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (receipt : StepReceipt input)
    (happly :
      applyAnchoredWireSplit input wire witness endpoints target = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.anchoredWireSplit wire witness endpoints target) receipt := by
  obtain ⟨witnessRegion, term, witnessShape, realizes⟩ :=
    applyAnchoredWireSplit_realizes happly
  obtain ⟨successRegion, successTerm, successShape, witnessOccurs,
    endpointsNodup, selectedOccurs, witnessKept, targetScopes,
    availabilityGate, rawEq⟩ :=
      applyAnchoredWireSplit_success input wire witness endpoints target receipt
        happly
  have shapeEq : CNode.term witnessRegion 0 term =
      CNode.term successRegion 0 successTerm :=
    witnessShape.symm.trans successShape
  cases shapeEq
  have targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature := realizes.result_eq ▸ receipt.result.property
  obtain ⟨availability⟩ := AnchoredWireSoundness.SplitAvailability.of_gate
    input wire witnessRegion target availabilityGate
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped htransport =>
      AnchoredWireSoundness.anchoredWireSplitOperationalOpen realizes boundary
        sourceRoot)
    (operationalIso := fun boundary sourceRoot mapped htransport =>
      AnchoredWireSoundness.anchoredWireSplitOperationalIso realizes boundary
        sourceRoot mapped htransport)
  intro boundary sourceRoot mapped htransport valid args
  have semantic := AnchoredWireSoundness.anchoredWireSplitRawOpen_denote_iff
    input boundary sourceRoot wire witness endpoints target witnessRegion term
    witnessShape witnessOccurs witnessKept selectedOccurs targetWellFormed
    availability Lambda.canonicalModel
    (Theory.interpretDefinitions context.definitions) args
  dsimp only
  unfold DirectedEntailment
  simpa [AnchoredWireSoundness.anchoredWireSplitSourceCheckedOpen,
    AnchoredWireSoundness.anchoredWireSplitOperationalOpen,
    AnchoredWireSoundness.anchoredWireSplitTargetCheckedOpen] using semantic

end VisualProof.Rule
