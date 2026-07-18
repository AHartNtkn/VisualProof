import VisualProof.Rule.Soundness.Equational.AnchoredWireContractBatch

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

theorem moveEndpointsRaw_nil
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (distinct : sourceWire ≠ targetWire) :
    moveEndpointsRaw input sourceWire targetWire [] = input := by
  cases input with
  | mk regionCount nodeCount wireCount root regions nodes wires =>
      simp only [moveEndpointsRaw]
      congr 1
      funext candidate
      by_cases sourceEq : candidate = sourceWire
      · subst candidate
        cases sourceValue : wires sourceWire with
        | mk scope current => simp
      · by_cases targetEq : candidate = targetWire
        · subst candidate
          simp [distinct.symm]
        · simp [sourceEq, targetEq]

def endpointBatchTargetOpen
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := moveEndpointsRaw input.val sourceWire targetWire endpoints
  boundary := boundary

theorem endpointBatchTargetOpen_wellFormed
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed :
      (moveEndpointsRaw input.val sourceWire targetWire endpoints).WellFormed
        signature) :
    (endpointBatchTargetOpen input sourceWire targetWire endpoints boundary
      ).WellFormed signature := {
  diagram_well_formed := targetWellFormed
  boundary_is_root_scoped := by
    intro wire member
    simpa [endpointBatchTargetOpen] using boundaryRoot wire member
}

def endpointBatchTargetCheckedOpen
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed :
      (moveEndpointsRaw input.val sourceWire targetWire endpoints).WellFormed
        signature) : CheckedOpenDiagram signature :=
  ⟨endpointBatchTargetOpen input sourceWire targetWire endpoints boundary,
    endpointBatchTargetOpen_wellFormed input sourceWire targetWire endpoints
      boundary boundaryRoot targetWellFormed⟩

structure StableOrderedEndpointAnchorData
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (current : CEndpoint input.val.nodeCount) where
  data : OrderedEndpointAnchorData input sourceWire targetWire current
  anchorWitnessNotMoved :
    ({ node := data.anchorWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ∉ endpoints
  localWitnessNotMoved :
    ({ node := data.localWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ∉ endpoints

/-- Ordered anchor data survives a different endpoint move when neither of its
two witness outputs is the moved endpoint. -/
def OrderedEndpointAnchorData.after_move
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (moved current : CEndpoint input.val.nodeCount)
    (targetWellFormed :
      (moveEndpointRaw input.val sourceWire targetWire moved).WellFormed
        signature)
    (data : OrderedEndpointAnchorData input sourceWire targetWire current)
    (anchorStable : ({ node := data.anchorWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ moved)
    (localStable : ({ node := data.localWitness, port := CPort.output } :
      CEndpoint input.val.nodeCount) ≠ moved) :
    OrderedEndpointAnchorData
      ⟨moveEndpointRaw input.val sourceWire targetWire moved,
        targetWellFormed⟩ sourceWire targetWire current := by
  let next : CheckedDiagram signature :=
    ⟨moveEndpointRaw input.val sourceWire targetWire moved,
      targetWellFormed⟩
  exact {
    anchorWire := data.anchorWire
    localWire := data.localWire
    wirePair := data.wirePair
    shallow := data.shallow
    deep := data.deep
    anchorWireVisible := by
      simpa only [moveEndpointRaw_wire_scope] using
        (moveEndpointRaw_encloses_iff input.val sourceWire targetWire moved
        (input.val.wires data.anchorWire).scope data.shallow).mpr
          data.anchorWireVisible
    sourceWireVisible := by
      simpa only [moveEndpointRaw_wire_scope] using
        (moveEndpointRaw_encloses_iff input.val sourceWire targetWire moved
        (input.val.wires sourceWire).scope data.deep).mpr
          data.sourceWireVisible
    targetWireVisible := by
      simpa only [moveEndpointRaw_wire_scope] using
        (moveEndpointRaw_encloses_iff input.val sourceWire targetWire moved
        (input.val.wires targetWire).scope data.deep).mpr
          data.targetWireVisible
    deepEnclosesEndpoint := by
      simpa only [moveEndpointRaw_nodes] using
        (moveEndpointRaw_encloses_iff input.val sourceWire targetWire moved
        data.deep (input.val.nodes current.node).region).mpr
          data.deepEnclosesEndpoint
    anchorWitness := data.anchorWitness
    localWitness := data.localWitness
    anchorWitnessRegion := data.anchorWitnessRegion
    localWitnessRegion := data.localWitnessRegion
    anchorTerm := data.anchorTerm
    localTerm := data.localTerm
    anchorWitnessShape := by
      simpa [next, moveEndpointRaw] using data.anchorWitnessShape
    localWitnessShape := by
      simpa [next, moveEndpointRaw] using data.localWitnessShape
    anchorWitnessOccurs := by
      exact (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire
        moved { node := data.anchorWitness, port := CPort.output }
        anchorStable data.anchorWire).mpr data.anchorWitnessOccurs
    localWitnessOccurs := by
      exact (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire
        moved { node := data.localWitness, port := CPort.output }
        localStable data.localWire).mpr data.localWitnessOccurs
    anchorWitnessNe := data.anchorWitnessNe
    localWitnessNe := data.localWitnessNe
    anchorWitnessPath := data.anchorWitnessPath
    localWitnessPath := data.localWitnessPath
    routePath := data.routePath
    rootPath := data.rootPath
    anchorWitnessRoute :=
      moveEndpointRaw_route input.val sourceWire targetWire moved
        data.anchorWitnessRoute
    anchorWitnessZero :=
      moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire moved
        data.anchorWitnessRoute data.anchorWitnessZero
    localWitnessRoute :=
      moveEndpointRaw_route input.val sourceWire targetWire moved
        data.localWitnessRoute
    localWitnessZero :=
      moveEndpointRaw_route_hasCutDepth input.val sourceWire targetWire moved
        data.localWitnessRoute data.localWitnessZero
    route := moveEndpointRaw_route input.val sourceWire targetWire moved data.route
    rootRoute :=
      moveEndpointRaw_route input.val sourceWire targetWire moved data.rootRoute
    termValues := data.termValues
  }

/-- A noduplicated batch of endpoint moves preserves denotation when every
selected endpoint carries stable ordered anchor data. -/
private theorem moveEndpointsOpen_denote_iff_of_anchor_data_aux
    (fuel : Nat)
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (fuelEq : fuel = endpoints.length)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (distinct : sourceWire ≠ targetWire)
    (nodup : endpoints.Nodup)
    (sourceOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs sourceWire endpoint)
    (targetEncloses : ∀ endpoint, endpoint ∈ endpoints →
      input.val.Encloses (input.val.wires targetWire).scope
        (input.val.nodes endpoint.node).region)
    (anchors : ∀ endpoint, (member : endpoint ∈ endpoints) →
      Nonempty (StableOrderedEndpointAnchorData input sourceWire targetWire
        endpoints endpoint))
    (targetWellFormed :
      (moveEndpointsRaw input.val sourceWire targetWire endpoints).WellFormed
        signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    (endpointMoveSourceCheckedOpen input boundary boundaryRoot).denote model
        named args ↔
      (endpointBatchTargetCheckedOpen input sourceWire targetWire endpoints
        boundary boundaryRoot targetWellFormed).denote model named args := by
  cases endpoints with
  | nil =>
      have rawEq := moveEndpointsRaw_nil input.val sourceWire targetWire distinct
      have checkedEq : endpointBatchTargetCheckedOpen input sourceWire targetWire
          [] boundary boundaryRoot targetWellFormed =
          endpointMoveSourceCheckedOpen input boundary boundaryRoot := by
        apply Subtype.ext
        change endpointBatchTargetOpen input sourceWire targetWire [] boundary =
          endpointMoveSourceOpen input boundary
        unfold endpointBatchTargetOpen endpointMoveSourceOpen
        congr 1
      let source := endpointMoveSourceCheckedOpen input boundary boundaryRoot
      let target := endpointBatchTargetCheckedOpen input sourceWire targetWire []
        boundary boundaryRoot targetWellFormed
      let iso : OpenConcreteIso source.val target.val :=
        OpenConcreteIso.ofEq (congrArg Subtype.val checkedEq.symm)
      have semantic := iso.denote_iff source.property target.property model named
        args
      have lengthProof : iso.boundary_length_eq =
          (rfl : boundary.length = boundary.length) := Subsingleton.elim _ _
      rw [lengthProof] at semantic
      exact semantic
  | cons moved tail =>
      have nodupParts := List.nodup_cons.mp nodup
      have movedNotTail : moved ∉ tail := nodupParts.1
      have tailNodup : tail.Nodup := nodupParts.2
      have movedOccurs := sourceOccurs moved (by simp)
      have movedEncloses := targetEncloses moved (by simp)
      have oneWellFormed := moveEndpointRaw_wellFormed input.val input.property
        sourceWire targetWire moved distinct movedOccurs movedEncloses
      obtain ⟨stableMoved⟩ := anchors moved (by simp)
      have headSemantic := moveEndpointOpen_denote_iff_of_anchor_data input
        boundary boundaryRoot sourceWire targetWire moved distinct movedOccurs
        oneWellFormed stableMoved.data model named args
      let next : CheckedDiagram signature :=
        ⟨moveEndpointRaw input.val sourceWire targetWire moved,
          oneWellFormed⟩
      have nextBoundaryRoot : ∀ wire, wire ∈ boundary →
          (next.val.wires wire).scope = next.val.root := by
        intro wire member
        simpa [next] using boundaryRoot wire member
      have tailWellFormed :
          (moveEndpointsRaw next.val sourceWire targetWire tail).WellFormed
            signature := by
        rw [show moveEndpointsRaw next.val sourceWire targetWire tail =
            moveEndpointsRaw input.val sourceWire targetWire (moved :: tail) by
          exact moveEndpointsRaw_cons input.val sourceWire targetWire moved tail
            distinct movedNotTail]
        exact targetWellFormed
      have tailSourceOccurs : ∀ endpoint, endpoint ∈ tail →
          next.val.EndpointOccurs sourceWire endpoint := by
        intro endpoint member
        have different : endpoint ≠ moved := by
          intro equality
          subst endpoint
          exact movedNotTail member
        exact (moveEndpointRaw_other_occurs_iff input.val sourceWire targetWire
          moved endpoint different sourceWire).mpr
            (sourceOccurs endpoint (by simp [member]))
      have tailTargetEncloses : ∀ endpoint, endpoint ∈ tail →
          next.val.Encloses (next.val.wires targetWire).scope
            (next.val.nodes endpoint.node).region := by
        intro endpoint member
        simpa only [next, moveEndpointRaw_wire_scope, moveEndpointRaw_nodes] using
          (moveEndpointRaw_encloses_iff input.val sourceWire targetWire moved
            (input.val.wires targetWire).scope
            (input.val.nodes endpoint.node).region).mpr
              (targetEncloses endpoint (by simp [member]))
      have tailAnchors : ∀ endpoint, (member : endpoint ∈ tail) →
          Nonempty (StableOrderedEndpointAnchorData next sourceWire targetWire
            tail endpoint) := by
        intro endpoint member
        obtain ⟨stable⟩ := anchors endpoint (by simp [member])
        have anchorStable :
            ({ node := stable.data.anchorWitness, port := CPort.output } :
              CEndpoint input.val.nodeCount) ≠ moved := by
          intro equality
          apply stable.anchorWitnessNotMoved
          simp [equality]
        have localStable :
            ({ node := stable.data.localWitness, port := CPort.output } :
              CEndpoint input.val.nodeCount) ≠ moved := by
          intro equality
          apply stable.localWitnessNotMoved
          simp [equality]
        let movedData := stable.data.after_move input sourceWire targetWire
          moved endpoint oneWellFormed anchorStable localStable
        exact ⟨{
          data := movedData
          anchorWitnessNotMoved := by
            intro witnessMember
            apply stable.anchorWitnessNotMoved
            exact List.mem_cons_of_mem moved witnessMember
          localWitnessNotMoved := by
            intro witnessMember
            apply stable.localWitnessNotMoved
            exact List.mem_cons_of_mem moved witnessMember
        }⟩
      have tailSemantic := moveEndpointsOpen_denote_iff_of_anchor_data_aux
        tail.length next sourceWire targetWire tail rfl boundary nextBoundaryRoot
        distinct tailNodup tailSourceOccurs tailTargetEncloses tailAnchors
        tailWellFormed model named args
      have sourceCheckedEq : endpointMoveSourceCheckedOpen next boundary
          nextBoundaryRoot = endpointMoveTargetCheckedOpen input boundary
            boundaryRoot sourceWire targetWire moved oneWellFormed := by
        apply Subtype.ext
        rfl
      have batchRawEq : moveEndpointsRaw next.val sourceWire targetWire tail =
          moveEndpointsRaw input.val sourceWire targetWire (moved :: tail) :=
        moveEndpointsRaw_cons input.val sourceWire targetWire moved tail distinct
          movedNotTail
      have targetCheckedEq : endpointBatchTargetCheckedOpen next sourceWire
          targetWire tail boundary nextBoundaryRoot tailWellFormed =
          endpointBatchTargetCheckedOpen input sourceWire targetWire
            (moved :: tail) boundary boundaryRoot targetWellFormed := by
        apply Subtype.ext
        change endpointBatchTargetOpen next sourceWire targetWire tail boundary =
          endpointBatchTargetOpen input sourceWire targetWire (moved :: tail)
            boundary
        unfold endpointBatchTargetOpen
        congr 1
      have tailAligned :
          (endpointMoveTargetCheckedOpen input boundary boundaryRoot sourceWire
            targetWire moved oneWellFormed).denote model named args ↔
          (endpointBatchTargetCheckedOpen input sourceWire targetWire
            (moved :: tail) boundary boundaryRoot targetWellFormed).denote model
              named args := by
        let oneTarget := endpointMoveTargetCheckedOpen input boundary boundaryRoot
          sourceWire targetWire moved oneWellFormed
        let nextSource := endpointMoveSourceCheckedOpen next boundary
          nextBoundaryRoot
        let tailTarget := endpointBatchTargetCheckedOpen next sourceWire
          targetWire tail boundary nextBoundaryRoot tailWellFormed
        let finalTarget := endpointBatchTargetCheckedOpen input sourceWire
          targetWire (moved :: tail) boundary boundaryRoot targetWellFormed
        let sourceIso : OpenConcreteIso oneTarget.val nextSource.val :=
          OpenConcreteIso.ofEq (congrArg Subtype.val sourceCheckedEq.symm)
        let targetIso : OpenConcreteIso tailTarget.val finalTarget.val :=
          OpenConcreteIso.ofEq (congrArg Subtype.val targetCheckedEq)
        have sourceSemantic := sourceIso.denote_iff oneTarget.property
          nextSource.property model named args
        have targetSemantic := targetIso.denote_iff tailTarget.property
          finalTarget.property model named args
        have sourceLengthProof : sourceIso.boundary_length_eq =
            (rfl : boundary.length = boundary.length) := Subsingleton.elim _ _
        have targetLengthProof : targetIso.boundary_length_eq =
            (rfl : boundary.length = boundary.length) := Subsingleton.elim _ _
        rw [sourceLengthProof] at sourceSemantic
        rw [targetLengthProof] at targetSemantic
        have sourceNormalized : oneTarget.denote model named args ↔
            nextSource.denote model named args := by
          exact sourceSemantic
        have targetNormalized : tailTarget.denote model named args ↔
            finalTarget.denote model named args := by
          exact targetSemantic
        exact sourceNormalized.trans (tailSemantic.trans targetNormalized)
      exact headSemantic.trans tailAligned
termination_by fuel
decreasing_by simp_all

/-- A noduplicated batch of endpoint moves preserves denotation when every
selected endpoint carries stable ordered anchor data. -/
theorem moveEndpointsOpen_denote_iff_of_anchor_data
    (input : CheckedDiagram signature)
    (sourceWire targetWire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (distinct : sourceWire ≠ targetWire)
    (nodup : endpoints.Nodup)
    (sourceOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs sourceWire endpoint)
    (targetEncloses : ∀ endpoint, endpoint ∈ endpoints →
      input.val.Encloses (input.val.wires targetWire).scope
        (input.val.nodes endpoint.node).region)
    (anchors : ∀ endpoint, (member : endpoint ∈ endpoints) →
      Nonempty (StableOrderedEndpointAnchorData input sourceWire targetWire
        endpoints endpoint))
    (targetWellFormed :
      (moveEndpointsRaw input.val sourceWire targetWire endpoints).WellFormed
        signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    (endpointMoveSourceCheckedOpen input boundary boundaryRoot).denote model
        named args ↔
      (endpointBatchTargetCheckedOpen input sourceWire targetWire endpoints
        boundary boundaryRoot targetWellFormed).denote model named args := by
  exact moveEndpointsOpen_denote_iff_of_anchor_data_aux endpoints.length input
    sourceWire targetWire endpoints rfl boundary boundaryRoot distinct nodup
    sourceOccurs targetEncloses anchors targetWellFormed model named args

end AnchoredWireContractSoundness

end VisualProof.Rule
