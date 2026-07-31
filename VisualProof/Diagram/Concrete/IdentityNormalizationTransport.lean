import VisualProof.Diagram.Concrete.IdentityNormalizationCore

namespace VisualProof

namespace ConcreteDiagram

namespace IdentityNormalizationCore

/-- Total signature-preserving representation of every source wire. -/
structure WireTransport
    (source target : ConcreteDiagram definitionCount) where
  wireImage : source.WireId → target.WireId
  wire_signature :
    ∀ wire,
      (target.wires (wireImage wire)).sig =
        (source.wires wire).sig

private def allWireIndex
  (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId) :
    Fin diagram.wiresList.length :=
  ⟨wire.val, by
    simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange, wire.isLt]⟩

@[simp] private theorem wiresList_get_allWireIndex
    (diagram : ConcreteDiagram definitionCount)
    (wire : diagram.WireId) :
    diagram.wiresList.get (allWireIndex diagram wire) = wire := by
  apply Fin.ext
  simp [ConcreteDiagram.wiresList, allWireIndex,
    Data.Finite.allFin_eq_finRange]

/-- Rule 1 retains every wire in canonical wire order. -/
def dropWireTransport
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    WireTransport source.val (dropCandidate source node eligible) where
  wireImage := allWireIndex source.val
  wire_signature := by
    intro wire
    change
      (source.val.wires
        (source.val.wiresList.get
          (allWireIndex source.val wire))).sig =
        (source.val.wires wire).sig
    rw [wiresList_get_allWireIndex]

theorem dropCandidate_nodeCount_lt
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : DropEligibility source node) :
    (dropCandidate source node eligible).nodeCount <
      source.val.nodeCount := by
  simpa [dropCandidate] using
    retainedNodes_singleton_length_lt source.val node

/-- A collapsed source wire is represented by the survivor exactly when incident. -/
def collapseRepresentative
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    source.val.WireId :=
  if wire ∈ source.val.identityIncidentWires node then
    eligible.survivor
  else
    wire

theorem collapseRepresentative_mem_retained
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    collapseRepresentative source node eligible wire ∈
      retainedWires source.val (eligible.second :: eligible.rest) := by
  have incidentNodup :=
    collapseIncidentWires_nodup source node eligible.identity.region
  rw [eligible.incident_eq] at incidentNodup
  have survivorNotAbsorbed :
      eligible.survivor ∉ eligible.second :: eligible.rest := by
    simpa using (List.nodup_cons.mp incidentNodup).1
  have absorbedSubset :
      ∀ candidate,
        candidate ∈ eligible.second :: eligible.rest →
        candidate ∈ source.val.identityIncidentWires node := by
    intro candidate member
    rw [← mem_collapseIncidentWires source node
      eligible.identity.region]
    rw [eligible.incident_eq]
    exact List.mem_cons_of_mem eligible.survivor member
  unfold collapseRepresentative retainedWires
  rw [List.mem_filter]
  constructor
  · exact Data.Finite.mem_allFin _
  · split
    · simpa using survivorNotAbsorbed
    · rename_i notIncident
      simp only [decide_eq_true_eq]
      intro absorbed
      exact notIncident (absorbedSubset wire absorbed)

private def collapseWireIndex
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    Fin
      (retainedWires source.val
        (eligible.second :: eligible.rest)).length :=
  (Data.Finite.indexOf?
    (retainedWires source.val (eligible.second :: eligible.rest))
    (collapseRepresentative source node eligible wire)).get
      (Data.Finite.indexOf?_isSome_iff.mpr
        (collapseRepresentative_mem_retained source node eligible wire))

@[simp] private theorem collapseWires_get_collapseWireIndex
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    (retainedWires source.val
      (eligible.second :: eligible.rest)).get
        (collapseWireIndex source node eligible wire) =
      collapseRepresentative source node eligible wire := by
  apply Data.Finite.indexOf?_sound
  exact
    (Option.some_get
      (Data.Finite.indexOf?_isSome_iff.mpr
        (collapseRepresentative_mem_retained source node eligible wire))).symm

private theorem collapseRepresentative_signature
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node)
    (wire : source.val.WireId) :
    (source.val.wires
      (collapseRepresentative source node eligible wire)).sig =
      (source.val.wires wire).sig := by
  unfold collapseRepresentative
  split
  · rename_i incident
    have survivorIncident :
        eligible.survivor ∈ source.val.identityIncidentWires node := by
      rw [← mem_collapseIncidentWires source node
        eligible.identity.region]
      rw [eligible.incident_eq]
      simp
    exact
      (identityIncidentWire_signature definitions source.val source.property
        eligible.identity.node_eq
        eligible.survivor survivorIncident).trans
      (identityIncidentWire_signature definitions source.val source.property
        eligible.identity.node_eq
        wire incident).symm
  · rfl

/-- Rule 2 maps every absorbed wire to the signature-equal survivor. -/
def collapseWireTransport
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    WireTransport source.val (collapseCandidate source node eligible) where
  wireImage := collapseWireIndex source node eligible
  wire_signature := by
    intro wire
    change
      (source.val.wires
        ((retainedWires source.val
          (eligible.second :: eligible.rest)).get
            (collapseWireIndex source node eligible wire))).sig =
        (source.val.wires wire).sig
    rw [collapseWires_get_collapseWireIndex]
    exact collapseRepresentative_signature source node eligible wire

theorem collapseCandidate_nodeCount_lt
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (eligible : CollapseEligibility source node) :
    (collapseCandidate source node eligible).nodeCount <
      source.val.nodeCount := by
  simpa [collapseCandidate] using
    retainedNodes_singleton_length_lt source.val node

/-- Rule 3 retains every wire in canonical wire order. -/
def fusionWireTransport
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    WireTransport source.val (fusionCandidate source left right eligible) where
  wireImage := allWireIndex source.val
  wire_signature := by
    intro wire
    change
      (source.val.wires
        (source.val.wiresList.get
          (allWireIndex source.val wire))).sig =
        (source.val.wires wire).sig
    rw [wiresList_get_allWireIndex]

theorem fusionCandidate_nodeCount_lt
    (source : CheckedDiagram definitions)
    (left right : source.val.NodeId)
    (eligible : FusionEligibility source left right) :
    (fusionCandidate source left right eligible).nodeCount <
      source.val.nodeCount := by
  simpa [fusionCandidate] using
    retainedNodes_singleton_length_lt source.val right

end IdentityNormalizationCore

end ConcreteDiagram

end VisualProof
