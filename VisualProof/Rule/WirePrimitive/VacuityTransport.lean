import VisualProof.Rule.Structural
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemoval
import VisualProof.Diagram.Concrete.WireQuantifierExhaustedWireRemovalCorrespondence

namespace VisualProof

namespace WirePrimitive

open StructuralCore

namespace Vacuity

open ConcreteWireQuantifier.ExhaustedWireRemovalSemantics

/-- Identity concrete isomorphism, used to turn checker equalities into exact
transport receipts without running an isomorphism checker. -/
def identityIso
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    ConcreteIso diagram diagram where
  regions := Data.Finite.FiniteEquiv.refl _
  nodes := Data.Finite.FiniteEquiv.refl _
  wires := Data.Finite.FiniteEquiv.refl _
  root := rfl
  region_table := by
    intro region
    cases data : diagram.regions region <;>
      simp [Data.Finite.FiniteEquiv.refl_apply, CRegion.rename, data]
  node_table := by
    intro node
    cases data : diagram.nodes node <;>
      simp [Data.Finite.FiniteEquiv.refl_apply, CNode.rename, data]
  wire_signature := by intro; rfl
  wire_scope := by intro; rfl
  endpointMap := fun _ endpoint => endpoint
  endpointInverse := fun _ endpoint => endpoint
  endpointMap_mem := by intros; assumption
  endpointInverse_mem := by intros; assumption
  endpointMap_left_inv := by intros; rfl
  endpointMap_right_inv := by intros; rfl
  endpointMap_corresponds := by
    intro wire endpoint incident
    unfold PortCorresponds
    constructor
    · rfl
    · have required := ConcreteDiagram.incident_port_required definitions
        diagram wellFormed wire endpoint incident
      cases nodeData : diagram.nodes endpoint.node with
      | atom => simp
      | ref => simp
      | identity region signature arity =>
          simp [ConcreteDiagram.requiredPorts, nodeData] at required
          obtain ⟨index, _, exact⟩ := required
          exact ⟨rfl, rfl, index, index, exact.symm, exact.symm⟩

/-- An exact concrete equality supplies an isomorphism without discovery. -/
def isoOfEq
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (leftWellFormed : left.WellFormed definitions)
    (exact : left = right) : ConcreteIso left right := by
  subst right
  exact identityIso left leftWellFormed

/-- Equality transport preserves the dense value of every region carrier. -/
@[simp] theorem isoOfEq_region_val
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (leftWellFormed : left.WellFormed definitions)
    (exact : left = right)
    (region : left.RegionId) :
    ((isoOfEq leftWellFormed exact).regions region).val = region.val := by
  subst right
  rfl

/--
Exact concrete provenance for a checked vacuous elimination.  The semantic
receipt identifies the unused binder; this companion receipt identifies the
actual endpoint-free concrete wire whose dense deletion is the public plain
endpoint.  Compiler reversal therefore never has to rediscover that wire.
-/
structure EliminationReceipt
    {plain bound : CheckedDiagram definitions}
    (input : VacuousInput plain bound)
    (_checked : CheckedVacuous input) where
  private mk ::
  wire : bound.val.WireId
  deletionIso : ConcreteIso plain.val
    (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate bound wire)
  siteExact :
    deletionIso.regions input.site =
      targetRegion bound wire (bound.val.wires wire).scope
  signatureExact : (bound.val.wires wire).sig = input.sig
  endpointsEmpty : (bound.val.wires wire).endpoints = []

/-- Record checker-owned exact deletion data; no candidate or isomorphism is
searched for. -/
def recordElimination
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    (checked : CheckedVacuous input)
    (wire : bound.val.WireId)
    (deletionIso : ConcreteIso plain.val
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate bound wire))
    (siteExact :
      deletionIso.regions input.site =
        targetRegion bound wire (bound.val.wires wire).scope)
    (signatureExact : (bound.val.wires wire).sig = input.sig)
    (endpointsEmpty : (bound.val.wires wire).endpoints = []) :
    EliminationReceipt input checked :=
  .mk wire deletionIso siteExact signatureExact endpointsEmpty

/-- Transport exact deletion provenance across the supplied suffix landing.
The bound endpoint and distinguished wire are retained, so cancellation is
composition rather than candidate reconstruction. -/
def transportElimination
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (real : CheckedDiagram definitions)
    (suffix : ConcreteIso real.val plain.val)
    (transportedInput : VacuousInput real bound)
    (transportedChecked : CheckedVacuous transportedInput)
    (siteExact : transportedInput.site = suffix.regions.symm input.site)
    (signatureExact : transportedInput.sig = input.sig) :
    EliminationReceipt transportedInput transportedChecked :=
  .mk receipt.wire (suffix.trans receipt.deletionIso) (by
    change receipt.deletionIso.regions
      (suffix.regions transportedInput.site) = _
    rw [siteExact]
    exact (congrArg receipt.deletionIso.regions
      (suffix.regions.right_inv input.site)).trans receipt.siteExact)
    (receipt.signatureExact.trans signatureExact.symm)
    receipt.endpointsEmpty

private theorem endpoint_eq
    {nodeCount : Nat} {left right : CEndpoint nodeCount}
    (node : left.node = right.node)
    (port : left.port = right.port) : left = right := by
  cases left
  cases right
  simp_all

/-- Exact source-built endpoint table of a retained wire in the canonical
vacuous-erasure candidate. -/
theorem candidateWire_endpoints
    (source : CheckedDiagram definitions)
    (removed : source.val.WireId)
    (wire : source.val.WireId)
    (survives : wire ≠ removed) :
    ((ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
      source removed).wires
        (targetWire source removed wire survives)).endpoints =
      (source.val.wires wire).endpoints.map (fun endpoint =>
        ({ node := targetNode source removed endpoint.node
           port := endpoint.port } :
          CEndpoint
            (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
              source removed).nodeCount)) := by
  unfold targetWire
  simp only [ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate,
    DenseList.get_index]
  unfold targetNode DenseList.index Internal.retainedNodes
  induction (source.val.wires wire).endpoints with
  | nil => rfl
  | cons endpoint tail induction =>
      simp only [List.filterMap_cons, List.map_cons]
      rw [dif_pos]
      · change _ :: _ = _ :: _
        exact congrArg (List.cons _) induction
      · simp [ConcreteDiagram.nodesList, Data.Finite.mem_allFin]

namespace EliminationReceipt

/-- Exact erased wire exposed to the inverse compiler. -/
def eliminatedWire
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) : bound.val.WireId :=
  receipt.wire

/-- The recorded distinguished wire is endpoint-free. -/
theorem endpoints_empty
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    (bound.val.wires receipt.wire).endpoints = [] :=
  receipt.endpointsEmpty

/-- The semantic receipt's selected plain region is exactly the dense image
of the recorded bound-wire scope. -/
theorem eliminatedSite_exact
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    receipt.deletionIso.regions input.site =
      targetRegion bound receipt.wire
        (bound.val.wires receipt.wire).scope :=
  receipt.siteExact

/-- The semantic receipt's binder signature is the recorded wire signature. -/
theorem eliminatedSignature_exact
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    (bound.val.wires receipt.wire).sig = input.sig :=
  receipt.signatureExact

abbrev RegionOrigin
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (_receipt : EliminationReceipt input checked) :=
  bound.val.RegionId

abbrev NodeOrigin
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (_receipt : EliminationReceipt input checked) :=
  bound.val.NodeId

abbrev WireOrigin
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :=
  { wire : bound.val.WireId // wire ≠ receipt.wire }

private def candidateRegionOriginEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    Data.Finite.FiniteEquiv
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        bound receipt.wire).RegionId
      receipt.RegionOrigin where
  toFun := sourceRegion bound receipt.wire
  invFun := targetRegion bound receipt.wire
  left_inv := targetRegion_sourceRegion bound receipt.wire
  right_inv := sourceRegion_targetRegion bound receipt.wire

private def candidateNodeOriginEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    Data.Finite.FiniteEquiv
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        bound receipt.wire).NodeId
      receipt.NodeOrigin where
  toFun := sourceNode bound receipt.wire
  invFun := targetNode bound receipt.wire
  left_inv := targetNode_sourceNode bound receipt.wire
  right_inv := sourceNode_targetNode bound receipt.wire

private def candidateWireOriginEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    Data.Finite.FiniteEquiv
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        bound receipt.wire).WireId
      receipt.WireOrigin where
  toFun := fun wire =>
    ⟨sourceWire bound receipt.wire wire,
      sourceWire_ne bound receipt.wire wire⟩
  invFun := fun origin =>
    targetWire bound receipt.wire origin.1 origin.2
  left_inv := targetWire_sourceWire bound receipt.wire
  right_inv := by
    intro origin
    apply Subtype.ext
    exact sourceWire_targetWire bound receipt.wire origin.1 origin.2

/-- Total public-plain to bound-source region origin correspondence. -/
def regionOriginEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    Data.Finite.FiniteEquiv plain.val.RegionId receipt.RegionOrigin :=
  receipt.deletionIso.regions.trans
    receipt.candidateRegionOriginEquiv

/-- Total public-plain to bound-source node origin correspondence. -/
def nodeOriginEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    Data.Finite.FiniteEquiv plain.val.NodeId receipt.NodeOrigin :=
  receipt.deletionIso.nodes.trans
    receipt.candidateNodeOriginEquiv

/-- Total public-plain to retained bound-source wire origin correspondence. -/
def wireOriginEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    Data.Finite.FiniteEquiv plain.val.WireId receipt.WireOrigin :=
  receipt.deletionIso.wires.trans
    receipt.candidateWireOriginEquiv

def targetRegionImage
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (region : receipt.RegionOrigin) : plain.val.RegionId :=
  receipt.regionOriginEquiv.symm region

def targetNodeImage
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (node : receipt.NodeOrigin) : plain.val.NodeId :=
  receipt.nodeOriginEquiv.symm node

def targetWireImage
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (wire : receipt.WireOrigin) : plain.val.WireId :=
  receipt.wireOriginEquiv.symm wire

@[simp] theorem regionOriginEquiv_targetRegionImage
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (region : receipt.RegionOrigin) :
    receipt.regionOriginEquiv (receipt.targetRegionImage region) = region :=
  receipt.regionOriginEquiv.right_inv region

@[simp] theorem nodeOriginEquiv_targetNodeImage
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (node : receipt.NodeOrigin) :
    receipt.nodeOriginEquiv (receipt.targetNodeImage node) = node :=
  receipt.nodeOriginEquiv.right_inv node

@[simp] theorem wireOriginEquiv_targetWireImage
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (wire : receipt.WireOrigin) :
    receipt.wireOriginEquiv (receipt.targetWireImage wire) = wire :=
  receipt.wireOriginEquiv.right_inv wire

@[simp] theorem regionOriginEquiv_root
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked) :
    receipt.regionOriginEquiv plain.val.root = bound.val.root := by
  unfold regionOriginEquiv candidateRegionOriginEquiv
  rw [Data.Finite.FiniteEquiv.trans_apply, receipt.deletionIso.root,
    target_root]
  exact sourceRegion_targetRegion bound receipt.wire bound.val.root

theorem region_data
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (region : plain.val.RegionId) :
    bound.val.regions (receipt.regionOriginEquiv region) =
      (plain.val.regions region).rename receipt.regionOriginEquiv := by
  unfold regionOriginEquiv candidateRegionOriginEquiv
  rw [Data.Finite.FiniteEquiv.trans_apply]
  have shape := sourceRegion_shape bound receipt.wire
    (receipt.deletionIso.regions region)
  rw [receipt.deletionIso.region_table region] at shape
  cases data : plain.val.regions region <;>
    simp [data, CRegion.rename] at shape ⊢ <;> exact shape

theorem node_data
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (node : plain.val.NodeId) :
    bound.val.nodes (receipt.nodeOriginEquiv node) =
      (plain.val.nodes node).rename receipt.regionOriginEquiv := by
  unfold nodeOriginEquiv candidateNodeOriginEquiv regionOriginEquiv
  rw [Data.Finite.FiniteEquiv.trans_apply]
  have shape := sourceNode_shape bound receipt.wire
    (receipt.deletionIso.nodes node)
  rw [receipt.deletionIso.node_table node] at shape
  cases data : plain.val.nodes node <;>
    simp [data, CNode.rename] at shape ⊢ <;> exact shape

@[simp] theorem wire_signature
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (wire : plain.val.WireId) :
    (bound.val.wires (receipt.wireOriginEquiv wire).1).sig =
      (plain.val.wires wire).sig := by
  unfold wireOriginEquiv candidateWireOriginEquiv
  rw [Data.Finite.FiniteEquiv.trans_apply]
  exact (sourceWire_signature bound receipt.wire
    (receipt.deletionIso.wires wire)).trans
      (receipt.deletionIso.wire_signature wire)

@[simp] theorem wire_scope
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (wire : plain.val.WireId) :
    (bound.val.wires (receipt.wireOriginEquiv wire).1).scope =
      receipt.regionOriginEquiv (plain.val.wires wire).scope := by
  unfold wireOriginEquiv candidateWireOriginEquiv regionOriginEquiv
  rw [Data.Finite.FiniteEquiv.trans_apply,
    Data.Finite.FiniteEquiv.trans_apply]
  exact (sourceWire_scope bound receipt.wire
    (receipt.deletionIso.wires wire)).symm.trans
      (congrArg (sourceRegion bound receipt.wire)
        (receipt.deletionIso.wire_scope wire))

/-- Source-owned reverse incidence after deleting the distinguished wire. -/
def nodeIncidence
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (node : receipt.NodeOrigin) : List (receipt.WireOrigin × CPort) :=
  (Data.Finite.allFin bound.val.wireCount).flatMap fun sourceWire =>
    if survives : sourceWire ≠ receipt.wire then
      (bound.val.wires sourceWire).endpoints.filterMap fun endpoint =>
        if endpoint.node = node then
          some (⟨sourceWire, survives⟩, endpoint.port)
        else
          none
    else
      []

private def candidateEndpointFiberEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (origin : receipt.WireOrigin)
    (candidateWire :
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        bound receipt.wire).WireId)
    (wireExact : candidateWire =
      targetWire bound receipt.wire origin.1 origin.2) :
    Data.Finite.FiniteEquiv
      { endpoint // endpoint ∈
        ((ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
          bound receipt.wire).wires candidateWire).endpoints }
      { endpoint // endpoint ∈ (bound.val.wires origin.1).endpoints } where
  toFun := fun endpoint =>
    ⟨⟨sourceNode bound receipt.wire endpoint.1.node,
      endpoint.1.port⟩, by
      have mappedMember : endpoint.1 ∈
          (bound.val.wires origin.1).endpoints.map (fun sourceEndpoint =>
            (⟨targetNode bound receipt.wire sourceEndpoint.node,
              sourceEndpoint.port⟩ : CEndpoint
                (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
                  bound receipt.wire).nodeCount)) := by
        rw [← candidateWire_endpoints bound receipt.wire
          origin.1 origin.2, ← wireExact]
        exact endpoint.2
      rcases List.mem_map.mp mappedMember with
        ⟨sourceEndpoint, member, exact⟩
      have nodeExact : sourceEndpoint.node =
          sourceNode bound receipt.wire endpoint.1.node := by
        have exactNode := congrArg CEndpoint.node exact
        simpa using congrArg (sourceNode bound receipt.wire) exactNode
      have portExact : sourceEndpoint.port = endpoint.1.port :=
        congrArg CEndpoint.port exact
      have endpointExact :
          (⟨sourceNode bound receipt.wire endpoint.1.node,
            endpoint.1.port⟩ : CEndpoint bound.val.nodeCount) =
            sourceEndpoint := by
        cases sourceEndpoint with
        | mk sourceNodeId sourcePort =>
            simp only at nodeExact portExact ⊢
            subst sourceNodeId
            subst sourcePort
            rfl
      rw [endpointExact]
      exact member⟩
  invFun := fun endpoint =>
    ⟨⟨targetNode bound receipt.wire endpoint.1.node,
      endpoint.1.port⟩, by
      rw [wireExact, candidateWire_endpoints bound receipt.wire
        origin.1 origin.2]
      exact List.mem_map.mpr ⟨endpoint.1, endpoint.2, rfl⟩⟩
  left_inv := by
    intro endpoint
    apply Subtype.ext
    apply endpoint_eq
    · exact targetNode_sourceNode bound receipt.wire endpoint.1.node
    · rfl
  right_inv := by
    intro endpoint
    apply Subtype.ext
    apply endpoint_eq
    · exact sourceNode_targetNode bound receipt.wire endpoint.1.node
    · rfl

structure EndpointFiberEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (origin : receipt.WireOrigin) where
  equivalence : Data.Finite.FiniteEquiv
    { endpoint // endpoint ∈
      (plain.val.wires (receipt.targetWireImage origin)).endpoints }
    { endpoint // endpoint ∈ (bound.val.wires origin.1).endpoints }
  forward_exact : ∀ endpoint,
    (equivalence endpoint).1 =
      ⟨sourceNode bound receipt.wire
          (receipt.deletionIso.endpointMap
            (receipt.targetWireImage origin) endpoint.1).node,
        (receipt.deletionIso.endpointMap
          (receipt.targetWireImage origin) endpoint.1).port⟩
  inverse_exact : ∀ endpoint,
    (equivalence.symm endpoint).1 =
      receipt.deletionIso.endpointInverse
        (receipt.targetWireImage origin)
        ⟨targetNode bound receipt.wire endpoint.1.node,
          endpoint.1.port⟩
  corresponds : ∀ (endpoint : { endpoint // endpoint ∈
      (plain.val.wires (receipt.targetWireImage origin)).endpoints }),
    PortCorresponds plain.val
      (ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        bound receipt.wire)
      receipt.deletionIso.nodes endpoint.1
      (receipt.deletionIso.endpointMap
        (receipt.targetWireImage origin) endpoint.1)

private theorem deletionIso_wire_target
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (origin : receipt.WireOrigin) :
    receipt.deletionIso.wires (receipt.targetWireImage origin) =
      targetWire bound receipt.wire origin.1 origin.2 := by
  apply receipt.candidateWireOriginEquiv.injective
  change receipt.wireOriginEquiv (receipt.targetWireImage origin) =
    receipt.candidateWireOriginEquiv
      (targetWire bound receipt.wire origin.1 origin.2)
  rw [receipt.wireOriginEquiv_targetWireImage]
  exact (receipt.candidateWireOriginEquiv.apply_symm_apply origin).symm

/-- Exact public-to-source endpoint fiber for one retained vacuity wire. -/
def endpointFiberEquiv
    {plain bound : CheckedDiagram definitions}
    {input : VacuousInput plain bound}
    {checked : CheckedVacuous input}
    (receipt : EliminationReceipt input checked)
    (origin : receipt.WireOrigin) :
    EndpointFiberEquiv receipt origin := by
  let publicFiber :=
    ConcreteIso.EndpointFiberEquiv.ofIso receipt.deletionIso
      (receipt.targetWireImage origin)
  have wireExact := receipt.deletionIso_wire_target origin
  let constructionFiber := receipt.candidateEndpointFiberEquiv origin
    (receipt.deletionIso.wires (receipt.targetWireImage origin)) wireExact
  refine
    { equivalence := publicFiber.equivalence.trans constructionFiber
      forward_exact := ?_
      inverse_exact := ?_
      corresponds := ?_ }
  · intro endpoint
    rfl
  · intro endpoint
    rfl
  · intro endpoint
    exact receipt.deletionIso.endpointMap_corresponds
      (receipt.targetWireImage origin) endpoint.1 endpoint.2

end EliminationReceipt

end Vacuity

end WirePrimitive

end VisualProof
