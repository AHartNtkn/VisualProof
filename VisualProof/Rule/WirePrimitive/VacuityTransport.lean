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

end EliminationReceipt

end Vacuity

end WirePrimitive

end VisualProof
