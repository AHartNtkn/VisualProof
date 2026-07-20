import VisualProof.Rule.Structural.Iteration

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

/-- Eliminate exactly the canonical cut subtree carried by the proof-bearing
payload once its generic normal-separation certificate checks. -/
def applyInconsistentCutElim
    (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount)
    (first second : Fin input.val.nodeCount)
    (payload : InconsistentCutPayload input region first second) :
    Except StepError (StepReceipt input) :=
  if _hcertificate : Lambda.checkNormalSeparation
      payload.firstTerm payload.secondTerm payload.certificate = true then
    .ok {
      result := ⟨input.val.removeRaw payload.selection {},
        ConcreteDiagram.removeRaw_wellFormed input payload.selection {}⟩
      provenance := removeWireProvenance input payload.selection
      interface := removeWireInterfaceTransport input payload.selection
    }
  else
    .error .invalidCertificate

theorem applyInconsistentCutElim_realizes
    (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount)
    (first second : Fin input.val.nodeCount)
    (payload : InconsistentCutPayload input region first second)
    (result : StepReceipt input)
    (happly : applyInconsistentCutElim input region first second payload =
      .ok result) :
    result.Realizes (input.val.removeRaw payload.selection {})
      (removeWireProvenance input payload.selection)
      (removeWireInterfaceTransport input payload.selection) := by
  unfold applyInconsistentCutElim at happly
  split at happly <;> try contradiction
  cases happly
  refine ⟨rfl, ?_, ?_⟩ <;> intro wire <;> simp

theorem applyInconsistentCutElim_invalidCertificate
    (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount)
    (first second : Fin input.val.nodeCount)
    (payload : InconsistentCutPayload input region first second)
    (hcertificate : Lambda.checkNormalSeparation
      payload.firstTerm payload.secondTerm payload.certificate = false) :
    applyInconsistentCutElim input region first second payload =
      .error .invalidCertificate := by
  simp [applyInconsistentCutElim, hcertificate]

/-- A generic construction example fixes every structural gate in the payload
interface without assigning any distinguished meaning to either closed term. -/
example (input : CheckedDiagram signature)
    (region : Fin input.val.regionCount)
    (first second : Fin input.val.nodeCount)
    (parent : Fin input.val.regionCount)
    (region_is_cut : input.val.regions region = .cut parent)
    (distinct : first ≠ second)
    (firstTerm secondTerm : Lambda.Term 0 (Fin 0))
    (firstNode : input.val.nodes first = .term region 0 firstTerm)
    (secondNode : input.val.nodes second = .term region 0 secondTerm)
    (outputWire : Fin input.val.wireCount)
    (firstOutput : input.val.EndpointOccurs outputWire
      { node := first, port := .output })
    (secondOutput : input.val.EndpointOccurs outputWire
      { node := second, port := .output })
    (certificate : Lambda.NormalSeparationCertificate)
    (selection : CheckedSelection input.val)
    (selection_eq : selection.val = {
      anchor := parent
      childRoots := [region]
      directNodes := []
      explicitWires := []
    }) : InconsistentCutPayload input region first second := {
  parent := parent
  region_is_cut := region_is_cut
  distinct := distinct
  firstTerm := firstTerm
  secondTerm := secondTerm
  firstNode := firstNode
  secondNode := secondNode
  outputWire := outputWire
  firstOutput := firstOutput
  secondOutput := secondOutput
  certificate := certificate
  selection := selection
  selection_eq := selection_eq
}

end VisualProof.Rule
