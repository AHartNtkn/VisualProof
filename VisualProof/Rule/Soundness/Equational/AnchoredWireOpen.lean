import VisualProof.Rule.Soundness.Equational.AnchoredWireRoot

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireSoundness

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
      witness endpoints target available witnessRegion term
      witnessShape witnessOccurs witnessKept selectedOccurs targetWellFormed
      wireEncloses availability.wire_encloses_target witnessRoute
      witnessZero sameDepth targetRoute
    exact anchoredWireSplitRaw_compileRoot_route_to_available input boundary
      sourceRoot wire endpoints target available term selectedOccurs
      targetWellFormed availability.wire_encloses_target rootRoute
      (fun equality => atRoot equality.symm) targetRoute site sourceBody targetBody
      sourceCompiled targetCompiled model named targetOuter

end AnchoredWireSoundness

end VisualProof.Rule
