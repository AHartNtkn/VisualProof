import VisualProof.Rule.Soundness.Congruence

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireSoundness

/-- The Boolean executor gate exposes the exact common availability region it
certifies.  Keeping this equivalence beside the semantic proof prevents the
proof from replacing the serialized gate with a stronger intrinsic premise. -/
theorem anchorAvailableAt_eq_true_iff
    (input : ConcreteDiagram)
    (wireScope witnessRegion target : Fin input.regionCount) :
    anchorAvailableAt input wireScope witnessRegion target = true ↔
      ∃ available : Fin input.regionCount,
        input.Encloses wireScope available ∧
        input.Encloses available witnessRegion ∧
        concreteCutDepth input available = concreteCutDepth input witnessRegion ∧
        input.Encloses available target := by
  simp [anchorAvailableAt]

/-- The semantic availability certificate recovered from an accepted split. -/
structure SplitAvailability
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (witnessRegion target : Fin input.val.regionCount) where
  available : Fin input.val.regionCount
  wire_encloses : input.val.Encloses (input.val.wires wire).scope available
  witness_inside : input.val.Encloses available witnessRegion
  same_depth : concreteCutDepth input.val available =
    concreteCutDepth input.val witnessRegion
  target_inside : input.val.Encloses available target

theorem SplitAvailability.of_gate
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (witnessRegion target : Fin input.val.regionCount)
    (accepted : anchorAvailableAt input.val (input.val.wires wire).scope
      witnessRegion target = true) :
    Nonempty (SplitAvailability input wire witnessRegion target) := by
  obtain ⟨available, wireEncloses, witnessInside, sameDepth, targetInside⟩ :=
    (anchorAvailableAt_eq_true_iff input.val (input.val.wires wire).scope
      witnessRegion target).mp accepted
  exact ⟨⟨available, wireEncloses, witnessInside, sameDepth, targetInside⟩⟩

theorem SplitAvailability.wire_encloses_target
    (availability : SplitAvailability input wire witnessRegion target) :
    input.val.Encloses (input.val.wires wire).scope target :=
  ConcreteElaboration.checked_encloses_trans input.property
    availability.wire_encloses availability.target_inside

/-- The witness is reached from the availability region through bubbles only,
which is exactly the route property needed to expose its closed equation from
the authoritative compiler denotation. -/
theorem SplitAvailability.witness_zero_route
    (availability : SplitAvailability input wire witnessRegion target) :
    ∃ path,
      ∃ route : Diagram.Splice.RegionRoute input.val availability.available
          witnessRegion path,
        route.HasCutDepth 0 := by
  obtain ⟨path, ⟨route⟩⟩ :=
    Diagram.Splice.regionRoute_complete_of_encloses input.val
      availability.available witnessRegion availability.witness_inside
  obtain ⟨depth, routeDepth⟩ := route.hasCutDepth_exists input.property
  have depthZero := CongruenceSoundness.route_cutDepth_zero_of_equal input
    route depth routeDepth availability.same_depth
  subst depth
  exact ⟨path, route, routeDepth⟩

theorem SplitAvailability.target_route
    (availability : SplitAvailability input wire witnessRegion target) :
    ∃ path,
      Nonempty (Diagram.Splice.RegionRoute input.val availability.available
        target path) :=
  Diagram.Splice.regionRoute_complete_of_encloses input.val
    availability.available target availability.target_inside

@[simp] theorem anchoredWireSplitRaw_regionCount
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).regionCount =
      input.val.regionCount := rfl

@[simp] theorem anchoredWireSplitRaw_nodeCount
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).nodeCount =
      input.val.nodeCount + 1 := rfl

@[simp] theorem anchoredWireSplitRaw_wireCount
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).wireCount =
      input.val.wireCount + 1 := rfl

@[simp] theorem anchoredWireSplitRaw_root
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).root =
      input.val.root := rfl

@[simp] theorem anchoredWireSplitRaw_regions
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (region : Fin input.val.regionCount) :
    (anchoredWireSplitRaw input wire endpoints target term).regions region =
      input.val.regions region := rfl

@[simp] theorem anchoredWireSplitRaw_oldNode
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0))
    (node : Fin input.val.nodeCount) :
    (anchoredWireSplitRaw input wire endpoints target term).nodes node.castSucc =
      input.val.nodes node := by
  simp [anchoredWireSplitRaw]

@[simp] theorem anchoredWireSplitRaw_freshNode
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    (anchoredWireSplitRaw input wire endpoints target term).nodes
        (Fin.last input.val.nodeCount) = .term target 0 term := by
  simp [anchoredWireSplitRaw]

@[simp] theorem anchoredWireSplitRaw_oldWire_scope
    (input : CheckedDiagram signature) (wire old : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    ((anchoredWireSplitRaw input wire endpoints target term).wires old.castSucc).scope =
      (input.val.wires old).scope := by
  simp [anchoredWireSplitRaw]

@[simp] theorem anchoredWireSplitRaw_freshWire_scope
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount) (term : Lambda.Term 0 (Fin 0)) :
    ((anchoredWireSplitRaw input wire endpoints target term).wires
      (Fin.last input.val.wireCount)).scope = target := by
  simp [anchoredWireSplitRaw]

end AnchoredWireSoundness

end VisualProof.Rule
