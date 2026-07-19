import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

variable {signature : List Nat}
  {input : CheckedDiagram signature}
  {bubble : Fin input.val.regionCount}
  {comprehension : CheckedOpenDiagram signature}
  {attachments : List (Fin input.val.wireCount)}
  {binders : List
    (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
  {payload : ComprehensionInstantiatePayload input bubble comprehension
    attachments binders}
  {fuel : Nat}
  {result : InstantiationState input attachments.length
    payload.binderSpine.proxyCount}
  {raw : ConcreteDiagram}

private theorem eraseDups_map_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (injective : Function.Injective f) :
    ∀ values : List α, (values.map f).eraseDups = values.eraseDups.map f
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      congr 1
      rw [← eraseDups_map_injective f injective
        (tail.filter fun value => !value == head)]
      apply congrArg List.eraseDups
      rw [List.filter_map]
      apply congrArg (List.map f)
      apply congrArg (fun predicate => List.filter predicate tail)
      funext value
      apply Bool.eq_iff_iff.mpr
      simp [injective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

/-- The exact ordered-open final presentation used by instantiation
soundness.  Every original boundary position is retained, in order, through
the certified injective final wire map. -/
def finalSourceOpen
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := elimTrace.sourceDiagram
  boundary := boundary.map (copyTrace.finalWireMap elimTrace)

def finalTargetOpen (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

theorem finalSourceOpen_exposedWires
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (boundary : List (Fin input.val.wireCount)) :
    (copyTrace.finalSourceOpen elimTrace boundary).exposedWires =
      (finalTargetOpen input boundary).exposedWires.map
        (copyTrace.finalWireMap elimTrace) := by
  unfold finalSourceOpen finalTargetOpen OpenConcreteDiagram.exposedWires
  exact eraseDups_map_injective _
    (copyTrace.finalWireMap_injective elimTrace boundaryNodup) boundary

/-- Exposed classes are exactly the mapped original exposed classes, with no
executor-created class admitted to the ordered boundary. -/
def finalOuterContextWitness
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (boundary : List (Fin input.val.wireCount)) :
    FinalContextWitness copyTrace elimTrace
      (copyTrace.finalSourceOpen elimTrace boundary).exposedWires
      (finalTargetOpen input boundary).exposedWires := by
  refine ⟨?_⟩
  intro wire member
  rw [copyTrace.finalSourceOpen_exposedWires elimTrace boundaryNodup boundary]
  exact List.mem_map.mpr ⟨wire, member, rfl⟩

theorem finalTargetOpen_wellFormed
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    (finalTargetOpen input boundary).WellFormed signature :=
  ⟨input.property, boundaryRoot⟩

theorem finalSourceOpen_wellFormed
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    (copyTrace.finalSourceOpen elimTrace boundary).WellFormed signature := by
  refine ⟨sourceWellFormed, ?_⟩
  intro mapped member
  obtain ⟨wire, wireMember, rfl⟩ := List.mem_map.mp member
  change (elimTrace.sourceDiagram.wires
      (copyTrace.finalWireMap elimTrace wire)).scope =
    elimTrace.sourceDiagram.root
  rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed boundaryNodup,
    boundaryRoot wire wireMember,
    copyTrace.finalRegionMap_root elimTrace finalWellFormed]

/-- The complete root contexts retain the certified image of every original
root wire.  Executor-created root wires are permitted only on the source
side and remain existentially local. -/
def finalRootContextWitness
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature) :
    FinalContextWitness copyTrace elimTrace
      (copyTrace.finalSourceOpen elimTrace boundary).rootWires
      (finalTargetOpen input boundary).rootWires := by
  let source : CheckedOpenDiagram signature :=
    ⟨copyTrace.finalSourceOpen elimTrace boundary,
      copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
        finalWellFormed boundaryNodup boundary boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨finalTargetOpen input boundary,
      finalTargetOpen_wellFormed input boundary boundaryRoot⟩
  refine ⟨?_⟩
  intro wire member
  apply (OpenConcreteDiagram.mem_rootWires_iff source.val source.property _).2
  change (elimTrace.sourceDiagram.wires
      (copyTrace.finalWireMap elimTrace wire)).scope =
    elimTrace.sourceDiagram.root
  rw [copyTrace.finalWireMap_scope elimTrace finalWellFormed boundaryNodup]
  have targetScope :=
    (OpenConcreteDiagram.mem_rootWires_iff target.val target.property wire).1
      member
  have targetScope' : (input.val.wires wire).scope = input.val.root := by
    simpa [target, finalTargetOpen] using targetScope
  rw [targetScope', copyTrace.finalRegionMap_root elimTrace finalWellFormed]

end InstantiationTrace

end VisualProof.Rule
