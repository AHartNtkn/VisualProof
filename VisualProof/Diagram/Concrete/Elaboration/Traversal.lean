import VisualProof.Diagram.Concrete.Elaboration.Finite

namespace VisualProof.Diagram.ConcreteElaboration

open VisualProof.Diagram

inductive LocalOccurrence (regions nodes : Nat)
  | node (node : Fin nodes)
  | child (region : Fin regions)
  deriving DecidableEq

def exactScopeWires (d : ConcreteDiagram)
    (region : Fin d.regionCount) : List (Fin d.wireCount) :=
  filterFin fun wire => decide ((d.wires wire).scope = region)

@[simp] theorem mem_exactScopeWires (d : ConcreteDiagram)
    (region : Fin d.regionCount) (wire : Fin d.wireCount) :
    wire ∈ exactScopeWires d region ↔ (d.wires wire).scope = region := by
  simp [exactScopeWires]

theorem exactScopeWires_nodup (d : ConcreteDiagram)
    (region : Fin d.regionCount) : (exactScopeWires d region).Nodup :=
  filterFin_nodup _

def localOccurrences (d : ConcreteDiagram)
    (region : Fin d.regionCount) :
    List (LocalOccurrence d.regionCount d.nodeCount) :=
  (filterFin fun node => decide ((d.nodes node).region = region)).map
      LocalOccurrence.node ++
    (filterFin fun child =>
      decide ((d.regions child).parent? = some region)).map
      LocalOccurrence.child

@[simp] theorem mem_localOccurrences_node (d : ConcreteDiagram)
    (region : Fin d.regionCount) (node : Fin d.nodeCount) :
    LocalOccurrence.node node ∈ localOccurrences d region ↔
      (d.nodes node).region = region := by
  simp [localOccurrences]

@[simp] theorem mem_localOccurrences_child (d : ConcreteDiagram)
    (region child : Fin d.regionCount) :
    LocalOccurrence.child child ∈ localOccurrences d region ↔
      (d.regions child).parent? = some region := by
  simp [localOccurrences]

theorem localOccurrences_nodup (d : ConcreteDiagram)
    (region : Fin d.regionCount) : (localOccurrences d region).Nodup := by
  simp only [localOccurrences, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (filterFin_nodup _).map LocalOccurrence.node (by
      intro a b hab h
      exact hab (LocalOccurrence.node.inj h))
  · exact (filterFin_nodup _).map LocalOccurrence.child (by
      intro a b hab h
      exact hab (LocalOccurrence.child.inj h))
  · intro a ha b hb h
    simp only [List.mem_map] at ha hb
    obtain ⟨node, _, rfl⟩ := ha
    obtain ⟨child, _, hchild⟩ := hb
    have impossible : LocalOccurrence.node node =
        (LocalOccurrence.child child :
          LocalOccurrence d.regionCount d.nodeCount) :=
      h.trans hchild.symm
    cases impossible

namespace ParentTraversal

theorem climb_succ_root_eq_none (d : ConcreteDiagram)
    (hroot : d.RootIsSheet) (steps : Nat) :
    d.climb (steps + 1) d.root = none := by
  unfold ConcreteDiagram.RootIsSheet at hroot
  simp [ConcreteDiagram.climb, hroot, CRegion.parent?]

theorem climb_to_root_steps_unique (d : ConcreteDiagram)
    (hroot : d.RootIsSheet) {region : Fin d.regionCount}
    {steps₁ steps₂ : Nat}
    (h₁ : d.climb steps₁ region = some d.root)
    (h₂ : d.climb steps₂ region = some d.root) :
    steps₁ = steps₂ := by
  induction steps₁ generalizing steps₂ region with
  | zero =>
      simp only [ConcreteDiagram.climb_zero] at h₁
      have hregion : region = d.root := Option.some.inj h₁
      subst region
      cases steps₂ with
      | zero => rfl
      | succ steps₂ =>
          rw [climb_succ_root_eq_none d hroot steps₂] at h₂
          contradiction
  | succ steps₁ ih =>
      cases steps₂ with
      | zero =>
          simp only [ConcreteDiagram.climb_zero] at h₂
          have hregion : region = d.root := Option.some.inj h₂
          subst region
          rw [climb_succ_root_eq_none d hroot steps₁] at h₁
          contradiction
      | succ steps₂ =>
          cases hparent : (d.regions region).parent? with
          | none => simp [ConcreteDiagram.climb, hparent] at h₁
          | some parent =>
              have hparent₁ :
                  d.climb steps₁ parent = some d.root := by
                simpa [ConcreteDiagram.climb, hparent] using h₁
              have hparent₂ :
                  d.climb steps₂ parent = some d.root := by
                simpa [ConcreteDiagram.climb, hparent] using h₂
              exact congrArg Nat.succ (ih hparent₁ hparent₂)

theorem climb_to_root_steps_le_regionCount (d : ConcreteDiagram)
    (hroot : d.RootIsSheet) (hreach : d.AllRegionsReachRoot)
    {region : Fin d.regionCount} {steps : Nat}
    (hsteps : d.climb steps region = some d.root) :
    steps ≤ d.regionCount := by
  obtain ⟨boundedSteps, hbounded⟩ := hreach region
  have heq : steps = boundedSteps.val :=
    climb_to_root_steps_unique d hroot hsteps hbounded
  rw [heq]
  exact Nat.le_of_lt_succ boundedSteps.isLt

theorem checked_climb_to_root_steps_le_regionCount
    (checked : CheckedDiagram signature)
    {region : Fin checked.val.regionCount} {steps : Nat}
    (hsteps : checked.val.climb steps region = some checked.val.root) :
    steps ≤ checked.val.regionCount :=
  climb_to_root_steps_le_regionCount checked.val
    checked.property.root_is_sheet
    checked.property.all_regions_reach_root hsteps

theorem checked_child_chain_has_fuel
    (checked : CheckedDiagram signature)
    {region : Fin checked.val.regionCount} {depth : Nat}
    (hdepth : checked.val.climb depth region = some checked.val.root) :
    0 < checked.val.regionCount + 1 - depth := by
  have hle := checked_climb_to_root_steps_le_regionCount checked hdepth
  omega

end ParentTraversal

end VisualProof.Diagram.ConcreteElaboration
