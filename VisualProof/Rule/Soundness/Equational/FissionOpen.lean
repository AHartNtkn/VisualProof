import VisualProof.Rule.Soundness.Equational.FissionSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace FissionSoundness

def sourceOpen (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := input.val
  boundary := boundary

def targetOpen (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount)) : OpenConcreteDiagram where
  diagram := fissionRaw input selected site producer residual
  boundary := boundary.map Fin.castSucc

theorem expectedTransport
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    (fissionInterfaceTransport input selected site producer residual
      ).transportBoundary boundary = some (boundary.map Fin.castSucc) := by
  apply InterfaceTransport.transportBoundary_eq_map
  intro wire member
  unfold fissionInterfaceTransport InterfaceTransport.append
    InterfaceTransport.rootFiltered
  dsimp only
  have mappedEq : Fin.cast (by rfl) (Fin.castAdd 1 wire) = wire.castSucc := by
    apply Fin.ext
    rfl
  change (if ((fissionRaw input selected site producer residual).wires
      (Fin.cast (by rfl) (Fin.castAdd 1 wire))).scope =
      (fissionRaw input selected site producer residual).root then
      some (Fin.cast (by rfl) (Fin.castAdd 1 wire)) else none) =
    some wire.castSucc
  have root : ((fissionRaw input selected site producer residual).wires
      wire.castSucc).scope = (fissionRaw input selected site producer residual).root := by
    rw [fissionRaw_oldWire_scope]
    exact sourceRoot wire member
  have condition : ((fissionRaw input selected site producer residual).wires
      (Fin.cast (by rfl) (Fin.castAdd 1 wire))).scope =
      (fissionRaw input selected site producer residual).root := by
    calc
      ((fissionRaw input selected site producer residual).wires
        (Fin.cast (by rfl) (Fin.castAdd 1 wire))).scope =
          ((fissionRaw input selected site producer residual).wires
            wire.castSucc).scope := congrArg
              (fun mapped =>
                ((fissionRaw input selected site producer residual).wires
                  mapped).scope) mappedEq
      _ = _ := root
  rw [if_pos condition]
  exact congrArg some mappedEq

def sourceCheckedOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    CheckedOpenDiagram signature :=
  ⟨sourceOpen input boundary, input.property, sourceRoot⟩

def targetCheckedOpen
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature) :
    CheckedOpenDiagram signature := by
  refine ⟨targetOpen input selected site producer residual boundary,
    targetWellFormed, ?_⟩
  intro mapped member
  rcases List.mem_map.mp member with ⟨wire, wireMember, rfl⟩
  change ((fissionRaw input selected site producer residual).wires
    wire.castSucc).scope = (fissionRaw input selected site producer residual).root
  rw [fissionRaw_oldWire_scope]
  exact sourceRoot wire wireMember

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
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp [injective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

theorem targetOpen_exposedWires
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount)) :
    (targetOpen input selected site producer residual boundary).exposedWires =
      (sourceOpen input boundary).exposedWires.map
        (fun wire : Fin input.val.wireCount => wire.castSucc) := by
  unfold targetOpen sourceOpen OpenConcreteDiagram.exposedWires
  apply eraseDups_map_injective
  intro left right equality
  apply Fin.ext
  simpa only [Fin.val_castSucc] using congrArg Fin.val equality

def rootFresh
    (input : CheckedDiagram signature)
    (site : Fin input.val.regionCount) :
    List (Fin (input.val.wireCount + 1)) :=
  if input.val.root = site then [Fin.last input.val.wireCount] else []

theorem targetOpen_hiddenWires
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount)) :
    (targetOpen input selected site producer residual boundary).hiddenWires =
      (sourceOpen input boundary).hiddenWires.map
          (fun wire : Fin input.val.wireCount => wire.castSucc) ++
        rootFresh input site := by
  unfold OpenConcreteDiagram.hiddenWires rootFresh
  change List.filter
      (fun wire => decide
        (wire ∉ (targetOpen input selected site producer residual boundary
          ).exposedWires))
      (ConcreteElaboration.exactScopeWires
        (fissionRaw input selected site producer residual) input.val.root) = _
  rw [fissionRaw_exactScopeWires, targetOpen_exposedWires]
  have oldPart :
      List.filter
          (fun wire => decide
            (wire ∉ (sourceOpen input boundary).exposedWires.map Fin.castSucc))
          (List.map Fin.castSucc
            (ConcreteElaboration.exactScopeWires input.val input.val.root)) =
        List.map Fin.castSucc
          (List.filter
            (fun wire => decide
              (wire ∉ (sourceOpen input boundary).exposedWires))
            (ConcreteElaboration.exactScopeWires input.val input.val.root)) := by
    rw [List.filter_map]
    apply congrArg (List.map Fin.castSucc)
    apply congrArg (fun predicate => List.filter predicate
      (ConcreteElaboration.exactScopeWires input.val input.val.root))
    funext wire
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro notMapped sourceMember
      exact notMapped (List.mem_map.mpr ⟨wire, sourceMember, rfl⟩)
    · intro notSource mappedMember
      rcases List.mem_map.mp mappedMember with ⟨old, oldMember, equality⟩
      have oldEq : old = wire := by
        apply Fin.ext
        simpa only [Fin.val_castSucc] using congrArg Fin.val equality
      exact notSource (by simpa [oldEq] using oldMember)
  by_cases rootSite : input.val.root = site
  · rw [if_pos rootSite]
    have split := List.filter_append
      (p := fun wire => decide
        (wire ∉ (sourceOpen input boundary).exposedWires.map Fin.castSucc))
      (List.map Fin.castSucc
        (ConcreteElaboration.exactScopeWires input.val input.val.root))
      [Fin.last input.val.wireCount]
    apply Eq.trans split
    rw [oldPart]
    congr 1
    apply List.filter_eq_self.mpr
    intro fresh freshMember
    have freshEq : fresh = Fin.last input.val.wireCount := by simpa using freshMember
    subst fresh
    apply decide_eq_true
    intro exposed
    unfold sourceOpen at exposed
    rcases List.mem_map.mp exposed with ⟨old, _, equality⟩
    change old.castSucc = Fin.last input.val.wireCount at equality
    have values := congrArg Fin.val equality
    simp only [Fin.val_castSucc, Fin.val_last] at values
    omega
  · rw [if_neg rootSite, List.append_nil]
    simpa [sourceOpen] using oldPart

theorem targetOpen_rootWires
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount)) :
    (targetOpen input selected site producer residual boundary).rootWires =
      (sourceOpen input boundary).rootWires.map
          (fun wire : Fin input.val.wireCount => wire.castSucc) ++
        rootFresh input site := by
  unfold OpenConcreteDiagram.rootWires
  rw [targetOpen_exposedWires, targetOpen_hiddenWires]
  calc
    List.map (fun wire : Fin input.val.wireCount => wire.castSucc)
          (sourceOpen input boundary).exposedWires ++
        (List.map (fun wire : Fin input.val.wireCount => wire.castSucc)
          (sourceOpen input boundary).hiddenWires ++ rootFresh input site) =
      (List.map (fun wire : Fin input.val.wireCount => wire.castSucc)
          (sourceOpen input boundary).exposedWires ++
        List.map (fun wire : Fin input.val.wireCount => wire.castSucc)
          (sourceOpen input boundary).hiddenWires) ++ rootFresh input site :=
        (List.append_assoc _ _ _).symm
    _ = List.map (fun wire : Fin input.val.wireCount => wire.castSucc)
          ((sourceOpen input boundary).exposedWires ++
            (sourceOpen input boundary).hiddenWires) ++ rootFresh input site := by
      exact congrArg (fun values => values ++ rootFresh input site)
        (List.map_append
          (f := fun wire : Fin input.val.wireCount => wire.castSucc)
          (l₁ := (sourceOpen input boundary).exposedWires)
          (l₂ := (sourceOpen input boundary).hiddenWires)).symm

noncomputable def rootIndex
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount)) :
    Fin (sourceOpen input boundary).rootWires.length →
      Fin (targetOpen input selected site producer residual boundary
        ).rootWires.length :=
  fun index =>
    let mapped := (sourceOpen input boundary).rootWires.map
        (fun wire : Fin input.val.wireCount => wire.castSucc) ++
      rootFresh input site
    let mappedIndex : Fin mapped.length := ⟨index.val, by
      simp [mapped]
      exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩
    Fin.cast (congrArg List.length
      (targetOpen_rootWires input selected site producer residual boundary)).symm
      mappedIndex

theorem rootIndex_get
    (index : Fin (sourceOpen input boundary).rootWires.length) :
    (targetOpen input selected site producer residual boundary).rootWires.get
        (rootIndex input selected site producer residual boundary index) =
      ((sourceOpen input boundary).rootWires.get index).castSucc := by
  let mapped := (sourceOpen input boundary).rootWires.map
      (fun wire : Fin input.val.wireCount => wire.castSucc) ++
    rootFresh input site
  let mappedIndex : Fin mapped.length := ⟨index.val, by
    simp [mapped]
    exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩
  have transported := List.get_of_eq
    (targetOpen_rootWires input selected site producer residual boundary)
      (rootIndex input selected site producer residual boundary index)
  rw [transported]
  let transportedIndex : Fin mapped.length := Fin.cast
    (congrArg List.length
      (targetOpen_rootWires input selected site producer residual boundary))
    (rootIndex input selected site producer residual boundary index)
  change mapped.get transportedIndex = _
  have indexEq : transportedIndex = mappedIndex := by apply Fin.ext; rfl
  rw [indexEq]
  have valid : index.val < ((sourceOpen input boundary).rootWires.map
      (fun wire : Fin input.val.wireCount => wire.castSucc) ++
        rootFresh input site).length := by
    rw [List.length_append, List.length_map]
    exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)
  change ((sourceOpen input boundary).rootWires.map
      (fun wire : Fin input.val.wireCount => wire.castSucc) ++
    rootFresh input site)[index.val]'valid = _
  rw [List.getElem_append_left (by
    rw [List.length_map]
    exact index.isLt)]
  exact List.getElem_map _

noncomputable def rootEmbedding
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature) :
    ContextEmbedding input selected site producer residual
      (sourceOpen input boundary).rootWires
      (targetOpen input selected site producer residual boundary).rootWires where
  index := rootIndex input selected site producer residual boundary
  get := rootIndex_get
  mem_old := by
    intro wire
    constructor
    · intro member
      have scope := (OpenConcreteDiagram.mem_rootWires_iff
        (targetCheckedOpen input selected site producer residual boundary
          sourceRoot targetWellFormed).val
        (targetCheckedOpen input selected site producer residual boundary
          sourceRoot targetWellFormed).property _).mp member
      change ((fissionRaw input selected site producer residual).wires
        wire.castSucc).scope = input.val.root at scope
      rw [fissionRaw_oldWire_scope] at scope
      exact (OpenConcreteDiagram.mem_rootWires_iff
        (sourceCheckedOpen input boundary sourceRoot).val
        (sourceCheckedOpen input boundary sourceRoot).property _).mpr scope
    · intro member
      have scope := (OpenConcreteDiagram.mem_rootWires_iff
        (sourceCheckedOpen input boundary sourceRoot).val
        (sourceCheckedOpen input boundary sourceRoot).property _).mp member
      apply (OpenConcreteDiagram.mem_rootWires_iff
        (targetCheckedOpen input selected site producer residual boundary
          sourceRoot targetWellFormed).val
        (targetCheckedOpen input selected site producer residual boundary
          sourceRoot targetWellFormed).property _).mpr
      change ((fissionRaw input selected site producer residual).wires
        wire.castSucc).scope = input.val.root
      rw [fissionRaw_oldWire_scope]
      exact scope

theorem targetExposedLength :
    (targetOpen input selected site producer residual boundary).exposedWires.length =
      (sourceOpen input boundary).exposedWires.length := by
  rw [targetOpen_exposedWires]
  exact List.length_map _

def exposedIndex :
    Fin (sourceOpen input boundary).exposedWires.length →
      Fin (targetOpen input selected site producer residual boundary
        ).exposedWires.length :=
  Fin.cast (targetExposedLength (input := input) (selected := selected)
    (site := site) (producer := producer) (residual := residual)
    (boundary := boundary)).symm

def sourceExposedIndex :
    Fin (targetOpen input selected site producer residual boundary
      ).exposedWires.length →
      Fin (sourceOpen input boundary).exposedWires.length :=
  Fin.cast (targetExposedLength (input := input) (selected := selected)
    (site := site) (producer := producer) (residual := residual)
    (boundary := boundary))

@[simp] theorem exposedIndex_sourceExposedIndex
    (index : Fin (targetOpen input selected site producer residual boundary
      ).exposedWires.length) :
    exposedIndex (input := input) (selected := selected) (site := site)
      (producer := producer) (residual := residual) (boundary := boundary)
      (sourceExposedIndex index) = index := by apply Fin.ext; rfl

@[simp] theorem sourceExposedIndex_exposedIndex
    (index : Fin (sourceOpen input boundary).exposedWires.length) :
    sourceExposedIndex
      (exposedIndex (input := input) (selected := selected) (site := site)
        (producer := producer) (residual := residual) (boundary := boundary)
        index) = index := by apply Fin.ext; rfl

theorem exposedIndex_get
    (index : Fin (sourceOpen input boundary).exposedWires.length) :
    (targetOpen input selected site producer residual boundary).exposedWires.get
        (exposedIndex index) =
      ((sourceOpen input boundary).exposedWires.get index).castSucc := by
  have transported := List.get_of_eq
    (targetOpen_exposedWires input selected site producer residual boundary)
      (exposedIndex index)
  rw [transported]
  change ((sourceOpen input boundary).exposedWires.map Fin.castSucc).get
      (Fin.cast (List.length_map _).symm index) = _
  simp [List.get_eq_getElem]

theorem boundaryLengthEq :
    (targetOpen input selected site producer residual boundary).boundary.length =
      (sourceOpen input boundary).boundary.length := by
  simp [targetOpen, sourceOpen]

theorem boundaryClass
    (position : Fin (sourceOpen input boundary).boundary.length) :
    exposedIndex
        ((sourceOpen input boundary).boundaryClass position) =
      (targetOpen input selected site producer residual boundary).boundaryClass
        (Fin.cast (boundaryLengthEq (input := input) (selected := selected)
          (site := site) (producer := producer) (residual := residual)
          (boundary := boundary)).symm position) := by
  apply OpenConcreteDiagram.boundaryClass_complete
  rw [exposedIndex_get, OpenConcreteDiagram.boundaryClass_sound]
  simp [targetOpen, sourceOpen, List.get_eq_getElem]

theorem targetHiddenLength :
    (targetOpen input selected site producer residual boundary).hiddenWires.length =
      (sourceOpen input boundary).hiddenWires.length +
        (rootFresh input site).length := by
  rw [targetOpen_hiddenWires]
  calc
    (List.map (fun wire : Fin input.val.wireCount => wire.castSucc)
        (sourceOpen input boundary).hiddenWires ++ rootFresh input site).length =
      (List.map (fun wire : Fin input.val.wireCount => wire.castSucc)
        (sourceOpen input boundary).hiddenWires).length +
          (rootFresh input site).length := List.length_append
    _ = (sourceOpen input boundary).hiddenWires.length +
        (rootFresh input site).length := by
      rw [List.length_map]
      rfl

def rootForwardLocal
    (sourceLocal : Fin (sourceOpen input boundary).hiddenWires.length → D)
    (fresh : Fin (rootFresh input site).length → D) :
    Fin (targetOpen input selected site producer residual boundary
      ).hiddenWires.length → D :=
  fun index => Fin.addCases sourceLocal fresh
    (Fin.cast (targetHiddenLength (input := input) (selected := selected)
      (site := site) (producer := producer) (residual := residual)
      (boundary := boundary)) index)

def rootBackwardLocal
    (targetLocal : Fin (targetOpen input selected site producer residual boundary
      ).hiddenWires.length → D) :
    Fin (sourceOpen input boundary).hiddenWires.length → D :=
  fun index => targetLocal
    (Fin.cast (targetHiddenLength (input := input) (selected := selected)
      (site := site) (producer := producer) (residual := residual)
      (boundary := boundary)).symm
      (Fin.castAdd (rootFresh input site).length index))

end FissionSoundness

end VisualProof.Rule
