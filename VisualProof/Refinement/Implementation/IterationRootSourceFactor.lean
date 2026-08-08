import VisualProof.Refinement.Implementation.IterationSourceFactor
import VisualProof.Concrete.Subgraph.Splice.Input.Layout.RootCompiler
import VisualProof.Concrete.State
import VisualProof.Data.List

namespace VisualProof.Refinement.Implementation.IterationRootSourceFactor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationPartition
open VisualProof.Refinement.Implementation.IterationSourceFactor

private theorem RegionIso.localEquivCast_apply
    {sourceWires targetWires sourceLocal targetLocal : Nat}
    {ambient : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region sourceWires rels}
    {target : Region targetWires rels}
    (iso : RegionIso ambient rels source target)
    (sourceLocalEq : source.localCount = sourceLocal)
    (targetLocalEq : target.localCount = targetLocal)
    (index : Fin source.localCount) :
    iso.localEquivCast sourceLocalEq targetLocalEq
        (Fin.cast sourceLocalEq index) =
      Fin.cast targetLocalEq (iso.localEquiv index) := by
  subst sourceLocal
  subst targetLocal
  rfl

private theorem ItemSeq.castWiresEq_eq_of_heq
    {source target : Nat} {rels : RelCtx}
    {first : ItemSeq source rels} {second : ItemSeq target rels}
    (equality : source = target) (equivalent : HEq first second) :
    first.castWiresEq equality = second := by
  subst target
  exact eq_of_heq equivalent

private theorem Fin.cast_castAdd
    {sourceOuter targetOuter localWires : Nat}
    (totalEq : sourceOuter + localWires = targetOuter + localWires)
    (index : Fin sourceOuter) :
    Fin.cast totalEq (Fin.castAdd localWires index) =
      Fin.castAdd localWires
        (Fin.cast (Nat.add_right_cancel totalEq) index) := by
  apply Fin.ext
  rfl

private theorem Fin.cast_natAdd
    {sourceOuter targetOuter localWires : Nat}
    (totalEq : sourceOuter + localWires = targetOuter + localWires)
    (index : Fin localWires) :
    Fin.cast totalEq (Fin.natAdd sourceOuter index) =
      Fin.natAdd targetOuter index := by
  apply Fin.ext
  exact congrArg (fun count => count + index.val)
    (Nat.add_right_cancel totalEq)

private theorem Fin.addCases_castAdd
    {sourceOuter targetOuter localWires : Nat}
    {α : Sort u}
    (totalEq : sourceOuter + localWires = targetOuter + localWires)
    (left : Fin targetOuter → α) (right : Fin localWires → α)
    (index : Fin sourceOuter) :
    Fin.addCases left right
        (Fin.cast totalEq (Fin.castAdd localWires index)) =
      left (Fin.cast (Nat.add_right_cancel totalEq) index) := by
  rw [Fin.cast_castAdd]
  exact Fin.addCases_left _

private theorem Fin.addCases_natAdd
    {sourceOuter targetOuter localWires : Nat}
    {α : Sort u}
    (totalEq : sourceOuter + localWires = targetOuter + localWires)
    (left : Fin targetOuter → α) (right : Fin localWires → α)
    (index : Fin localWires) :
    Fin.addCases left right
        (Fin.cast totalEq (Fin.natAdd sourceOuter index)) =
      right index := by
  rw [Fin.cast_natAdd]
  exact Fin.addCases_right _

private theorem Fin.addCases_zero
    {sourceOuter targetOuter : Nat}
    {α : Sort u}
    (totalEq : sourceOuter = targetOuter + 0)
    (left : Fin targetOuter → α) (right : Fin 0 → α)
    (index : Fin sourceOuter) :
    Fin.addCases left right (Fin.cast totalEq index) =
      left (Fin.cast (totalEq.trans (Nat.add_zero targetOuter)) index) := by
  have castEq : Fin.cast totalEq index =
      Fin.castAdd 0
        (Fin.cast (totalEq.trans (Nat.add_zero targetOuter)) index) := by
    apply Fin.ext
    rfl
  rw [castEq]
  exact Fin.addCases_left _

private noncomputable def OpenDiagramIso.castArity
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality)
      (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem OpenDiagram.castArity_withBody
    {sourceArity targetArity : Nat}
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (body : Region diagram.externalClasses []) :
    (diagram.withBody body).castArity equality =
      (diagram.castArity equality).withBody
        (body.castWiresEq
          (OpenDiagram.castArity_externalClasses diagram equality).symm) := by
  subst targetArity
  rfl

private theorem perm_of_nodup_and_mem_iff
    {values other : List α} [BEq α] [LawfulBEq α]
    (valuesNodup : values.Nodup) (otherNodup : other.Nodup)
    (members : ∀ value, value ∈ values ↔ value ∈ other) :
    values.Perm other := by
  rw [List.perm_iff_count]
  intro value
  rw [valuesNodup.count, otherNodup.count]
  by_cases member : value ∈ values
  · have otherMember : value ∈ other := (members value).1 member
    simp [member, otherMember]
  · have otherNotMember : value ∉ other :=
      fun present => member ((members value).2 present)
    simp [member, otherNotMember]

/-- Hidden root wires retained outside the selected factor. -/
def retainedHiddenWires
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram) :
    List (Fin source.val.diagram.wireCount) :=
  source.val.hiddenWires.filter
    (fun wire => decide (wire ∉ selection.val.explicitWires))

theorem explicitWire_mem_hiddenWires
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (anchorRoot : selection.val.anchor = source.val.diagram.root)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.val.boundary)
    {wire : Fin source.val.diagram.wireCount}
    (member : wire ∈ selection.val.explicitWires) :
    wire ∈ source.val.hiddenWires := by
  apply (Concrete.OpenDiagram.mem_hiddenWires source.val wire).2
  constructor
  · exact (selection.property.explicitWires_at_anchor wire member).trans
      anchorRoot
  · intro exposed
    exact (boundaryDisjoint wire member)
      ((Concrete.OpenDiagram.mem_exposedWires source.val wire).mp exposed)

theorem retainedHiddenWires_append_explicit_perm
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (anchorRoot : selection.val.anchor = source.val.diagram.root)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.val.boundary) :
    (retainedHiddenWires source selection ++
      selection.val.explicitWires).Perm source.val.hiddenWires := by
  let selected := source.val.hiddenWires.filter
    (fun wire => !(decide (wire ∉ selection.val.explicitWires)))
  have selectedPerm : selected.Perm selection.val.explicitWires := by
    apply perm_of_nodup_and_mem_iff
    · exact (source.val.hiddenWires_nodup.filter _)
    · exact selection.property.explicitWires_nodup
    · intro wire
      constructor
      · intro selectedMember
        have facts := List.mem_filter.mp selectedMember
        by_cases member : wire ∈ selection.val.explicitWires
        · exact member
        · simp [member] at facts
      · intro member
        change wire ∈ selected
        apply List.mem_filter.mpr
        exact ⟨explicitWire_mem_hiddenWires source selection anchorRoot
          boundaryDisjoint member, by simp [member]⟩
  have partition :
      (retainedHiddenWires source selection ++ selected).Perm
        source.val.hiddenWires := by
    have split := List.filter_append_perm
      (fun wire => decide (wire ∉ selection.val.explicitWires))
      source.val.hiddenWires
    simpa only [retainedHiddenWires, selected] using split
  exact (List.Perm.append_left (retainedHiddenWires source selection)
    selectedPerm).symm.trans partition

/-- Root-local reindexing that leaves the selected explicit block local. -/
noncomputable def rootLocalEquiv
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (anchorRoot : selection.val.anchor = source.val.diagram.root)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.val.boundary) :
    FiniteEquiv
      (Fin ((retainedHiddenWires source selection).length +
        selection.val.explicitWires.length))
      (Fin source.val.hiddenWires.length) :=
  let wires := retainedHiddenWires source selection ++
    selection.val.explicitWires
  let permutation := retainedHiddenWires_append_explicit_perm source selection
    anchorRoot boundaryDisjoint
  let sourceNodup := permutation.nodup_iff.mpr source.val.hiddenWires_nodup
  (FiniteEquiv.finCast (by simp [wires])).trans
    (permIndexEquiv wires source.val.hiddenWires permutation sourceNodup
      source.val.hiddenWires_nodup)

theorem rootLocalEquiv_spec
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (anchorRoot : selection.val.anchor = source.val.diagram.root)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.val.boundary)
    (index : Fin ((retainedHiddenWires source selection).length +
      selection.val.explicitWires.length)) :
    source.val.hiddenWires.get
        (rootLocalEquiv source selection anchorRoot boundaryDisjoint index) =
      (retainedHiddenWires source selection ++
        selection.val.explicitWires).get (Fin.cast (by simp) index) := by
  let wires := retainedHiddenWires source selection ++
    selection.val.explicitWires
  let permutation := retainedHiddenWires_append_explicit_perm source selection
    anchorRoot boundaryDisjoint
  let sourceNodup := permutation.nodup_iff.mpr source.val.hiddenWires_nodup
  exact permIndexEquiv_spec wires source.val.hiddenWires permutation sourceNodup
    source.val.hiddenWires_nodup (Fin.cast (by simp [wires]) index)

/-- Root wires outside the selected factor, ordered as exposed classes first
and retained hidden locals second. -/
def rootOuterWires
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram) :
    List (Fin source.val.diagram.wireCount) :=
  source.val.exposedWires ++ retainedHiddenWires source selection

theorem retainedAnchorWires_mem_iff_rootOuterWires
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (anchorRoot : selection.val.anchor = source.val.diagram.root)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.val.boundary)
    (wire : Fin source.val.diagram.wireCount) :
    wire ∈ retainedAnchorWires source.val.diagram selection ↔
      wire ∈ rootOuterWires source selection := by
  rw [mem_retainedAnchorWires]
  simp only [rootOuterWires, List.mem_append, retainedHiddenWires,
    List.mem_filter, decide_eq_true_eq,
    Concrete.OpenDiagram.mem_hiddenWires]
  constructor
  · intro facts
    by_cases exposed : wire ∈ source.val.exposedWires
    · exact Or.inl exposed
    · exact Or.inr ⟨⟨facts.1.trans anchorRoot, exposed⟩, facts.2⟩
  · intro member
    constructor
    · rcases member with exposed | hidden
      · exact (source.property.exposed_root_scoped exposed).trans
          anchorRoot.symm
      · exact hidden.1.1.trans anchorRoot.symm
    · rcases member with exposed | hidden
      · intro explicit
        exact (boundaryDisjoint wire explicit)
          ((Concrete.OpenDiagram.mem_exposedWires source.val wire).mp exposed)
      · exact hidden.2

theorem rootOuterWires_nodup
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram) :
    (rootOuterWires source selection).Nodup := by
  rw [rootOuterWires, List.nodup_append]
  refine ⟨source.val.exposedWires_nodup,
    source.val.hiddenWires_nodup.filter _, ?_⟩
  intro exposed exposedMember retained retainedMember equality
  subst retained
  exact source.val.exposedWires_hiddenWires_disjoint exposed exposedMember
    exposed (List.mem_filter.mp retainedMember).1 rfl

/-- Reindexes the closed retained anchor carrier as exposed root classes
followed by retained hidden locals. -/
noncomputable def rootOuterEquiv
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (anchorRoot : selection.val.anchor = source.val.diagram.root)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.val.boundary) :
    FiniteEquiv
      (Fin (retainedAnchorWires source.val.diagram selection).length)
      (Fin (rootOuterWires source selection).length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin source.val.diagram.wireCount))
    (retainedAnchorWires source.val.diagram selection)
    (rootOuterWires source selection)
    (retainedAnchorWires_nodup source.val.diagram selection)
    (rootOuterWires_nodup source selection)
    (fun wire => by
      simpa using (retainedAnchorWires_mem_iff_rootOuterWires source selection
        anchorRoot boundaryDisjoint wire).symm)

theorem rootOuterEquiv_spec
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (anchorRoot : selection.val.anchor = source.val.diagram.root)
    (boundaryDisjoint :
      selection.val.explicitWires.Disjoint source.val.boundary)
    (index : Fin
      (retainedAnchorWires source.val.diagram selection).length) :
    (rootOuterWires source selection).get
        (rootOuterEquiv source selection anchorRoot boundaryDisjoint index) =
      (retainedAnchorWires source.val.diagram selection).get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin source.val.diagram.wireCount))
    (retainedAnchorWires source.val.diagram selection)
    (rootOuterWires source selection)
    (retainedAnchorWires_nodup source.val.diagram selection)
    (rootOuterWires_nodup source selection)
    (fun wire => by
      simpa using (retainedAnchorWires_mem_iff_rootOuterWires source selection
        anchorRoot boundaryDisjoint wire).symm) index

noncomputable def rootLeaf
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root) :
    Concrete.Splice.Region.ContextPath.CompilerLeaf source.diagram.val
      selection.val.anchor
      (.here (Concrete.Elaboration.finishRegion source.diagram.val
        ([] : Concrete.Elaboration.WireContext source.diagram.val)
        source.diagram.val.root
        (Concrete.Splice.Input.compiledSpliceClosedRootItems
          source.diagram).items)) := by
  rw [anchorRoot]
  exact Concrete.Splice.Input.compiledSpliceClosedRootLeaf source.diagram

theorem rootAnchorLocal_eq
    {arity : Nat}
    (source : Concrete.State arity)
    (selection : CheckedSelection source.diagram.val)
    (anchorRoot : selection.val.anchor = source.diagram.val.root)
    (layout : FragmentLayout source.diagram.val selection)
    {fragmentRels : RelCtx}
    (fragmentContext : Concrete.Elaboration.WireContext
      (source.diagram.val.extractDiagramRaw selection layout))
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (source.diagram.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration
        (source.diagram.val.extractDiagramRaw selection layout)
        fragmentBinders layout.bodyContainer)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (fragmentItems : ItemSeq fragmentContext.length fragmentRels)
    {target : Fin source.diagram.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute source.diagram.val
      selection.val.anchor target path)
    (result : SourceFactorResult source.diagram selection layout
      (rootLeaf source selection anchorRoot)
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route) :
    result.anchorLocal =
      (retainedAnchorWires source.diagram.val selection).length := by
  have lengthEq := result.route_alignment.retainedLength
  simpa [retainedContext, rootLeaf] using lengthEq.symm

section RootFactor

variable {arity : Nat}
variable (source : Concrete.State arity)
variable (selection : CheckedSelection source.diagram.val)
variable (anchorRoot : selection.val.anchor = source.diagram.val.root)
variable (boundaryDisjoint :
  selection.val.explicitWires.Disjoint source.checked.val.boundary)
variable (layout : FragmentLayout source.diagram.val selection)
variable {fragmentRels : RelCtx}
variable (fragmentContext : Concrete.Elaboration.WireContext
  (source.diagram.val.extractDiagramRaw selection layout))
variable (fragmentBinders : Concrete.Elaboration.BinderContext
  (source.diagram.val.extractDiagramRaw selection layout) fragmentRels)
variable (fragmentEnumeration :
  Concrete.Elaboration.BinderContext.Enumeration
    (source.diagram.val.extractDiagramRaw selection layout)
    fragmentBinders layout.bodyContainer)
variable (fragmentExact : fragmentContext.Exact layout.bodyContainer)
variable (fragmentItems : ItemSeq fragmentContext.length fragmentRels)
variable {target : Fin source.diagram.val.regionCount} {path : List Nat}
variable (route : Concrete.Splice.RegionRoute source.diagram.val
  selection.val.anchor target path)
variable (result : SourceFactorResult source.diagram selection layout
  (rootLeaf source selection anchorRoot)
  fragmentContext fragmentBinders fragmentEnumeration fragmentExact
  fragmentItems route)

theorem ancestorLength_eq :
    (rootLeaf source selection anchorRoot).inheritedWires.length +
        result.anchorLocal =
      (retainedAnchorWires source.diagram.val selection).length := by
  have inheritedZero :
      (rootLeaf source selection anchorRoot).inheritedWires.length = 0 := by
    simpa [Region.ContextPath.toFocus] using
      (rootLeaf source selection anchorRoot).inheritedLength
  rw [inheritedZero, Nat.zero_add]
  exact rootAnchorLocal_eq source selection anchorRoot layout fragmentContext
    fragmentBinders fragmentEnumeration fragmentExact fragmentItems route
    result

/-- The route's retained ancestor carrier in exposed-first, hidden-second
root order. -/
noncomputable def ancestorWire : FiniteEquiv
    (Fin ((rootLeaf source selection anchorRoot).inheritedWires.length +
      result.anchorLocal))
    (Fin (rootOuterWires source.checked selection).length) :=
  (FiniteEquiv.finCast (ancestorLength_eq source selection anchorRoot layout
    fragmentContext fragmentBinders fragmentEnumeration fragmentExact
    fragmentItems route result)).trans
      (rootOuterEquiv source.checked selection anchorRoot boundaryDisjoint)

theorem rootOuterLength_eq :
    (rootOuterWires source.checked selection).length =
      source.checked.elaborate.externalClasses +
        (retainedHiddenWires source.checked selection).length := by
  simp [rootOuterWires]

/-- Canonical recursive alignment of the retained route after moving its
ancestor carrier into open-root order. -/
noncomputable def routeAlignment :=
  (RegionIso.renameWiresEquiv
    ((Region.mk 0 result.route_alignment.retainedItems).castWiresEq
      result.route_alignment.retainedLength)
    (ancestorWire source selection anchorRoot boundaryDisjoint layout
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route result)).alignContextPath
        result.route_alignment.factoredWitness

/-- The routed retained witness in the open-root external/local split. -/
noncomputable def routedWitness :=
  (routeAlignment source selection anchorRoot boundaryDisjoint layout
    fragmentContext fragmentBinders fragmentEnumeration fragmentExact
    fragmentItems route result).targetWitness.castWiresEq
      (rootOuterLength_eq source selection)

/-- The selected factor in the open-root external/local split. -/
noncomputable def selected : Region
    (source.checked.elaborate.externalClasses +
      (retainedHiddenWires source.checked selection).length) [] :=
  (result.selected.renameWires
    (ancestorWire source selection anchorRoot boundaryDisjoint layout
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route result)).castWiresEq
        (rootOuterLength_eq source selection)

/-- Root selection has no enclosing recursive frame. -/
def outer : DiagramContext
    source.checked.elaborate.externalClasses
    source.checked.elaborate.externalClasses [] [] :=
  .hole

/-- Route-derived descendant context after canonical open-root alignment. -/
noncomputable def descendant :=
  (routedWitness source selection anchorRoot boundaryDisjoint layout
    fragmentContext fragmentBinders fragmentEnumeration fragmentExact
    fragmentItems route result).toFocus.context

/-- Route-derived remainder after canonical open-root alignment. -/
noncomputable def remainder :=
  (routedWitness source selection anchorRoot boundaryDisjoint layout
    fragmentContext fragmentBinders fragmentEnumeration fragmentExact
    fragmentItems route result).toFocus.body

/-- Base-ready root source body. Exposed classes remain inherited, retained
hidden wires are rebound once at the anchor, and selected explicit wires stay
local to the selected factor. -/
noncomputable def factorBody : Region
    source.checked.elaborate.externalClasses [] :=
  (outer source).fill
    (Region.adjoinAt (retainedHiddenWires source.checked selection).length
      (.nil : ItemSeq
        (source.checked.elaborate.externalClasses +
          (retainedHiddenWires source.checked selection).length) [])
      ((selected source selection anchorRoot boundaryDisjoint layout
          fragmentContext fragmentBinders fragmentEnumeration fragmentExact
          fragmentItems route result).conjoin
        ((descendant source selection anchorRoot boundaryDisjoint layout
          fragmentContext fragmentBinders fragmentEnumeration fragmentExact
          fragmentItems route result).fill
            (remainder source selection anchorRoot boundaryDisjoint layout
              fragmentContext fragmentBinders fragmentEnumeration
              fragmentExact fragmentItems route result))))

/-- Operation-specific source certificate consumed verbatim by the root
branch of iteration refinement. -/
structure Certificate where
  source_iso : OpenDiagramIso
    (source.checked.elaborate.castArity source.boundary_length)
    ((source.checked.elaborate.castArity source.boundary_length).withBody
      ((factorBody source selection anchorRoot boundaryDisjoint layout
          fragmentContext fragmentBinders fragmentEnumeration fragmentExact
          fragmentItems route result).castWiresEq
        (OpenDiagram.castArity_externalClasses source.checked.elaborate
          source.boundary_length).symm))

noncomputable def complete :
    Certificate source selection anchorRoot boundaryDisjoint layout
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route result := by
  let openCompiled :=
    Concrete.Splice.Input.compiledSpliceOpenRootItems source.checked
  let closedCompiled :=
    Concrete.Splice.Input.compiledSpliceClosedRootItems source.diagram
  let closedOpenIso :=
    Concrete.compiledOpenRootItemsIsoFromExactContext
      source.checked
      (Concrete.Elaboration.exactScopeWires source.diagram.val
        source.diagram.val.root)
      (Concrete.Elaboration.closedRootWires_exact source.diagram.property)
      closedCompiled.computation openCompiled.computation
  have bodyIso : RegionIso
      (FiniteEquiv.refl (Fin source.checked.elaborate.externalClasses)) []
      source.checked.elaborate.body
      (factorBody source selection anchorRoot boundaryDisjoint layout
        fragmentContext fragmentBinders fragmentEnumeration fragmentExact
        fragmentItems route result) := by
    generalize targetEq :
      (sourceFactorTargetRegion source.diagram selection
        (rootLeaf source selection anchorRoot) route result.anchorLocal
        result.selected result.route_alignment) = factorTarget
    let sourceFactorIso : RegionIso
        (FiniteEquiv.finCast
          (rootLeaf source selection anchorRoot).inheritedLength.symm) []
        (Concrete.Elaboration.finishRegion source.diagram.val
          ([] : Concrete.Elaboration.WireContext source.diagram.val)
          source.diagram.val.root closedCompiled.items)
        factorTarget :=
      Eq.mp (congrArg (fun target => RegionIso
        (FiniteEquiv.finCast
          (rootLeaf source selection anchorRoot).inheritedLength.symm) []
        (Concrete.Elaboration.finishRegion source.diagram.val
          ([] : Concrete.Elaboration.WireContext source.diagram.val)
          source.diagram.val.root closedCompiled.items)
        target) targetEq) result.source_iso
    have factorTargetLocal : factorTarget.localCount =
        (retainedAnchorWires source.diagram.val selection).length +
          selection.val.explicitWires.length := by
      rw [← targetEq]
      exact sourceFactorTargetRegion_localWires source.diagram selection
        (rootLeaf source selection anchorRoot) route result.anchorLocal
        result.selected result.route_alignment result.selected_local
    have sourceLocalEq : sourceFactorIso.localEquivCast
        (anchorBody_localWires source.diagram selection
          (rootLeaf source selection anchorRoot)) factorTargetLocal =
        (anchorLocalEquiv source.diagram.val selection).symm := by
      have transported := RegionIso.localEquivCast_castEndpoints
        result.source_iso rfl targetEq
        (anchorBody_localWires source.diagram selection
          (rootLeaf source selection anchorRoot))
        (sourceFactorTargetRegion_localWires source.diagram selection
          (rootLeaf source selection anchorRoot) route result.anchorLocal
          result.selected result.route_alignment result.selected_local)
        (anchorBody_localWires source.diagram selection
          (rootLeaf source selection anchorRoot)) factorTargetLocal
      calc
        _ = result.source_iso.localEquivCast
            (anchorBody_localWires source.diagram selection
              (rootLeaf source selection anchorRoot))
            (sourceFactorTargetRegion_localWires source.diagram selection
              (rootLeaf source selection anchorRoot) route result.anchorLocal
              result.selected result.route_alignment result.selected_local) := by
              simpa [sourceFactorIso] using transported
        _ = _ := result.source_local
    cases isoEq : sourceFactorIso with
    | @mk sourceWires targetWires sourceLocal targetLocal ambient targetRels
        sourceItems targetItems localEquiv factorItems =>
        have sourceFactorLocal : sourceFactorIso.localEquiv = localEquiv := by
          exact congrArg RegionIso.localEquiv isoEq
        let sourceCastEq :=
          Concrete.Elaboration.WireContext.length_extend
            ([] : Concrete.Elaboration.WireContext source.diagram.val)
            source.diagram.val.root
        let sourceCastWire := FiniteEquiv.finCast sourceCastEq
        have sourceCastItems : ItemSeqIso sourceCastWire []
            closedCompiled.items
            (closedCompiled.items.castWiresEq sourceCastEq) := by
          rw [ItemSeq.castWiresEq_eq_renameWires]
          exact ItemSeqIso.renameWiresEquiv closedCompiled.items sourceCastWire
        have closedFactorItems := sourceCastItems.trans factorItems
        have openFactorItems := closedOpenIso.symm.trans closedFactorItems
        have targetLocalEq : targetLocal =
            (retainedAnchorWires source.diagram.val selection).length +
              selection.val.explicitWires.length := by
          simpa [Region.localCount] using factorTargetLocal
        subst targetLocal
        let exactScopeLengthEq :
            (Concrete.Elaboration.exactScopeWires source.diagram.val
              source.diagram.val.root).length =
            (Concrete.Elaboration.exactScopeWires source.diagram.val
              selection.val.anchor).length := by
          rw [anchorRoot]
        let canonicalLocal :=
          (FiniteEquiv.finCast exactScopeLengthEq).trans
            (anchorLocalEquiv source.diagram.val selection).symm
        have localEq : localEquiv = canonicalLocal := by
          apply FiniteEquiv.ext
          intro index
          have applied := congrArg
            (fun equivalence => equivalence (Fin.cast exactScopeLengthEq index))
            sourceLocalEq
          change (sourceFactorIso.localEquivCast
              (anchorBody_localWires source.diagram selection
                (rootLeaf source selection anchorRoot)) factorTargetLocal)
              (Fin.cast
                (anchorBody_localWires source.diagram selection
                  (rootLeaf source selection anchorRoot)) index) = _ at applied
          have projected := RegionIso.localEquivCast_apply sourceFactorIso
            (anchorBody_localWires source.diagram selection
              (rootLeaf source selection anchorRoot)) factorTargetLocal index
          have combined := projected.symm.trans applied
          rw [sourceFactorLocal] at combined
          simpa [canonicalLocal, RegionIso.localEquivCast,
            FiniteEquiv.finCast] using combined
        let targetSourceEq :
            (rootLeaf source selection anchorRoot).inheritedWires.length +
                ((retainedAnchorWires source.diagram.val selection).length +
                  selection.val.explicitWires.length) =
              ((rootLeaf source selection anchorRoot).inheritedWires.length +
                  result.anchorLocal) +
                selection.val.explicitWires.length := by
          rw [rootAnchorLocal_eq source selection anchorRoot layout
            fragmentContext fragmentBinders fragmentEnumeration fragmentExact
            fragmentItems route result]
          omega
        let targetOpenEq :
            (rootOuterWires source.checked selection).length +
                selection.val.explicitWires.length =
              source.checked.elaborate.externalClasses +
                ((retainedHiddenWires source.checked selection).length +
                  selection.val.explicitWires.length) := by
          rw [rootOuterLength_eq source selection]
          omega
        let targetWire : FiniteEquiv
            (Fin ((rootLeaf source selection anchorRoot).inheritedWires.length +
              ((retainedAnchorWires source.diagram.val selection).length +
                selection.val.explicitWires.length)))
            (Fin (source.checked.elaborate.externalClasses +
              ((retainedHiddenWires source.checked selection).length +
                selection.val.explicitWires.length))) :=
          (FiniteEquiv.finCast targetSourceEq).trans
            ((extendWireEquiv
              (ancestorWire source selection anchorRoot boundaryDisjoint layout
                fragmentContext fragmentBinders fragmentEnumeration
                fragmentExact fragmentItems route result)
              (FiniteEquiv.refl
                (Fin selection.val.explicitWires.length))).trans
              (FiniteEquiv.finCast targetOpenEq))
        let computedWire :=
          ((Concrete.exactContextToOpenRootWireEquiv source.checked
            (Concrete.Elaboration.exactScopeWires source.diagram.val
              source.diagram.val.root)
            (Concrete.Elaboration.closedRootWires_exact
              source.diagram.property)).symm.trans
            (sourceCastWire.trans
              (extendWireEquiv
                (FiniteEquiv.finCast
                  (rootLeaf source selection anchorRoot).inheritedLength.symm)
                localEquiv))).trans targetWire
        have targetOpenItems :=
          ItemSeqIso.renameWiresEquiv targetItems targetWire
        have sourceTargetItems : ItemSeqIso computedWire [] openCompiled.items
            (targetItems.renameWires targetWire) := by
          simpa only [computedWire] using
            openFactorItems.trans targetOpenItems
        let sourceOpenEq : source.checked.val.rootWires.length =
            source.checked.elaborate.externalClasses +
              source.checked.val.hiddenWires.length := by
          simp [Concrete.OpenDiagram.rootWires]
        let canonicalWire := Concrete.Elaboration.castFinEquiv sourceOpenEq rfl
          (extendWireEquiv
            (FiniteEquiv.refl
              (Fin source.checked.elaborate.externalClasses))
            (rootLocalEquiv source.checked selection anchorRoot
              boundaryDisjoint).symm)
        let targetList : List (Fin source.checked.val.diagram.wireCount) :=
          rootOuterWires source.checked selection ++
            (by
              simpa only [Concrete.State.diagram] using
                selection.val.explicitWires)
        let factorList : List (Fin source.diagram.val.wireCount) :=
          retainedAnchorWires source.diagram.val selection ++
            selection.val.explicitWires
        let targetListEq : targetList.length =
            source.checked.elaborate.externalClasses +
              ((retainedHiddenWires source.checked selection).length +
                selection.val.explicitWires.length) := by
          simpa [targetList] using targetOpenEq
        have inheritedZero :
            (rootLeaf source selection anchorRoot).inheritedWires.length = 0 := by
          simpa [Region.ContextPath.toFocus] using
            (rootLeaf source selection anchorRoot).inheritedLength
        let factorListEq :
            (rootLeaf source selection anchorRoot).inheritedWires.length +
                ((retainedAnchorWires source.diagram.val selection).length +
                  selection.val.explicitWires.length) = factorList.length := by
          simp [factorList, inheritedZero]
        have targetWireSpec (index : Fin
            ((rootLeaf source selection anchorRoot).inheritedWires.length +
              ((retainedAnchorWires source.diagram.val selection).length +
                selection.val.explicitWires.length))) :
            targetList.get
                (Fin.cast targetListEq.symm (targetWire index)) =
              factorList.get (Fin.cast factorListEq index) := by
          let prepared := Fin.cast targetSourceEq index
          have indexEq : Fin.cast targetSourceEq.symm prepared = index := by
            apply Fin.ext
            rfl
          rw [← indexEq]
          refine Fin.addCases (fun outerIndex => ?_)
            (fun explicitIndex => ?_) prepared
          · have outerSpec := rootOuterEquiv_spec source.checked selection
              anchorRoot boundaryDisjoint
              (Fin.cast
                (ancestorLength_eq source selection anchorRoot layout
                  fragmentContext fragmentBinders fragmentEnumeration
                  fragmentExact fragmentItems route result)
                outerIndex)
            calc
              _ = (rootOuterWires source.checked selection).get
                  (ancestorWire source selection anchorRoot boundaryDisjoint
                    layout fragmentContext fragmentBinders
                    fragmentEnumeration fragmentExact fragmentItems route
                    result outerIndex) := by
                    simp [targetList, targetWire, extendWireEquiv,
                      FiniteEquiv.finCast]
              _ = (retainedAnchorWires source.diagram.val selection).get
                  (Fin.cast
                    (ancestorLength_eq source selection anchorRoot layout
                      fragmentContext fragmentBinders fragmentEnumeration
                      fragmentExact fragmentItems route result)
                    outerIndex) := by
                    simpa [ancestorWire, FiniteEquiv.trans_apply,
                      FiniteEquiv.finCast, Concrete.State.diagram] using
                        outerSpec
              _ = _ := by
                have bound : outerIndex.val <
                    (retainedAnchorWires source.diagram.val selection).length := by
                  simpa [ancestorLength_eq source selection anchorRoot layout
                    fragmentContext fragmentBinders fragmentEnumeration
                    fragmentExact fragmentItems route result] using
                      outerIndex.isLt
                let retainedIndex : Fin
                    (retainedAnchorWires source.diagram.val selection).length :=
                  ⟨outerIndex.val, bound⟩
                have retainedIndexEq :
                    Fin.cast
                      (ancestorLength_eq source selection anchorRoot layout
                        fragmentContext fragmentBinders fragmentEnumeration
                        fragmentExact fragmentItems route result)
                      outerIndex = retainedIndex := by
                  apply Fin.ext
                  rfl
                rw [retainedIndexEq]
                exact (Concrete.Elaboration.get_append_castAdd
                  (retainedAnchorWires source.diagram.val selection)
                  selection.val.explicitWires retainedIndex).symm
          · have prefixLength := ancestorLength_eq source selection anchorRoot
                layout fragmentContext fragmentBinders fragmentEnumeration
                fragmentExact fragmentItems route result
            simp [targetList, factorList, targetWire, extendWireEquiv,
              FiniteEquiv.finCast, prefixLength]
            rfl
        have targetListNodup : targetList.Nodup := by
          dsimp only [targetList]
          rw [List.nodup_append]
          refine ⟨rootOuterWires_nodup source.checked selection,
            selection.property.explicitWires_nodup, ?_⟩
          intro outer outerMember explicit explicitMember equality
          subst explicit
          rw [rootOuterWires, List.mem_append] at outerMember
          rcases outerMember with exposed | retained
          · exact (boundaryDisjoint outer explicitMember)
              ((Concrete.OpenDiagram.mem_exposedWires source.checked.val
                outer).mp exposed)
          · have facts := List.mem_filter.mp retained
            simp [explicitMember] at facts
        have wholeWireEq : computedWire = canonicalWire := by
          apply FiniteEquiv.ext
          intro index
          apply Fin.ext
          let exactTransport :=
            Concrete.exactContextToOpenRootWireEquiv source.checked
              (Concrete.Elaboration.exactScopeWires source.diagram.val
                source.diagram.val.root)
              (Concrete.Elaboration.closedRootWires_exact
                source.diagram.property)
          let exactIndex := exactTransport.symm index
          let flatIndex :=
            (anchorLocalEquiv source.diagram.val selection).symm
              (Fin.cast exactScopeLengthEq exactIndex)
          let preFactorWire := sourceCastWire.trans
            (extendWireEquiv
              (FiniteEquiv.finCast
                (rootLeaf source selection anchorRoot).inheritedLength.symm)
              localEquiv)
          have sourceIndexEq : sourceCastWire exactIndex =
              Fin.natAdd 0 exactIndex := by
            dsimp only [sourceCastWire]
            apply Fin.ext
            simp [FiniteEquiv.finCast]
          have preFactorEq : preFactorWire exactIndex =
              Fin.natAdd
                (rootLeaf source selection anchorRoot).inheritedWires.length
                flatIndex := by
            dsimp only [preFactorWire]
            rw [FiniteEquiv.trans_apply, sourceIndexEq, localEq]
            calc
              _ = Fin.natAdd
                  (rootLeaf source selection anchorRoot).inheritedWires.length
                  (canonicalLocal exactIndex) :=
                extendWireEquiv_local
                  (FiniteEquiv.finCast
                    (rootLeaf source selection anchorRoot).inheritedLength.symm)
                  canonicalLocal exactIndex
              _ = _ := by
                apply Fin.ext
                rfl
          have factorIndexEq :
              Fin.cast factorListEq (preFactorWire exactIndex) =
                Fin.cast (by simp [factorList]) flatIndex := by
            rw [preFactorEq]
            apply Fin.ext
            simp [inheritedZero]
          have factorValue :
              factorList.get
                  (Fin.cast factorListEq (preFactorWire exactIndex)) =
                (Concrete.Elaboration.exactScopeWires source.diagram.val
                  source.diagram.val.root).get exactIndex := by
            rw [factorIndexEq]
            have localSpec := anchorLocalEquiv_spec source.diagram.val
              selection flatIndex
            have inverse := (anchorLocalEquiv source.diagram.val selection)
              |>.right_inv (Fin.cast exactScopeLengthEq exactIndex)
            have flatForward :
                anchorLocalEquiv source.diagram.val selection flatIndex =
                  Fin.cast exactScopeLengthEq exactIndex := by
              simpa only [flatIndex] using inverse
            rw [flatForward] at localSpec
            simpa [factorList, exactScopeLengthEq, anchorRoot] using
              localSpec.symm
          have exactValue :
              (Concrete.Elaboration.exactScopeWires source.diagram.val
                  source.diagram.val.root).get exactIndex =
                source.checked.val.rootWires.get index := by
            have transportSpec :=
              Concrete.exactContextToOpenRootWireEquiv_spec source.checked
                (Concrete.Elaboration.exactScopeWires source.diagram.val
                  source.diagram.val.root)
                (Concrete.Elaboration.closedRootWires_exact
                  source.diagram.property) exactIndex
            have inverse := exactTransport.right_inv index
            have exactForward : exactTransport exactIndex = index := by
              simpa only [exactIndex] using inverse
            change source.checked.val.rootWires.get
                (exactTransport exactIndex) = _ at transportSpec
            rw [exactForward] at transportSpec
            exact transportSpec.symm
          have computedValue :
              targetList.get
                  (Fin.cast targetListEq.symm (computedWire index)) =
                source.checked.val.rootWires.get index := by
            change targetList.get
                (Fin.cast targetListEq.symm
                  (targetWire (preFactorWire exactIndex))) = _
            exact (targetWireSpec (preFactorWire exactIndex)).trans
              (factorValue.trans exactValue)
          have canonicalValue :
              targetList.get
                  (Fin.cast targetListEq.symm (canonicalWire index)) =
                source.checked.val.rootWires.get index := by
            let sourcePosition := Fin.cast sourceOpenEq index
            have indexEq : Fin.cast sourceOpenEq.symm sourcePosition = index := by
              apply Fin.ext
              rfl
            rw [← indexEq]
            refine Fin.addCases (fun exposedIndex => ?_)
              (fun hiddenIndex => ?_) sourcePosition
            · simp [canonicalWire, Concrete.Elaboration.castFinEquiv,
                targetList, rootOuterWires,
                Concrete.OpenDiagram.rootWires, extendWireEquiv]
            · let targetLocal :=
                (rootLocalEquiv source.checked selection anchorRoot
                  boundaryDisjoint).symm hiddenIndex
              have localSpec := rootLocalEquiv_spec source.checked selection
                anchorRoot boundaryDisjoint targetLocal
              have inverse :=
                (rootLocalEquiv source.checked selection anchorRoot
                  boundaryDisjoint).right_inv hiddenIndex
              have forward :
                  rootLocalEquiv source.checked selection anchorRoot
                      boundaryDisjoint targetLocal = hiddenIndex := by
                simpa only [targetLocal] using inverse
              rw [forward] at localSpec
              simpa [canonicalWire, Concrete.Elaboration.castFinEquiv,
                targetList, rootOuterWires,
                Concrete.OpenDiagram.rootWires, extendWireEquiv,
                targetLocal] using localSpec.symm
          have positions :
              (Fin.cast targetListEq.symm (computedWire index)).val =
                (Fin.cast targetListEq.symm (canonicalWire index)).val := by
            exact (List.getElem_inj targetListNodup).mp (by
              simpa only [List.get_eq_getElem] using
                computedValue.trans canonicalValue.symm)
          exact positions
        have canonicalItems : ItemSeqIso canonicalWire [] openCompiled.items
            (targetItems.renameWires targetWire) := by
          rw [← wholeWireEq]
          exact sourceTargetItems
        let targetBody : Region source.checked.elaborate.externalClasses [] :=
          .mk ((retainedHiddenWires source.checked selection).length +
              selection.val.explicitWires.length)
            (targetItems.renameWires targetWire)
        let rawBodyIso : RegionIso
            (FiniteEquiv.refl
              (Fin source.checked.elaborate.externalClasses)) []
            (.mk source.checked.val.hiddenWires.length
              (openCompiled.items.castWiresEq sourceOpenEq)) targetBody :=
          Concrete.Elaboration.regionIso_of_cast sourceOpenEq rfl
            (FiniteEquiv.refl
              (Fin source.checked.elaborate.externalClasses))
            (rootLocalEquiv source.checked selection anchorRoot
              boundaryDisjoint).symm openCompiled.items
            (targetItems.renameWires targetWire) canonicalItems
        generalize selectedEq : result.selected = selectedRegion
        cases selectedRegion with
        | mk selectedLocal selectedItems =>
          have selectedLocalEq : selectedLocal =
              selection.val.explicitWires.length := by
            obtain ⟨items, shape⟩ := result.selected_local
            rw [selectedEq] at shape
            injection shape
          subst selectedLocal
          have targetShape := targetEq
          rw [selectedEq] at targetShape
          simp only [sourceFactorTargetRegion] at targetShape
          rw [result.route_alignment.factoredWitness.toFocus.rebuild]
            at targetShape
          simp only [Region.conjoin, Region.adjoinAt,
            Region.castWiresEq_mk,
            ItemSeq.castWiresEq_eq_renameWires,
            ItemSeq.renameWires_append, Nat.add_zero] at targetShape
          injection targetShape with outerEq relsEq localWiresEq targetItemsEq
          have targetItemsEq' := ItemSeq.castWiresEq_eq_of_heq
            (congrArg
              (fun count =>
                (rootLeaf source selection anchorRoot).inheritedWires.length +
                  count)
              localWiresEq) targetItemsEq
          have targetBodyEq : targetBody =
              factorBody source selection anchorRoot boundaryDisjoint layout
                fragmentContext fragmentBinders fragmentEnumeration
                fragmentExact fragmentItems route result := by
            change targetBody =
              (outer source).fill
                (Region.adjoinAt
                  (retainedHiddenWires source.checked selection).length
                  (.nil : ItemSeq
                    (source.checked.elaborate.externalClasses +
                      (retainedHiddenWires source.checked selection).length)
                    [])
                  ((selected source selection anchorRoot boundaryDisjoint
                      layout fragmentContext fragmentBinders
                      fragmentEnumeration fragmentExact fragmentItems route
                      result).conjoin
                    ((routedWitness source selection anchorRoot
                      boundaryDisjoint layout fragmentContext fragmentBinders
                      fragmentEnumeration fragmentExact fragmentItems route
                      result).toFocus.context.fill
                      (routedWitness source selection anchorRoot
                        boundaryDisjoint layout fragmentContext
                        fragmentBinders fragmentEnumeration fragmentExact
                        fragmentItems route result).toFocus.body)))
            rw [(routedWitness source selection anchorRoot boundaryDisjoint
              layout fragmentContext fragmentBinders fragmentEnumeration
              fragmentExact fragmentItems route result).toFocus.rebuild]
            dsimp only [targetBody, outer, selected, routedWitness]
            rw [← targetItemsEq']
            rw [selectedEq]
            simp only [DiagramContext.fill, Region.adjoinAt, Region.conjoin,
              Region.castWiresEq_mk, Region.renameWires,
              ItemSeq.castWiresEq_eq_renameWires,
              ItemSeq.renameWires_append, ItemSeq.renameWires_comp,
              ItemSeq.renameWires, ItemSeq.nil_append, Nat.add_zero]
            apply congrArg (Region.mk
              ((retainedHiddenWires source.checked selection).length +
                selection.val.explicitWires.length))
            congr 1
            · apply congrArg (fun wire => selectedItems.renameWires wire)
              funext index
              refine Fin.addCases (fun inherited => ?_)
                (fun explicit => ?_) index
              · apply Fin.ext
                simp [targetWire, FiniteEquiv.trans_apply,
                  FiniteEquiv.finCast, extendWireEquiv,
                  Region.adjoinMaterialWire, Region.conjoinLeftWire,
                  extendWireRenaming, Function.comp_apply,
                  Fin.addCases_castAdd]
              · apply Fin.ext
                simp [targetWire, FiniteEquiv.trans_apply,
                  FiniteEquiv.finCast, extendWireEquiv,
                  Region.adjoinMaterialWire, Region.conjoinLeftWire,
                  extendWireRenaming, Function.comp_apply,
                  Fin.addCases_natAdd]
                simp [rootOuterWires]
            · apply congrArg (fun wire =>
                result.route_alignment.retainedItems.renameWires wire)
              funext index
              apply Fin.ext
              simp [targetWire, FiniteEquiv.trans_apply,
                FiniteEquiv.finCast, extendWireEquiv,
                Region.adjoinMaterialWire, Region.conjoinRightWire,
                extendWireRenaming, Function.comp_apply,
                Fin.addCases_zero]
          rw [openCompiled.elaborate_body, ← targetBodyEq]
          simpa [Concrete.Elaboration.finishRoot] using rawBodyIso
  let baseIso : OpenDiagramIso source.checked.elaborate
      (source.checked.elaborate.withBody
        (factorBody source selection anchorRoot boundaryDisjoint layout
          fragmentContext fragmentBinders fragmentEnumeration fragmentExact
          fragmentItems route result)) :=
    OpenDiagram.withBody_iso bodyIso
  let castIso := OpenDiagramIso.castArity source.boundary_length baseIso
  refine ⟨?_⟩
  rw [← OpenDiagram.castArity_withBody]
  exact castIso

end RootFactor

end VisualProof.Refinement.Implementation.IterationRootSourceFactor
