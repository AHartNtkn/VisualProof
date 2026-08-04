import VisualProof.Rule.Soundness.Comprehension.InstantiationTerminalTrace

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace InstantiationSemantic

private theorem filterFin_survivor_origin
    (domain : SurvivorDomain size)
    (sourceP : Fin size → Bool)
    (targetP : domain.Carrier → Bool)
    (predicateEq : ∀ index, targetP index = sourceP (domain.origin index))
    (subset : ∀ original, sourceP original = true →
      domain.survives original = true) :
    (filterFin targetP).map domain.origin = filterFin sourceP := by
  have enumerationEq :
      (allFin domain.count).map domain.origin = domain.enumeration := by
    rw [allFin_eq_finRange, List.finRange, List.map_ofFn]
    change List.ofFn (fun index ↦ domain.enumeration.get index) =
      domain.enumeration
    exact List.ofFn_getElem
  unfold filterFin
  have filterEq :
      List.filter targetP (allFin domain.count) =
        List.filter (sourceP ∘ domain.origin) (allFin domain.count) := by
    apply congrArg (fun predicate ↦
      List.filter predicate (allFin domain.count))
    funext index
    exact predicateEq index
  rw [filterEq, ← List.filter_map, enumerationEq]
  change List.filter sourceP
      (List.filter domain.survives (allFin size)) =
    List.filter sourceP (allFin size)
  rw [List.filter_filter]
  apply congrArg (fun predicate ↦ List.filter predicate (allFin size))
  funext original
  cases selected : sourceP original with
  | false => simp [selected]
  | true => simp [selected, subset original selected]

/-- Forget the dense node compaction performed after all instantiation copies,
while leaving the unchanged region carrier untouched. -/
def dropOccurrenceOrigin
    (state : InstantiationState origin parameterCount proxyCount) :
    ConcreteElaboration.LocalOccurrence
        (dropInstantiationAtomsRaw state).regionCount
        (dropInstantiationAtomsRaw state).nodeCount →
      ConcreteElaboration.LocalOccurrence state.diagram.val.regionCount
        state.diagram.val.nodeCount
  | .node node => .node ((instantiationAtomDomain state).origin node)
  | .child region => .child region

/-- Boolean occurrence predicate selecting precisely the nodes retained by
post-copy compaction; region occurrences are never removed. -/
def dropOccurrenceSurvives
    (state : InstantiationState origin parameterCount proxyCount) :
    ConcreteElaboration.LocalOccurrence state.diagram.val.regionCount
      state.diagram.val.nodeCount → Bool
  | .node node => (instantiationAtomDomain state).survives node
  | .child _ => true

/-- The dropped diagram's authoritative compiler traversal is exactly the
copied diagram's traversal with executor-processed atoms removed.  Stable
finite enumeration preserves the order of every surviving node and every
child region. -/
theorem dropInstantiationAtomsRaw_localOccurrences_origin
    (state : InstantiationState origin parameterCount proxyCount)
    (region : Fin state.diagram.val.regionCount) :
    (ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw state)
        region).map (dropOccurrenceOrigin state) =
      (ConcreteElaboration.localOccurrences state.diagram.val region).filter
        (dropOccurrenceSurvives state) := by
  let domain := instantiationAtomDomain state
  let sourceP : Fin state.diagram.val.nodeCount → Bool := fun node ↦
    decide ((state.diagram.val.nodes node).region = region)
  let survivingP : Fin state.diagram.val.nodeCount → Bool := fun node ↦
    sourceP node && domain.survives node
  let targetP : Fin domain.count → Bool := fun node ↦
    decide (((dropInstantiationAtomsRaw state).nodes node).region = region)
  have predicateEq : ∀ node,
      targetP node = survivingP (domain.origin node) := by
    intro node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true, targetP, survivingP,
      sourceP]
    change (state.diagram.val.nodes (domain.origin node)).region = region ↔
      (state.diagram.val.nodes (domain.origin node)).region = region ∧
        domain.survives (domain.origin node) = true
    simp only [domain.origin_survives, and_true]
  have subset : ∀ node, survivingP node = true →
      domain.survives node = true := by
    intro node selected
    have selected' : sourceP node = true ∧ domain.survives node = true := by
      simpa [survivingP] using selected
    exact selected'.2
  have origins := filterFin_survivor_origin domain survivingP targetP
    predicateEq subset
  have sourceFilter : filterFin survivingP =
      (filterFin sourceP).filter domain.survives := by
    unfold filterFin survivingP
    rw [List.filter_filter]
    apply congrArg (fun predicate ↦
      List.filter predicate (allFin state.diagram.val.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp [and_comm]
  have mappedNodes :
      ((filterFin targetP).map
        (ConcreteElaboration.LocalOccurrence.node
          (regions := state.diagram.val.regionCount))).map
          (dropOccurrenceOrigin state) =
        ((filterFin sourceP).map
          (ConcreteElaboration.LocalOccurrence.node
            (regions := state.diagram.val.regionCount))).filter
          (dropOccurrenceSurvives state) := by
    rw [List.filter_map]
    have predicateEq' :
        dropOccurrenceSurvives state ∘
            (ConcreteElaboration.LocalOccurrence.node
              (regions := state.diagram.val.regionCount)) =
          domain.survives := by
      funext node
      rfl
    rw [predicateEq', ← sourceFilter, ← origins]
    induction filterFin targetP with
    | nil => rfl
    | cons node tail ih =>
        simp only [List.map_cons]
        change ConcreteElaboration.LocalOccurrence.node (domain.origin node) ::
            (tail.map ConcreteElaboration.LocalOccurrence.node).map
              (dropOccurrenceOrigin state) =
          ConcreteElaboration.LocalOccurrence.node (domain.origin node) ::
            (tail.map domain.origin).map
              ConcreteElaboration.LocalOccurrence.node
        exact congrArg
          (fun rest =>
            ConcreteElaboration.LocalOccurrence.node (domain.origin node) ::
              rest) ih
  let children := filterFin fun child : Fin state.diagram.val.regionCount ↦
    decide ((state.diagram.val.regions child).parent? = some region)
  unfold ConcreteElaboration.localOccurrences
  change (((filterFin targetP).map
      (ConcreteElaboration.LocalOccurrence.node
        (regions := state.diagram.val.regionCount))) ++
    children.map (ConcreteElaboration.LocalOccurrence.child
      (nodes := domain.count))).map (dropOccurrenceOrigin state) = _
  rw [List.filter_append]
  have mappedAppend :
      ((((filterFin targetP).map
          (ConcreteElaboration.LocalOccurrence.node
            (regions := state.diagram.val.regionCount))) ++
        (children.map (ConcreteElaboration.LocalOccurrence.child
          (nodes := domain.count)))).map (dropOccurrenceOrigin state)) =
      (((filterFin targetP).map
          (ConcreteElaboration.LocalOccurrence.node
            (regions := state.diagram.val.regionCount))).map
          (dropOccurrenceOrigin state)) ++
        ((children.map (ConcreteElaboration.LocalOccurrence.child
          (nodes := domain.count))).map (dropOccurrenceOrigin state)) := by
    exact List.map_append
  rw [mappedAppend]
  have mappedChildren :
      (children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := domain.count))).map (dropOccurrenceOrigin state) =
      children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := state.diagram.val.nodeCount)) := by
    induction children with
    | nil => rfl
    | cons child tail ih =>
        simp only [List.map_cons]
        change ConcreteElaboration.LocalOccurrence.child child ::
            (tail.map ConcreteElaboration.LocalOccurrence.child).map
              (dropOccurrenceOrigin state) =
          ConcreteElaboration.LocalOccurrence.child child ::
            tail.map ConcreteElaboration.LocalOccurrence.child
        exact congrArg
          (fun rest =>
            ConcreteElaboration.LocalOccurrence.child child :: rest) ih
  have filteredChildren :
      (children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := state.diagram.val.nodeCount))).filter
          (dropOccurrenceSurvives state) =
      children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := state.diagram.val.nodeCount)) := by
    apply List.filter_eq_self.mpr
    intro occurrence member
    obtain ⟨child, _, rfl⟩ := List.mem_map.mp member
    rfl
  change
    ((filterFin targetP).map ConcreteElaboration.LocalOccurrence.node).map
          (dropOccurrenceOrigin state) ++
        (children.map ConcreteElaboration.LocalOccurrence.child).map
          (dropOccurrenceOrigin state) =
      ((filterFin sourceP).map ConcreteElaboration.LocalOccurrence.node).filter
          (dropOccurrenceSurvives state) ++
        (children.map ConcreteElaboration.LocalOccurrence.child).filter
          (dropOccurrenceSurvives state)
  calc
    _ = ((filterFin sourceP).map
          ConcreteElaboration.LocalOccurrence.node).filter
            (dropOccurrenceSurvives state) ++
        (children.map ConcreteElaboration.LocalOccurrence.child).map
          (dropOccurrenceOrigin state) :=
      congrArg
        (fun left => left ++
          (children.map ConcreteElaboration.LocalOccurrence.child).map
            (dropOccurrenceOrigin state)) mappedNodes
    _ = _ := congrArg
      (fun right =>
        ((filterFin sourceP).map
          ConcreteElaboration.LocalOccurrence.node).filter
            (dropOccurrenceSurvives state) ++ right)
      (mappedChildren.trans filteredChildren.symm)

end InstantiationSemantic

end VisualProof.Rule
