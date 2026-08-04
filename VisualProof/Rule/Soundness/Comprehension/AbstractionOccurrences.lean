import VisualProof.Rule.Soundness.Comprehension.AbstractionFrame

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace AbstractionRawTrace

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) =
      (allFin n).map (Fin.castAdd 1) ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun xs : List (Fin (n + 1)) => xs ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  apply Fin.ext
  rfl

private theorem allFin_add (n m : Nat) :
    allFin (n + m) =
      (allFin n).map (Fin.castAdd m) ++
        (allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, allFin, List.map_nil, List.append_nil]
      have hfun : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        apply Fin.ext
        rfl
      rw [hfun, List.map_id]
  | succ m ih =>
      change allFin ((n + m) + 1) = _
      rw [allFin_succ_last (n + m), ih, List.map_append,
        allFin_succ_last m, List.map_append, List.map_map,
        List.append_assoc]
      simp only [List.map_map]
      have hleft :
          (Fin.castAdd 1 ∘ Fin.castAdd m : Fin n → Fin ((n + m) + 1)) =
            Fin.castAdd (m + 1) := by
        funext index
        apply Fin.ext
        rfl
      have hmiddle :
          (Fin.castAdd 1 ∘ Fin.natAdd n : Fin m → Fin ((n + m) + 1)) =
            (Fin.natAdd n ∘ Fin.castAdd 1) := by
        funext index
        apply Fin.ext
        rfl
      have hlast : Fin.last (n + m) = Fin.natAdd n (Fin.last m) := by
        apply Fin.ext
        rfl
      rw [hleft, hmiddle, hlast]
      rfl

/-- Ownership of every surviving source node also survives. -/
theorem nodeOwner_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true) :
    trace.domains.regions.survives (input.val.nodes node).region = true := by
  apply (region_survives_iff input occurrences _).2
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, ownerSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at ownerSelected
  have nodeSelected : node ∈
      (occurrences.get index).selection.selectedNodes :=
    ((occurrences.get index).selection.mem_selectedNodes node).2
      (Or.inr
        (((occurrences.get index).selection.mem_selectedRegions _).1
          ownerSelected))
  exact ((node_survives_iff input occurrences node).1 survives) (by
    rw [abstractionNodes, List.mem_flatMap]
    exact ⟨occurrences.get index, List.get_mem _ _, nodeSelected⟩)

/-- A surviving original node is owned either by the fresh wrap bubble when
it was directly selected by `wrap`, or by the compact image of its original
owner. -/
theorem targetNode_region
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true)
    (expectedOwner : Fin input.val.regionCount)
    (nodeRegion : (input.val.nodes node).region = expectedOwner) :
    (trace.diagram.nodes (trace.targetNode node survives)).region =
      if node ∈ wrap.val.directNodes then trace.bubble
      else trace.regionMap expectedOwner := by
  have result := trace.abstractNode?_targetNode node survives
  unfold abstractNode? at result
  by_cases direct : node ∈ wrap.val.directNodes
  · simp only [direct, if_pos]
    cases shape : input.val.nodes node with
    | term owner freePorts term =>
        simp only [shape, direct, if_pos, Option.map_some] at result
        exact congrArg CNode.region (Option.some.inj result).symm
    | atom owner binder =>
        have binderSurvives := trace.atomBinder_survives node survives owner
          binder shape
        simp only [shape, direct, if_pos,
          trace.domains.regions.index?_index binder binderSurvives,
          Option.map_some] at result
        exact congrArg CNode.region (Option.some.inj result).symm
    | named owner definition arity =>
        simp only [shape, direct, if_pos, Option.map_some] at result
        exact congrArg CNode.region (Option.some.inj result).symm
  · simp only [direct, if_false]
    cases shape : input.val.nodes node with
    | term owner freePorts term =>
        have actualOwnerSurvives :
          trace.domains.regions.survives owner = true := by
          simpa [shape] using trace.nodeOwner_survives node survives
        have ownerEq : expectedOwner = owner := by
          simpa [shape] using nodeRegion.symm
        subst expectedOwner
        simp only [shape, direct, if_false,
          trace.domains.regions.index?_index owner actualOwnerSurvives,
          Option.map_some] at result
        simp only [shape, CNode.region]
        rw [trace.regionMap_of_survives owner actualOwnerSurvives]
        simpa only [targetRegion] using
          congrArg CNode.region (Option.some.inj result).symm
    | atom owner binder =>
        have actualOwnerSurvives :
          trace.domains.regions.survives owner = true := by
          simpa [shape] using trace.nodeOwner_survives node survives
        have ownerEq : expectedOwner = owner := by
          simpa [shape] using nodeRegion.symm
        subst expectedOwner
        have binderSurvives := trace.atomBinder_survives node survives owner
          binder shape
        simp only [shape, direct, if_false,
          trace.domains.regions.index?_index owner actualOwnerSurvives,
          trace.domains.regions.index?_index binder binderSurvives,
          Option.map_some] at result
        simp only [shape, CNode.region]
        rw [trace.regionMap_of_survives owner actualOwnerSurvives]
        simpa only [targetRegion] using
          congrArg CNode.region (Option.some.inj result).symm
    | named owner definition arity =>
        have actualOwnerSurvives :
          trace.domains.regions.survives owner = true := by
          simpa [shape] using trace.nodeOwner_survives node survives
        have ownerEq : expectedOwner = owner := by
          simpa [shape] using nodeRegion.symm
        subst expectedOwner
        simp only [shape, direct, if_false,
          trace.domains.regions.index?_index owner actualOwnerSurvives,
          Option.map_some] at result
        simp only [shape, CNode.region]
        rw [trace.regionMap_of_survives owner actualOwnerSurvives]
        simpa only [targetRegion] using
          congrArg CNode.region (Option.some.inj result).symm

/-- The parent of every surviving non-sheet region survives. -/
theorem regionParent_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child parent : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (childParent : (input.val.regions child).parent? = some parent) :
    trace.domains.regions.survives parent = true := by
  apply (region_survives_iff input occurrences parent).2
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, parentSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at parentSelected
  have parentSelects :=
    ((occurrences.get index).selection.mem_selectedRegions parent).1
      parentSelected
  have parentEncloses : input.val.Encloses parent child := by
    have hpositive := child.isLt
    refine ⟨⟨1, by omega⟩, ?_⟩
    simp [ConcreteDiagram.climb, childParent]
  have childSelected : child ∈
      (occurrences.get index).selection.selectedRegions :=
    ((occurrences.get index).selection.mem_selectedRegions child).2
      (parentSelects.downward input.property parentEncloses)
  exact ((region_survives_iff input occurrences child).1 survives) (by
    rw [abstractionRegions, List.mem_flatMap]
    exact ⟨occurrences.get index, List.get_mem _ _, childSelected⟩)

/-- A surviving direct child is reparented to the fresh wrap bubble exactly
when it is a direct wrap child; otherwise its original parent is compacted. -/
theorem targetRegion_parent
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child parent : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (childParent : (input.val.regions child).parent? = some parent) :
    (trace.diagram.regions (trace.targetRegion child survives)).parent? =
      if child ∈ wrap.val.childRoots then some trace.bubble
      else some (trace.targetRegion parent
        (trace.regionParent_survives child parent survives childParent)) := by
  have result := trace.abstractRegion?_targetRegion child survives
  unfold abstractRegion? at result
  have parentSurvives := trace.regionParent_survives child parent survives
    childParent
  cases shape : input.val.regions child with
  | sheet =>
      rw [shape] at childParent
      contradiction
  | cut actualParent =>
      have actualParentEq : actualParent = parent := by
        rw [shape] at childParent
        exact Option.some.inj childParent
      subst actualParent
      by_cases direct : child ∈ wrap.val.childRoots
      · simp only [shape, direct, if_pos] at result ⊢
        exact congrArg CRegion.parent? (Option.some.inj result).symm
      · simp only [shape, direct, if_false,
          trace.domains.regions.index?_index parent parentSurvives,
          Option.map_some] at result ⊢
        simpa only [targetRegion] using
          congrArg CRegion.parent? (Option.some.inj result).symm
  | bubble actualParent arity =>
      have actualParentEq : actualParent = parent := by
        rw [shape] at childParent
        exact Option.some.inj childParent
      subst actualParent
      by_cases direct : child ∈ wrap.val.childRoots
      · simp only [shape, direct, if_pos] at result ⊢
        exact congrArg CRegion.parent? (Option.some.inj result).symm
      · simp only [shape, direct, if_false,
          trace.domains.regions.index?_index parent parentSurvives,
          Option.map_some] at result ⊢
        simpa only [targetRegion] using
          congrArg CRegion.parent? (Option.some.inj result).symm

/-- Dense target-node ownership at a regular region is equivalent to source
ownership at that region. -/
theorem targetNode_region_iff_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (compact : Fin trace.domains.nodes.count) :
    (trace.diagram.nodes
        (Fin.castAdd occurrences.length compact)).region =
          trace.targetRegion parent regular.1 ↔
      (input.val.nodes (trace.domains.nodes.origin compact)).region = parent := by
  let original := trace.domains.nodes.origin compact
  have survives : trace.domains.nodes.survives original = true :=
    trace.domains.nodes.origin_survives compact
  have targetEq : trace.targetNode original survives =
      Fin.castAdd occurrences.length compact := by
    unfold targetNode
    apply Fin.ext
    have values := congrArg Fin.val
      (trace.domains.nodes.index_origin compact)
    exact values
  rw [← targetEq, trace.targetNode_region original survives
    (input.val.nodes original).region rfl]
  by_cases direct : original ∈ wrap.val.directNodes
  · simp only [direct, if_pos]
    constructor
    · intro equal
      exact False.elim
        (trace.targetRegion_ne_bubble parent regular.1 equal.symm)
    · intro ownerEq
      exact False.elim (regular.2.1 (ownerEq.symm.trans
        (wrap.property.directNodes_at_anchor original direct)))
  · simp only [direct, if_false]
    rw [trace.regionMap_of_survives _
      (trace.nodeOwner_survives original survives)]
    constructor
    · exact trace.targetRegion_injective
    · intro ownerEq
      subst parent
      rfl

/-- Dense target-child ownership at a regular region is equivalent to source
direct parenthood at that region. -/
theorem targetRegion_parent_iff_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (compact : Fin trace.domains.regions.count) :
    (trace.diagram.regions (Fin.castSucc compact)).parent? =
          some (trace.targetRegion parent regular.1) ↔
      (input.val.regions (trace.domains.regions.origin compact)).parent? =
        some parent := by
  let child := trace.domains.regions.origin compact
  have survives : trace.domains.regions.survives child = true :=
    trace.domains.regions.origin_survives compact
  have targetEq : trace.targetRegion child survives = Fin.castSucc compact := by
    unfold targetRegion
    apply Fin.ext
    have values := congrArg Fin.val
      (trace.domains.regions.index_origin compact)
    exact values
  rw [← targetEq]
  cases childParent : (input.val.regions child).parent? with
  | none =>
      have childRoot : child = input.val.root := by
        cases shape : input.val.regions child with
        | sheet => exact input.property.only_root_is_sheet child shape
        | cut actualParent =>
            rw [shape] at childParent
            contradiction
        | bubble actualParent arity =>
            rw [shape] at childParent
            contradiction
      have rootTarget : trace.targetRegion child survives =
          trace.diagram.root := by
        simpa [childRoot] using trace.targetRegion_root
      have rootShape : trace.diagram.regions trace.diagram.root = .sheet := by
        rw [← rootTarget]
        have result := trace.abstractRegion?_targetRegion child survives
        unfold abstractRegion? at result
        have sourceRootShape : input.val.regions child = .sheet := by
          simpa [childRoot] using input.property.root_is_sheet
        simp only [sourceRootShape] at result
        exact (Option.some.inj result).symm
      rw [rootTarget]
      rw [rootShape]
      simp [CRegion.parent?]
  | some actualParent =>
      rw [trace.targetRegion_parent child actualParent survives childParent]
      by_cases direct : child ∈ wrap.val.childRoots
      · simp only [direct, if_pos]
        constructor
        · intro equal
          exact False.elim
            (trace.targetRegion_ne_bubble parent regular.1
              (Option.some.inj equal).symm)
        · intro parentEq
          have actualEq := Option.some.inj parentEq
          subst actualParent
          exact False.elim (regular.2.1 (Option.some.inj
            (childParent.symm.trans
              (wrap.property.childRoots_direct child direct))))
      · simp only [direct, if_false, Option.some.injEq]
        constructor
        · intro equal
          exact trace.targetRegion_injective (Option.some.inj equal)
        · intro parentEq
          subst actualParent
          rfl

theorem targetAtom_region_ne_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (index : Fin occurrences.length) :
    (trace.diagram.nodes (trace.targetAtom index)).region ≠
      trace.targetRegion parent regular.1 := by
  unfold targetAtom
  rw [trace.diagram_atom]
  simp only [CNode.region]
  by_cases same : (occurrences.get index).selection.val.anchor =
      wrap.val.anchor
  · rw [trace.atomOwner_eq_bubble_of_anchor_eq index same]
    intro equal
    exact trace.targetRegion_ne_bubble parent regular.1 equal.symm
  · rw [trace.atomOwner_eq_targetRegion_of_anchor_ne payload index same]
    intro equal
    exact regular.2.2 index (trace.targetRegion_injective equal).symm

theorem bubble_parent_ne_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent) :
    (trace.diagram.regions trace.bubble).parent? ≠
      some (trace.targetRegion parent regular.1) := by
  rw [trace.diagram_bubble]
  simp only [CRegion.parent?, Option.some.injEq]
  have parentIndex : trace.parentBase = trace.domains.regions.index
      wrap.val.anchor (wrap_anchor_survives payload) := by
    have indexed := trace.domains.regions.index?_index wrap.val.anchor
      (wrap_anchor_survives payload)
    exact Option.some.inj (trace.parent_result.symm.trans indexed)
  intro equal
  have equal' := Option.some.inj equal
  rw [parentIndex] at equal'
  change trace.targetRegion wrap.val.anchor (wrap_anchor_survives payload) =
    trace.targetRegion parent regular.1 at equal'
  exact regular.2.1 (trace.targetRegion_injective equal').symm

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
    change List.ofFn (fun index => domain.enumeration.get index) =
      domain.enumeration
    exact List.ofFn_getElem
  unfold filterFin
  have filterEq :
      List.filter targetP (allFin domain.count) =
        List.filter (sourceP ∘ domain.origin) (allFin domain.count) := by
    apply congrArg (fun predicate =>
      List.filter predicate (allFin domain.count))
    funext index
    exact predicateEq index
  rw [filterEq, ← List.filter_map, enumerationEq]
  change List.filter sourceP
      (List.filter domain.survives (allFin size)) =
    List.filter sourceP (allFin size)
  rw [List.filter_filter]
  apply congrArg (fun predicate => List.filter predicate (allFin size))
  funext original
  cases selected : sourceP original with
  | false => simp [selected]
  | true => simp [selected, subset original selected]

/-- Total occurrence map used by the regular frame compiler.  Values outside
the regular local traversal are irrelevant and map opaquely to the fresh
bubble. -/
def occurrenceMap
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (regular : trace.FrameRegular region) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
        trace.diagram.nodeCount
  | .node node =>
      if survives : trace.domains.nodes.survives node = true then
        .node (trace.targetNode node survives)
      else
        .child trace.bubble
  | .child child => .child (trace.regionMap child)

theorem occurrenceMap_node_of_region
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (regular : trace.FrameRegular region)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = region) :
    trace.occurrenceMap region regular (.node node) =
      .node (trace.targetNode node
        (trace.node_survives_of_regular region regular node nodeRegion)) := by
  unfold occurrenceMap
  change (if survives : trace.domains.nodes.survives node = true then
      ConcreteElaboration.LocalOccurrence.node (trace.targetNode node survives)
    else ConcreteElaboration.LocalOccurrence.child trace.bubble) = _
  rw [dif_pos (trace.node_survives_of_regular region regular node nodeRegion)]
  congr

@[simp] theorem occurrenceMap_child
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (region : Fin input.val.regionCount)
    (regular : trace.FrameRegular region)
    (child : Fin input.val.regionCount) :
    trace.occurrenceMap region regular (.child child) =
      .child (trace.regionMap child) := rfl

theorem regular_nodeFilters
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent) :
    (filterFin fun node : Fin trace.diagram.nodeCount =>
      decide ((trace.diagram.nodes node).region =
        trace.targetRegion parent regular.1)) =
      (filterFin fun node : Fin trace.domains.nodes.count =>
        decide ((trace.diagram.nodes
          (Fin.castAdd occurrences.length node)).region =
            trace.targetRegion parent regular.1)).map
        (Fin.castAdd occurrences.length) := by
  change (filterFin fun node : Fin
      (trace.domains.nodes.count + occurrences.length) =>
      decide ((trace.diagram.nodes node).region =
        trace.targetRegion parent regular.1)) = _
  unfold filterFin
  rw [allFin_add trace.domains.nodes.count occurrences.length,
    List.filter_append, List.filter_map]
  rw [List.filter_map]
  have freshEmpty : List.filter
      ((fun node : Fin
          (trace.domains.nodes.count + occurrences.length) => decide
        ((trace.diagram.nodes node).region =
          trace.targetRegion parent regular.1)) ∘
        Fin.natAdd trace.domains.nodes.count)
      (allFin occurrences.length) = [] := by
    have allFalse : ∀ index : Fin occurrences.length,
        decide ((trace.diagram.nodes
          (Fin.natAdd trace.domains.nodes.count index)).region =
            trace.targetRegion parent regular.1) = false := by
      intro index
      apply decide_eq_false_iff_not.mpr
      simpa only [targetAtom] using
        trace.targetAtom_region_ne_regular payload parent regular index
    have predicateFalse :
        ((fun node : Fin
            (trace.domains.nodes.count + occurrences.length) => decide
          ((trace.diagram.nodes node).region =
            trace.targetRegion parent regular.1)) ∘
          Fin.natAdd trace.domains.nodes.count) =
          fun _ => false := by
      funext index
      exact allFalse index
    rw [predicateFalse]
    simp
  rw [freshEmpty]
  simp only [List.map_nil, List.append_nil, targetAtom]
  rfl

theorem regular_childFilters
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent) :
    (filterFin fun child : Fin trace.diagram.regionCount =>
      decide ((trace.diagram.regions child).parent? =
        some (trace.targetRegion parent regular.1))) =
      (filterFin fun child : Fin trace.domains.regions.count =>
        decide ((trace.diagram.regions (Fin.castSucc child)).parent? =
        some (trace.targetRegion parent regular.1))).map Fin.castSucc := by
  change (filterFin fun child : Fin
      (trace.domains.regions.count + 1) =>
      decide ((trace.diagram.regions child).parent? =
        some (trace.targetRegion parent regular.1))) = _
  unfold filterFin
  rw [allFin_add trace.domains.regions.count 1, List.filter_append,
    List.filter_map]
  have freshFin : allFin 1 = [0] := by decide
  rw [freshFin]
  simp only [List.filter_cons, List.filter_nil, List.map_cons, List.map_nil]
  have lastEq : Fin.natAdd trace.domains.regions.count (0 : Fin 1) =
      trace.bubble := by
    apply Fin.ext
    rfl
  simp only [lastEq, decide_eq_false
    (trace.bubble_parent_ne_regular payload parent regular), Bool.false_eq_true,
    ↓reduceIte, List.append_nil]
  apply List.map_congr_left
  intro child _
  apply Fin.ext
  rfl

/-- The target's canonical node traversal at a regular frame region is the
source node traversal mapped through dense survivor indices. -/
theorem regular_nodeOccurrences
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent) :
    (filterFin fun node : Fin trace.diagram.nodeCount =>
      decide ((trace.diagram.nodes node).region = trace.regionMap parent)).map
        ConcreteElaboration.LocalOccurrence.node =
      ((filterFin fun node : Fin input.val.nodeCount =>
        decide ((input.val.nodes node).region = parent)).map
          ConcreteElaboration.LocalOccurrence.node).map
        (trace.occurrenceMap parent regular) := by
  rw [trace.regionMap_of_survives parent regular.1]
  rw [trace.regular_nodeFilters payload parent regular]
  let sourceP : Fin input.val.nodeCount → Bool := fun node =>
    decide ((input.val.nodes node).region = parent)
  let targetP : Fin trace.domains.nodes.count → Bool := fun node =>
    decide ((trace.diagram.nodes
      (Fin.castAdd occurrences.length node)).region =
        trace.targetRegion parent regular.1)
  have predicateEq : ∀ node,
      targetP node = sourceP (trace.domains.nodes.origin node) := by
    intro node
    apply Bool.eq_iff_iff.mpr
    simpa [targetP, sourceP] using
      trace.targetNode_region_iff_regular parent regular node
  have subset : ∀ node, sourceP node = true →
      trace.domains.nodes.survives node = true := by
    intro node selected
    exact trace.node_survives_of_regular parent regular node
      (by simpa [sourceP] using selected)
  have origins := filterFin_survivor_origin trace.domains.nodes sourceP
    targetP predicateEq subset
  change ((filterFin targetP).map
      (Fin.castAdd occurrences.length)).map
        ConcreteElaboration.LocalOccurrence.node =
    ((filterFin sourceP).map
      ConcreteElaboration.LocalOccurrence.node).map
        (trace.occurrenceMap parent regular)
  rw [← origins]
  simp only [List.map_map]
  apply List.map_congr_left
  intro compact member
  simp only [Function.comp_apply]
  have survives := trace.domains.nodes.origin_survives compact
  have sourceRegion :
      (input.val.nodes (trace.domains.nodes.origin compact)).region = parent :=
    (trace.targetNode_region_iff_regular parent regular compact).1
      (decide_eq_true_iff.mp ((mem_filterFin compact).1 member))
  rw [trace.occurrenceMap_node_of_region parent regular
    (trace.domains.nodes.origin compact) sourceRegion]
  congr 1
  unfold targetNode
  apply Fin.ext
  have values := congrArg Fin.val (trace.domains.nodes.index_origin compact)
  exact values.symm

/-- The target's canonical child traversal at a regular frame region is the
source child traversal mapped through dense survivor indices. -/
theorem regular_childOccurrences
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent) :
    (filterFin fun child : Fin trace.diagram.regionCount =>
      decide ((trace.diagram.regions child).parent? =
        some (trace.regionMap parent))).map
        ConcreteElaboration.LocalOccurrence.child =
      ((filterFin fun child : Fin input.val.regionCount =>
        decide ((input.val.regions child).parent? = some parent)).map
          ConcreteElaboration.LocalOccurrence.child).map
        (trace.occurrenceMap parent regular) := by
  rw [trace.regionMap_of_survives parent regular.1]
  rw [trace.regular_childFilters payload parent regular]
  let sourceP : Fin input.val.regionCount → Bool := fun child =>
    decide ((input.val.regions child).parent? = some parent)
  let targetP : Fin trace.domains.regions.count → Bool := fun child =>
    decide ((trace.diagram.regions (Fin.castSucc child)).parent? =
      some (trace.targetRegion parent regular.1))
  have predicateEq : ∀ child,
      targetP child = sourceP (trace.domains.regions.origin child) := by
    intro child
    apply Bool.eq_iff_iff.mpr
    simpa [targetP, sourceP] using
      trace.targetRegion_parent_iff_regular parent regular child
  have subset : ∀ child, sourceP child = true →
      trace.domains.regions.survives child = true := by
    intro child selected
    exact trace.child_survives_of_regular parent child regular
      (by simpa [sourceP] using selected)
  have origins := filterFin_survivor_origin trace.domains.regions sourceP
    targetP predicateEq subset
  change ((filterFin targetP).map Fin.castSucc).map
      ConcreteElaboration.LocalOccurrence.child =
    ((filterFin sourceP).map
      ConcreteElaboration.LocalOccurrence.child).map
        (trace.occurrenceMap parent regular)
  rw [← origins]
  simp only [List.map_map]
  apply List.map_congr_left
  intro compact member
  simp only [Function.comp_apply, occurrenceMap_child]
  have sourceParent :
      (input.val.regions (trace.domains.regions.origin compact)).parent? =
        some parent :=
    (trace.targetRegion_parent_iff_regular parent regular compact).1
      (decide_eq_true_iff.mp ((mem_filterFin compact).1 member))
  have survives := trace.child_survives_of_regular parent
    (trace.domains.regions.origin compact) regular sourceParent
  rw [trace.regionMap_of_survives _ survives]
  congr 1
  unfold targetRegion
  apply Fin.ext
  have values := congrArg Fin.val
    (trace.domains.regions.index_origin compact)
  exact values.symm

/-- Exact ordered compiler traversal of every regular abstraction frame
region. -/
theorem localOccurrences_map_of_regular
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent) :
    ConcreteElaboration.localOccurrences trace.diagram
        (trace.regionMap parent) =
      (ConcreteElaboration.localOccurrences input.val parent).map
        (trace.occurrenceMap parent regular) := by
  unfold ConcreteElaboration.localOccurrences
  rw [List.map_append]
  rw [trace.regular_nodeOccurrences payload parent regular,
    trace.regular_childOccurrences payload parent regular]

end AbstractionRawTrace

end VisualProof.Rule
