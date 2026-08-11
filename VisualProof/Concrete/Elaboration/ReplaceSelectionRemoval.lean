import VisualProof.Concrete.Elaboration.Selection

/-! Source-derived compiler transport through exact selection removal. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Elaboration

namespace FrameDomains

/-- Whether one source occurrence survives the exact selection frame. -/
def occurrenceSurvives (domains : FrameDomains d selection) :
    LocalOccurrence d.regionCount d.nodeCount → Bool
  | .node node => domains.nodes.survives node
  | .child region => domains.regions.survives region

/-- Recover the source identity represented by one dense frame occurrence. -/
def originOccurrence (domains : FrameDomains d selection) :
    LocalOccurrence domains.regions.count domains.nodes.count →
      LocalOccurrence d.regionCount d.nodeCount
  | .node node => .node (domains.nodes.origin node)
  | .child region => .child (domains.regions.origin region)

private theorem map_origin_allFin (domain : SurvivorDomain size) :
    (allFin domain.count).map domain.origin = domain.enumeration := by
  rw [allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  change List.ofFn (fun index : Fin domain.enumeration.length =>
    domain.enumeration.get index) = domain.enumeration
  exact List.ofFn_getElem

private theorem map_origin_filterFin (domain : SurvivorDomain size)
    (predicate : Fin size → Bool) :
    (filterFin fun index : domain.Carrier =>
      predicate (domain.origin index)).map domain.origin =
        (filterFin predicate).filter domain.survives := by
  unfold filterFin
  change (((allFin domain.count).filter
      (predicate ∘ domain.origin)).map domain.origin) = _
  rw [← List.filter_map, map_origin_allFin]
  unfold SurvivorDomain.enumeration
  unfold filterFin
  rw [List.filter_filter]
  symm
  rw [List.filter_filter]
  apply List.filter_congr
  intro original _
  cases domain.survives original <;> cases predicate original <;> rfl

private theorem removeRaw_node_region_origin
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (node : domains.nodes.Carrier) :
    domains.regions.origin
        ((host.val.removeRaw selection domains).nodes node).region =
      (host.val.nodes (domains.nodes.origin node)).region := by
  have reindexed := Diagram.removeRaw_node_reindexed host selection domains node
  cases nodeKind : host.val.nodes (domains.nodes.origin node) with
  | atom region binder =>
      have regionSurvives := domains.nodeRegion_survives
        (domains.nodes.origin_survives node)
      have binderSurvives := domains.atomBinder_survives host selection
        (domains.nodes.origin_survives node) nodeKind
      simp only [nodeKind, CNode.region] at regionSurvives
      simp only [nodeKind, SurvivorDomain.reindexNode?] at reindexed
      rw [domains.regions.index?_index region regionSurvives,
        domains.regions.index?_index binder binderSurvives] at reindexed
      have nodeEq := Option.some.inj reindexed
      have regionEq := congrArg CNode.region nodeEq
      calc
        _ = domains.regions.origin
            (domains.regions.index region regionSurvives) :=
          congrArg domains.regions.origin regionEq.symm
        _ = region := domains.regions.origin_index region regionSurvives
  | identity region arity =>
      have regionSurvives := domains.nodeRegion_survives
        (domains.nodes.origin_survives node)
      simp only [nodeKind, CNode.region] at regionSurvives
      simp only [nodeKind, SurvivorDomain.reindexNode?] at reindexed
      rw [domains.regions.index?_index region regionSurvives] at reindexed
      have nodeEq := Option.some.inj reindexed
      have regionEq := congrArg CNode.region nodeEq
      calc
        _ = domains.regions.origin
            (domains.regions.index region regionSurvives) :=
          congrArg domains.regions.origin regionEq.symm
        _ = region := domains.regions.origin_index region regionSurvives

private theorem removeRaw_node_region_eq_iff
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : domains.regions.Carrier)
    (node : domains.nodes.Carrier) :
    ((host.val.removeRaw selection domains).nodes node).region = region ↔
      (host.val.nodes (domains.nodes.origin node)).region =
        domains.regions.origin region := by
  constructor
  · intro equality
    rw [← domains.removeRaw_node_region_origin host selection node,
      equality]
  · intro equality
    apply domains.regions.origin_injective
    rw [domains.removeRaw_node_region_origin host selection node, equality]

private theorem removeRaw_parent_eq_iff
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region child : domains.regions.Carrier) :
    ((host.val.removeRaw selection domains).regions child).parent? =
        some region ↔
      (host.val.regions (domains.regions.origin child)).parent? =
        some (domains.regions.origin region) := by
  have reindexed := Diagram.removeRaw_region_reindexed host selection domains
    child
  cases childKind : host.val.regions (domains.regions.origin child) with
  | sheet =>
      simp only [childKind, SurvivorDomain.reindexRegion?] at reindexed
      have kindEq := Option.some.inj reindexed
      rw [← kindEq]
      change (none = some region ↔
        none = some (domains.regions.origin region))
      constructor <;> intro impossible <;> cases impossible
  | cut parent =>
      have parentEq :
          (host.val.regions (domains.regions.origin child)).parent? =
            some parent := (congrArg CRegion.parent? childKind).trans rfl
      have parentSurvives := domains.parent_survives host selection
        (domains.regions.origin_survives child) parentEq
      simp only [childKind, SurvivorDomain.reindexRegion?] at reindexed
      rw [domains.regions.index?_index parent parentSurvives] at reindexed
      have kindEq := Option.some.inj reindexed
      rw [← kindEq]
      simp only [CRegion.parent?, Option.some.injEq]
      constructor
      · intro equality
        have equality' := Option.some.inj equality
        rw [← equality', domains.regions.origin_index]
      · intro equality
        apply congrArg some
        apply domains.regions.origin_injective
        rw [domains.regions.origin_index, equality]
  | bubble parent arity =>
      have parentEq :
          (host.val.regions (domains.regions.origin child)).parent? =
            some parent := (congrArg CRegion.parent? childKind).trans rfl
      have parentSurvives := domains.parent_survives host selection
        (domains.regions.origin_survives child) parentEq
      simp only [childKind, SurvivorDomain.reindexRegion?] at reindexed
      rw [domains.regions.index?_index parent parentSurvives] at reindexed
      have kindEq := Option.some.inj reindexed
      rw [← kindEq]
      simp only [CRegion.parent?, Option.some.injEq]
      constructor
      · intro equality
        have equality' := Option.some.inj equality
        rw [← equality', domains.regions.origin_index]
      · intro equality
        apply congrArg some
        apply domains.regions.origin_injective
        rw [domains.regions.origin_index, equality]

/-- Dense frame occurrence order is exactly the source occurrence order with
the removed selection occurrences filtered out. -/
theorem map_localOccurrences_removeRaw
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : domains.regions.Carrier) :
    (localOccurrences (host.val.removeRaw selection domains) region).map
        domains.originOccurrence =
      (localOccurrences host.val (domains.regions.origin region)).filter
        domains.occurrenceSurvives := by
  let sourceNodePredicate : Fin host.val.nodeCount → Bool := fun node =>
    decide ((host.val.nodes node).region = domains.regions.origin region)
  let sourceChildPredicate : Fin host.val.regionCount → Bool := fun child =>
    decide ((host.val.regions child).parent? =
      some (domains.regions.origin region))
  have nodes :
      (filterFin fun node : domains.nodes.Carrier =>
        decide (((host.val.removeRaw selection domains).nodes node).region =
          region)).map domains.nodes.origin =
        (filterFin sourceNodePredicate).filter domains.nodes.survives := by
    rw [← map_origin_filterFin domains.nodes sourceNodePredicate]
    apply congrArg (List.map domains.nodes.origin)
    apply List.filter_congr
    intro node _
    simp only [sourceNodePredicate]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_iff] using
      domains.removeRaw_node_region_eq_iff host selection region node
  have children :
      (filterFin fun child : domains.regions.Carrier =>
        decide (((host.val.removeRaw selection domains).regions child).parent? =
          some region)).map domains.regions.origin =
        (filterFin sourceChildPredicate).filter
          domains.regions.survives := by
    rw [← map_origin_filterFin domains.regions sourceChildPredicate]
    apply congrArg (List.map domains.regions.origin)
    apply List.filter_congr
    intro child _
    simp only [sourceChildPredicate]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_iff] using
      domains.removeRaw_parent_eq_iff host selection region child
  have nodeOccurrences := congrArg (List.map fun node =>
    (LocalOccurrence.node node :
      LocalOccurrence host.val.regionCount host.val.nodeCount)) nodes
  have childOccurrences := congrArg (List.map fun child =>
    (LocalOccurrence.child child :
      LocalOccurrence host.val.regionCount host.val.nodeCount)) children
  have mapNodeOccurrences (values : List domains.nodes.Carrier) :
      List.map domains.originOccurrence
          (values.map fun node =>
            (LocalOccurrence.node node : LocalOccurrence
              domains.regions.count domains.nodes.count)) =
        (values.map domains.nodes.origin).map fun node =>
          (LocalOccurrence.node node :
            LocalOccurrence host.val.regionCount host.val.nodeCount) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro node _
    rfl
  have mapChildOccurrences (values : List domains.regions.Carrier) :
      List.map domains.originOccurrence
          (values.map fun child =>
            (LocalOccurrence.child child : LocalOccurrence
              domains.regions.count domains.nodes.count)) =
        (values.map domains.regions.origin).map fun child =>
          (LocalOccurrence.child child :
            LocalOccurrence host.val.regionCount host.val.nodeCount) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro child _
    rfl
  unfold localOccurrences
  calc
    _ = List.map domains.originOccurrence
          ((filterFin fun node : domains.nodes.Carrier =>
            decide (((host.val.removeRaw selection domains).nodes node).region =
              region)).map fun node =>
                (LocalOccurrence.node node : LocalOccurrence
                  domains.regions.count domains.nodes.count)) ++
        List.map domains.originOccurrence
          ((filterFin fun child : domains.regions.Carrier =>
            decide (((host.val.removeRaw selection domains).regions
              child).parent? = some region)).map fun child =>
                (LocalOccurrence.child child : LocalOccurrence
                  domains.regions.count domains.nodes.count)) :=
      List.map_append
    _ = (List.filter domains.nodes.survives
          (filterFin sourceNodePredicate)).map (fun node =>
            (LocalOccurrence.node node : LocalOccurrence
              host.val.regionCount host.val.nodeCount)) ++
        (List.filter domains.regions.survives
          (filterFin sourceChildPredicate)).map (fun child =>
            (LocalOccurrence.child child : LocalOccurrence
              host.val.regionCount host.val.nodeCount)) := by
      rw [mapNodeOccurrences, mapChildOccurrences, nodeOccurrences,
        childOccurrences]
    _ = _ := by
      rw [List.filter_append, List.filter_map, List.filter_map]
      rfl

/-- The dense frame position corresponding to one retained source child
occurrence.  Its position is selected only in the filtered source occurrence
stream, then transported across the exact occurrence-list equation. -/
structure MappedChildOccurrenceIndex
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {parent child : Fin host.val.regionCount}
    (parentSurvives : domains.regions.survives parent = true)
    (childSurvives : domains.regions.survives child = true) where
  index : Fin (localOccurrences (host.val.removeRaw selection domains)
    (domains.regions.index parent parentSurvives)).length
  occurrence : (localOccurrences (host.val.removeRaw selection domains)
    (domains.regions.index parent parentSurvives)).get index =
      .child (domains.regions.index child childSurvives)

/-- Reindex one intrinsic source child position through exact selection
removal without inspecting or searching the target occurrence stream. -/
noncomputable def mapChildOccurrenceIndex
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {parent child : Fin host.val.regionCount}
    (parentSurvives : domains.regions.survives parent = true)
    (childSurvives : domains.regions.survives child = true)
    (sourceIndex : Fin (localOccurrences host.val parent).length)
    (sourceOccurrence : (localOccurrences host.val parent).get sourceIndex =
      .child child) :
    MappedChildOccurrenceIndex host selection domains parentSurvives
      childSurvives := by
  let sourceOccurrences := localOccurrences host.val parent
  let filteredOccurrences :=
    sourceOccurrences.filter domains.occurrenceSurvives
  have sourceMember : (.child child : LocalOccurrence host.val.regionCount
      host.val.nodeCount) ∈ sourceOccurrences := by
    rw [← sourceOccurrence]
    exact List.get_mem sourceOccurrences sourceIndex
  have filteredMember : (.child child : LocalOccurrence host.val.regionCount
      host.val.nodeCount) ∈ filteredOccurrences := by
    exact List.mem_filter.mpr ⟨sourceMember, childSurvives⟩
  let filteredExistence := indexOf?_complete filteredMember
  let filteredIndex := Classical.choose filteredExistence
  have filteredFound : indexOf? filteredOccurrences (.child child) =
      some filteredIndex := Classical.choose_spec filteredExistence
  have filteredGet : filteredOccurrences.get filteredIndex =
      (.child child : LocalOccurrence host.val.regionCount
        host.val.nodeCount) := indexOf?_sound filteredFound
  let targetOccurrences := localOccurrences
    (host.val.removeRaw selection domains)
    (domains.regions.index parent parentSurvives)
  have occurrencesEq :
      targetOccurrences.map domains.originOccurrence = filteredOccurrences := by
    simpa only [targetOccurrences, filteredOccurrences, sourceOccurrences,
      domains.regions.origin_index] using
        domains.map_localOccurrences_removeRaw host selection
          (domains.regions.index parent parentSurvives)
  have targetLength : filteredOccurrences.length = targetOccurrences.length := by
    have lengths := congrArg List.length occurrencesEq
    simpa only [List.length_map] using lengths.symm
  let targetIndex : Fin targetOccurrences.length :=
    Fin.cast targetLength filteredIndex
  let mappedIndex : Fin
      (targetOccurrences.map domains.originOccurrence).length :=
    Fin.cast (by simp only [List.length_map]; rfl) targetIndex
  have transported := List.get_of_eq occurrencesEq mappedIndex
  have filteredPosition :
      Fin.cast (congrArg List.length occurrencesEq) mappedIndex =
        filteredIndex := by
    apply Fin.ext
    rfl
  change (targetOccurrences.map domains.originOccurrence).get mappedIndex =
    filteredOccurrences.get
      (Fin.cast (congrArg List.length occurrencesEq) mappedIndex)
    at transported
  rw [filteredPosition, filteredGet] at transported
  have targetOrigin :
      domains.originOccurrence (targetOccurrences.get targetIndex) =
        (.child child : LocalOccurrence host.val.regionCount
          host.val.nodeCount) := by
    simpa only [List.get_eq_getElem, List.getElem_map] using transported
  cases targetOccurrenceEq : targetOccurrences.get targetIndex with
  | node targetNode =>
      simp only [targetOccurrenceEq, originOccurrence] at targetOrigin
      cases targetOrigin
  | child targetChild =>
      have targetChildOrigin : domains.regions.origin targetChild = child := by
        simpa only [targetOccurrenceEq, originOccurrence,
          LocalOccurrence.child.injEq] using targetOrigin
      have targetChildEq : targetChild =
          domains.regions.index child childSurvives := by
        apply domains.regions.origin_injective
        rw [targetChildOrigin, domains.regions.origin_index]
      exact {
        index := targetIndex
        occurrence := by rw [targetOccurrenceEq, targetChildEq]
      }

/-- A retained source cut remains the corresponding dense frame cut. -/
theorem removeRaw_cut
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {parent child : Fin host.val.regionCount}
    (parentSurvives : domains.regions.survives parent = true)
    (childSurvives : domains.regions.survives child = true)
    (childKind : host.val.regions child = .cut parent) :
    (host.val.removeRaw selection domains).regions
        (domains.regions.index child childSurvives) =
      .cut (domains.regions.index parent parentSurvives) := by
  have reindexed := Diagram.removeRaw_region_reindexed host selection domains
    (domains.regions.index child childSurvives)
  simp only [domains.regions.origin_index, childKind,
    SurvivorDomain.reindexRegion?] at reindexed
  rw [domains.regions.index?_index parent parentSurvives] at reindexed
  exact (Option.some.inj reindexed).symm

/-- A retained source bubble remains the corresponding dense frame bubble. -/
theorem removeRaw_bubble
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {parent child : Fin host.val.regionCount}
    (parentSurvives : domains.regions.survives parent = true)
    (childSurvives : domains.regions.survives child = true)
    (arity : Nat)
    (childKind : host.val.regions child = .bubble parent arity) :
    (host.val.removeRaw selection domains).regions
        (domains.regions.index child childSurvives) =
      .bubble (domains.regions.index parent parentSurvives) arity := by
  have reindexed := Diagram.removeRaw_region_reindexed host selection domains
    (domains.regions.index child childSurvives)
  simp only [domains.regions.origin_index, childKind,
    SurvivorDomain.reindexRegion?] at reindexed
  rw [domains.regions.index?_index parent parentSurvives] at reindexed
  exact (Option.some.inj reindexed).symm

private theorem removeRaw_wire_scope_eq_iff
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : domains.regions.Carrier)
    (wire : domains.wires.Carrier) :
    ((host.val.removeRaw selection domains).wires wire).scope = region ↔
      (host.val.wires (domains.wires.origin wire)).scope =
        domains.regions.origin region := by
  let sourceScope :=
    (host.val.wires (domains.wires.origin wire)).scope
  let sourceScopeSurvives := domains.wireScope_survives
    (domains.wires.origin_survives wire)
  have scopeEq := Diagram.removeRaw_wire_scope host selection domains wire
  constructor
  · intro equality
    rw [scopeEq] at equality
    rw [← equality, domains.regions.origin_index]
  · intro equality
    rw [scopeEq]
    apply domains.regions.origin_injective
    rw [domains.regions.origin_index, equality]

/-- Dense frame local-wire order is exactly the source local-wire order with
the removed selection wires filtered out. -/
theorem map_exactScopeWires_removeRaw
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : domains.regions.Carrier) :
    (exactScopeWires (host.val.removeRaw selection domains) region).map
        domains.wires.origin =
      (exactScopeWires host.val (domains.regions.origin region)).filter
        domains.wires.survives := by
  let sourcePredicate : Fin host.val.wireCount → Bool := fun wire =>
    decide ((host.val.wires wire).scope = domains.regions.origin region)
  change
    (filterFin fun wire : domains.wires.Carrier =>
      decide (((host.val.removeRaw selection domains).wires wire).scope =
        region)).map domains.wires.origin =
      (filterFin sourcePredicate).filter domains.wires.survives
  rw [← map_origin_filterFin domains.wires sourcePredicate]
  apply congrArg (List.map domains.wires.origin)
  apply List.filter_congr
  intro wire _
  simp only [sourcePredicate]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_iff] using
    domains.removeRaw_wire_scope_eq_iff host selection region wire

/-- Compact one source wire context through the exact frame survivor receipt. -/
def mapWireContext (domains : FrameDomains d selection)
    (context : WireContext d) : WireContext (d.removeRaw selection domains) :=
  context.filterMap domains.wires.index?

/-- Mapping a compacted wire context back to source identities gives exactly
the stable source sublist of surviving wires. -/
theorem map_mapWireContext_origin
    (domains : FrameDomains d selection) (context : WireContext d) :
    (domains.mapWireContext context).map domains.wires.origin =
      context.filter domains.wires.survives := by
  induction context with
  | nil => rfl
  | cons wire tail inductionHypothesis =>
      change (tail.filterMap domains.wires.index?).map
          domains.wires.origin = tail.filter domains.wires.survives
        at inductionHypothesis
      change ((wire :: tail).filterMap domains.wires.index?).map
          domains.wires.origin =
        (wire :: tail).filter domains.wires.survives
      cases survives : domains.wires.survives wire with
      | false =>
          have missing : domains.wires.index? wire = none :=
            (domains.wires.index?_eq_none_iff wire).2 survives
          rw [List.filterMap_cons_none missing]
          simp only [List.filter, survives]
          exact inductionHypothesis
      | true =>
          have found := domains.wires.index?_index wire survives
          rw [List.filterMap_cons_some found]
          simp only [List.map_cons, List.filter, survives]
          rw [domains.wires.origin_index, inductionHypothesis]

/-- Context compaction preserves concatenation exactly. -/
theorem mapWireContext_append (domains : FrameDomains d selection)
    (first second : WireContext d) :
    domains.mapWireContext (first ++ second) =
      domains.mapWireContext first ++ domains.mapWireContext second := by
  exact List.filterMap_append

/-- The canonical compacted source local block is the target frame's exact
local block at the represented dense region. -/
theorem mapWireContext_exactScope
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : domains.regions.Carrier) :
    domains.mapWireContext
        (exactScopeWires host.val (domains.regions.origin region)) =
      exactScopeWires (host.val.removeRaw selection domains) region := by
  apply (List.map_inj_right domains.wires.origin_injective).mp
  rw [domains.map_mapWireContext_origin,
    domains.map_exactScopeWires_removeRaw host selection]

/-- Route-context extension commutes with exact frame compaction. -/
theorem mapWireContext_extend
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val)
    (region : domains.regions.Carrier) :
    domains.mapWireContext
        (context.extend (domains.regions.origin region)) =
      (domains.mapWireContext context).extend region := by
  unfold WireContext.extend
  rw [domains.mapWireContext_append,
    domains.mapWireContext_exactScope host selection region]

/-- Restrict a source binder context to the retained dense frame regions. -/
def mapBinderContext (domains : FrameDomains d selection)
    (context : BinderContext d rels) :
    BinderContext (d.removeRaw selection domains) rels :=
  fun region => context (domains.regions.origin region)

/-- Empty binder state is preserved by exact frame compaction. -/
theorem mapBinderContext_empty (domains : FrameDomains d selection) :
    domains.mapBinderContext BinderContext.empty = BinderContext.empty := by
  rfl

/-- Pushing a surviving source binder commutes with exact frame compaction. -/
theorem mapBinderContext_push
    (domains : FrameDomains d selection)
    (context : BinderContext d rels)
    (binder : Fin d.regionCount)
    (binderSurvives : domains.regions.survives binder = true)
    (arity : Nat) :
    domains.mapBinderContext (context.push binder arity) =
      (domains.mapBinderContext context).push
        (domains.regions.index binder binderSurvives) arity := by
  funext candidate
  have candidate_eq_iff :
      domains.regions.origin candidate = binder ↔
        candidate = domains.regions.index binder binderSurvives := by
    constructor
    · intro equality
      apply domains.regions.origin_injective
      rw [equality, domains.regions.origin_index]
    · intro equality
      rw [equality, domains.regions.origin_index]
  by_cases equality : domains.regions.origin candidate = binder
  · have targetEquality := candidate_eq_iff.mp equality
    simp only [mapBinderContext, BinderContext.push, targetEquality,
      domains.regions.origin_index, ↓reduceIte]
  · have targetInequality :
        candidate ≠ domains.regions.index binder binderSurvives :=
      fun targetEquality => equality (candidate_eq_iff.mpr targetEquality)
    simp only [mapBinderContext, BinderContext.push, equality,
      targetInequality, ↓reduceIte]

/-- The source lexical position represented by one compacted frame-context
position.  Lookup is performed only in the supplied source context. -/
noncomputable def mapWireContextOriginIndex
    (domains : FrameDomains d selection) (context : WireContext d)
    (index : Fin (domains.mapWireContext context).length) :
    Fin context.length := by
  let mappedWire := domains.wires.origin
    ((domains.mapWireContext context).get index)
  have mappedMember : mappedWire ∈
      (domains.mapWireContext context).map domains.wires.origin := by
    exact List.mem_map.mpr ⟨(domains.mapWireContext context).get index,
      List.get_mem _ index, rfl⟩
  have sourceMember : mappedWire ∈ context := by
    rw [domains.map_mapWireContext_origin] at mappedMember
    exact (List.mem_filter.mp mappedMember).1
  exact Classical.choose (WireContext.lookup?_complete sourceMember)

/-- A compacted context position retrieves its represented source wire at the
source-only position selected above. -/
theorem mapWireContextOriginIndex_get
    (domains : FrameDomains d selection) (context : WireContext d)
    (index : Fin (domains.mapWireContext context).length) :
    context.get (domains.mapWireContextOriginIndex context index) =
      domains.wires.origin ((domains.mapWireContext context).get index) := by
  let mappedWire := domains.wires.origin
    ((domains.mapWireContext context).get index)
  have mappedMember : mappedWire ∈
      (domains.mapWireContext context).map domains.wires.origin := by
    exact List.mem_map.mpr ⟨(domains.mapWireContext context).get index,
      List.get_mem _ index, rfl⟩
  have sourceMember : mappedWire ∈ context := by
    rw [domains.map_mapWireContext_origin] at mappedMember
    exact (List.mem_filter.mp mappedMember).1
  exact indexOf?_sound
    (Classical.choose_spec (WireContext.lookup?_complete sourceMember))

/-- A retained dense node represents exactly its source node with region and
binder identities mapped back through the survivor receipt. -/
theorem removeRaw_node_origin
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (node : domains.nodes.Carrier) :
    host.val.nodes (domains.nodes.origin node) =
      match (host.val.removeRaw selection domains).nodes node with
      | .atom region binder =>
          .atom (domains.regions.origin region)
            (domains.regions.origin binder)
      | .identity region arity =>
          .identity (domains.regions.origin region) arity := by
  let original := domains.nodes.origin node
  have survives := domains.nodes.origin_survives node
  have indexEq : domains.nodes.index original survives = node :=
    domains.nodes.index_origin node
  cases sourceKind : host.val.nodes original with
  | atom region binder =>
      rw [← indexEq]
      rw [Diagram.removeRaw_atom host selection domains survives sourceKind]
      simp only
      rw [domains.regions.origin_index, domains.regions.origin_index]
  | identity region arity =>
      rw [← indexEq]
      rw [Diagram.removeRaw_identity host selection domains survives sourceKind]
      simp only
      rw [domains.regions.origin_index]

/-- Every retained frame endpoint occurrence maps back to the represented
source endpoint occurrence. -/
theorem endpointOccurs_removeRaw_origin_forward
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (wire : domains.wires.Carrier) (node : domains.nodes.Carrier)
    (port : CPort)
    (occurs : (host.val.removeRaw selection domains).EndpointOccurs wire
      ⟨node, port⟩) :
    host.val.EndpointOccurs (domains.wires.origin wire)
      ⟨domains.nodes.origin node, port⟩ := by
  obtain ⟨original, sourceOccurs, reindexed⟩ :=
    (Diagram.mem_removeRaw_wire_endpoints_iff host selection domains wire
      ⟨node, port⟩).1 occurs
  have originalEq := Diagram.reindexEndpoint?_origin domains reindexed
  simpa only [originalEq] using sourceOccurs

/-- Every source endpoint at a retained node comes from its unique dense frame
wire. -/
theorem endpointOccurs_removeRaw_origin_backward
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceWire : Fin host.val.wireCount) (node : domains.nodes.Carrier)
    (port : CPort)
    (occurs : host.val.EndpointOccurs sourceWire
      ⟨domains.nodes.origin node, port⟩) :
    ∃ targetWire : domains.wires.Carrier,
      domains.wires.origin targetWire = sourceWire ∧
        (host.val.removeRaw selection domains).EndpointOccurs targetWire
          ⟨node, port⟩ := by
  have nodeSurvives := domains.nodes.origin_survives node
  have wireSurvives := domains.incidentWire_survives host selection
    occurs nodeSurvives
  let targetWire := domains.wires.index sourceWire wireSurvives
  refine ⟨targetWire, domains.wires.origin_index sourceWire wireSurvives, ?_⟩
  apply (Diagram.mem_removeRaw_wire_endpoints_iff host selection domains
    targetWire ⟨node, port⟩).2
  refine ⟨⟨domains.nodes.origin node, port⟩, ?_, ?_⟩
  · simpa only [targetWire, domains.wires.origin_index] using occurs
  · unfold SurvivorDomain.reindexEndpoint?
    rw [domains.nodes.index?_index]
    change some ({
      node := domains.nodes.index (domains.nodes.origin node)
        (domains.nodes.origin_survives node)
      port := port
    } : CEndpoint domains.nodes.count) =
      some ({ node := node, port := port } : CEndpoint domains.nodes.count)
    exact congrArg some (congrArg (fun targetNode => ({
      node := targetNode
      port := port
    } : CEndpoint domains.nodes.count)) (domains.nodes.index_origin node))

/-- Port lookup at a retained frame node is the source port lookup transported
through the exact compacted-context position map. -/
theorem resolvePort?_removeRaw_origin_map
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val) (contextNodup : context.Nodup)
    (node : domains.nodes.Carrier) (port : CPort) :
    resolvePort? host.val context (domains.nodes.origin node) port =
      (resolvePort? (host.val.removeRaw selection domains)
        (domains.mapWireContext context) node port).map
          (domains.mapWireContextOriginIndex context) := by
  apply resolvePort?_map_of_embedding
    (domains.mapWireContext context) context node (domains.nodes.origin node)
    domains.wires.origin domains.wires.origin_injective
    (domains.mapWireContextOriginIndex context) contextNodup
    (domains.mapWireContextOriginIndex_get context)
  · intro wire sourceOccurs
    exact domains.endpointOccurs_removeRaw_origin_forward host selection wire
      node port sourceOccurs
  · intro sourceWire sourceOccurs
    exact domains.endpointOccurs_removeRaw_origin_backward host selection
      sourceWire node port sourceOccurs
  · intro wire _ sourceMember
    exact List.mem_filterMap.mpr
      ⟨domains.wires.origin wire, sourceMember,
        domains.wires.index?_origin wire⟩
  · exact host.property.wire_endpoints_are_disjoint

/-- Compilation of a retained frame node maps back to the exact source-node
item.  Thus source success determines frame-node success without a fresh
compiler choice. -/
theorem compileNode?_removeRaw_origin_map
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val) (contextNodup : context.Nodup)
    (binders : BinderContext host.val rels)
    (node : domains.nodes.Carrier) :
    compileNode? host.val context binders (domains.nodes.origin node) =
      (compileNode? (host.val.removeRaw selection domains)
        (domains.mapWireContext context) (domains.mapBinderContext binders)
        node).map
          (Item.renameWires (domains.mapWireContextOriginIndex context)) := by
  let regionMap :
      Fin (host.val.removeRaw selection domains).regionCount →
        Fin host.val.regionCount := domains.regions.origin
  let binderMap :
      Fin (host.val.removeRaw selection domains).regionCount →
        Fin host.val.regionCount := regionMap
  let wireMap :
      Fin (domains.mapWireContext context).length → Fin context.length :=
    domains.mapWireContextOriginIndex context
  let relationMap : RelationRenaming rels rels := fun relation => relation
  have mapped := compileNode?_map
    (source := host.val.removeRaw selection domains) (target := host.val)
    (domains.mapWireContext context) context
    (domains.mapBinderContext binders) binders node
    (domains.nodes.origin node) regionMap binderMap wireMap relationMap
    (by
      cases targetKind : (host.val.removeRaw selection domains).nodes node with
      | atom region binder =>
          have mappedKind :=
            domains.removeRaw_node_origin host selection node
          rw [targetKind] at mappedKind
          simpa only [regionMap, binderMap] using mappedKind
      | identity region arity =>
          have mappedKind :=
            domains.removeRaw_node_origin host selection node
          rw [targetKind] at mappedKind
          simpa only [regionMap, binderMap] using mappedKind)
    (domains.resolvePort?_removeRaw_origin_map host selection context
      contextNodup node)
    (by
      intro _ binder _
      unfold mapBinderContext
      cases binders (domains.regions.origin binder) <;> rfl)
  simpa only [wireMap, relationMap, Item.renameRelations_id] using mapped

/-- The exact retained-frame node item determined by one successful source
node computation. -/
structure MappedNodeCompilation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val) (binders : BinderContext host.val rels)
    (node : domains.nodes.Carrier) (sourceItem : Item context.length rels) where
  targetItem : Item (domains.mapWireContext context).length rels
  target_compiled :
    compileNode? (host.val.removeRaw selection domains)
      (domains.mapWireContext context) (domains.mapBinderContext binders) node =
        some targetItem
  source_item_eq :
    sourceItem =
      targetItem.renameWires (domains.mapWireContextOriginIndex context)

/-- Source-node success fixes the retained-frame node computation and item;
no frame compiler witness is independently selected. -/
def mapNodeCompilation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val) (contextNodup : context.Nodup)
    (binders : BinderContext host.val rels)
    (node : domains.nodes.Carrier) (sourceItem : Item context.length rels)
    (sourceCompiled :
      compileNode? host.val context binders (domains.nodes.origin node) =
        some sourceItem) :
    MappedNodeCompilation host selection domains context binders node
      sourceItem := by
  have mapped := domains.compileNode?_removeRaw_origin_map host selection
    context contextNodup binders node
  cases targetCompiled : compileNode? (host.val.removeRaw selection domains)
      (domains.mapWireContext context) (domains.mapBinderContext binders) node with
  | none =>
      rw [targetCompiled] at mapped
      simp only [Option.map_none] at mapped
      rw [mapped] at sourceCompiled
      contradiction
  | some targetItem =>
      refine {
        targetItem := targetItem
        target_compiled := targetCompiled
        source_item_eq := ?_
      }
      rw [targetCompiled] at mapped
      simp only [Option.map_some] at mapped
      rw [mapped] at sourceCompiled
      exact (Option.some.inj sourceCompiled).symm

/-- A checked selection never removes its own retained anchor. -/
theorem anchor_survives
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) :
    domains.regions.survives selection.val.anchor = true := by
  rw [domains.region_survives_iff]
  right
  intro selected
  obtain ⟨child, childSelected, childEncloses⟩ :=
    (selection.mem_selectedRegions selection.val.anchor).1 selected
  exact checked_direct_child_not_encloses_parent host.property
    (selection.property.childRoots_direct child childSelected) childEncloses

/-- The exact route, intrinsic path, and binder derivation transported through
selection removal as one dependent compiler certificate. -/
structure MappedRegionCompilerDerivation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {origin site : Fin host.val.regionCount}
    {context siteContext : WireContext host.val}
    {startRels siteRels : Theory.RelCtx}
    {startBinders : BinderContext host.val startRels}
    {siteBinders : BinderContext host.val siteRels}
    {sourcePath : List Nat}
    {sourceRoute : ConcreteCompilerRoute host.val (.region origin context)
      site siteContext}
    (sourceDerivation : sourceRoute.Derivation startBinders sourcePath
      siteBinders)
    (siteSurvives : domains.regions.survives site = true) where
  originSurvives : domains.regions.survives origin = true
  targetPath : List Nat
  route : ConcreteCompilerRoute (host.val.removeRaw selection domains)
    (.region (domains.regions.index origin originSurvives)
      (domains.mapWireContext context))
    (domains.regions.index site siteSurvives)
    (domains.mapWireContext siteContext)
  derivation : route.Derivation (domains.mapBinderContext startBinders)
    targetPath (domains.mapBinderContext siteBinders)

/-- Transport one source region derivation through survivor reindexing.  Each
target path index is obtained from the filtered source occurrence stream. -/
noncomputable def mapRegionCompilerDerivation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {origin site : Fin host.val.regionCount}
    {context siteContext : WireContext host.val}
    {startRels siteRels : Theory.RelCtx}
    {startBinders : BinderContext host.val startRels}
    {siteBinders : BinderContext host.val siteRels}
    {sourcePath : List Nat}
    {sourceRoute : ConcreteCompilerRoute host.val (.region origin context)
      site siteContext}
    (sourceDerivation : sourceRoute.Derivation startBinders sourcePath
      siteBinders)
    (siteSurvives : domains.regions.survives site = true) :
    MappedRegionCompilerDerivation host selection domains sourceDerivation
      siteSurvives := by
  cases sourceDerivation with
  | regionHere =>
      exact {
        originSurvives := siteSurvives
        targetPath := []
        route := .regionHere (domains.regions.index origin siteSurvives)
          (domains.mapWireContext context)
        derivation := .regionHere (domains.regions.index origin siteSurvives)
          (domains.mapWireContext context)
          (domains.mapBinderContext startBinders)
      }
  | @regionStepCut _ child _ _ _ _ _ parent childKind sourceIndex
      sourceOccurrence _ _ _ nestedRoute nestedDerivation =>
      let nestedResult := mapRegionCompilerDerivation host selection domains
        nestedDerivation siteSurvives
      let childSurvives := nestedResult.originSurvives
      let originSurvives := domains.parent_survives host selection
        childSurvives parent
      let mappedOccurrence := domains.mapChildOccurrenceIndex host selection
        originSurvives childSurvives sourceIndex sourceOccurrence
      have targetParent :
          ((host.val.removeRaw selection domains).regions
            (domains.regions.index child childSurvives)).parent? =
            some (domains.regions.index origin originSurvives) := by
        exact Diagram.removeRaw_parent host selection domains
          childSurvives parent
      have targetKind := domains.removeRaw_cut host selection originSurvives
        childSurvives childKind
      have contextEq :
          domains.mapWireContext (context.extend origin) =
            (domains.mapWireContext context).extend
              (domains.regions.index origin originSurvives) := by
        simpa only [domains.regions.origin_index] using
          domains.mapWireContext_extend host selection context
            (domains.regions.index origin originSurvives)
      let targetNested : Sigma fun route : ConcreteCompilerRoute
          (host.val.removeRaw selection domains)
          (.region (domains.regions.index child childSurvives)
            ((domains.mapWireContext context).extend
              (domains.regions.index origin originSurvives)))
          (domains.regions.index site siteSurvives)
          (domains.mapWireContext siteContext) =>
        route.Derivation (domains.mapBinderContext startBinders)
          nestedResult.targetPath
          (domains.mapBinderContext siteBinders) := by
        rw [← contextEq]
        exact ⟨nestedResult.route, nestedResult.derivation⟩
      exact {
        originSurvives := originSurvives
        targetPath := mappedOccurrence.index.val :: nestedResult.targetPath
        route := .regionStep targetParent targetNested.1
        derivation := ConcreteCompilerRoute.Derivation.regionStepCut
          (domains.mapBinderContext startBinders) targetParent targetKind
          mappedOccurrence.index mappedOccurrence.occurrence targetNested.2
      }
  | @regionStepBubble _ child _ _ _ _ _ arity parent childKind sourceIndex
      sourceOccurrence _ _ _ nestedRoute nestedDerivation =>
      let nestedResult := mapRegionCompilerDerivation host selection domains
        nestedDerivation siteSurvives
      let childSurvives := nestedResult.originSurvives
      let originSurvives := domains.parent_survives host selection
        childSurvives parent
      let mappedOccurrence := domains.mapChildOccurrenceIndex host selection
        originSurvives childSurvives sourceIndex sourceOccurrence
      have targetParent :
          ((host.val.removeRaw selection domains).regions
            (domains.regions.index child childSurvives)).parent? =
            some (domains.regions.index origin originSurvives) := by
        exact Diagram.removeRaw_parent host selection domains
          childSurvives parent
      have targetKind := domains.removeRaw_bubble host selection
        originSurvives childSurvives arity childKind
      have contextEq :
          domains.mapWireContext (context.extend origin) =
            (domains.mapWireContext context).extend
              (domains.regions.index origin originSurvives) := by
        simpa only [domains.regions.origin_index] using
          domains.mapWireContext_extend host selection context
            (domains.regions.index origin originSurvives)
      let targetNested : Sigma fun route : ConcreteCompilerRoute
          (host.val.removeRaw selection domains)
          (.region (domains.regions.index child childSurvives)
            ((domains.mapWireContext context).extend
              (domains.regions.index origin originSurvives)))
          (domains.regions.index site siteSurvives)
          (domains.mapWireContext siteContext) =>
        route.Derivation
          ((domains.mapBinderContext startBinders).push
            (domains.regions.index child childSurvives) arity)
          nestedResult.targetPath
          (domains.mapBinderContext siteBinders) := by
        rw [← domains.mapBinderContext_push startBinders child
          childSurvives arity, ← contextEq]
        exact ⟨nestedResult.route, nestedResult.derivation⟩
      exact {
        originSurvives := originSurvives
        targetPath := mappedOccurrence.index.val :: nestedResult.targetPath
        route := .regionStep targetParent targetNested.1
        derivation := ConcreteCompilerRoute.Derivation.regionStepBubble
          (domains.mapBinderContext startBinders) targetParent targetKind
          mappedOccurrence.index mappedOccurrence.occurrence targetNested.2
      }

/-- The exact open-root route, intrinsic path, and binder derivation
transported through selection removal as one dependent certificate. -/
structure MappedOpenCompilerDerivation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {ambient locals : WireContext host.val}
    {site : Fin host.val.regionCount}
    {siteContext : WireContext host.val}
    {siteRels : Theory.RelCtx}
    {siteBinders : BinderContext host.val siteRels}
    {sourcePath : List Nat}
    {sourceRoute : ConcreteCompilerRoute host.val (.openRoot ambient locals)
      site siteContext}
    (sourceDerivation : sourceRoute.Derivation BinderContext.empty sourcePath
      siteBinders)
    (siteSurvives : domains.regions.survives site = true) where
  targetPath : List Nat
  route : ConcreteCompilerRoute (host.val.removeRaw selection domains)
    (.openRoot (domains.mapWireContext ambient)
      (domains.mapWireContext locals))
    (domains.regions.index site siteSurvives)
    (domains.mapWireContext siteContext)
  derivation : route.Derivation BinderContext.empty targetPath
    (domains.mapBinderContext siteBinders)

/-- Transport one open-root source derivation through exact selection
removal.  Root-child positions come only from filtered source occurrences. -/
noncomputable def mapOpenCompilerDerivation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {ambient locals : WireContext host.val}
    {site : Fin host.val.regionCount}
    {siteContext : WireContext host.val}
    {siteRels : Theory.RelCtx}
    {siteBinders : BinderContext host.val siteRels}
    {sourcePath : List Nat}
    {sourceRoute : ConcreteCompilerRoute host.val (.openRoot ambient locals)
      site siteContext}
    (sourceDerivation : sourceRoute.Derivation BinderContext.empty sourcePath
      siteBinders)
    (siteSurvives : domains.regions.survives site = true) :
    MappedOpenCompilerDerivation host selection domains sourceDerivation
      siteSurvives := by
  cases sourceDerivation with
  | root =>
      have rootEq : domains.regions.index host.val.root siteSurvives =
          (host.val.removeRaw selection domains).root := by
        change domains.regions.index host.val.root siteSurvives = domains.root
        unfold FrameDomains.root
        rfl
      let targetRoot : Sigma fun route : ConcreteCompilerRoute
          (host.val.removeRaw selection domains)
          (.openRoot (domains.mapWireContext ambient)
            (domains.mapWireContext locals))
          (domains.regions.index host.val.root siteSurvives)
          (domains.mapWireContext ambient) =>
        route.Derivation BinderContext.empty []
          (domains.mapBinderContext BinderContext.empty) := by
        rw [rootEq, domains.mapBinderContext_empty]
        exact ⟨.root (domains.mapWireContext ambient)
          (domains.mapWireContext locals),
          .root (domains.mapWireContext ambient)
            (domains.mapWireContext locals)⟩
      exact {
        targetPath := []
        route := targetRoot.1
        derivation := targetRoot.2
      }
  | @rootStepCut _ _ child _ _ parent childKind sourceIndex
      sourceOccurrence _ _ _ nestedRoute nestedDerivation =>
      let nestedResult := mapRegionCompilerDerivation host selection domains
        nestedDerivation siteSurvives
      let childSurvives := nestedResult.originSurvives
      let rootSurvives := domains.parent_survives host selection
        childSurvives parent
      let mappedOccurrence := domains.mapChildOccurrenceIndex host selection
        rootSurvives childSurvives sourceIndex sourceOccurrence
      have rootEq : domains.regions.index host.val.root rootSurvives =
          (host.val.removeRaw selection domains).root := by
        change domains.regions.index host.val.root rootSurvives = domains.root
        unfold FrameDomains.root
        rfl
      have targetParent :
          ((host.val.removeRaw selection domains).regions
            (domains.regions.index child childSurvives)).parent? =
            some (host.val.removeRaw selection domains).root := by
        rw [← rootEq]
        exact Diagram.removeRaw_parent host selection domains
          childSurvives parent
      have targetKind :
          (host.val.removeRaw selection domains).regions
              (domains.regions.index child childSurvives) =
            .cut (host.val.removeRaw selection domains).root := by
        rw [← rootEq]
        exact domains.removeRaw_cut host selection rootSurvives
          childSurvives childKind
      have contextEq :
          domains.mapWireContext (ambient ++ locals) =
            domains.mapWireContext ambient ++
              domains.mapWireContext locals :=
        domains.mapWireContext_append ambient locals
      let targetNested : Sigma fun route : ConcreteCompilerRoute
          (host.val.removeRaw selection domains)
          (.region (domains.regions.index child childSurvives)
            (domains.mapWireContext ambient ++
              domains.mapWireContext locals))
          (domains.regions.index site siteSurvives)
          (domains.mapWireContext siteContext) =>
        route.Derivation BinderContext.empty nestedResult.targetPath
          (domains.mapBinderContext siteBinders) := by
        rw [← domains.mapBinderContext_empty, ← contextEq]
        exact ⟨nestedResult.route, nestedResult.derivation⟩
      exact {
        targetPath := mappedOccurrence.index.val :: nestedResult.targetPath
        route := .rootStep targetParent targetNested.1
        derivation := ConcreteCompilerRoute.Derivation.rootStepCut
          targetParent targetKind mappedOccurrence.index
          mappedOccurrence.occurrence targetNested.2
      }
  | @rootStepBubble _ _ child _ _ arity parent childKind sourceIndex
      sourceOccurrence _ _ _ nestedRoute nestedDerivation =>
      let nestedResult := mapRegionCompilerDerivation host selection domains
        nestedDerivation siteSurvives
      let childSurvives := nestedResult.originSurvives
      let rootSurvives := domains.parent_survives host selection
        childSurvives parent
      let mappedOccurrence := domains.mapChildOccurrenceIndex host selection
        rootSurvives childSurvives sourceIndex sourceOccurrence
      have rootEq : domains.regions.index host.val.root rootSurvives =
          (host.val.removeRaw selection domains).root := by
        change domains.regions.index host.val.root rootSurvives = domains.root
        unfold FrameDomains.root
        rfl
      have targetParent :
          ((host.val.removeRaw selection domains).regions
            (domains.regions.index child childSurvives)).parent? =
            some (host.val.removeRaw selection domains).root := by
        rw [← rootEq]
        exact Diagram.removeRaw_parent host selection domains
          childSurvives parent
      have targetKind :
          (host.val.removeRaw selection domains).regions
              (domains.regions.index child childSurvives) =
            .bubble (host.val.removeRaw selection domains).root arity := by
        rw [← rootEq]
        exact domains.removeRaw_bubble host selection rootSurvives
          childSurvives arity childKind
      have contextEq :
          domains.mapWireContext (ambient ++ locals) =
            domains.mapWireContext ambient ++
              domains.mapWireContext locals :=
        domains.mapWireContext_append ambient locals
      let targetNested : Sigma fun route : ConcreteCompilerRoute
          (host.val.removeRaw selection domains)
          (.region (domains.regions.index child childSurvives)
            (domains.mapWireContext ambient ++
              domains.mapWireContext locals))
          (domains.regions.index site siteSurvives)
          (domains.mapWireContext siteContext) =>
        route.Derivation
          (BinderContext.empty.push
            (domains.regions.index child childSurvives) arity)
          nestedResult.targetPath
          (domains.mapBinderContext siteBinders) := by
        rw [← domains.mapBinderContext_empty,
          ← domains.mapBinderContext_push BinderContext.empty child
            childSurvives arity, ← contextEq]
        exact ⟨nestedResult.route, nestedResult.derivation⟩
      exact {
        targetPath := mappedOccurrence.index.val :: nestedResult.targetPath
        route := .rootStep targetParent targetNested.1
        derivation := ConcreteCompilerRoute.Derivation.rootStepBubble
          targetParent targetKind mappedOccurrence.index
          mappedOccurrence.occurrence targetNested.2
      }

end FrameDomains

end VisualProof.Concrete
