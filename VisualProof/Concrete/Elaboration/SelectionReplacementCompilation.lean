import VisualProof.Concrete.Elaboration.SpliceRootCompilation

/-! Source-derived elaboration for the flat selection-replacement primitive. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Elaboration

private theorem State.eq_of_checked_val_eq
    (left right : State arity)
    (checkedEq : left.checked.val = right.checked.val) : left = right := by
  rcases left with ⟨leftChecked, leftBoundaryLength⟩
  rcases right with ⟨rightChecked, rightBoundaryLength⟩
  dsimp only at checkedEq ⊢
  have checkedSubtypeEq : leftChecked = rightChecked := Subtype.ext checkedEq
  subst rightChecked
  have boundaryLengthEq : leftBoundaryLength = rightBoundaryLength :=
    Subsingleton.elim _ _
  subst rightBoundaryLength
  rfl

/-- The unique removal and splice receipts underlying one successful flat
selection replacement.  This is proof-only decomposition of the existing
primitive receipt, not an alternate execution path. -/
structure SelectionReplacementDecomposition
    {arity : Nat} (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (operation : OperationReceipt source.diagram)
    (receipt : Receipt source) where
  prepared : PreparedSelectionReplacement source.diagram selection replacement
  spliced : OperationReceipt prepared.spliceInput.frame
  prepared_success :
    prepareSelectionReplacement source.diagram selection replacement =
      .ok prepared
  splice_success : spliceRaw prepared.spliceInput = .ok spliced
  operation_eq : operation = prepared.composeReceipt spliced
  frameReceipt : Receipt source
  frame_packed : prepared.frameReceipt.toReceipt source = some frameReceipt
  prepared_frame_eq : prepared.frame = frameReceipt.target.diagram
  splice_frame_eq : prepared.spliceInput.frame = frameReceipt.target.diagram
  spliceReceipt : Receipt frameReceipt.target
  splice_packed :
    (spliced.castInput splice_frame_eq).toReceipt frameReceipt.target =
      some spliceReceipt
  target_eq : spliceReceipt.target = receipt.target

/-- Split a successful flat replacement receipt at its computed intermediate
frame boundary. -/
noncomputable def replaceSelectionRaw_decomposition
    {arity : Nat} (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (replacement : SelectionReplacement source.diagram selection)
    (operation : OperationReceipt source.diagram)
    (receipt : Receipt source)
    (success : replaceSelectionRaw source.diagram selection replacement =
      .ok operation)
    (packed : operation.toReceipt source = some receipt) :
    SelectionReplacementDecomposition source selection replacement operation
      receipt := by
  unfold replaceSelectionRaw at success
  split at success <;> try contradiction
  rename_i prepared preparedSuccess
  split at success <;> try contradiction
  rename_i spliced spliceSuccess
  cases success
  unfold OperationReceipt.toReceipt at packed
  split at packed <;> try contradiction
  rename_i finalBoundary finalTransport
  cases packed
  let splicedAtFrame := spliced.castInput prepared.spliceFrameEq
  have composedTransport :
      (prepared.frameTransport.compose
        splicedAtFrame.interface).transportBoundary
          source.checked.val.boundary = some finalBoundary := by
    simpa only [PreparedSelectionReplacement.composeReceipt] using
      finalTransport
  let boundaryDecomposition :=
    (WireTransport.transportBoundary_compose_iff prepared.frameTransport
      splicedAtFrame.interface source.checked.val.boundary
      finalBoundary).1 composedTransport
  let intermediateBoundary := Classical.choose boundaryDecomposition
  have frameTransport := (Classical.choose_spec boundaryDecomposition).1
  have spliceTransport := (Classical.choose_spec boundaryDecomposition).2
  let frameChecked : CheckedOpen := {
    val := {
      diagram := prepared.frame.val
      boundary := intermediateBoundary
    }
    property := {
      diagram_well_formed := prepared.frame.property
      boundary_is_root_scoped :=
        prepared.frameTransport.transportBoundary_root_scoped
          source.checked.property.boundary_is_root_scoped frameTransport
    }
  }
  let frameState : State arity := {
    checked := frameChecked
    boundary_length :=
      (prepared.frameTransport.transportBoundary_length frameTransport).trans
        source.boundary_length
  }
  let frameReceipt : Receipt source := {
    target := frameState
    provenance := prepared.frameProvenance
    boundary := {
      image := fun position => frameState.checked.val.boundary.get
        (Fin.cast frameState.boundary_length.symm position)
      target_boundary := fun _ => rfl
    }
  }
  have framePacked : prepared.frameReceipt.toReceipt source =
      some frameReceipt := by
    unfold OperationReceipt.toReceipt
    split
    · rename_i transported
      change prepared.frameTransport.transportBoundary
        source.checked.val.boundary = none at transported
      have impossible :
          (none : Option (List (Fin prepared.frame.val.wireCount))) =
            some intermediateBoundary := transported.symm.trans frameTransport
      contradiction
    · rename_i mapped transported
      change prepared.frameTransport.transportBoundary
        source.checked.val.boundary = some mapped at transported
      have mappedEq : mapped = intermediateBoundary :=
        Option.some.inj (transported.symm.trans frameTransport)
      subst mapped
      rfl
  have preparedFrameEq : prepared.frame = frameReceipt.target.diagram := rfl
  have spliceFrameEq : prepared.spliceInput.frame =
      frameReceipt.target.diagram :=
    prepared.spliceFrameEq.trans preparedFrameEq
  let splicedAtIntermediate := spliced.castInput spliceFrameEq
  have spliceTransportAtIntermediate :
      splicedAtIntermediate.interface.transportBoundary
          frameReceipt.target.checked.val.boundary = some finalBoundary := by
    simpa only [splicedAtIntermediate, spliceFrameEq, preparedFrameEq,
      frameReceipt, frameState, frameChecked] using spliceTransport
  let spliceChecked : CheckedOpen := {
    val := {
      diagram := splicedAtIntermediate.result.val
      boundary := finalBoundary
    }
    property := {
      diagram_well_formed := splicedAtIntermediate.result.property
      boundary_is_root_scoped :=
        splicedAtIntermediate.interface.transportBoundary_root_scoped
          frameReceipt.target.checked.property.boundary_is_root_scoped
          spliceTransportAtIntermediate
    }
  }
  let spliceState : State arity := {
    checked := spliceChecked
    boundary_length :=
      (splicedAtIntermediate.interface.transportBoundary_length
        spliceTransportAtIntermediate).trans
          frameReceipt.target.boundary_length
  }
  let spliceReceipt : Receipt frameReceipt.target := {
    target := spliceState
    provenance := splicedAtIntermediate.provenance
    boundary := {
      image := fun position => spliceState.checked.val.boundary.get
        (Fin.cast spliceState.boundary_length.symm position)
      target_boundary := fun _ => rfl
    }
  }
  have splicePacked : splicedAtIntermediate.toReceipt frameReceipt.target =
      some spliceReceipt := by
    unfold OperationReceipt.toReceipt
    split
    · rename_i transported
      have impossible :
          (none : Option (List
            (Fin splicedAtIntermediate.result.val.wireCount))) =
              some finalBoundary :=
        transported.symm.trans spliceTransportAtIntermediate
      contradiction
    · rename_i mapped transported
      have mappedEq : mapped = finalBoundary :=
        Option.some.inj
          (transported.symm.trans spliceTransportAtIntermediate)
      subst mapped
      rfl
  have targetEq : spliceReceipt.target =
      ({
        checked := {
          val := {
            diagram := (prepared.composeReceipt spliced).result.val
            boundary := finalBoundary
          }
          property := {
            diagram_well_formed :=
              (prepared.composeReceipt spliced).result.property
            boundary_is_root_scoped :=
              (prepared.composeReceipt spliced).interface
                |>.transportBoundary_root_scoped
                  source.checked.property.boundary_is_root_scoped
                  finalTransport
          }
        }
        boundary_length :=
          ((prepared.composeReceipt spliced).interface
            |>.transportBoundary_length finalTransport).trans
              source.boundary_length
      } : State arity) := by
    apply State.eq_of_checked_val_eq
    rfl
  exact {
    prepared := prepared
    spliced := spliced
    prepared_success := preparedSuccess
    splice_success := spliceSuccess
    operation_eq := rfl
    frameReceipt := frameReceipt
    frame_packed := framePacked
    prepared_frame_eq := preparedFrameEq
    splice_frame_eq := spliceFrameEq
    spliceReceipt := spliceReceipt
    splice_packed := splicePacked
    target_eq := targetEq
  }

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
  unfold localOccurrences localNodeOccurrences localChildOccurrences
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

/-- Compile one retained dense node from its source compiler result.  The
erasure equation points back into the source context; no target node result is
supplied by the caller. -/
private theorem mapNodeCompilation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val) (contextNodup : context.Nodup)
    (binders : BinderContext host.val rels)
    (node : domains.nodes.Carrier)
    {sourceItem : CompiledItem host.val context rels binders}
    (sourceCompiled : compileNode? host.val context binders
      (domains.nodes.origin node) = some sourceItem) :
    ∃ targetItem : CompiledItem (host.val.removeRaw selection domains)
        (domains.mapWireContext context) rels
        (domains.mapBinderContext binders),
      compileNode? (host.val.removeRaw selection domains)
          (domains.mapWireContext context) (domains.mapBinderContext binders)
          node = some targetItem ∧
      sourceItem.erase =
        (targetItem.erase.renameWires
          (domains.mapWireContextOriginIndex context)).renameRelations
            (fun relation => relation) := by
  have mapped := compileNode?_map
    (source := host.val.removeRaw selection domains) (target := host.val)
    (domains.mapWireContext context) context
    (domains.mapBinderContext binders) binders node
    (domains.nodes.origin node) domains.regions.origin
    domains.regions.origin (domains.mapWireContextOriginIndex context)
    (fun relation => relation)
    (by
      have nodeOrigin := domains.removeRaw_node_origin host selection node
      cases targetKind : (host.val.removeRaw selection domains).nodes node with
      | atom region binder => simpa [targetKind] using nodeOrigin
      | identity region arity => simpa [targetKind] using nodeOrigin)
    (domains.resolvePort?_removeRaw_origin_map host selection context
      contextNodup node)
    (by
      intro region binder nodeKind
      change binders (domains.regions.origin binder) =
        (binders (domains.regions.origin binder)).map _
      cases binders (domains.regions.origin binder) with
      | none => rfl
      | some value => cases value; rfl)
  rw [sourceCompiled] at mapped
  cases targetCompiled : compileNode? (host.val.removeRaw selection domains)
      (domains.mapWireContext context) (domains.mapBinderContext binders) node
      with
  | none => simp [targetCompiled] at mapped
  | some targetItem =>
      refine ⟨targetItem, rfl, ?_⟩
      rw [targetCompiled] at mapped
      exact Option.some.inj mapped

/-- The exact frame compiler call represented by one surviving source call. -/
private def mappedCall
    (domains : FrameDomains d selection) (call : CompilerCall d)
    (originSurvives : domains.regions.survives call.origin = true) :
    CompilerCall (d.removeRaw selection domains) :=
  match call with
  | .root outer locals =>
      .root (domains.mapWireContext outer) (domains.mapWireContext locals)
  | .nested origin context rels binders =>
      .nested (domains.regions.index origin originSurvives)
        (domains.mapWireContext context) rels
        (domains.mapBinderContext binders)

@[simp] private theorem mappedCall_origin
    (domains : FrameDomains d selection) (call : CompilerCall d)
    (originSurvives : domains.regions.survives call.origin = true) :
    (domains.mappedCall call originSurvives).origin =
      domains.regions.index call.origin originSurvives := by
  cases call with
  | root outer locals =>
      change domains.root = domains.regions.index d.root originSurvives
      apply domains.regions.origin_injective
      rw [domains.root_origin, domains.regions.origin_index]
  | nested origin context rels binders => rfl

private theorem mappedCall_fullContext
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection) (call : CompilerCall host.val)
    (originSurvives : domains.regions.survives call.origin = true) :
    (domains.mappedCall call originSurvives).fullContext =
      domains.mapWireContext call.fullContext := by
  cases call with
  | root outer locals =>
      simpa [mappedCall, CompilerCall.fullContext] using
        (domains.mapWireContext_append outer locals).symm
  | nested origin context rels binders =>
      simp only [mappedCall, CompilerCall.fullContext,
        CompilerCall.localContext]
      rw [domains.mapWireContext_append]
      apply congrArg (domains.mapWireContext context ++ ·)
      have localEq := domains.mapWireContext_exactScope host selection
        (domains.regions.index origin originSurvives)
      rw [domains.regions.origin_index] at localEq
      exact localEq.symm

end FrameDomains

end VisualProof.Concrete
