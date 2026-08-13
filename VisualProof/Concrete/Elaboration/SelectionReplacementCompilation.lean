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

private theorem nodup_of_map_injective
    (map : α → β)
    (values : List α) (mappedNodup : (values.map map).Nodup) :
    values.Nodup := by
  induction values with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup ⊢
      refine ⟨?_, inductionHypothesis mappedNodup.2⟩
      intro member
      exact mappedNodup.1 (List.mem_map.mpr ⟨head, member, rfl⟩)

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

/-- Compact one source occurrence when it survives the frame removal. -/
def indexOccurrence? (domains : FrameDomains d selection) :
    LocalOccurrence d.regionCount d.nodeCount →
      Option (LocalOccurrence domains.regions.count domains.nodes.count)
  | .node node => (domains.nodes.index? node).map .node
  | .child region => (domains.regions.index? region).map .child

/-- Total occurrence compaction.  The root fallback is unreachable on every
compiler block to which the removal proof applies. -/
def indexOccurrence (domains : FrameDomains d selection) :
    LocalOccurrence d.regionCount d.nodeCount →
      LocalOccurrence domains.regions.count domains.nodes.count := fun value =>
  (domains.indexOccurrence? value).getD (.child domains.root)

theorem indexOccurrence?_eq_some_iff
    (domains : FrameDomains d selection)
    (source : LocalOccurrence d.regionCount d.nodeCount)
    (target : LocalOccurrence domains.regions.count domains.nodes.count) :
    domains.indexOccurrence? source = some target ↔
      domains.originOccurrence target = source := by
  cases source with
  | node node =>
      cases target with
      | child region => simp [indexOccurrence?, originOccurrence]
      | node targetNode =>
          simp only [indexOccurrence?, Option.map_eq_some_iff,
            LocalOccurrence.node.injEq]
          constructor
          · rintro ⟨indexed, found, rfl⟩
            exact congrArg LocalOccurrence.node
              ((domains.nodes.index?_eq_some_iff node indexed).1 found)
          · intro equality
            have originEq : domains.nodes.origin targetNode = node :=
              LocalOccurrence.node.inj equality
            refine ⟨targetNode, ?_, rfl⟩
            rw [← originEq]
            exact domains.nodes.index?_origin targetNode
  | child region =>
      cases target with
      | node node => simp [indexOccurrence?, originOccurrence]
      | child targetRegion =>
          simp only [indexOccurrence?, Option.map_eq_some_iff,
            LocalOccurrence.child.injEq]
          constructor
          · rintro ⟨indexed, found, rfl⟩
            exact congrArg LocalOccurrence.child
              ((domains.regions.index?_eq_some_iff region indexed).1 found)
          · intro equality
            have originEq : domains.regions.origin targetRegion = region :=
              LocalOccurrence.child.inj equality
            refine ⟨targetRegion, ?_, rfl⟩
            rw [← originEq]
            exact domains.regions.index?_origin targetRegion

theorem indexOccurrence?_isSome
    (domains : FrameDomains d selection)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount) :
    (domains.indexOccurrence? occurrence).isSome =
      domains.occurrenceSurvives occurrence := by
  cases occurrence with
  | node node =>
      unfold indexOccurrence? occurrenceSurvives
      change ((domains.nodes.index? node).map LocalOccurrence.node).isSome =
        domains.nodes.survives node
      cases survives : domains.nodes.survives node with
      | false =>
          have missing := (domains.nodes.index?_eq_none_iff node).2 survives
          rw [missing]
          rfl
      | true =>
          rw [domains.nodes.index?_index node survives]
          rfl
  | child region =>
      unfold indexOccurrence? occurrenceSurvives
      change ((domains.regions.index? region).map
        LocalOccurrence.child).isSome = domains.regions.survives region
      cases survives : domains.regions.survives region with
      | false =>
          have missing := (domains.regions.index?_eq_none_iff region).2 survives
          rw [missing]
          rfl
      | true =>
          rw [domains.regions.index?_index region survives]
          rfl

theorem originOccurrence_indexOccurrence
    (domains : FrameDomains d selection)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount)
    (survives : domains.occurrenceSurvives occurrence = true) :
    domains.originOccurrence (domains.indexOccurrence occurrence) =
      occurrence := by
  have present : (domains.indexOccurrence? occurrence).isSome = true := by
    rw [domains.indexOccurrence?_isSome]
    exact survives
  obtain ⟨target, targetEq⟩ := Option.isSome_iff_exists.mp present
  rw [indexOccurrence, targetEq]
  exact (domains.indexOccurrence?_eq_some_iff occurrence target).1 targetEq

theorem originOccurrence_injective
    (domains : FrameDomains d selection) :
    Function.Injective domains.originOccurrence := by
  intro left right equality
  cases left with
  | node left =>
      cases right with
      | child right => contradiction
      | node right =>
          apply congrArg LocalOccurrence.node
          apply domains.nodes.origin_injective
          exact LocalOccurrence.node.inj equality
  | child left =>
      cases right with
      | node right => contradiction
      | child right =>
          apply congrArg LocalOccurrence.child
          apply domains.regions.origin_injective
          exact LocalOccurrence.child.inj equality

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

private theorem removeRaw_climb_origin
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (steps : Nat) (start finish : domains.regions.Carrier)
    (climb : (host.val.removeRaw selection domains).climb steps start =
      some finish) :
    host.val.climb steps (domains.regions.origin start) =
      some (domains.regions.origin finish) := by
  induction steps generalizing start with
  | zero =>
      have equality : start = finish := Option.some.inj climb
      subst finish
      rfl
  | succ steps inductionHypothesis =>
      simp only [Diagram.climb] at climb ⊢
      cases parentEq : ((host.val.removeRaw selection domains).regions
          start).parent? with
      | none => rw [parentEq] at climb; contradiction
      | some parent =>
          rw [parentEq] at climb
          have sourceParent := (domains.removeRaw_parent_eq_iff host selection
            parent start).1 parentEq
          rw [sourceParent]
          exact inductionHypothesis parent climb

/-- Enclosure in the compact frame reflects enclosure between the represented
source regions. -/
theorem removeRaw_encloses_origin
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (ancestor descendant : domains.regions.Carrier)
    (encloses : (host.val.removeRaw selection domains).Encloses ancestor
      descendant) :
    host.val.Encloses (domains.regions.origin ancestor)
      (domains.regions.origin descendant) := by
  obtain ⟨steps, climb⟩ := encloses
  exact ⟨⟨steps.val, by
    have frameBound : steps.val <
        (host.val.removeRaw selection domains).regionCount + 1 := steps.isLt
    have countLe : (host.val.removeRaw selection domains).regionCount ≤
        host.val.regionCount := by
      change domains.regions.count ≤ host.val.regionCount
      exact fin_card_le_of_injective domains.regions.origin
        domains.regions.origin_injective
    have sourceBound : 0 < host.val.regionCount :=
      Nat.zero_lt_of_lt (domains.regions.origin descendant).isLt
    omega⟩, domains.removeRaw_climb_origin host selection steps.val
      descendant ancestor climb⟩

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

/-- When a complete source block survives, dense frame occurrence order is
its pointwise compacted order. -/
theorem localOccurrences_removeRaw_eq_map_index
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : Fin host.val.regionCount)
    (regionSurvives : domains.regions.survives region = true)
    (allSurvive : ∀ occurrence,
      occurrence ∈ localOccurrences host.val region →
        domains.occurrenceSurvives occurrence = true) :
    localOccurrences (host.val.removeRaw selection domains)
        (domains.regions.index region regionSurvives) =
      (localOccurrences host.val region).map domains.indexOccurrence := by
  apply (List.map_inj_right domains.originOccurrence_injective).mp
  have targetOrigins := domains.map_localOccurrences_removeRaw host selection
    (domains.regions.index region regionSurvives)
  rw [domains.regions.origin_index] at targetOrigins
  rw [targetOrigins, List.filter_eq_self.mpr allSurvive]
  rw [List.map_map]
  symm
  calc
    _ = List.map id (localOccurrences host.val region) := by
      apply List.map_congr_left
      intro occurrence member
      exact domains.originOccurrence_indexOccurrence occurrence
        (allSurvive occurrence member)
    _ = _ := List.map_id _

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

/-- A dense frame bubble is represented by the source bubble of the same
arity. -/
theorem removeRaw_bubble_origin
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (binder parent : domains.regions.Carrier) (arity : Nat)
    (kind : (host.val.removeRaw selection domains).regions binder =
      .bubble parent arity) :
    host.val.regions (domains.regions.origin binder) =
      .bubble (domains.regions.origin parent) arity := by
  have reindexed := Diagram.removeRaw_region_reindexed host selection domains
    binder
  cases sourceKind : host.val.regions (domains.regions.origin binder) with
  | sheet =>
      rw [sourceKind] at reindexed
      simp only [SurvivorDomain.reindexRegion?] at reindexed
      rw [← Option.some.inj reindexed] at kind
      contradiction
  | cut sourceParent =>
      have sourceParentEq :
          (host.val.regions (domains.regions.origin binder)).parent? =
            some sourceParent := (congrArg CRegion.parent? sourceKind).trans rfl
      have parentSurvives := domains.parent_survives host selection
        (domains.regions.origin_survives binder) sourceParentEq
      rw [sourceKind] at reindexed
      simp only [SurvivorDomain.reindexRegion?] at reindexed
      rw [domains.regions.index?_index sourceParent parentSurvives] at reindexed
      rw [← Option.some.inj reindexed] at kind
      contradiction
  | bubble sourceParent sourceArity =>
      have sourceParentEq :
          (host.val.regions (domains.regions.origin binder)).parent? =
            some sourceParent := (congrArg CRegion.parent? sourceKind).trans rfl
      have parentSurvives := domains.parent_survives host selection
        (domains.regions.origin_survives binder) sourceParentEq
      rw [sourceKind] at reindexed
      simp only [SurvivorDomain.reindexRegion?] at reindexed
      rw [domains.regions.index?_index sourceParent parentSurvives] at reindexed
      have targetKind := Option.some.inj reindexed
      have parts := CRegion.bubble.inj (targetKind.trans kind)
      have parentEq : domains.regions.index sourceParent parentSurvives =
          parent := parts.1
      have arityEq : sourceArity = arity := parts.2
      subst sourceArity
      apply congrArg (fun value => CRegion.bubble value arity)
      rw [← parentEq, domains.regions.origin_index]

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

/-- Exact lexical visibility descends to the dense survivor frame. -/
theorem mapWireContext_exact
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val)
    (region : domains.regions.Carrier)
    (exact : context.Exact (domains.regions.origin region)) :
    (domains.mapWireContext context).Exact region := by
  constructor
  · apply nodup_of_map_injective domains.wires.origin
    rw [domains.map_mapWireContext_origin]
    exact exact.nodup.filter _
  · intro wire
    constructor
    · intro targetMember
      obtain ⟨sourceWire, sourceMember, indexed⟩ :=
        List.mem_filterMap.mp targetMember
      have sourceEq := (domains.wires.index?_eq_some_iff sourceWire wire).1
        indexed
      subst sourceWire
      have sourceEncloses := (exact.mem_iff _).1 sourceMember
      have scopeSurvives := domains.wireScope_survives
        (domains.wires.origin_survives wire)
      have targetEncloses := Diagram.removeRaw_encloses host selection domains
        scopeSurvives (domains.regions.origin_survives region) sourceEncloses
      have scopeEq := Diagram.removeRaw_wire_scope host selection domains wire
      rw [domains.regions.index_origin] at targetEncloses
      rw [scopeEq]
      exact targetEncloses
    · intro targetEncloses
      have reflected := domains.removeRaw_encloses_origin host selection
        ((host.val.removeRaw selection domains).wires wire).scope region
        targetEncloses
      have scopeEq := Diagram.removeRaw_wire_scope host selection domains wire
      rw [scopeEq, domains.regions.origin_index] at reflected
      have sourceMember := (exact.mem_iff _).2 reflected
      exact List.mem_filterMap.mpr
        ⟨domains.wires.origin wire, sourceMember,
          domains.wires.index?_origin wire⟩

/-- Every wire visible strictly above the selected anchor survives removal.
The only removable visible wires are owned exactly at, or below, the anchor. -/
theorem visibleWire_survives_above
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : Fin host.val.regionCount)
    (above : host.val.Encloses region selection.val.anchor)
    (different : region ≠ selection.val.anchor)
    (context : WireContext host.val) (exact : context.Exact region)
    (wire : Fin host.val.wireCount) (member : wire ∈ context) :
    domains.wires.survives wire = true := by
  apply (domains.wire_survives_iff wire).2
  intro removed
  have scopeEnclosesRegion : host.val.Encloses
      (host.val.wires wire).scope region := (exact.mem_iff wire).1 member
  have scopeEnclosesAnchor := checked_encloses_trans host.property
    scopeEnclosesRegion above
  rcases (selection.mem_internalWires_expanded wire).1 removed with
    selectedScope | explicit
  · obtain ⟨child, childMember, childEnclosesScope⟩ := selectedScope
    have childParent := selection.property.childRoots_direct child childMember
    have anchorEnclosesChild : host.val.Encloses selection.val.anchor child := by
      refine ⟨⟨1, by omega⟩, ?_⟩
      simp [Diagram.climb, childParent]
    have anchorEnclosesScope := checked_encloses_trans host.property
      anchorEnclosesChild childEnclosesScope
    have scopeEq := checked_encloses_antisymm host.property
      scopeEnclosesAnchor anchorEnclosesScope
    rw [scopeEq] at scopeEnclosesRegion
    have regionEq := checked_encloses_antisymm host.property
      above scopeEnclosesRegion
    exact different regionEq
  · have scopeEq := selection.property.explicitWires_at_anchor wire explicit
    rw [scopeEq] at scopeEnclosesRegion
    have regionEq := checked_encloses_antisymm host.property
      scopeEnclosesRegion above
    exact different regionEq.symm

/-- Every direct occurrence of a surviving region outside the selected
subtree survives. -/
theorem localOccurrence_survives_away
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : Fin host.val.regionCount)
    (regionSurvives : domains.regions.survives region = true)
    (away : ¬ host.val.Encloses region selection.val.anchor)
    (occurrence : LocalOccurrence host.val.regionCount host.val.nodeCount)
    (member : occurrence ∈ localOccurrences host.val region) :
    domains.occurrenceSurvives occurrence = true := by
  cases occurrence with
  | node node =>
      change domains.nodes.survives node = true
      apply (domains.node_survives_iff node).2
      intro selected
      have nodeRegion := (mem_localOccurrences_node host.val region node).mp
        member
      rcases (selection.mem_selectedNodes node).1 selected with
        direct | selectedRegion
      · have atAnchor := selection.property.directNodes_at_anchor node direct
        have regionEq : region = selection.val.anchor :=
          nodeRegion.symm.trans atAnchor
        apply away
        rw [regionEq]
        exact Diagram.Encloses.refl host.val selection.val.anchor
      · have ownerSelected : region ∈ selection.selectedRegions := by
          rw [← nodeRegion]
          exact (selection.mem_selectedRegions _).2 selectedRegion
        rcases (domains.region_survives_iff region).1 regionSurvives with
          regionRoot | regionNotSelected
        ·
          obtain ⟨selectedRoot, selectedRootMember, selectedRootEncloses⟩ :=
            (selection.mem_selectedRegions _).1 ownerSelected
          have selectedRootEnclosesRoot : host.val.Encloses selectedRoot
              host.val.root := by
            simpa only [regionRoot] using selectedRootEncloses
          have impossible := encloses_sheet_eq host.property.root_is_sheet
            selectedRootEnclosesRoot
          subst selectedRoot
          have selectedRootParent := selection.property.childRoots_direct
            host.val.root selectedRootMember
          rw [host.property.root_is_sheet] at selectedRootParent
          contradiction
        · exact regionNotSelected ownerSelected
  | child child =>
      change domains.regions.survives child = true
      apply (domains.region_survives_iff child).2
      by_cases atRoot : child = host.val.root
      · exact Or.inl atRoot
      · right
        intro selected
        have childParent := (mem_localOccurrences_child host.val region child).mp
          member
        obtain ⟨root, rootMember, rootEnclosesChild⟩ :=
          (selection.mem_selectedRegions child).1 selected
        rcases encloses_direct_child childParent rootEnclosesChild with
          rootEq | rootEnclosesRegion
        · subst child
          have rootParent := selection.property.childRoots_direct root rootMember
          have regionEq := Option.some.inj (childParent.symm.trans rootParent)
          subst region
          exact away (Diagram.Encloses.refl host.val selection.val.anchor)
        · have selectedRegion : region ∈ selection.selectedRegions :=
            (selection.mem_selectedRegions region).2
              ⟨root, rootMember, rootEnclosesRegion⟩
          rcases (domains.region_survives_iff region).1 regionSurvives with
            regionRoot | regionNotSelected
          · subst region
            have rootEq := encloses_sheet_eq host.property.root_is_sheet
              rootEnclosesRegion
            subst root
            have rootParent := selection.property.childRoots_direct
              host.val.root rootMember
            rw [host.property.root_is_sheet] at rootParent
            contradiction
          · exact regionNotSelected selectedRegion

/-- Compaction is position-preserving when every wire in the source context
survives. -/
theorem mapWireContext_origin_eq
    (domains : FrameDomains d selection) (context : WireContext d)
    (allSurvive : ∀ wire, wire ∈ context →
      domains.wires.survives wire = true) :
    (domains.mapWireContext context).map domains.wires.origin = context := by
  rw [domains.map_mapWireContext_origin]
  exact List.filter_eq_self.mpr allSurvive

/-- Canonical position equivalence for an unchanged lexical context. -/
noncomputable def mapWireContextEquiv
    (domains : FrameDomains d selection) (context : WireContext d)
    (allSurvive : ∀ wire, wire ∈ context →
      domains.wires.survives wire = true) :
    FiniteEquiv (Fin (domains.mapWireContext context).length)
      (Fin context.length) := by
  apply FiniteEquiv.finCast
  simpa using congrArg List.length
    (domains.mapWireContext_origin_eq context allSurvive)

/-- The unchanged-context equivalence retrieves the represented source wire. -/
theorem mapWireContextEquiv_get
    (domains : FrameDomains d selection) (context : WireContext d)
    (allSurvive : ∀ wire, wire ∈ context →
      domains.wires.survives wire = true)
    (index : Fin (domains.mapWireContext context).length) :
    context.get (domains.mapWireContextEquiv context allSurvive index) =
      domains.wires.origin ((domains.mapWireContext context).get index) := by
  have equality := domains.mapWireContext_origin_eq context allSurvive
  have lengthEq : (domains.mapWireContext context).length = context.length := by
    simpa using congrArg List.length equality
  let sourceIndex : Fin context.length := ⟨index.val, by
    rw [← lengthEq]
    exact index.isLt⟩
  have positionEq : domains.mapWireContextEquiv context allSurvive index =
      sourceIndex := by
    apply Fin.ext
    rfl
  have point := congrArg (fun values => values[index.val]?) equality
  have mappedBound : index.val <
      ((domains.mapWireContext context).map domains.wires.origin).length := by
    rw [List.length_map]
    exact index.isLt
  have sourceBound : index.val < context.length := sourceIndex.isLt
  dsimp only at point
  rw [List.getElem?_eq_getElem mappedBound,
    List.getElem?_eq_getElem sourceBound] at point
  rw [positionEq]
  simpa only [List.get_eq_getElem, List.getElem_map] using
    (Option.some.inj point).symm

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

/-- Lexical binder coverage descends to the dense survivor frame. -/
theorem mapBinderContext_covers
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : BinderContext host.val rels)
    (region : domains.regions.Carrier)
    (covers : context.Covers (domains.regions.origin region)) :
    (domains.mapBinderContext context).Covers region := by
  intro binder parent arity bubble encloses
  have sourceBubble := domains.removeRaw_bubble_origin host selection
    binder parent arity bubble
  have sourceEncloses := domains.removeRaw_encloses_origin host selection
    binder region encloses
  obtain ⟨relation, lookup⟩ := covers (domains.regions.origin binder)
    (domains.regions.origin parent) arity sourceBubble sourceEncloses
  exact ⟨relation, by simpa [mapBinderContext] using lookup⟩

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

/-- The exact compacted call is total from the source lexical certificates;
no frame compiler result is accepted as input. -/
private theorem mappedCallCompilation
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (call : CompilerCall host.val)
    (originSurvives : domains.regions.survives call.origin = true)
    (exact : call.fullContext.Exact call.origin)
    (covers : call.binders.Covers call.origin) :
    ∃ body : CompiledRegion (host.val.removeRaw selection domains)
        (domains.mappedCall call originSurvives),
      (domains.mappedCall call originSurvives).compile?
          (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains) = some body := by
  let targetCall := domains.mappedCall call originSurvives
  have targetExact : targetCall.fullContext.Exact targetCall.origin := by
    rw [domains.mappedCall_origin call originSurvives,
      domains.mappedCall_fullContext host selection call originSurvives]
    exact domains.mapWireContext_exact host selection call.fullContext
      (domains.regions.index call.origin originSurvives) (by
        simpa only [domains.regions.origin_index] using exact)
  have targetCovers : targetCall.binders.Covers targetCall.origin := by
    rw [domains.mappedCall_origin call originSurvives]
    cases call with
    | root outer locals =>
        exact domains.mapBinderContext_covers host selection
          BinderContext.empty (domains.regions.index host.val.root
            originSurvives) (by
              simpa only [domains.regions.origin_index] using covers)
    | nested origin context rels binders =>
        exact domains.mapBinderContext_covers host selection binders
          (domains.regions.index origin originSurvives) (by
            simpa only [domains.regions.origin_index] using covers)
  exact CompilerCall.compile?_complete
    (Diagram.removeRaw_wellFormed host selection domains) targetCall
      targetExact targetCovers

end FrameDomains

end VisualProof.Concrete
