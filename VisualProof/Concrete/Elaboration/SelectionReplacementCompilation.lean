import VisualProof.Concrete.Elaboration.SpliceRootCompilation

/-! Source-derived elaboration for the flat selection-replacement primitive. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Elaboration

private theorem OpenDiagram.eq_of_parts
    (left right : OpenDiagram)
    (diagramEq : left.diagram = right.diagram)
    (boundaryEq : left.boundary.map
        (Fin.cast (congrArg Diagram.wireCount diagramEq)) = right.boundary) :
    left = right := by
  rcases left with ⟨leftDiagram, leftBoundary⟩
  rcases right with ⟨rightDiagram, rightBoundary⟩
  dsimp only at diagramEq boundaryEq ⊢
  cases diagramEq
  have castFunction : Fin.cast (congrArg Diagram.wireCount
      (Eq.refl leftDiagram)) = id := by
    funext index
    apply Fin.ext
    rfl
  rw [castFunction, List.map_id] at boundaryEq
  subst rightBoundary
  rfl

private theorem List.filterMap_cast_self
    (values : List α) (map : α → Option (Fin count))
    (equality : count = count) :
    values.filterMap (fun value => (map value).map (Fin.cast equality)) =
      values.filterMap map := by
  have castFunction : Fin.cast equality = id := by
    funext index
    apply Fin.ext
    rfl
  rw [castFunction]
  simp

private theorem compileOccurrence?_congr_occurrence
    {d : Diagram} (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    {left right : LocalOccurrence d.regionCount d.nodeCount}
    (occurrenceEq : left = right)
    (leftDirect : left ∈ localOccurrences d parent)
    (rightDirect : right ∈ localOccurrences d parent) :
    compileOccurrence? d hwf parent context binders left leftDirect =
      compileOccurrence? d hwf parent context binders right rightDirect := by
  subst right
  rfl

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
  let splicedAtFrame : OperationReceipt prepared.frame := by
    simpa [PreparedSelectionReplacement.spliceInput,
      PreparedSelectionReplacement.frame] using spliced
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
      frameReceipt.target.diagram := by
    simpa [PreparedSelectionReplacement.spliceInput,
      PreparedSelectionReplacement.frame] using preparedFrameEq
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

/-- Successful packing of the intermediate removal frame proves that every
open-interface wire survived the selected material removal. -/
theorem SelectionReplacementDecomposition.exposedWire_survives
    (decomposition : SelectionReplacementDecomposition source selection
      replacement operation receipt)
    (wire : Fin source.checked.val.diagram.wireCount)
    (member : wire ∈ source.checked.val.exposedWires) :
    decomposition.prepared.domains.wires.survives wire = true := by
  have boundaryMember : wire ∈ source.checked.val.boundary :=
    (OpenDiagram.mem_exposedWires source.checked.val wire).mp member
  obtain ⟨position, positionEq⟩ := List.mem_iff_get.mp boundaryMember
  subst wire
  have transported := decomposition.prepared.frameTransport.transportBoundary_get
    (decomposition.prepared.frameReceipt.toReceipt_boundary
      decomposition.frame_packed) position
  cases rejected : decomposition.prepared.domains.wires.survives
      (source.checked.val.boundary.get position) with
  | false =>
      have imageNone : decomposition.prepared.frameTransport.image?
          (source.checked.val.boundary.get position) = none := by
        exact WireTransport.survivors_image?_eq_none
          decomposition.prepared.domains.wires rfl
          (source.checked.val.boundary.get position) rejected
      have impossible := imageNone.symm.trans transported
      contradiction
  | true => rfl

private theorem WireTransport.survivors_transportBoundary_eq_filterMap
    (source target : Diagram)
    (domain : SurvivorDomain source.wireCount)
    (wireCountEq : target.wireCount = domain.count)
    {boundary : List (Fin source.wireCount)}
    {mapped : List (Fin target.wireCount)}
    (success : (WireTransport.survivors source target domain wireCountEq
      ).transportBoundary boundary = some mapped) :
    mapped = boundary.filterMap fun wire =>
      (domain.index? wire).map (Fin.cast wireCountEq.symm) := by
  induction boundary generalizing mapped with
  | nil => simpa [WireTransport.transportBoundary] using
      Option.some.inj success
  | cons head tail inductionHypothesis =>
      cases indexed : domain.index? head with
      | none =>
          have imageNone :
              (WireTransport.survivors source target domain wireCountEq
                ).image? head = none := by
            simp [WireTransport.survivors, WireTransport.rootFiltered,
              indexed]
          simp [WireTransport.transportBoundary, imageNone] at success
      | some dense =>
          let targetWire := Fin.cast wireCountEq.symm dense
          have candidate :
              (domain.index? head).map (Fin.cast wireCountEq.symm) =
                some targetWire := by
            rw [indexed]
            rfl
          by_cases rootScoped : (target.wires targetWire).scope = target.root
          · have imageSome :
                (WireTransport.survivors source target domain wireCountEq
                  ).image? head = some targetWire := by
              change (do
                let mapped ← (domain.index? head).map
                  (Fin.cast wireCountEq.symm)
                if (target.wires mapped).scope = target.root then
                  some mapped else none) = some targetWire
              rw [indexed]
              simp only [Option.map_some]
              change (if (target.wires targetWire).scope = target.root then
                some targetWire else none) = some targetWire
              rw [if_pos rootScoped]
            cases tailResult :
                (WireTransport.survivors source target domain wireCountEq
                  ).transportBoundary tail with
            | none =>
                simp [WireTransport.transportBoundary, imageSome, tailResult]
                  at success
            | some mappedTail =>
                have mappedEq : targetWire :: mappedTail = mapped := by
                  simpa [WireTransport.transportBoundary, imageSome,
                    tailResult] using success
                subst mapped
                simp only [List.filterMap_cons, candidate]
                rw [inductionHypothesis tailResult]
          ·
            have imageNone :
                (WireTransport.survivors source target domain wireCountEq
                  ).image? head = none := by
              change (do
                let mapped ← (domain.index? head).map
                  (Fin.cast wireCountEq.symm)
                if (target.wires mapped).scope = target.root then
                  some mapped else none) = none
              rw [indexed]
              simp only [Option.map_some]
              change (if (target.wires targetWire).scope = target.root then
                some targetWire else none) = none
              rw [if_neg rootScoped]
            simp [WireTransport.transportBoundary, imageNone] at success

namespace FrameDomains

/-- Distinct direct children cannot both enclose the same selected site. -/
theorem sibling_not_encloses
    (host : Checked)
    {parent selected sibling site : Fin host.val.regionCount}
    (selectedParent : (host.val.regions selected).parent? = some parent)
    (siblingParent : (host.val.regions sibling).parent? = some parent)
    (different : sibling ≠ selected)
    (selectedEncloses : host.val.Encloses selected site) :
    ¬ host.val.Encloses sibling site := by
  intro siblingEncloses
  rcases host.val.enclosingRegions_comparable selectedEncloses
      siblingEncloses with selectedSibling | siblingSelected
  · rcases encloses_direct_child siblingParent selectedSibling with
      same | selectedParentEncloses
    · exact different same.symm
    · exact checked_direct_child_not_encloses_parent host.property
        selectedParent selectedParentEncloses
  · rcases encloses_direct_child selectedParent siblingSelected with
      same | siblingParentEncloses
    · exact different same
    · exact checked_direct_child_not_encloses_parent host.property
        siblingParent siblingParentEncloses

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

@[simp] theorem indexOccurrence_node
    (domains : FrameDomains d selection) (node : Fin d.nodeCount)
    (survives : domains.nodes.survives node = true) :
    domains.indexOccurrence (.node node) =
      .node (domains.nodes.index node survives) := by
  unfold indexOccurrence indexOccurrence?
  change ((domains.nodes.index? node).map LocalOccurrence.node).getD
      (.child domains.root) = _
  rw [domains.nodes.index?_index node survives]
  rfl

@[simp] theorem indexOccurrence_child
    (domains : FrameDomains d selection) (region : Fin d.regionCount)
    (survives : domains.regions.survives region = true) :
    domains.indexOccurrence (.child region) =
      .child (domains.regions.index region survives) := by
  unfold indexOccurrence indexOccurrence?
  change ((domains.regions.index? region).map LocalOccurrence.child).getD
      (.child domains.root) = _
  rw [domains.regions.index?_index region survives]
  rfl

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

/-- Dense frame occurrence order is the stable compaction of precisely the
surviving source occurrences. -/
theorem localOccurrences_removeRaw_eq_map_filter
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : domains.regions.Carrier) :
    localOccurrences (host.val.removeRaw selection domains) region =
      ((localOccurrences host.val (domains.regions.origin region)).filter
        domains.occurrenceSurvives).map domains.indexOccurrence := by
  apply (List.map_inj_right domains.originOccurrence_injective).mp
  rw [domains.map_localOccurrences_removeRaw host selection region,
    List.map_map]
  symm
  calc
    _ = List.map id
        ((localOccurrences host.val
          (domains.regions.origin region)).filter
            domains.occurrenceSurvives) := by
      apply List.map_congr_left
      intro occurrence member
      exact domains.originOccurrence_indexOccurrence occurrence
        (List.mem_filter.mp member).2
    _ = _ := List.map_id _

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

/-- The canonical open survivor frame, including the exact ordered boundary
transport used by selection replacement. -/
def frameOpen (source : OpenDiagram) (selection : CheckedSelection source.diagram)
    (domains : FrameDomains source.diagram selection) : OpenDiagram where
  diagram := source.diagram.removeRaw selection domains
  boundary := source.boundary.filterMap domains.wires.index?

/-- The intermediate receipt is exactly the canonical open survivor frame;
its boundary is derived from the receipt transport rather than selected
independently. -/
theorem SelectionReplacementDecomposition.frame_open_eq
    (decomposition : SelectionReplacementDecomposition source selection
      replacement operation receipt) :
    decomposition.frameReceipt.target.checked.val =
      decomposition.prepared.domains.frameOpen source.checked.val selection := by
  have transported := decomposition.prepared.frameReceipt.toReceipt_boundary
    decomposition.frame_packed
  have boundaryEq :
      decomposition.frameReceipt.target.checked.val.boundary.map
          (Fin.cast (congrArg Diagram.wireCount
            (decomposition.prepared.frameReceipt.toReceipt_result
              decomposition.frame_packed))) =
        source.checked.val.boundary.filterMap
          decomposition.prepared.domains.wires.index? := by
    let wireCountEq : decomposition.prepared.frame.val.wireCount =
        decomposition.prepared.domains.wires.count := rfl
    have exactBoundary :=
      WireTransport.survivors_transportBoundary_eq_filterMap
        source.checked.val.diagram decomposition.prepared.frame.val
        decomposition.prepared.domains.wires wireCountEq transported
    have wireCountEqRefl : wireCountEq = rfl := Subsingleton.elim _ _
    rw [wireCountEqRefl] at exactBoundary
    exact exactBoundary.trans (List.filterMap_cast_self
      source.checked.val.boundary
      decomposition.prepared.domains.wires.index? _)
  exact OpenDiagram.eq_of_parts _ _
    (decomposition.prepared.frameReceipt.toReceipt_result
      decomposition.frame_packed) boundaryEq

private theorem eraseDups_filterMap_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (map : α → Option β)
    (injective : ∀ {left right value}, map left = some value →
      map right = some value → left = right)
    (values : List α) :
    (values.filterMap map).eraseDups = values.eraseDups.filterMap map := by
  cases values with
  | nil => rfl
  | cons head tail =>
      cases found : map head with
      | none =>
          rw [List.filterMap_cons_none found, List.eraseDups_cons]
          have filterEq :
              (tail.filter fun value => !value == head).filterMap map =
                tail.filterMap map := by
            induction tail with
            | nil => rfl
            | cons value rest ih =>
                by_cases equality : value = head
                · subst value
                  simp [found, ih]
                · cases valueFound : map value <;>
                    simp [valueFound, beq_false_of_ne equality, ih]
          rw [List.filterMap_cons_none found]
          calc
            (tail.filterMap map).eraseDups =
                ((tail.filter fun value => !value == head).filterMap map
                  ).eraseDups := congrArg List.eraseDups filterEq.symm
            _ = _ := eraseDups_filterMap_injective map injective
              (tail.filter fun value => !value == head)
      | some mapped =>
          rw [List.filterMap_cons_some found, List.eraseDups_cons,
            List.eraseDups_cons, List.filterMap_cons_some found]
          have filterEq :
              (tail.filterMap map).filter (fun value => !value == mapped) =
                (tail.filter fun value => !value == head).filterMap map := by
            induction tail with
            | nil => rfl
            | cons value rest ih =>
                cases valueFound : map value with
                | none =>
                    have equality : value ≠ head := by
                      intro same
                      subst value
                      rw [found] at valueFound
                      contradiction
                    simp [valueFound, beq_false_of_ne equality, ih]
                | some target =>
                    by_cases equality : value = head
                    · subst value
                      have targetEq : target = mapped :=
                        Option.some.inj (valueFound.symm.trans found)
                      subst target
                      simp [found, ih]
                    · have targetNe : target ≠ mapped := by
                        intro targetEq
                        exact equality (injective valueFound
                          (targetEq ▸ found))
                      simp [valueFound, beq_false_of_ne equality,
                        beq_false_of_ne targetNe, ih]
          rw [filterEq,
            eraseDups_filterMap_injective map injective
              (tail.filter fun value => !value == head)]
termination_by values.length
decreasing_by
  all_goals simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

theorem frameOpen_exposedWires
    (source : OpenDiagram) (selection : CheckedSelection source.diagram)
    (domains : FrameDomains source.diagram selection) :
    (domains.frameOpen source selection).exposedWires =
      domains.mapWireContext source.exposedWires := by
  exact eraseDups_filterMap_injective domains.wires.index?
    (fun {_ _ _} leftEq rightEq =>
      survivor_index?_injective domains.wires leftEq rightEq)
    source.boundary

private theorem filter_filterMap_not_mem
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (map : α → Option β)
    (injective : ∀ {left right value}, map left = some value →
      map right = some value → left = right)
    (values excluded : List α) :
    (values.filterMap map).filter
        (fun value => decide (value ∉ excluded.filterMap map)) =
      (values.filter fun value => decide (value ∉ excluded)).filterMap map := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have tailEq :
          (tail.filterMap map).filter
              (fun value => !decide (value ∈ excluded.filterMap map)) =
            (tail.filter fun value => !decide (value ∈ excluded)
              ).filterMap map := by
        simpa only [decide_not] using ih
      cases found : map head with
      | none =>
          by_cases member : head ∈ excluded <;>
            simp [found, member, tailEq]
      | some mapped =>
          have memberEq : mapped ∈ excluded.filterMap map ↔ head ∈ excluded := by
            constructor
            · intro member
              obtain ⟨value, valueMember, valueEq⟩ :=
                List.mem_filterMap.mp member
              have same := injective found valueEq
              simpa [same] using valueMember
            · intro member
              exact List.mem_filterMap.mpr ⟨head, member, found⟩
          by_cases member : head ∈ excluded
          · have mappedMember := memberEq.mpr member
            simp [found, member, mappedMember, tailEq]
          · have mappedNotMember : mapped ∉ excluded.filterMap map :=
              fun mappedMember => member (memberEq.mp mappedMember)
            simp [found, member, mappedNotMember, tailEq]
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

theorem frameOpen_hiddenWires
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (domains : FrameDomains source.checked.val.diagram selection) :
    (domains.frameOpen source.checked.val selection).hiddenWires =
      domains.mapWireContext source.checked.val.hiddenWires := by
  have rootScope := domains.mapWireContext_exactScope source.diagram selection
    domains.root
  have rootScope' : domains.mapWireContext
        (exactScopeWires source.checked.val.diagram
          source.checked.val.diagram.root) =
      exactScopeWires (source.checked.val.diagram.removeRaw selection domains)
        domains.root := by
    have rootOrigin : domains.regions.origin domains.root =
        source.checked.val.diagram.root := domains.root_origin
    change domains.mapWireContext (exactScopeWires
        source.checked.val.diagram (domains.regions.origin domains.root)) =
      exactScopeWires (source.checked.val.diagram.removeRaw selection domains)
        domains.root at rootScope
    rw [rootOrigin] at rootScope
    exact rootScope
  unfold OpenDiagram.hiddenWires
  change (exactScopeWires
      (source.checked.val.diagram.removeRaw selection domains)
      (source.checked.val.diagram.removeRaw selection domains).root).filter
        (fun wire => decide (wire ∉
          (domains.frameOpen source.checked.val selection).exposedWires)) = _
  rw [Diagram.removeRaw_root, ← rootScope', frameOpen_exposedWires]
  exact filter_filterMap_not_mem domains.wires.index?
    (fun {_ _ _} leftEq rightEq =>
      survivor_index?_injective domains.wires leftEq rightEq)
    (exactScopeWires source.checked.val.diagram
      source.checked.val.diagram.root) source.checked.val.exposedWires

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

/-- Every inherited outer wire at the selected anchor survives.  A selected
wire whose scope is the anchor belongs to the disjoint local block; a selected
descendant scope cannot enclose its direct parent. -/
theorem outerWire_survives_anchor
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (outer : WireContext host.val)
    (fullExact : (outer.extend selection.val.anchor).Exact
      selection.val.anchor)
    (wire : Fin host.val.wireCount) (member : wire ∈ outer) :
    domains.wires.survives wire = true := by
  apply (domains.wire_survives_iff wire).2
  intro removed
  have scopeEncloses : host.val.Encloses (host.val.wires wire).scope
      selection.val.anchor :=
    (fullExact.mem_iff wire).1 (List.mem_append_left _ member)
  rcases (selection.mem_internalWires_expanded wire).1 removed with
    selectedScope | explicit
  · obtain ⟨root, rootMember, rootEnclosesScope⟩ := selectedScope
    have rootParent := selection.property.childRoots_direct root rootMember
    have rootEnclosesAnchor := checked_encloses_trans host.property
      rootEnclosesScope scopeEncloses
    exact checked_direct_child_not_encloses_parent host.property rootParent
      rootEnclosesAnchor
  · have scopeEq := selection.property.explicitWires_at_anchor wire explicit
    have localMember : wire ∈ exactScopeWires host.val selection.val.anchor :=
      (mem_exactScopeWires host.val selection.val.anchor wire).2 scopeEq
    have nodup := fullExact.nodup
    rw [WireContext.extend, List.nodup_append] at nodup
    exact nodup.2.2 wire member wire localMember rfl

/-- Every wire visible from a surviving region incomparable with the selected
anchor survives removal. -/
theorem visibleWire_survives_away
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : Fin host.val.regionCount)
    (regionSurvives : domains.regions.survives region = true)
    (away : ¬ host.val.Encloses region selection.val.anchor)
    (outside : ¬ host.val.Encloses selection.val.anchor region)
    (context : WireContext host.val) (exact : context.Exact region)
    (wire : Fin host.val.wireCount) (member : wire ∈ context) :
    domains.wires.survives wire = true := by
  apply (domains.wire_survives_iff wire).2
  intro removed
  have scopeEnclosesRegion : host.val.Encloses
      (host.val.wires wire).scope region := (exact.mem_iff wire).1 member
  rcases (selection.mem_internalWires_expanded wire).1 removed with
    selectedScope | explicit
  · obtain ⟨root, rootMember, rootEnclosesScope⟩ := selectedScope
    have rootEnclosesRegion := checked_encloses_trans host.property
      rootEnclosesScope scopeEnclosesRegion
    have regionSelected : region ∈ selection.selectedRegions :=
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
    · exact regionNotSelected regionSelected
  · have scopeEq := selection.property.explicitWires_at_anchor wire explicit
    rw [scopeEq] at scopeEnclosesRegion
    exact outside scopeEnclosesRegion

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

/-- Every direct occurrence strictly above the selected anchor survives
removal.  Selection-owned occurrences can only occur at or below the anchor. -/
theorem localOccurrence_survives_above
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (region : Fin host.val.regionCount)
    (above : host.val.Encloses region selection.val.anchor)
    (different : region ≠ selection.val.anchor)
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
        exact different (nodeRegion.symm.trans atAnchor)
      · have regionSelected : region ∈ selection.selectedRegions := by
          rw [← nodeRegion]
          exact (selection.mem_selectedRegions _).2 selectedRegion
        obtain ⟨root, rootMember, rootEnclosesRegion⟩ :=
          (selection.mem_selectedRegions region).1 regionSelected
        have anchorEnclosesRoot : host.val.Encloses selection.val.anchor root := by
          have rootParent := selection.property.childRoots_direct root rootMember
          refine ⟨⟨1, by omega⟩, ?_⟩
          simp [Diagram.climb, rootParent]
        have anchorEnclosesRegion := checked_encloses_trans host.property
          anchorEnclosesRoot rootEnclosesRegion
        exact different (checked_encloses_antisymm host.property above
          anchorEnclosesRegion)
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
          exact different (Option.some.inj (childParent.symm.trans rootParent))
        · have anchorEnclosesRoot : host.val.Encloses
              selection.val.anchor root := by
            have rootParent := selection.property.childRoots_direct root rootMember
            refine ⟨⟨1, by omega⟩, ?_⟩
            simp [Diagram.climb, rootParent]
          have anchorEnclosesRegion := checked_encloses_trans host.property
            anchorEnclosesRoot rootEnclosesRegion
          exact different (checked_encloses_antisymm host.property above
            anchorEnclosesRegion)

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

@[simp] theorem mapWireContextEquiv_val
    (domains : FrameDomains d selection) (context : WireContext d)
    (allSurvive : ∀ wire, wire ∈ context →
      domains.wires.survives wire = true)
    (index : Fin (domains.mapWireContext context).length) :
    (domains.mapWireContextEquiv context allSurvive index).val = index.val :=
  rfl

/-- Survivor-position equivalences compose across lexical context extension. -/
theorem mapWireContextEquiv_append
    (domains : FrameDomains d selection)
    (outer locals : WireContext d)
    (outerSurvives : ∀ wire, wire ∈ outer →
      domains.wires.survives wire = true)
    (localSurvives : ∀ wire, wire ∈ locals →
      domains.wires.survives wire = true)
    (allSurvive : ∀ wire, wire ∈ outer ++ locals →
      domains.wires.survives wire = true) :
    castFinEquiv (by
        rw [domains.mapWireContext_append]
        exact List.length_append.symm)
      (by exact List.length_append.symm)
      (domains.mapWireContextEquiv (outer ++ locals) allSurvive) =
    extendWireEquiv
      (domains.mapWireContextEquiv outer outerSurvives)
      (domains.mapWireContextEquiv locals localSurvives) := by
  have outerLength : (domains.mapWireContext outer).length = outer.length := by
    simpa using congrArg List.length
      (domains.mapWireContext_origin_eq outer outerSurvives)
  apply FiniteEquiv.ext
  intro index
  apply Fin.ext
  refine Fin.addCases (m := (domains.mapWireContext outer).length)
    (n := (domains.mapWireContext locals).length) (fun inherited => ?_)
      (fun localIndex => ?_) index
  · simp [castFinEquiv, extendWireEquiv]
  · simp [castFinEquiv, extendWireEquiv]
    exact outerLength

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

theorem mapWireContextOriginIndex_lookup
    (domains : FrameDomains d selection) (context : WireContext d)
    (index : Fin (domains.mapWireContext context).length) :
    context.lookup?
        (domains.wires.origin ((domains.mapWireContext context).get index)) =
      some (domains.mapWireContextOriginIndex context index) := by
  unfold mapWireContextOriginIndex
  exact Classical.choose_spec (WireContext.lookup?_complete (by
    have mappedMember : domains.wires.origin
        ((domains.mapWireContext context).get index) ∈
        (domains.mapWireContext context).map domains.wires.origin :=
      List.mem_map.mpr ⟨_, List.get_mem _ index, rfl⟩
    rw [domains.map_mapWireContext_origin] at mappedMember
    exact (List.mem_filter.mp mappedMember).1))

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

theorem mapWireContextOriginIndex_eq_equiv
    (domains : FrameDomains d selection) (context : WireContext d)
    (contextNodup : context.Nodup)
    (allSurvive : ∀ wire, wire ∈ context →
      domains.wires.survives wire = true) :
    domains.mapWireContextOriginIndex context =
      domains.mapWireContextEquiv context allSurvive := by
  funext index
  apply Fin.ext
  have getEquiv := domains.mapWireContextEquiv_get context allSurvive index
  exact congrArg Fin.val ((WireContext.lookup?_unique contextNodup
    (domains.mapWireContextOriginIndex_lookup context index)
    (other := domains.mapWireContextEquiv context allSurvive index)
    getEquiv).symm)

/-- Reverse the retained-port law through the canonical context equivalence
when the complete context survives. -/
theorem resolvePort?_removeRaw_index_map
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val) (contextNodup : context.Nodup)
    (allSurvive : ∀ wire, wire ∈ context →
      domains.wires.survives wire = true)
    (node : domains.nodes.Carrier) (port : CPort) :
    resolvePort? (host.val.removeRaw selection domains)
        (domains.mapWireContext context) node port =
      (resolvePort? host.val context (domains.nodes.origin node) port).map
        (domains.mapWireContextEquiv context allSurvive).symm := by
  have forward := domains.resolvePort?_removeRaw_origin_map host selection
    context contextNodup node port
  let wireEquiv := domains.mapWireContextEquiv context allSurvive
  have positionEq : domains.mapWireContextOriginIndex context = wireEquiv :=
    domains.mapWireContextOriginIndex_eq_equiv context contextNodup allSurvive
  rw [positionEq] at forward
  cases sourceEq : resolvePort? host.val context
      (domains.nodes.origin node) port with
  | none =>
      rw [sourceEq] at forward
      cases targetEq : resolvePort? (host.val.removeRaw selection domains)
          (domains.mapWireContext context) node port <;>
        simp [targetEq] at forward ⊢
  | some sourceIndex =>
      rw [sourceEq] at forward
      cases targetEq : resolvePort? (host.val.removeRaw selection domains)
          (domains.mapWireContext context) node port with
      | none => simp [targetEq] at forward
      | some targetIndex =>
          simp only [targetEq, Option.map_some, Option.some.injEq] at forward ⊢
          rw [forward]
          exact (wireEquiv.left_inv targetIndex).symm

/-- Compile one retained dense node back to its represented source node. -/
private theorem mapNodeCompilationBack
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (context : WireContext host.val) (contextNodup : context.Nodup)
    (allSurvive : ∀ wire, wire ∈ context →
      domains.wires.survives wire = true)
    (binders : BinderContext host.val rels)
    (node : domains.nodes.Carrier)
    {frameItem : CompiledItem (host.val.removeRaw selection domains)
      (domains.mapWireContext context) rels
      (domains.mapBinderContext binders)}
    (frameCompiled : compileNode? (host.val.removeRaw selection domains)
      (domains.mapWireContext context) (domains.mapBinderContext binders) node =
        some frameItem) :
    ∃ sourceItem : CompiledItem host.val context rels binders,
      compileNode? host.val context binders (domains.nodes.origin node) =
        some sourceItem ∧
      sourceItem.erase = frameItem.erase.renameWires
        (domains.mapWireContextEquiv context allSurvive) := by
  obtain ⟨sourceItem, sourceCompiled, eraseEq⟩ := compileNode?_map_success
    (source := host.val.removeRaw selection domains) (target := host.val)
    (domains.mapWireContext context) context
    (domains.mapBinderContext binders) binders node
    (domains.nodes.origin node) domains.regions.origin domains.regions.origin
    (domains.mapWireContextEquiv context allSurvive) (fun relation => relation)
    (by
      have nodeOrigin := domains.removeRaw_node_origin host selection node
      cases targetKind : (host.val.removeRaw selection domains).nodes node with
      | atom region binder => simpa [targetKind] using nodeOrigin
      | identity region arity => simpa [targetKind] using nodeOrigin)
    (by
      intro port
      have ports := domains.resolvePort?_removeRaw_origin_map host selection
        context contextNodup node port
      rw [domains.mapWireContextOriginIndex_eq_equiv context contextNodup
        allSurvive] at ports
      exact ports)
    (by
      intro region binder nodeKind
      change binders (domains.regions.origin binder) =
        (binders (domains.regions.origin binder)).map _
      cases binders (domains.regions.origin binder) with
      | none => rfl
      | some value => cases value; rfl)
    frameCompiled
  exact ⟨sourceItem, sourceCompiled, by
    simpa only [Item.renameRelations_id] using eraseEq⟩

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

/-- Actual-context form of retained node compilation.  The sole context
presentation equality is eliminated at this boundary, before any compiled
result escapes. -/
theorem mapNodeCompilationAt
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceContext : WireContext host.val)
    (targetContext : WireContext (host.val.removeRaw selection domains))
    (targetEq : targetContext = domains.mapWireContext sourceContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : BinderContext host.val rels)
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (bindersEq : targetBinders =
      domains.mapBinderContext sourceBinders)
    (node : domains.nodes.Carrier)
    (allSurvive : ∀ wire, wire ∈ sourceContext →
      domains.wires.survives wire = true)
    {sourceItem : CompiledItem host.val sourceContext rels sourceBinders}
    (sourceCompiled : compileNode? host.val sourceContext sourceBinders
      (domains.nodes.origin node) = some sourceItem) :
    Nonempty (Σ targetItem : CompiledItem
        (host.val.removeRaw selection domains) targetContext rels
        targetBinders,
      PSigma (fun _ : compileNode? (host.val.removeRaw selection domains)
          targetContext targetBinders node = some targetItem =>
        ItemIso ((FiniteEquiv.finCast (congrArg List.length targetEq)).trans
          (domains.mapWireContextEquiv sourceContext allSurvive)) rels
          targetItem.erase sourceItem.erase)) := by
  subst targetContext
  subst targetBinders
  obtain ⟨targetItem, targetCompiled, erased⟩ :=
    domains.mapNodeCompilation host selection sourceContext sourceNodup
      sourceBinders node sourceCompiled
  rw [domains.mapWireContextOriginIndex_eq_equiv sourceContext sourceNodup
    allSurvive] at erased
  refine ⟨⟨targetItem, ⟨targetCompiled, ?_⟩⟩⟩
  rw [erased]
  have wireEq :
      (FiniteEquiv.finCast (congrArg List.length (Eq.refl
          (domains.mapWireContext sourceContext)))).trans
          (domains.mapWireContextEquiv sourceContext allSurvive) =
        domains.mapWireContextEquiv sourceContext allSurvive := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [wireEq]
  simpa only [Item.renameRelations_id] using
    ItemIso.renameWiresEquiv targetItem.erase
      (domains.mapWireContextEquiv sourceContext allSurvive)

/-- Success-only node transport in the actual compact context chosen by the
enclosing compiler call.  Context and binder presentation equalities are
eliminated here; no transported compiled value escapes this boundary. -/
structure MappedNodeSuccessAt
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (targetContext : WireContext (host.val.removeRaw selection domains))
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (node : domains.nodes.Carrier) where
  item : CompiledItem (host.val.removeRaw selection domains) targetContext
    rels targetBinders
  compiled : compileNode? (host.val.removeRaw selection domains) targetContext
    targetBinders node = some item

theorem mapNodeCompilationSuccessAt
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceContext : WireContext host.val)
    (targetContext : WireContext (host.val.removeRaw selection domains))
    (contextEq : targetContext = domains.mapWireContext sourceContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : BinderContext host.val rels)
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (bindersEq : targetBinders = domains.mapBinderContext sourceBinders)
    (node : domains.nodes.Carrier)
    {sourceItem : CompiledItem host.val sourceContext rels sourceBinders}
    (sourceCompiled : compileNode? host.val sourceContext sourceBinders
      (domains.nodes.origin node) = some sourceItem) :
    Nonempty (MappedNodeSuccessAt host selection domains targetContext
      targetBinders node) := by
  subst targetContext
  subst targetBinders
  obtain ⟨targetItem, targetCompiled, _⟩ :=
    domains.mapNodeCompilation host selection sourceContext sourceNodup
      sourceBinders node sourceCompiled
  exact ⟨⟨targetItem, targetCompiled⟩⟩

/-- One source-determined compact compilation at a surviving nested call.
The caller owns the actual target context and binder presentation. -/
structure SurvivorRegionResult
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (origin : Fin host.val.regionCount)
    (survives : domains.regions.survives origin = true)
    (targetOuter : WireContext (host.val.removeRaw selection domains))
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels) where
  body : CompiledRegion (host.val.removeRaw selection domains)
    (.nested (domains.regions.index origin survives) targetOuter rels
      targetBinders)
  compiled : compileRegion? (host.val.removeRaw selection domains)
    (Diagram.removeRaw_wellFormed host selection domains)
    (domains.regions.index origin survives) targetOuter targetBinders =
      some body

/-- Compile the stable surviving filter of one successful source subtree.
Recursive target calls are constructed only from the source compiler
induction; target contexts and binders remain caller-owned throughout. -/
theorem compileRegionSurvivors
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (origin : Fin host.val.regionCount)
    (survives : domains.regions.survives origin = true)
    (sourceOuter : WireContext host.val)
    (sourceBinders : BinderContext host.val rels)
    (targetOuter : WireContext (host.val.removeRaw selection domains))
    (outerEq : targetOuter = domains.mapWireContext sourceOuter)
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (bindersEq : targetBinders = domains.mapBinderContext sourceBinders)
    (sourceExact : (sourceOuter.extend origin).Exact origin)
    (sourceBody : CompiledRegion host.val
      (.nested origin sourceOuter rels sourceBinders))
    (sourceCompiled : compileRegion? host.val host.property origin sourceOuter
      sourceBinders = some sourceBody) :
    Nonempty (SurvivorRegionResult host selection domains origin survives
      targetOuter targetBinders) := by
  let motive : CompilerCall host.val -> Prop := fun call =>
    match call with
    | .root _ _ => True
    | .nested currentOrigin currentOuter currentRels currentBinders =>
        forall
          (currentSurvives : domains.regions.survives currentOrigin = true)
          (currentTargetOuter : WireContext
            (host.val.removeRaw selection domains))
          (currentOuterEq : currentTargetOuter =
            domains.mapWireContext currentOuter)
          (currentTargetBinders : BinderContext
            (host.val.removeRaw selection domains) currentRels)
          (currentBindersEq : currentTargetBinders =
            domains.mapBinderContext currentBinders)
          (currentExact : (currentOuter.extend currentOrigin).Exact
            currentOrigin)
          (currentBody : CompiledRegion host.val
            (.nested currentOrigin currentOuter currentRels currentBinders)),
          compileRegion? host.val host.property currentOrigin currentOuter
              currentBinders = some currentBody ->
            Nonempty (SurvivorRegionResult host selection domains
              currentOrigin currentSurvives currentTargetOuter
              currentTargetBinders)
  have mapped : motive (.nested origin sourceOuter rels sourceBinders) := by
    refine CompilerCall.compile?.induct host.val host.property
      (motive := motive) (fun call induction => ?_)
      (.nested origin sourceOuter rels sourceBinders)
    cases call with
    | root ambient locals => exact True.intro
    | nested currentOrigin currentOuter currentRels currentBinders =>
        intro currentSurvives currentTargetOuter currentOuterEq
          currentTargetBinders currentBindersEq currentExact currentBody
          currentCompiled
        rcases currentBody with ⟨sourceItems⟩
        have sourceItemsCompiled := compileRegion?_items_of_success
          host.property currentOrigin currentOuter currentBinders
          currentCompiled
        have sourceOrigins : sourceItems.origins =
            localOccurrences host.val currentOrigin :=
          compileItems?_origins host.property currentOrigin
            (currentOuter.extend currentOrigin) currentBinders
            sourceItemsCompiled
        let survivors :=
          (sourceItems.partition domains.occurrenceSurvives).material
        let sourceDirect : forall occurrence, occurrence ∈ survivors.origins ->
            occurrence ∈ localOccurrences host.val currentOrigin := by
          intro occurrence member
          rw [← sourceOrigins]
          exact (sourceItems.partition_material_stable
            domains.occurrenceSurvives).mem member
        let allSourceDirect : forall occurrence,
            occurrence ∈ sourceItems.origins ->
              occurrence ∈ localOccurrences host.val currentOrigin := by
          intro occurrence member
          exact sourceOrigins ▸ member
        have sourceItemsCompiled' : compileItems? host.val host.property
            currentOrigin (currentOuter.extend currentOrigin) currentBinders
            sourceItems.origins allSourceDirect = some sourceItems := by
          exact (compileItems?_congr_occurrences host.property currentOrigin
            (currentOuter.extend currentOrigin) currentBinders sourceOrigins
            allSourceDirect (fun _ member => member)).trans
              sourceItemsCompiled
        have survivorsCompiled : compileItems? host.val host.property
            currentOrigin (currentOuter.extend currentOrigin) currentBinders
            survivors.origins sourceDirect = some survivors := by
          have divided := compileItems?_partition_success host.property
            currentOrigin (currentOuter.extend currentOrigin) currentBinders
            domains.occurrenceSurvives sourceItems allSourceDirect
              sourceItemsCompiled'
          simpa only [sourceDirect] using divided.2
        let targetOrigin := domains.regions.index currentOrigin currentSurvives
        let sourceFull := currentOuter.extend currentOrigin
        let targetFull := currentTargetOuter.extend targetOrigin
        have targetFullEq : targetFull =
            domains.mapWireContext sourceFull := by
          dsimp only [targetFull, sourceFull, targetOrigin]
          rw [currentOuterEq]
          calc
            (domains.mapWireContext currentOuter).extend
                (domains.regions.index currentOrigin currentSurvives) =
              domains.mapWireContext (currentOuter.extend
                (domains.regions.origin
                  (domains.regions.index currentOrigin currentSurvives))) :=
                (domains.mapWireContext_extend host selection currentOuter
                  (domains.regions.index currentOrigin currentSurvives)).symm
            _ = domains.mapWireContext
                (currentOuter.extend currentOrigin) := by
              exact congrArg domains.mapWireContext
                (congrArg (WireContext.extend currentOuter)
                  (domains.regions.origin_index currentOrigin
                    currentSurvives))
        have survivorOrigins : survivors.origins =
            (localOccurrences host.val currentOrigin).filter
              domains.occurrenceSurvives := by
          dsimp only [survivors]
          rw [CompiledItems.partition_material_origins, sourceOrigins]
        let targetDirect : forall occurrence,
            occurrence ∈ survivors.origins.map domains.indexOccurrence ->
              occurrence ∈ localOccurrences
                (host.val.removeRaw selection domains) targetOrigin := by
          intro occurrence member
          rw [domains.localOccurrences_removeRaw_eq_map_filter host selection
            targetOrigin, domains.regions.origin_index, ← survivorOrigins]
          exact member
        let mappedItems := compileItems?_map_success_only host.property
          (Diagram.removeRaw_wellFormed host selection domains)
          currentOrigin targetOrigin sourceFull targetFull currentBinders
          currentTargetBinders survivors.origins domains.indexOccurrence
          sourceDirect targetDirect
          (by
            intro occurrence member sourceItem occurrenceCompiled
            have occurrenceSurvives :
                domains.occurrenceSurvives occurrence = true := by
              rw [survivorOrigins] at member
              exact (List.mem_filter.mp member).2
            cases occurrence with
            | node node =>
                change domains.nodes.survives node = true at occurrenceSurvives
                let targetNode := domains.nodes.index node occurrenceSurvives
                have mappedEq : domains.indexOccurrence (.node node) =
                    .node targetNode := by
                  apply domains.originOccurrence_injective
                  rw [domains.originOccurrence_indexOccurrence (.node node)
                    occurrenceSurvives]
                  exact congrArg LocalOccurrence.node
                    (domains.nodes.origin_index node occurrenceSurvives).symm
                have sourceNodeCompiled : compileNode? host.val sourceFull
                    currentBinders node = some sourceItem := by
                  simpa only [compileOccurrence?_node] using occurrenceCompiled
                let targetNodeResult := Classical.choice
                  (domains.mapNodeCompilationSuccessAt host selection sourceFull
                    targetFull targetFullEq currentExact.nodup currentBinders
                    currentTargetBinders currentBindersEq targetNode (by
                      have originEq := domains.nodes.origin_index node
                        occurrenceSurvives
                      rw [originEq]
                      exact sourceNodeCompiled))
                have targetNodeDirect : LocalOccurrence.node targetNode ∈
                    localOccurrences (host.val.removeRaw selection domains)
                      targetOrigin := by
                  exact Eq.mp (congrArg (fun candidate => candidate ∈
                    localOccurrences (host.val.removeRaw selection domains)
                      targetOrigin) mappedEq)
                    (targetDirect (domains.indexOccurrence (.node node))
                      (List.mem_map.mpr ⟨.node node, member, rfl⟩))
                refine ⟨targetNodeResult.item, ?_⟩
                exact (compileOccurrence?_congr_occurrence _ _ _ _ mappedEq
                  _ targetNodeDirect).trans (by
                    simpa only [compileOccurrence?_node] using
                      targetNodeResult.compiled)
            | child child =>
                change domains.regions.survives child = true at occurrenceSurvives
                let targetChild := domains.regions.index child
                  occurrenceSurvives
                have mappedEq : domains.indexOccurrence (.child child) =
                    .child targetChild := by
                  apply domains.originOccurrence_injective
                  rw [domains.originOccurrence_indexOccurrence (.child child)
                    occurrenceSurvives]
                  exact congrArg LocalOccurrence.child
                    (domains.regions.origin_index child
                      occurrenceSurvives).symm
                have sourceParent := (mem_localOccurrences_child host.val
                  currentOrigin child).mp (sourceDirect (.child child) member)
                have childExact := currentExact.extend_child host.property
                  sourceParent
                have targetChildDirect : LocalOccurrence.child targetChild ∈
                    localOccurrences (host.val.removeRaw selection domains)
                      targetOrigin := by
                  exact Eq.mp (congrArg (fun candidate => candidate ∈
                    localOccurrences (host.val.removeRaw selection domains)
                      targetOrigin) mappedEq)
                    (targetDirect (domains.indexOccurrence (.child child))
                      (List.mem_map.mpr ⟨.child child, member, rfl⟩))
                cases sourceKind : host.val.regions child with
                | sheet =>
                    rw [compileOccurrence?_child_sheet host.property
                      currentOrigin child sourceFull currentBinders
                      (sourceDirect (.child child) member) sourceKind]
                      at occurrenceCompiled
                    contradiction
                | cut parent =>
                    have parentEq : parent = currentOrigin := by
                      simpa [sourceKind, CRegion.parent?] using sourceParent
                    subst parent
                    obtain ⟨sourceChild, childCompiled, itemEq⟩ :=
                      compileOccurrence?_child_cut_success host.property
                        currentOrigin child sourceFull currentBinders
                        (sourceDirect (.child child) member) sourceKind
                        occurrenceCompiled
                    subst sourceItem
                    let childResult := Classical.choice
                      (induction child sourceParent sourceFull currentBinders
                        occurrenceSurvives targetFull targetFullEq
                        currentTargetBinders currentBindersEq childExact
                        sourceChild childCompiled)
                    let targetItem : CompiledItem
                        (host.val.removeRaw selection domains) targetFull
                        currentRels currentTargetBinders :=
                      .cut childResult.body
                    have targetKind := domains.removeRaw_cut host selection
                      currentSurvives occurrenceSurvives sourceKind
                    refine ⟨targetItem, ?_⟩
                    exact (compileOccurrence?_congr_occurrence _ _ _ _
                      mappedEq _ targetChildDirect).trans (by
                        change compileOccurrence?
                          (host.val.removeRaw selection domains)
                          (Diagram.removeRaw_wellFormed host selection domains)
                          targetOrigin targetFull currentTargetBinders
                          (.child targetChild) targetChildDirect =
                            some (.cut childResult.body)
                        rw [compileOccurrence?_child_cut
                          (Diagram.removeRaw_wellFormed host selection domains)
                          targetOrigin targetChild targetFull
                          currentTargetBinders targetChildDirect
                          (by simpa [targetChild] using targetKind),
                          childResult.compiled]
                        rfl)
                | bubble parent arity =>
                    have parentEq : parent = currentOrigin := by
                      simpa [sourceKind, CRegion.parent?] using sourceParent
                    subst parent
                    obtain ⟨sourceChild, childCompiled, itemEq⟩ :=
                      compileOccurrence?_child_bubble_success host.property
                        currentOrigin child sourceFull currentBinders arity
                        (sourceDirect (.child child) member) sourceKind
                        occurrenceCompiled
                    subst sourceItem
                    let targetPushed := currentTargetBinders.push targetChild arity
                    have targetPushedEq : targetPushed =
                        domains.mapBinderContext
                          (currentBinders.push child arity) := by
                      dsimp only [targetPushed]
                      rw [currentBindersEq]
                      exact (domains.mapBinderContext_push currentBinders child
                        occurrenceSurvives arity).symm
                    let childResult := Classical.choice
                      (induction child sourceParent sourceFull
                        (currentBinders.push child arity) occurrenceSurvives
                        targetFull targetFullEq targetPushed targetPushedEq
                        childExact sourceChild childCompiled)
                    let targetItem : CompiledItem
                        (host.val.removeRaw selection domains) targetFull
                        currentRels currentTargetBinders :=
                      .bubble arity childResult.body
                    have targetKind := domains.removeRaw_bubble host selection
                      currentSurvives occurrenceSurvives arity sourceKind
                    refine ⟨targetItem, ?_⟩
                    exact (compileOccurrence?_congr_occurrence _ _ _ _
                      mappedEq _ targetChildDirect).trans (by
                        change compileOccurrence?
                          (host.val.removeRaw selection domains)
                          (Diagram.removeRaw_wellFormed host selection domains)
                          targetOrigin targetFull currentTargetBinders
                          (.child targetChild) targetChildDirect =
                            some (.bubble arity childResult.body)
                        rw [compileOccurrence?_child_bubble
                          (Diagram.removeRaw_wellFormed host selection domains)
                          targetOrigin targetChild targetFull
                          currentTargetBinders arity targetChildDirect
                          (by simpa [targetChild] using targetKind),
                          childResult.compiled]
                        rfl))
          survivorsCompiled
        obtain ⟨targetItems, targetItemsCompiled⟩ := mappedItems
        have occurrencesEq : localOccurrences
            (host.val.removeRaw selection domains) targetOrigin =
              survivors.origins.map domains.indexOccurrence := by
          rw [domains.localOccurrences_removeRaw_eq_map_filter host selection
            targetOrigin, domains.regions.origin_index, ← survivorOrigins]
        let targetBody : CompiledRegion
            (host.val.removeRaw selection domains)
            (.nested targetOrigin currentTargetOuter currentRels
              currentTargetBinders) := .mk targetItems
        have targetCompiled : compileRegion?
            (host.val.removeRaw selection domains)
            (Diagram.removeRaw_wellFormed host selection domains)
            targetOrigin currentTargetOuter currentTargetBinders =
              some targetBody := by
          rw [compileRegion?_eq_compileItems?]
          have normalized := (compileItems?_congr_occurrences
            (Diagram.removeRaw_wellFormed host selection domains) targetOrigin
            targetFull currentTargetBinders occurrencesEq
            (fun _ member => member) targetDirect).trans targetItemsCompiled
          rw [normalized]
          rfl
        exact ⟨⟨targetBody, targetCompiled⟩⟩
  exact mapped survives targetOuter outerEq targetBinders bindersEq sourceExact
    sourceBody sourceCompiled

/-- Source-determined compact compilation for the sheet root.  Nested child
calls delegate to `compileRegionSurvivors`; the root itself introduces no
second recursive compiler authority. -/
structure SurvivorRootResult
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (targetAmbient targetLocal : WireContext
      (host.val.removeRaw selection domains)) where
  body : CompiledRegion (host.val.removeRaw selection domains)
    (.root targetAmbient targetLocal)
  compiled : compileRoot? (host.val.removeRaw selection domains)
    (Diagram.removeRaw_wellFormed host selection domains)
    targetAmbient targetLocal = some body

theorem compileRootSurvivors
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceAmbient sourceLocal : WireContext host.val)
    (targetAmbient targetLocal : WireContext
      (host.val.removeRaw selection domains))
    (ambientEq : targetAmbient = domains.mapWireContext sourceAmbient)
    (localEq : targetLocal = domains.mapWireContext sourceLocal)
    (sourceExact : (sourceAmbient ++ sourceLocal).Exact host.val.root)
    (sourceBody : CompiledRegion host.val
      (.root sourceAmbient sourceLocal))
    (sourceCompiled : compileRoot? host.val host.property sourceAmbient
      sourceLocal = some sourceBody) :
    Nonempty (SurvivorRootResult host selection domains targetAmbient
      targetLocal) := by
  rcases sourceBody with ⟨sourceItems⟩
  have sourceItemsCompiled := CompilerCall.compile?_items_of_success
    host.property (.root sourceAmbient sourceLocal) sourceCompiled
  have sourceOrigins : sourceItems.origins =
      localOccurrences host.val host.val.root :=
    compileItems?_origins host.property host.val.root
      (sourceAmbient ++ sourceLocal) BinderContext.empty sourceItemsCompiled
  let survivors :=
    (sourceItems.partition domains.occurrenceSurvives).material
  let sourceDirect : forall occurrence, occurrence ∈ survivors.origins ->
      occurrence ∈ localOccurrences host.val host.val.root := by
    intro occurrence member
    rw [← sourceOrigins]
    exact (sourceItems.partition_material_stable
      domains.occurrenceSurvives).mem member
  let allSourceDirect : forall occurrence,
      occurrence ∈ sourceItems.origins ->
        occurrence ∈ localOccurrences host.val host.val.root := by
    intro occurrence member
    exact sourceOrigins ▸ member
  have sourceItemsCompiled' : compileItems? host.val host.property
      host.val.root (sourceAmbient ++ sourceLocal) BinderContext.empty
      sourceItems.origins allSourceDirect = some sourceItems := by
    exact (compileItems?_congr_occurrences host.property host.val.root
      (sourceAmbient ++ sourceLocal) BinderContext.empty sourceOrigins
      allSourceDirect (fun _ member => member)).trans sourceItemsCompiled
  have survivorsCompiled : compileItems? host.val host.property host.val.root
      (sourceAmbient ++ sourceLocal) BinderContext.empty survivors.origins
      sourceDirect = some survivors := by
    exact (compileItems?_partition_success host.property host.val.root
      (sourceAmbient ++ sourceLocal) BinderContext.empty
      domains.occurrenceSurvives sourceItems allSourceDirect
      sourceItemsCompiled').2
  let targetRoot := domains.root
  let sourceFull := sourceAmbient ++ sourceLocal
  let targetFull := targetAmbient ++ targetLocal
  have targetFullEq : targetFull = domains.mapWireContext sourceFull := by
    dsimp only [targetFull, sourceFull]
    rw [ambientEq, localEq, domains.mapWireContext_append]
  have survivorOrigins : survivors.origins =
      (localOccurrences host.val host.val.root).filter
        domains.occurrenceSurvives := by
    dsimp only [survivors]
    rw [CompiledItems.partition_material_origins, sourceOrigins]
  let targetDirect : forall occurrence,
      occurrence ∈ survivors.origins.map domains.indexOccurrence ->
        occurrence ∈ localOccurrences
          (host.val.removeRaw selection domains) targetRoot := by
    intro occurrence member
    rw [domains.localOccurrences_removeRaw_eq_map_filter host selection
      targetRoot, domains.root_origin, ← survivorOrigins]
    exact member
  let mappedItems := compileItems?_map_success_only host.property
    (Diagram.removeRaw_wellFormed host selection domains) host.val.root
    targetRoot sourceFull targetFull BinderContext.empty BinderContext.empty
    survivors.origins domains.indexOccurrence sourceDirect targetDirect
    (by
      intro occurrence member sourceItem occurrenceCompiled
      have occurrenceSurvives : domains.occurrenceSurvives occurrence = true := by
        rw [survivorOrigins] at member
        exact (List.mem_filter.mp member).2
      cases occurrence with
      | node node =>
          change domains.nodes.survives node = true at occurrenceSurvives
          let targetNode := domains.nodes.index node occurrenceSurvives
          have mappedEq : domains.indexOccurrence (.node node) =
              .node targetNode := by
            apply domains.originOccurrence_injective
            rw [domains.originOccurrence_indexOccurrence (.node node)
              occurrenceSurvives]
            exact congrArg LocalOccurrence.node
              (domains.nodes.origin_index node occurrenceSurvives).symm
          have sourceNodeCompiled : compileNode? host.val sourceFull
              BinderContext.empty node = some sourceItem := by
            simpa only [compileOccurrence?_node] using occurrenceCompiled
          let targetNodeResult := Classical.choice
            (domains.mapNodeCompilationSuccessAt host selection sourceFull
              targetFull targetFullEq sourceExact.nodup BinderContext.empty
              BinderContext.empty rfl targetNode (by
                have originEq := domains.nodes.origin_index node
                  occurrenceSurvives
                rw [originEq]
                exact sourceNodeCompiled))
          have targetNodeDirect : LocalOccurrence.node targetNode ∈
              localOccurrences (host.val.removeRaw selection domains)
                targetRoot := by
            exact Eq.mp (congrArg (fun candidate => candidate ∈
              localOccurrences (host.val.removeRaw selection domains)
                targetRoot) mappedEq)
              (targetDirect (domains.indexOccurrence (.node node))
                (List.mem_map.mpr ⟨.node node, member, rfl⟩))
          refine ⟨targetNodeResult.item, ?_⟩
          exact (compileOccurrence?_congr_occurrence _ _ _ _ mappedEq _
            targetNodeDirect).trans (by
              simpa only [compileOccurrence?_node] using
                targetNodeResult.compiled)
      | child child =>
          change domains.regions.survives child = true at occurrenceSurvives
          let targetChild := domains.regions.index child occurrenceSurvives
          have mappedEq : domains.indexOccurrence (.child child) =
              .child targetChild := by
            apply domains.originOccurrence_injective
            rw [domains.originOccurrence_indexOccurrence (.child child)
              occurrenceSurvives]
            exact congrArg LocalOccurrence.child
              (domains.regions.origin_index child occurrenceSurvives).symm
          have sourceParent := (mem_localOccurrences_child host.val
            host.val.root child).mp (sourceDirect (.child child) member)
          have childExact := sourceExact.extend_child host.property sourceParent
          have targetChildDirect : LocalOccurrence.child targetChild ∈
              localOccurrences (host.val.removeRaw selection domains)
                targetRoot := by
            exact Eq.mp (congrArg (fun candidate => candidate ∈
              localOccurrences (host.val.removeRaw selection domains)
                targetRoot) mappedEq)
              (targetDirect (domains.indexOccurrence (.child child))
                (List.mem_map.mpr ⟨.child child, member, rfl⟩))
          cases sourceKind : host.val.regions child with
          | sheet =>
              rw [compileOccurrence?_child_sheet host.property host.val.root
                child sourceFull BinderContext.empty
                (sourceDirect (.child child) member) sourceKind]
                at occurrenceCompiled
              contradiction
          | cut parent =>
              have parentEq : parent = host.val.root := by
                simpa [sourceKind, CRegion.parent?] using sourceParent
              subst parent
              obtain ⟨sourceChild, childCompiled, itemEq⟩ :=
                compileOccurrence?_child_cut_success host.property
                  host.val.root child sourceFull BinderContext.empty
                  (sourceDirect (.child child) member) sourceKind
                  occurrenceCompiled
              subst sourceItem
              let childResult := Classical.choice
                (domains.compileRegionSurvivors host selection child
                  occurrenceSurvives sourceFull BinderContext.empty targetFull
                  targetFullEq BinderContext.empty rfl childExact sourceChild
                  childCompiled)
              let targetItem : CompiledItem
                  (host.val.removeRaw selection domains) targetFull []
                  BinderContext.empty := .cut childResult.body
              have targetKind := domains.removeRaw_cut host selection
                domains.root_survives occurrenceSurvives sourceKind
              refine ⟨targetItem, ?_⟩
              exact (compileOccurrence?_congr_occurrence _ _ _ _ mappedEq _
                targetChildDirect).trans (by
                  change compileOccurrence?
                    (host.val.removeRaw selection domains)
                    (Diagram.removeRaw_wellFormed host selection domains)
                    targetRoot targetFull BinderContext.empty
                    (.child targetChild) targetChildDirect =
                      some (.cut childResult.body)
                  rw [compileOccurrence?_child_cut
                    (Diagram.removeRaw_wellFormed host selection domains)
                    targetRoot targetChild targetFull BinderContext.empty
                    targetChildDirect (by simpa [targetRoot, targetChild]
                      using targetKind), childResult.compiled]
                  rfl)
          | bubble parent arity =>
              have parentEq : parent = host.val.root := by
                simpa [sourceKind, CRegion.parent?] using sourceParent
              subst parent
              obtain ⟨sourceChild, childCompiled, itemEq⟩ :=
                compileOccurrence?_child_bubble_success host.property
                  host.val.root child sourceFull BinderContext.empty arity
                  (sourceDirect (.child child) member) sourceKind
                  occurrenceCompiled
              subst sourceItem
              let targetPushed : BinderContext
                  (host.val.removeRaw selection domains) [arity] :=
                BinderContext.empty.push targetChild arity
              have targetPushedEq : targetPushed =
                  domains.mapBinderContext
                    (BinderContext.empty.push child arity) := by
                dsimp only [targetPushed]
                exact (domains.mapBinderContext_push BinderContext.empty child
                  occurrenceSurvives arity).symm
              let childResult := Classical.choice
                (domains.compileRegionSurvivors host selection child
                  occurrenceSurvives sourceFull
                  (BinderContext.empty.push child arity) targetFull targetFullEq
                  targetPushed targetPushedEq childExact sourceChild
                  childCompiled)
              let targetItem : CompiledItem
                  (host.val.removeRaw selection domains) targetFull []
                  BinderContext.empty := .bubble arity childResult.body
              have targetKind := domains.removeRaw_bubble host selection
                domains.root_survives occurrenceSurvives arity sourceKind
              refine ⟨targetItem, ?_⟩
              exact (compileOccurrence?_congr_occurrence _ _ _ _ mappedEq _
                targetChildDirect).trans (by
                  change compileOccurrence?
                    (host.val.removeRaw selection domains)
                    (Diagram.removeRaw_wellFormed host selection domains)
                    targetRoot targetFull BinderContext.empty
                    (.child targetChild) targetChildDirect =
                      some (.bubble arity childResult.body)
                  rw [compileOccurrence?_child_bubble
                    (Diagram.removeRaw_wellFormed host selection domains)
                    targetRoot targetChild targetFull BinderContext.empty arity
                    targetChildDirect (by simpa [targetRoot, targetChild]
                      using targetKind), childResult.compiled]
                  rfl))
    survivorsCompiled
  obtain ⟨targetItems, targetItemsCompiled⟩ := mappedItems
  have occurrencesEq : localOccurrences
      (host.val.removeRaw selection domains) targetRoot =
        survivors.origins.map domains.indexOccurrence := by
    rw [domains.localOccurrences_removeRaw_eq_map_filter host selection
      targetRoot, domains.root_origin, ← survivorOrigins]
  let targetBody : CompiledRegion (host.val.removeRaw selection domains)
      (.root targetAmbient targetLocal) := .mk targetItems
  have targetCompiled : compileRoot?
      (host.val.removeRaw selection domains)
      (Diagram.removeRaw_wellFormed host selection domains)
      targetAmbient targetLocal = some targetBody := by
    rw [compileRoot?_eq_compileItems?]
    change (do
      let items ← compileItems? (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains) targetRoot
        targetFull BinderContext.empty
        (localOccurrences (host.val.removeRaw selection domains) targetRoot)
        (fun _ member => member)
      pure (CompiledRegion.mk items : CompiledRegion
        (host.val.removeRaw selection domains)
          (.root targetAmbient targetLocal))) = some targetBody
    have normalized := (compileItems?_congr_occurrences
      (Diagram.removeRaw_wellFormed host selection domains) targetRoot
      targetFull BinderContext.empty occurrencesEq (fun _ member => member)
      targetDirect).trans targetItemsCompiled
    rw [normalized]
    rfl
  exact ⟨⟨targetBody, targetCompiled⟩⟩

/-- Semantic result for one unchanged nested subtree in the actual compact
parent context supplied by its caller. -/
abbrev AwayRegionResult
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceOrigin : Fin host.val.regionCount)
    (sourceOuter : WireContext host.val)
    (sourceBinders : BinderContext host.val rels)
    (originSurvives : domains.regions.survives sourceOrigin = true)
    (targetOuter : WireContext (host.val.removeRaw selection domains))
    (outerEq : targetOuter = domains.mapWireContext sourceOuter)
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (exact : (sourceOuter.extend sourceOrigin).Exact sourceOrigin)
    (away : ¬ host.val.Encloses sourceOrigin selection.val.anchor)
    (outside : ¬ host.val.Encloses selection.val.anchor sourceOrigin)
    (sourceBody : CompiledRegion host.val
      (.nested sourceOrigin sourceOuter rels sourceBinders)) :=
  Nonempty (Σ targetBody : CompiledRegion
      (host.val.removeRaw selection domains)
      (.nested (domains.regions.index sourceOrigin originSurvives)
        targetOuter rels targetBinders),
    PSigma (fun _ : compileRegion? (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceOrigin originSurvives) targetOuter
          targetBinders = some targetBody =>
      RegionIso
        ((FiniteEquiv.finCast (congrArg List.length outerEq)).trans
          (domains.mapWireContextEquiv sourceOuter (fun wire member =>
            domains.visibleWire_survives_away host selection sourceOrigin
              originSurvives away outside
              (sourceOuter.extend sourceOrigin) exact wire
              (List.mem_append_left _ member))))
        rels targetBody.erase sourceBody.erase))

/-- Compile an unchanged source subtree in the compact frame.  The target
outer context is supplied by the enclosing fold and normalized only inside
this theorem. -/
theorem compileRegionAway
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceOrigin : Fin host.val.regionCount)
    (sourceOuter : WireContext host.val)
    (sourceBinders : BinderContext host.val rels)
    (originSurvives : domains.regions.survives sourceOrigin = true)
    (targetOuter : WireContext (host.val.removeRaw selection domains))
    (outerEq : targetOuter = domains.mapWireContext sourceOuter)
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (bindersEq : targetBinders = domains.mapBinderContext sourceBinders)
    (exact : (sourceOuter.extend sourceOrigin).Exact sourceOrigin)
    (covers : sourceBinders.Covers sourceOrigin)
    (away : ¬ host.val.Encloses sourceOrigin selection.val.anchor)
    (outside : ¬ host.val.Encloses selection.val.anchor sourceOrigin)
    (sourceBody : CompiledRegion host.val
      (.nested sourceOrigin sourceOuter rels sourceBinders))
    (sourceCompiled : compileRegion? host.val host.property sourceOrigin
      sourceOuter sourceBinders = some sourceBody) :
    AwayRegionResult host selection domains sourceOrigin sourceOuter
      sourceBinders originSurvives targetOuter outerEq targetBinders exact
      away outside
      sourceBody := by
  let motive : CompilerCall host.val → Prop := fun current =>
    match current with
    | .root _ _ => True
    | .nested currentOrigin currentOuter currentRels currentBinders =>
        ∀ (currentSurvives :
              domains.regions.survives currentOrigin = true)
          (currentTargetOuter : WireContext
            (host.val.removeRaw selection domains))
          (currentOuterEq : currentTargetOuter =
            domains.mapWireContext currentOuter)
          (currentTargetBinders : BinderContext
            (host.val.removeRaw selection domains) currentRels)
          (currentBindersEq : currentTargetBinders =
            domains.mapBinderContext currentBinders)
          (currentExact : (currentOuter.extend currentOrigin).Exact
            currentOrigin)
          (currentCovers : currentBinders.Covers currentOrigin)
          (currentAway : ¬ host.val.Encloses currentOrigin
            selection.val.anchor)
          (currentOutside : ¬ host.val.Encloses selection.val.anchor
            currentOrigin)
          (currentBody : CompiledRegion host.val
            (.nested currentOrigin currentOuter currentRels
              currentBinders)),
        compileRegion? host.val host.property currentOrigin currentOuter
            currentBinders = some currentBody →
          AwayRegionResult host selection domains currentOrigin currentOuter
            currentBinders currentSurvives currentTargetOuter currentOuterEq
            currentTargetBinders currentExact currentAway currentOutside
            currentBody
  have mapped : motive (.nested sourceOrigin sourceOuter rels
      sourceBinders) := by
    refine CompilerCall.compile?.induct host.val host.property
      (motive := motive) (fun current induction => ?_)
      (.nested sourceOrigin sourceOuter rels sourceBinders)
    cases current with
    | root ambient locals => exact True.intro
    | nested currentOrigin currentOuter currentRels currentBinders =>
        intro currentSurvives currentTargetOuter currentOuterEq
          currentTargetBinders currentBindersEq currentExact currentCovers
          currentAway currentOutside currentBody currentCompiled
        subst currentTargetOuter
        subst currentTargetBinders
        rcases currentBody with ⟨sourceItems⟩
        let current : CompilerCall host.val := .nested currentOrigin
          currentOuter currentRels currentBinders
        have sourceItemsCompiled := compileRegion?_items_of_success
          host.property currentOrigin currentOuter currentBinders
          currentCompiled
        let occurrenceSurvives : ∀ occurrence,
            occurrence ∈ localOccurrences host.val currentOrigin →
              domains.occurrenceSurvives occurrence = true := by
          intro occurrence member
          exact domains.localOccurrence_survives_away host selection
            currentOrigin currentSurvives currentAway occurrence member
        have targetOccurrences :=
          domains.localOccurrences_removeRaw_eq_map_index host selection
            currentOrigin currentSurvives occurrenceSurvives
        let sourceOccurrences := localOccurrences host.val currentOrigin
        let sourceDirect : ∀ occurrence, occurrence ∈ sourceOccurrences →
            occurrence ∈ localOccurrences host.val currentOrigin :=
          fun _ member => member
        let targetDirect : ∀ occurrence,
            occurrence ∈ sourceOccurrences.map domains.indexOccurrence →
              occurrence ∈ localOccurrences
                (host.val.removeRaw selection domains)
                (domains.regions.index currentOrigin currentSurvives) := by
          intro occurrence member
          rw [targetOccurrences]
          exact member
        have targetLocalEq := domains.mapWireContext_exactScope host selection
          (domains.regions.index currentOrigin currentSurvives)
        rw [domains.regions.origin_index] at targetLocalEq
        have targetFullEq :
            domains.mapWireContext currentOuter ++
                exactScopeWires (host.val.removeRaw selection domains)
                  (domains.regions.index currentOrigin currentSurvives) =
              domains.mapWireContext (currentOuter.extend currentOrigin) := by
          rw [← targetLocalEq, ← domains.mapWireContext_append]
          rfl
        let allWiresSurvive : ∀ wire,
            wire ∈ currentOuter.extend currentOrigin →
              domains.wires.survives wire = true := by
          intro wire member
          exact domains.visibleWire_survives_away host selection currentOrigin
            currentSurvives currentAway currentOutside
            (currentOuter.extend currentOrigin) currentExact wire member
        let fullBack : FiniteEquiv
            (Fin (domains.mapWireContext currentOuter ++
              exactScopeWires (host.val.removeRaw selection domains)
                (domains.regions.index currentOrigin currentSurvives)).length)
            (Fin (currentOuter.extend currentOrigin).length) :=
          (FiniteEquiv.finCast (congrArg List.length targetFullEq)).trans
            (domains.mapWireContextEquiv
              (currentOuter.extend currentOrigin) allWiresSurvive)
        let mappedItems := compileItems?_map_iso_success host.property
          (Diagram.removeRaw_wellFormed host selection domains)
          currentOrigin (domains.regions.index currentOrigin currentSurvives)
          (currentOuter.extend currentOrigin)
          (domains.mapWireContext currentOuter ++
            exactScopeWires (host.val.removeRaw selection domains)
              (domains.regions.index currentOrigin currentSurvives))
          currentBinders (domains.mapBinderContext currentBinders)
          sourceOccurrences domains.indexOccurrence sourceDirect targetDirect
          fullBack.symm (by
            intro occurrence member sourceItem occurrenceCompiled
            cases occurrence with
            | node node =>
                have nodeSurvives := occurrenceSurvives (.node node)
                  (sourceDirect (.node node) member)
                let targetNode := domains.nodes.index node nodeSurvives
                have mappedNodeEq : domains.indexOccurrence (.node node) =
                    .node targetNode := by
                  apply domains.originOccurrence_injective
                  rw [domains.originOccurrence_indexOccurrence (.node node)
                    nodeSurvives]
                  exact congrArg LocalOccurrence.node
                    (domains.nodes.origin_index node nodeSurvives).symm
                have sourceNodeCompiled : compileNode? host.val
                    (currentOuter.extend currentOrigin) currentBinders node =
                      some sourceItem := by
                  simpa only [compileOccurrence?_node] using
                    occurrenceCompiled
                let nodeResult := Classical.choice
                  (domains.mapNodeCompilationAt host selection
                    (currentOuter.extend currentOrigin)
                    (domains.mapWireContext currentOuter ++
                      exactScopeWires (host.val.removeRaw selection domains)
                        (domains.regions.index currentOrigin currentSurvives))
                    targetFullEq currentExact.nodup currentBinders
                    (domains.mapBinderContext currentBinders) rfl targetNode
                    allWiresSurvive (by
                      have targetNodeOrigin : domains.nodes.origin targetNode =
                          node := domains.nodes.origin_index node nodeSurvives
                      rw [targetNodeOrigin]
                      exact sourceNodeCompiled))
                have targetNodeDirect : LocalOccurrence.node targetNode ∈
                    localOccurrences (host.val.removeRaw selection domains)
                      (domains.regions.index currentOrigin
                        currentSurvives) :=
                  Eq.mp (congrArg (fun occurrence => occurrence ∈
                    localOccurrences (host.val.removeRaw selection domains)
                      (domains.regions.index currentOrigin currentSurvives))
                    mappedNodeEq)
                    (targetDirect (domains.indexOccurrence (.node node))
                      (List.mem_map.mpr ⟨.node node, member, rfl⟩))
                refine ⟨⟨nodeResult.fst, ⟨?_, ?_⟩⟩⟩
                · calc
                    compileOccurrence?
                        (host.val.removeRaw selection domains)
                        (Diagram.removeRaw_wellFormed host selection domains)
                        (domains.regions.index currentOrigin currentSurvives)
                        (domains.mapWireContext currentOuter ++
                          exactScopeWires
                            (host.val.removeRaw selection domains)
                            (domains.regions.index currentOrigin
                              currentSurvives))
                        (domains.mapBinderContext currentBinders)
                        (domains.indexOccurrence (.node node)) _ =
                      compileOccurrence?
                        (host.val.removeRaw selection domains)
                        (Diagram.removeRaw_wellFormed host selection domains)
                        (domains.regions.index currentOrigin currentSurvives)
                        (domains.mapWireContext currentOuter ++
                          exactScopeWires
                            (host.val.removeRaw selection domains)
                            (domains.regions.index currentOrigin
                              currentSurvives))
                        (domains.mapBinderContext currentBinders)
                        (.node targetNode) targetNodeDirect :=
                      compileOccurrence?_congr_occurrence _ _ _ _
                        mappedNodeEq _ targetNodeDirect
                    _ = some nodeResult.fst := by
                      simpa only [compileOccurrence?_node] using
                        nodeResult.snd.fst
                · simpa [fullBack] using nodeResult.snd.snd.symm
            | child child =>
                have childSurvives := occurrenceSurvives (.child child)
                  (sourceDirect (.child child) member)
                let targetChild := domains.regions.index child childSurvives
                have mappedChildEq : domains.indexOccurrence (.child child) =
                    .child targetChild := by
                  apply domains.originOccurrence_injective
                  rw [domains.originOccurrence_indexOccurrence (.child child)
                    childSurvives]
                  exact congrArg LocalOccurrence.child
                    (domains.regions.origin_index child childSurvives).symm
                have sourceParent := (mem_localOccurrences_child host.val
                  currentOrigin child).mp (sourceDirect (.child child) member)
                have parentChild : host.val.Encloses currentOrigin child := by
                  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
                  simp [Diagram.climb, sourceParent]
                have childAway : ¬ host.val.Encloses child
                    selection.val.anchor := by
                  intro childEncloses
                  exact currentAway (checked_encloses_trans host.property
                    parentChild childEncloses)
                have childOutside : ¬ host.val.Encloses selection.val.anchor
                    child := by
                  intro anchorEncloses
                  rcases encloses_direct_child sourceParent anchorEncloses with
                    anchorEq | anchorEnclosesParent
                  · subst child
                    exact currentAway parentChild
                  · exact currentOutside anchorEnclosesParent
                have childExact := currentExact.extend_child host.property
                  sourceParent
                cases sourceKind : host.val.regions child with
                | sheet =>
                    rw [compileOccurrence?_child_sheet host.property
                      currentOrigin child (currentOuter.extend currentOrigin)
                      currentBinders (sourceDirect (.child child) member)
                      sourceKind] at occurrenceCompiled
                    contradiction
                | cut sourceKindParent =>
                    have parentEq : sourceKindParent = currentOrigin := by
                      simpa [sourceKind, CRegion.parent?] using sourceParent
                    subst sourceKindParent
                    obtain ⟨sourceChildBody, sourceChildCompiled,
                        sourceItemEq⟩ :=
                      compileOccurrence?_child_cut_success host.property
                        currentOrigin child (currentOuter.extend currentOrigin)
                        currentBinders (sourceDirect (.child child) member)
                        sourceKind occurrenceCompiled
                    subst sourceItem
                    have targetKind := domains.removeRaw_cut host selection
                      currentSurvives childSurvives sourceKind
                    let childMapped := induction child sourceParent
                      (currentOuter.extend currentOrigin) currentBinders
                      childSurvives
                      (domains.mapWireContext currentOuter ++
                        exactScopeWires
                          (host.val.removeRaw selection domains)
                          (domains.regions.index currentOrigin currentSurvives))
                      targetFullEq (domains.mapBinderContext currentBinders)
                      rfl childExact
                      (BinderContext.covers_cut_child currentCovers sourceKind)
                      childAway childOutside sourceChildBody
                      sourceChildCompiled
                    let childResult := Classical.choice childMapped
                    let targetItem : CompiledItem
                        (host.val.removeRaw selection domains)
                        (domains.mapWireContext currentOuter ++
                          exactScopeWires
                            (host.val.removeRaw selection domains)
                            (domains.regions.index currentOrigin
                              currentSurvives)) currentRels
                        (domains.mapBinderContext currentBinders) :=
                      .cut childResult.fst
                    have targetChildDirect : LocalOccurrence.child targetChild ∈
                        localOccurrences (host.val.removeRaw selection domains)
                          (domains.regions.index currentOrigin
                            currentSurvives) := by
                      exact Eq.mp (congrArg (fun occurrence => occurrence ∈
                        localOccurrences
                          (host.val.removeRaw selection domains)
                          (domains.regions.index currentOrigin currentSurvives))
                        mappedChildEq)
                        (targetDirect
                          (domains.indexOccurrence (.child child))
                          (List.mem_map.mpr ⟨.child child, member, rfl⟩))
                    refine ⟨⟨targetItem, ⟨?_, ?_⟩⟩⟩
                    · calc
                        compileOccurrence?
                            (host.val.removeRaw selection domains)
                            (Diagram.removeRaw_wellFormed host selection domains)
                            (domains.regions.index currentOrigin currentSurvives)
                            (domains.mapWireContext currentOuter ++
                              exactScopeWires
                                (host.val.removeRaw selection domains)
                                (domains.regions.index currentOrigin
                                  currentSurvives))
                            (domains.mapBinderContext currentBinders)
                            (domains.indexOccurrence (.child child)) _ =
                          compileOccurrence?
                            (host.val.removeRaw selection domains)
                            (Diagram.removeRaw_wellFormed host selection domains)
                            (domains.regions.index currentOrigin currentSurvives)
                            (domains.mapWireContext currentOuter ++
                              exactScopeWires
                                (host.val.removeRaw selection domains)
                                (domains.regions.index currentOrigin
                                  currentSurvives))
                            (domains.mapBinderContext currentBinders)
                            (.child targetChild) targetChildDirect :=
                          compileOccurrence?_congr_occurrence _ _ _ _
                            mappedChildEq _ targetChildDirect
                        _ = some targetItem := by
                          rw [compileOccurrence?_child_cut
                            (Diagram.removeRaw_wellFormed host selection domains)
                            (domains.regions.index currentOrigin currentSurvives)
                            targetChild
                            (domains.mapWireContext currentOuter ++
                              exactScopeWires
                                (host.val.removeRaw selection domains)
                                (domains.regions.index currentOrigin
                                  currentSurvives))
                            (domains.mapBinderContext currentBinders)
                            targetChildDirect
                            (by simpa [targetChild,
                              FrameDomains.indexOccurrence] using targetKind)]
                          rw [childResult.snd.fst]
                          rfl
                    · simpa [targetItem, fullBack] using
                        (ItemIso.cut childResult.snd.snd).symm
                | bubble sourceKindParent arity =>
                    have parentEq : sourceKindParent = currentOrigin := by
                      simpa [sourceKind, CRegion.parent?] using sourceParent
                    subst sourceKindParent
                    obtain ⟨sourceChildBody, sourceChildCompiled,
                        sourceItemEq⟩ :=
                      compileOccurrence?_child_bubble_success host.property
                        currentOrigin child (currentOuter.extend currentOrigin)
                        currentBinders arity
                        (sourceDirect (.child child) member) sourceKind
                        occurrenceCompiled
                    subst sourceItem
                    have targetKind := domains.removeRaw_bubble host selection
                      currentSurvives childSurvives arity sourceKind
                    let targetPushed :=
                      (domains.mapBinderContext currentBinders).push
                        targetChild arity
                    have targetPushedEq : targetPushed =
                        domains.mapBinderContext
                          (currentBinders.push child arity) := by
                      exact (domains.mapBinderContext_push currentBinders child
                        childSurvives arity).symm
                    let childMapped := induction child sourceParent
                      (currentOuter.extend currentOrigin)
                      (currentBinders.push child arity) childSurvives
                      (domains.mapWireContext currentOuter ++
                        exactScopeWires
                          (host.val.removeRaw selection domains)
                          (domains.regions.index currentOrigin currentSurvives))
                      targetFullEq targetPushed targetPushedEq childExact
                      (BinderContext.push_covers_bubble_child currentCovers
                        sourceKind)
                      childAway childOutside sourceChildBody
                      sourceChildCompiled
                    let childResult := Classical.choice childMapped
                    let targetItem : CompiledItem
                        (host.val.removeRaw selection domains)
                        (domains.mapWireContext currentOuter ++
                          exactScopeWires
                            (host.val.removeRaw selection domains)
                            (domains.regions.index currentOrigin
                              currentSurvives)) currentRels
                        (domains.mapBinderContext currentBinders) :=
                      .bubble arity childResult.fst
                    have targetChildDirect : LocalOccurrence.child targetChild ∈
                        localOccurrences (host.val.removeRaw selection domains)
                          (domains.regions.index currentOrigin
                            currentSurvives) := by
                      exact Eq.mp (congrArg (fun occurrence => occurrence ∈
                        localOccurrences
                          (host.val.removeRaw selection domains)
                          (domains.regions.index currentOrigin currentSurvives))
                        mappedChildEq)
                        (targetDirect
                          (domains.indexOccurrence (.child child))
                          (List.mem_map.mpr ⟨.child child, member, rfl⟩))
                    refine ⟨⟨targetItem, ⟨?_, ?_⟩⟩⟩
                    · calc
                        compileOccurrence?
                            (host.val.removeRaw selection domains)
                            (Diagram.removeRaw_wellFormed host selection domains)
                            (domains.regions.index currentOrigin currentSurvives)
                            (domains.mapWireContext currentOuter ++
                              exactScopeWires
                                (host.val.removeRaw selection domains)
                                (domains.regions.index currentOrigin
                                  currentSurvives))
                            (domains.mapBinderContext currentBinders)
                            (domains.indexOccurrence (.child child)) _ =
                          compileOccurrence?
                            (host.val.removeRaw selection domains)
                            (Diagram.removeRaw_wellFormed host selection domains)
                            (domains.regions.index currentOrigin currentSurvives)
                            (domains.mapWireContext currentOuter ++
                              exactScopeWires
                                (host.val.removeRaw selection domains)
                                (domains.regions.index currentOrigin
                                  currentSurvives))
                            (domains.mapBinderContext currentBinders)
                            (.child targetChild) targetChildDirect :=
                          compileOccurrence?_congr_occurrence _ _ _ _
                            mappedChildEq _ targetChildDirect
                        _ = some targetItem := by
                          rw [compileOccurrence?_child_bubble
                            (Diagram.removeRaw_wellFormed host selection domains)
                            (domains.regions.index currentOrigin currentSurvives)
                            targetChild
                            (domains.mapWireContext currentOuter ++
                              exactScopeWires
                                (host.val.removeRaw selection domains)
                                (domains.regions.index currentOrigin
                                  currentSurvives))
                            (domains.mapBinderContext currentBinders) arity
                            targetChildDirect
                            (by simpa [targetChild,
                              FrameDomains.indexOccurrence] using targetKind)]
                          rw [childResult.snd.fst]
                          rfl
                    · simpa [targetItem, fullBack] using
                        (ItemIso.bubble childResult.snd.snd).symm)
          (by simpa [sourceOccurrences, sourceDirect] using sourceItemsCompiled)
        let result := Classical.choice mappedItems
        let targetCall : CompilerCall
            (host.val.removeRaw selection domains) :=
          .nested (domains.regions.index currentOrigin currentSurvives)
            (domains.mapWireContext currentOuter) currentRels
            (domains.mapBinderContext currentBinders)
        let targetBody : CompiledRegion
            (host.val.removeRaw selection domains) targetCall := .mk result.fst
        have canonicalTargetItems : compileItems?
            (host.val.removeRaw selection domains)
            (Diagram.removeRaw_wellFormed host selection domains)
            (domains.regions.index currentOrigin currentSurvives)
            ((domains.mapWireContext currentOuter).extend
              (domains.regions.index currentOrigin currentSurvives))
            (domains.mapBinderContext currentBinders)
            (localOccurrences (host.val.removeRaw selection domains)
              (domains.regions.index currentOrigin currentSurvives))
            (fun _ member => member) = some result.fst := by
          exact (compileItems?_congr_occurrences
            (Diagram.removeRaw_wellFormed host selection domains)
            (domains.regions.index currentOrigin currentSurvives)
            ((domains.mapWireContext currentOuter).extend
              (domains.regions.index currentOrigin currentSurvives))
            (domains.mapBinderContext currentBinders) targetOccurrences
            (fun _ member => member) targetDirect).trans result.snd.fst
        have targetCompiled : compileRegion?
            (host.val.removeRaw selection domains)
            (Diagram.removeRaw_wellFormed host selection domains)
            (domains.regions.index currentOrigin currentSurvives)
            (domains.mapWireContext currentOuter)
            (domains.mapBinderContext currentBinders) = some targetBody := by
          rw [compileRegion?_eq_compileItems?]
          rw [canonicalTargetItems]
          rfl
        refine ⟨⟨targetBody, ⟨targetCompiled, ?_⟩⟩⟩
        have itemsIso := result.snd.snd.symm
        have outerSurvives : ∀ wire, wire ∈ currentOuter →
            domains.wires.survives wire = true := by
          intro wire member
          exact allWiresSurvive wire (List.mem_append_left _ member)
        have localSurvives : ∀ wire,
            wire ∈ exactScopeWires host.val currentOrigin →
              domains.wires.survives wire = true := by
          intro wire member
          exact allWiresSurvive wire (List.mem_append_right _ member)
        let localBack : FiniteEquiv
            (Fin (exactScopeWires (host.val.removeRaw selection domains)
              (domains.regions.index currentOrigin currentSurvives)).length)
            (Fin (exactScopeWires host.val currentOrigin).length) :=
          (FiniteEquiv.finCast (congrArg List.length targetLocalEq.symm)).trans
            (domains.mapWireContextEquiv
              (exactScopeWires host.val currentOrigin) localSurvives)
        let targetCast := FiniteEquiv.finCast
          (CompilerCall.fullContext_length targetCall)
        let sourceCast := FiniteEquiv.finCast
          (CompilerCall.fullContext_length current)
        let castedItemsIso :=
          (ItemSeqIso.renameWiresEquiv result.fst.erase targetCast).symm |>.trans
            (itemsIso.trans
              (ItemSeqIso.renameWiresEquiv sourceItems.erase sourceCast))
        have fullBackSymm : fullBack.symm.symm = fullBack := by
          rfl
        rw [fullBackSymm] at castedItemsIso
        have outerLength : (domains.mapWireContext currentOuter).length =
            currentOuter.length := by
          simpa using congrArg List.length
            (domains.mapWireContext_origin_eq currentOuter outerSurvives)
        have castedWireEq : targetCast.symm.trans
            (fullBack.trans sourceCast) = extendWireEquiv
              (domains.mapWireContextEquiv currentOuter outerSurvives)
              localBack := by
          apply FiniteEquiv.ext
          intro index
          apply Fin.ext
          refine Fin.addCases (m := (domains.mapWireContext currentOuter).length)
            (n := (exactScopeWires (host.val.removeRaw selection domains)
              (domains.regions.index currentOrigin currentSurvives)).length)
            (fun inherited => ?_) (fun localIndex => ?_) index
          · simp [targetCast, sourceCast, targetCall, current, fullBack,
              localBack, FiniteEquiv.finCast, extendWireEquiv]
          · simp [targetCast, sourceCast, targetCall, current, fullBack,
              localBack, FiniteEquiv.finCast, extendWireEquiv]
            exact outerLength
        have alignedItemsIso : ItemSeqIso
            (extendWireEquiv
              (domains.mapWireContextEquiv currentOuter outerSurvives)
              localBack) currentRels
            (ItemSeq.renameWires targetCast.toFun result.fst.erase)
            (ItemSeq.renameWires sourceCast.toFun sourceItems.erase) :=
          castedWireEq ▸ castedItemsIso
        let expectedOuter :=
          (FiniteEquiv.finCast (congrArg List.length (Eq.refl
            (domains.mapWireContext currentOuter)))).trans
              (domains.mapWireContextEquiv currentOuter outerSurvives)
        have outerBackEq : expectedOuter =
            domains.mapWireContextEquiv currentOuter outerSurvives := by
          apply FiniteEquiv.ext
          intro index
          rfl
        change RegionIso expectedOuter currentRels targetBody.erase
          (CompiledRegion.mk sourceItems).erase
        rw [outerBackEq]
        simpa [targetBody, targetCall, current, CompiledRegion.erase,
          CompilerCall.finish, CompilerCall.castFullItems,
          ItemSeq.castWiresEq_eq_renameWires] using
            (RegionIso.mk localBack alignedItemsIso)
  exact mapped originSurvives targetOuter outerEq targetBinders bindersEq
    exact covers away outside sourceBody sourceCompiled

/-- Semantic transport for one finite sibling block strictly above the
selected anchor.  The caller owns the actual target context; this theorem
owns only the stable source-order mapping and the block isomorphism. -/
abbrev AboveBlockResult
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceParent : Fin host.val.regionCount)
    (sourceContext : WireContext host.val)
    (sourceBinders : BinderContext host.val rels)
    (parentSurvives : domains.regions.survives sourceParent = true)
    (above : host.val.Encloses sourceParent selection.val.anchor)
    (different : sourceParent ≠ selection.val.anchor)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetContext : WireContext (host.val.removeRaw selection domains))
    (contextEq : targetContext = domains.mapWireContext sourceContext)
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (items : CompiledItems host.val sourceContext rels sourceBinders)
    (sourceDirect : forall occurrence, occurrence ∈ items.origins ->
      occurrence ∈ localOccurrences host.val sourceParent) :=
  Nonempty (Sigma fun targetItems : CompiledItems
      (host.val.removeRaw selection domains) targetContext rels targetBinders =>
    PSigma fun _ : compileItems? (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceParent parentSurvives) targetContext
        targetBinders (items.origins.map domains.indexOccurrence)
        (fun occurrence member => by
          rw [domains.localOccurrences_removeRaw_eq_map_index host selection
            sourceParent parentSurvives (fun candidate candidateMember =>
              domains.localOccurrence_survives_above host selection
                sourceParent above different candidate candidateMember)]
          obtain ⟨sourceOccurrence, sourceMember, rfl⟩ :=
            List.mem_map.mp member
          exact List.mem_map.mpr
            ⟨sourceOccurrence, sourceDirect sourceOccurrence sourceMember,
              rfl⟩) = some targetItems =>
      ItemSeqIso
        ((domains.mapWireContextEquiv sourceContext (fun wire member =>
          domains.visibleWire_survives_above host selection sourceParent above
            different sourceContext sourceExact wire member)).symm.trans
          (FiniteEquiv.finCast (congrArg List.length contextEq).symm))
        rels items.erase targetItems.erase)

/-- Compile and align an unchanged sibling block in the dense frame.  Child
subtrees are compiled by `compileRegionAway`; no target traversal or target
compiler witness is accepted. -/
theorem compileAboveBlock
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceParent : Fin host.val.regionCount)
    (sourceContext : WireContext host.val)
    (sourceBinders : BinderContext host.val rels)
    (parentSurvives : domains.regions.survives sourceParent = true)
    (above : host.val.Encloses sourceParent selection.val.anchor)
    (different : sourceParent ≠ selection.val.anchor)
    (targetContext : WireContext (host.val.removeRaw selection domains))
    (contextEq : targetContext = domains.mapWireContext sourceContext)
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) rels)
    (bindersEq : targetBinders = domains.mapBinderContext sourceBinders)
    (sourceExact : sourceContext.Exact sourceParent)
    (sourceCovers : sourceBinders.Covers sourceParent)
    (items : CompiledItems host.val sourceContext rels sourceBinders)
    (sourceDirect : forall occurrence, occurrence ∈ items.origins ->
      occurrence ∈ localOccurrences host.val sourceParent)
    (childrenAway : forall child,
      LocalOccurrence.child child ∈ items.origins ->
        ¬ host.val.Encloses child selection.val.anchor)
    (childrenOutside : forall child,
      LocalOccurrence.child child ∈ items.origins ->
        ¬ host.val.Encloses selection.val.anchor child)
    (sourceCompiled : compileItems? host.val host.property sourceParent
      sourceContext sourceBinders items.origins sourceDirect = some items) :
    AboveBlockResult host selection domains sourceParent sourceContext
      sourceBinders parentSurvives above different sourceExact targetContext
      contextEq targetBinders items sourceDirect := by
  let allSurvive : forall wire, wire ∈ sourceContext ->
      domains.wires.survives wire = true := by
    intro wire member
    exact domains.visibleWire_survives_above host selection sourceParent above
      different sourceContext sourceExact wire member
  let targetDirect : forall occurrence,
      occurrence ∈ items.origins.map domains.indexOccurrence ->
        occurrence ∈ localOccurrences (host.val.removeRaw selection domains)
          (domains.regions.index sourceParent parentSurvives) := by
    intro occurrence member
    rw [domains.localOccurrences_removeRaw_eq_map_index host selection
      sourceParent parentSurvives (fun candidate candidateMember =>
        domains.localOccurrence_survives_above host selection sourceParent
          above different candidate candidateMember)]
    obtain ⟨sourceOccurrence, sourceMember, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr
      ⟨sourceOccurrence, sourceDirect sourceOccurrence sourceMember, rfl⟩
  let fullForward : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    (domains.mapWireContextEquiv sourceContext allSurvive).symm.trans
      (FiniteEquiv.finCast (congrArg List.length contextEq).symm)
  let mapped := compileItems?_map_iso_success host.property
    (Diagram.removeRaw_wellFormed host selection domains)
    sourceParent (domains.regions.index sourceParent parentSurvives)
    sourceContext targetContext sourceBinders targetBinders items.origins
    domains.indexOccurrence sourceDirect targetDirect fullForward (by
      intro occurrence member sourceItem occurrenceCompiled
      cases occurrence with
      | node node =>
          have nodeSurvives : domains.nodes.survives node = true := by
            exact domains.localOccurrence_survives_above host selection
              sourceParent above different (.node node)
                (sourceDirect (.node node) member)
          let targetNode := domains.nodes.index node nodeSurvives
          have mappedNodeEq : domains.indexOccurrence (.node node) =
              .node targetNode := by
            apply domains.originOccurrence_injective
            rw [domains.originOccurrence_indexOccurrence (.node node)
              nodeSurvives]
            exact congrArg LocalOccurrence.node
              (domains.nodes.origin_index node nodeSurvives).symm
          have sourceNodeCompiled : compileNode? host.val sourceContext
              sourceBinders node = some sourceItem := by
            simpa only [compileOccurrence?_node] using occurrenceCompiled
          let nodeResult := Classical.choice
            (domains.mapNodeCompilationAt host selection sourceContext
              targetContext contextEq sourceExact.nodup sourceBinders
              targetBinders bindersEq targetNode allSurvive (by
                have originEq : domains.nodes.origin targetNode = node :=
                  domains.nodes.origin_index node nodeSurvives
                rw [originEq]
                exact sourceNodeCompiled))
          have targetNodeDirect : LocalOccurrence.node targetNode ∈
              localOccurrences (host.val.removeRaw selection domains)
                (domains.regions.index sourceParent parentSurvives) := by
            exact Eq.mp (congrArg (fun candidate => candidate ∈
              localOccurrences (host.val.removeRaw selection domains)
                (domains.regions.index sourceParent parentSurvives))
              mappedNodeEq) (targetDirect (domains.indexOccurrence
                (.node node)) (List.mem_map.mpr ⟨.node node, member, rfl⟩))
          refine ⟨⟨nodeResult.fst, ⟨?_, ?_⟩⟩⟩
          · exact (compileOccurrence?_congr_occurrence _ _ _ _ mappedNodeEq
              _ targetNodeDirect).trans (by
                simpa only [compileOccurrence?_node] using nodeResult.snd.fst)
          · simpa [fullForward] using nodeResult.snd.snd.symm
      | child child =>
          have childSurvives : domains.regions.survives child = true := by
            exact domains.localOccurrence_survives_above host selection
              sourceParent above different (.child child)
                (sourceDirect (.child child) member)
          let targetChild := domains.regions.index child childSurvives
          have mappedChildEq : domains.indexOccurrence (.child child) =
              .child targetChild := by
            apply domains.originOccurrence_injective
            rw [domains.originOccurrence_indexOccurrence (.child child)
              childSurvives]
            exact congrArg LocalOccurrence.child
              (domains.regions.origin_index child childSurvives).symm
          have sourceParentEq := (mem_localOccurrences_child host.val
            sourceParent child).mp (sourceDirect (.child child) member)
          have childExact := sourceExact.extend_child host.property
            sourceParentEq
          cases sourceKind : host.val.regions child with
          | sheet =>
              rw [compileOccurrence?_child_sheet host.property sourceParent
                child sourceContext sourceBinders
                (sourceDirect (.child child) member) sourceKind]
                at occurrenceCompiled
              contradiction
          | cut sourceKindParent =>
              have parentEq : sourceKindParent = sourceParent := by
                simpa [sourceKind, CRegion.parent?] using sourceParentEq
              subst sourceKindParent
              obtain ⟨sourceChildBody, sourceChildCompiled, sourceItemEq⟩ :=
                compileOccurrence?_child_cut_success host.property sourceParent
                  child sourceContext sourceBinders
                  (sourceDirect (.child child) member) sourceKind
                  occurrenceCompiled
              subst sourceItem
              have targetKind := domains.removeRaw_cut host selection
                parentSurvives childSurvives sourceKind
              let childMapped := domains.compileRegionAway host selection child
                sourceContext sourceBinders childSurvives targetContext
                contextEq targetBinders bindersEq childExact
                (BinderContext.covers_cut_child sourceCovers sourceKind)
                (childrenAway child member) (childrenOutside child member)
                sourceChildBody sourceChildCompiled
              obtain ⟨⟨targetChildBody, targetChildCompiled0,
                  targetChildIso⟩⟩ := childMapped
              let targetItem : CompiledItem
                  (host.val.removeRaw selection domains) targetContext rels
                  targetBinders := .cut targetChildBody
              have targetChildDirect : LocalOccurrence.child targetChild ∈
                  localOccurrences (host.val.removeRaw selection domains)
                    (domains.regions.index sourceParent parentSurvives) := by
                exact Eq.mp (congrArg (fun candidate => candidate ∈
                  localOccurrences (host.val.removeRaw selection domains)
                    (domains.regions.index sourceParent parentSurvives))
                  mappedChildEq) (targetDirect (domains.indexOccurrence
                    (.child child))
                      (List.mem_map.mpr ⟨.child child, member, rfl⟩))
              refine ⟨⟨targetItem, ⟨?_, ?_⟩⟩⟩
              · exact (compileOccurrence?_congr_occurrence _ _ _ _
                  mappedChildEq _ targetChildDirect).trans (by
                    change compileOccurrence?
                      (host.val.removeRaw selection domains)
                      (Diagram.removeRaw_wellFormed host selection domains)
                      (domains.regions.index sourceParent parentSurvives)
                      targetContext targetBinders (.child targetChild)
                      targetChildDirect = some (.cut targetChildBody)
                    rw [compileOccurrence?_child_cut
                      (Diagram.removeRaw_wellFormed host selection domains)
                      (domains.regions.index sourceParent parentSurvives)
                      targetChild targetContext targetBinders targetChildDirect
                      (by simpa [targetChild,
                        FrameDomains.indexOccurrence] using targetKind)]
                    have targetChildCompiled : compileRegion?
                        (host.val.removeRaw selection domains)
                        (Diagram.removeRaw_wellFormed host selection domains)
                        targetChild targetContext targetBinders =
                          some targetChildBody := by
                      simpa [targetChild] using targetChildCompiled0
                    rw [targetChildCompiled]
                    rfl)
              · simpa [targetItem, fullForward] using
                  (ItemIso.cut targetChildIso).symm
          | bubble sourceKindParent arity =>
              have parentEq : sourceKindParent = sourceParent := by
                simpa [sourceKind, CRegion.parent?] using sourceParentEq
              subst sourceKindParent
              obtain ⟨sourceChildBody, sourceChildCompiled, sourceItemEq⟩ :=
                compileOccurrence?_child_bubble_success host.property
                  sourceParent child sourceContext sourceBinders arity
                  (sourceDirect (.child child) member) sourceKind
                  occurrenceCompiled
              subst sourceItem
              have targetKind := domains.removeRaw_bubble host selection
                parentSurvives childSurvives arity sourceKind
              let targetPushed := targetBinders.push targetChild arity
              have targetPushedEq : targetPushed = domains.mapBinderContext
                  (sourceBinders.push child arity) := by
                unfold targetPushed
                rw [bindersEq]
                exact (domains.mapBinderContext_push sourceBinders child
                  childSurvives arity).symm
              let childMapped := domains.compileRegionAway host selection child
                sourceContext (sourceBinders.push child arity) childSurvives
                targetContext contextEq targetPushed targetPushedEq childExact
                (BinderContext.push_covers_bubble_child sourceCovers sourceKind)
                (childrenAway child member) (childrenOutside child member)
                sourceChildBody sourceChildCompiled
              obtain ⟨⟨targetChildBody, targetChildCompiled0,
                  targetChildIso⟩⟩ := childMapped
              let targetItem : CompiledItem
                  (host.val.removeRaw selection domains) targetContext rels
                  targetBinders := .bubble arity targetChildBody
              have targetChildDirect : LocalOccurrence.child targetChild ∈
                  localOccurrences (host.val.removeRaw selection domains)
                    (domains.regions.index sourceParent parentSurvives) := by
                exact Eq.mp (congrArg (fun candidate => candidate ∈
                  localOccurrences (host.val.removeRaw selection domains)
                    (domains.regions.index sourceParent parentSurvives))
                  mappedChildEq) (targetDirect (domains.indexOccurrence
                    (.child child))
                      (List.mem_map.mpr ⟨.child child, member, rfl⟩))
              refine ⟨⟨targetItem, ⟨?_, ?_⟩⟩⟩
              · exact (compileOccurrence?_congr_occurrence _ _ _ _
                  mappedChildEq _ targetChildDirect).trans (by
                    change compileOccurrence?
                      (host.val.removeRaw selection domains)
                      (Diagram.removeRaw_wellFormed host selection domains)
                      (domains.regions.index sourceParent parentSurvives)
                      targetContext targetBinders (.child targetChild)
                      targetChildDirect = some
                        (.bubble arity targetChildBody)
                    rw [compileOccurrence?_child_bubble
                      (Diagram.removeRaw_wellFormed host selection domains)
                      (domains.regions.index sourceParent parentSurvives)
                      targetChild targetContext targetBinders arity
                      targetChildDirect (by simpa [targetChild,
                        FrameDomains.indexOccurrence] using targetKind)]
                    have targetChildCompiled : compileRegion?
                        (host.val.removeRaw selection domains)
                        (Diagram.removeRaw_wellFormed host selection domains)
                        targetChild targetContext
                          (targetBinders.push targetChild arity) =
                            some targetChildBody := by
                      simpa [targetChild, targetPushed] using
                        targetChildCompiled0
                    rw [targetChildCompiled]
                    rfl)
              · simpa [targetItem, fullForward] using
                  (ItemIso.bubble targetChildIso).symm)
    sourceCompiled
  exact mapped

end FrameDomains

end VisualProof.Concrete
