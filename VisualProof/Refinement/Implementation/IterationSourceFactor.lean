import VisualProof.Refinement.Implementation.IterationExtractionSelected
import VisualProof.Refinement.Implementation.IterationRoute
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.IterationSourceFactor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationPartition
open VisualProof.Refinement.Implementation.IterationRoute

/-- Anchor-local wires retained by the source context.  The explicit block is
owned by the selected factor instead. -/
def retainedAnchorWires
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) : List (Fin input.wireCount) :=
  (Concrete.Elaboration.exactScopeWires input selection.val.anchor).filter
    (fun wire => !(decide (wire ∈ selection.val.explicitWires)))

/-- Complete outer context of the selected factor: inherited wires followed
by anchor-local wires not explicitly owned by the selection. -/
def retainedContext
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    Concrete.Elaboration.WireContext input :=
  inherited ++ retainedAnchorWires input selection

theorem retainedContext_length
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    (retainedContext input selection inherited).length =
      inherited.length + (retainedAnchorWires input selection).length := by
  simp [retainedContext]

theorem explicitWire_mem_exactScopeWires
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    {wire : Fin input.wireCount}
    (member : wire ∈ selection.val.explicitWires) :
    wire ∈ Concrete.Elaboration.exactScopeWires input
      selection.val.anchor := by
  rw [Concrete.Elaboration.mem_exactScopeWires]
  exact selection.property.explicitWires_at_anchor wire member

theorem retainedAnchorWires_nodup
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (retainedAnchorWires input selection).Nodup := by
  exact (Concrete.Elaboration.exactScopeWires_nodup input
    selection.val.anchor).filter _

@[simp] theorem mem_retainedAnchorWires
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wire : Fin input.wireCount) :
    wire ∈ retainedAnchorWires input selection ↔
      (input.wires wire).scope = selection.val.anchor ∧
        wire ∉ selection.val.explicitWires := by
  simp [retainedAnchorWires]

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

theorem selectedExplicitFilter_perm
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    ((Concrete.Elaboration.exactScopeWires input selection.val.anchor).filter
      (fun wire => decide (wire ∈ selection.val.explicitWires))).Perm
      selection.val.explicitWires := by
  apply perm_of_nodup_and_mem_iff
  · exact (Concrete.Elaboration.exactScopeWires_nodup input
      selection.val.anchor).filter _
  · exact selection.property.explicitWires_nodup
  · intro wire
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun member => member.2
    · intro member
      exact ⟨explicitWire_mem_exactScopeWires input selection member, member⟩

theorem retainedAnchorWires_append_explicit_perm
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (retainedAnchorWires input selection ++
      selection.val.explicitWires).Perm
      (Concrete.Elaboration.exactScopeWires input selection.val.anchor) := by
  let exact := Concrete.Elaboration.exactScopeWires input selection.val.anchor
  let selected := exact.filter
    (fun wire => decide (wire ∈ selection.val.explicitWires))
  have partition : (retainedAnchorWires input selection ++ selected).Perm exact := by
    have split := List.filter_append_perm
      (fun wire => decide (wire ∈ selection.val.explicitWires)) exact
    exact (List.perm_append_comm.trans (by
      simpa only [retainedAnchorWires, exact, selected] using split))
  exact (List.Perm.append_left (retainedAnchorWires input selection)
    (selectedExplicitFilter_perm input selection)).symm.trans partition

theorem retainedContext_append_explicit_perm
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    (retainedContext input selection inherited ++
      selection.val.explicitWires).Perm
      (inherited.extend selection.val.anchor) := by
  simpa only [retainedContext, Concrete.Elaboration.WireContext.extend,
    List.append_assoc] using
    List.Perm.append_left inherited
      (retainedAnchorWires_append_explicit_perm input selection)

/-- The local-wire equivalence that moves the explicit block out of the
anchor binder and into the selected factor. -/
noncomputable def anchorLocalEquiv
    (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    FiniteEquiv
      (Fin ((retainedAnchorWires input selection).length +
        selection.val.explicitWires.length))
      (Fin (Concrete.Elaboration.exactScopeWires input
        selection.val.anchor).length) :=
  let source := retainedAnchorWires input selection ++
    selection.val.explicitWires
  let target := Concrete.Elaboration.exactScopeWires input
    selection.val.anchor
  let permutation := retainedAnchorWires_append_explicit_perm input selection
  let targetNodup := Concrete.Elaboration.exactScopeWires_nodup input
    selection.val.anchor
  let sourceNodup := permutation.nodup_iff.mpr targetNodup
  (FiniteEquiv.finCast (by simp [source])).trans
    (IterationPartition.permIndexEquiv source target permutation sourceNodup
      targetNodup)

theorem anchorLocalEquiv_spec
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (index : Fin ((retainedAnchorWires input selection).length +
      selection.val.explicitWires.length)) :
    (Concrete.Elaboration.exactScopeWires input
      selection.val.anchor).get (anchorLocalEquiv input selection index) =
    (retainedAnchorWires input selection ++
      selection.val.explicitWires).get (Fin.cast (by simp) index) := by
  let source := retainedAnchorWires input selection ++
    selection.val.explicitWires
  let target := Concrete.Elaboration.exactScopeWires input
    selection.val.anchor
  let permutation := retainedAnchorWires_append_explicit_perm input selection
  let targetNodup := Concrete.Elaboration.exactScopeWires_nodup input
    selection.val.anchor
  let sourceNodup := permutation.nodup_iff.mpr targetNodup
  exact IterationPartition.permIndexEquiv_spec source target permutation
    sourceNodup targetNodup (Fin.cast (by simp [source]) index)

/-- Complete wire equivalence at the anchor, factored as identity on inherited
wires and the retained/explicit local partition. -/
noncomputable def anchorWireEquiv
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    FiniteEquiv
      (Fin (inherited.length +
        ((retainedAnchorWires input selection).length +
          selection.val.explicitWires.length)))
      (Fin (inherited.length +
        (Concrete.Elaboration.exactScopeWires input
          selection.val.anchor).length)) :=
  extendWireEquiv (FiniteEquiv.refl (Fin inherited.length))
    (anchorLocalEquiv input selection)

theorem retainedContext_member_full
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input)
    {wire : Fin input.wireCount}
    (member : wire ∈ retainedContext input selection inherited) :
    wire ∈ inherited.extend selection.val.anchor := by
  rcases List.mem_append.mp member with inheritedMember | retainedMember
  · exact List.mem_append.mpr (Or.inl inheritedMember)
  · exact List.mem_append.mpr (Or.inr
      ((Concrete.Elaboration.mem_exactScopeWires input
        selection.val.anchor wire).2
        ((mem_retainedAnchorWires input selection wire).1 retainedMember).1))

/-- Canonical inclusion of the retained wire context into the compiler's full
anchor context.  This is an index lookup into the authoritative context, not
a second compilation or context authority. -/
noncomputable def retainedContextIndexMap
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    Fin (retainedContext input selection inherited).length →
      Fin (inherited.extend selection.val.anchor).length :=
  fun index => Classical.choose (indexOf?_complete
    (retainedContext_member_full input selection inherited
      (List.get_mem _ index)))

theorem retainedContextIndexMap_spec
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input)
    (index : Fin (retainedContext input selection inherited).length) :
    (inherited.extend selection.val.anchor).get
        (retainedContextIndexMap input selection inherited index) =
      (retainedContext input selection inherited).get index := by
  unfold retainedContextIndexMap
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (retainedContext_member_full input selection inherited
      (List.get_mem _ index))))

theorem retainedContextIndexMap_extend_zero
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    extendWireRenaming (retainedContextIndexMap input selection inherited) 0 =
      retainedContextIndexMap input selection inherited := by
  funext index
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) index
  · simp only [extendWireRenaming, Fin.addCases_left]
    apply Fin.ext
    rfl
  · exact Fin.elim0 localIndex

/-- A checked selection never contains its own anchor in a selected child
subtree. -/
theorem anchor_not_selected
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val) :
    ¬ selection.val.SelectsRegion selection.val.anchor := by
  rintro ⟨root, rootMember, rootEncloses⟩
  exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
    input.property
    (selection.property.childRoots_direct root rootMember) rootEncloses

theorem keptNode_not_direct
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    {node : Fin input.nodeCount}
    (member : Concrete.Elaboration.LocalOccurrence.node node ∈
      keptOccurrences input selection) :
    node ∉ selection.val.directNodes := by
  rw [keptOccurrences, List.mem_filter] at member
  simpa [occurrenceSelected] using member.2

theorem keptChild_not_root
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    {child : Fin input.regionCount}
    (member : Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input selection) :
    child ∉ selection.val.childRoots := by
  rw [keptOccurrences, List.mem_filter] at member
  simpa [occurrenceSelected] using member.2

/-- Direct retained nodes cannot be incident to an explicit selection-owned
anchor wire. -/
theorem keptNode_noExplicitEndpoint
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {node : Fin input.val.nodeCount}
    (kept : Concrete.Elaboration.LocalOccurrence.node node ∈
      keptOccurrences input.val selection)
    {wire : Fin input.val.wireCount}
    (explicit : wire ∈ selection.val.explicitWires)
    (port : CPort) :
    ¬ input.val.EndpointOccurs wire ⟨node, port⟩ := by
  intro occurs
  have selectedNode : selection.val.SelectsNode node :=
    (selection.mem_selectedNodes node).1
      (selection.explicitWire_endpoint_selected explicit occurs)
  rcases selectedNode with direct | selectedRegion
  · exact keptNode_not_direct input.val selection kept direct
  · have nodeAtAnchor := (Concrete.Elaboration.mem_localOccurrences_node input.val
      selection.val.anchor node).1
      ((List.mem_filter.mp kept).1)
    rw [nodeAtAnchor] at selectedRegion
    exact anchor_not_selected input selection selectedRegion

/-- Every node below a retained direct child is outside the selection.  This
is the tree separation fact used by the restricted recursive compiler. -/
theorem keptChild_descendant_not_selectedNode
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {child : Fin input.val.regionCount}
    (kept : Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input.val selection)
    {node : Fin input.val.nodeCount}
    (below : input.val.Encloses child (input.val.nodes node).region) :
    ¬ selection.val.SelectsNode node := by
  intro selectedNode
  have childParent : (input.val.regions child).parent? =
      some selection.val.anchor :=
    (Concrete.Elaboration.mem_localOccurrences_child input.val
      selection.val.anchor child).1 ((List.mem_filter.mp kept).1)
  rcases selectedNode with direct | selectedRegion
  · have nodeAtAnchor := selection.property.directNodes_at_anchor node direct
    rw [nodeAtAnchor] at below
    exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
      input.property childParent below
  · obtain ⟨root, rootMember, rootBelow⟩ := selectedRegion
    have rootParent := selection.property.childRoots_direct root rootMember
    have equal :=
      Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
        input.property rootParent childParent rootBelow below
    exact keptChild_not_root input.val selection kept (equal ▸ rootMember)

/-- No occurrence recursively compiled below a retained child can mention an
explicit anchor wire. -/
theorem keptChild_descendant_noExplicitEndpoint
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {child : Fin input.val.regionCount}
    (kept : Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input.val selection)
    {node : Fin input.val.nodeCount}
    (below : input.val.Encloses child (input.val.nodes node).region)
    {wire : Fin input.val.wireCount}
    (explicit : wire ∈ selection.val.explicitWires)
    (port : CPort) :
    ¬ input.val.EndpointOccurs wire ⟨node, port⟩ := by
  intro occurs
  apply keptChild_descendant_not_selectedNode input selection kept below
  exact (selection.mem_selectedNodes node).1
    (selection.explicitWire_endpoint_selected explicit occurs)

/-- A retained lexical context embeds into the authoritative full context,
and every full-only wire belongs to the selection-owned explicit block. -/
private structure RetainedContextEmbedding
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (source target : Concrete.Elaboration.WireContext input) where
  index : Fin source.length → Fin target.length
  get : ∀ sourceIndex,
    target.get (index sourceIndex) = source.get sourceIndex
  missing_explicit : ∀ {wire : Fin input.wireCount},
    wire ∈ target → wire ∉ source → wire ∈ selection.val.explicitWires

private noncomputable def retainedContextEmbedding
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (inherited : Concrete.Elaboration.WireContext input) :
    RetainedContextEmbedding input selection
      (retainedContext input selection inherited)
      (inherited.extend selection.val.anchor) where
  index := retainedContextIndexMap input selection inherited
  get := retainedContextIndexMap_spec input selection inherited
  missing_explicit := by
    intro wire fullMember retainedMissing
    by_cases explicit : wire ∈ selection.val.explicitWires
    · exact explicit
    · exfalso
      apply retainedMissing
      rw [retainedContext]
      rcases List.mem_append.mp fullMember with inheritedMember | localMember
      · exact List.mem_append.mpr (Or.inl inheritedMember)
      · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
          ⟨localMember, by simp [explicit]⟩))

namespace RetainedContextEmbedding

/-- Extend a retained-to-full embedding through the compiler's identical
exact-local suffix at a child region. -/
private noncomputable def extend
    (embedding : RetainedContextEmbedding input selection source target)
    (region : Fin input.regionCount) :
    RetainedContextEmbedding input selection
      (source.extend region) (target.extend region) where
  index := fun index =>
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend target region).symm
      (extendWireRenaming embedding.index
        (Concrete.Elaboration.exactScopeWires input region).length
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend source region)
          index))
  get := by
    intro index
    let split := Fin.cast
      (Concrete.Elaboration.WireContext.length_extend source region) index
    have recover : Fin.cast
        (Concrete.Elaboration.WireContext.length_extend source region).symm
        split = index := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
    · simpa [Concrete.Elaboration.WireContext.extend, extendWireRenaming]
        using embedding.get outer
    · simp [Concrete.Elaboration.WireContext.extend, extendWireRenaming]
  missing_explicit := by
    intro wire targetMember sourceMissing
    rcases List.mem_append.mp targetMember with inheritedMember | localMember
    · apply embedding.missing_explicit inheritedMember
      intro sourceMember
      exact sourceMissing (List.mem_append.mpr (Or.inl sourceMember))
    · exact False.elim (sourceMissing
        (List.mem_append.mpr (Or.inr localMember)))

end RetainedContextEmbedding

private theorem directChild_encloses
    {input : Concrete.Diagram}
    {parent child : Fin input.regionCount}
    (direct : (input.regions child).parent? = some parent) :
    input.Encloses parent child := by
  have positive : 0 < input.regionCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
  refine ⟨⟨1, by omega⟩, ?_⟩
  change (match (input.regions child).parent? with
    | none => none
    | some directParent => input.climb 0 directParent) = some parent
  rw [direct]
  rfl

/-- `finishRegion` commutes with a retained-context embedding extended through
the region's exact local wires. -/
private theorem finishRegion_renameWires
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (region : Fin input.regionCount)
    (source target : Concrete.Elaboration.WireContext input)
    (embedding : RetainedContextEmbedding input selection source target)
    (items : ItemSeq (source.extend region).length rels) :
    Concrete.Elaboration.finishRegion input target region
        (items.renameWires (embedding.extend region).index) =
      (Concrete.Elaboration.finishRegion input source region items).renameWires
        embedding.index := by
  unfold Concrete.Elaboration.finishRegion
  simp only [ItemSeq.castWiresEq_eq_renameWires,
    ItemSeq.renameWires_comp, Region.renameWires]
  apply congrArg (Region.mk
    (Concrete.Elaboration.exactScopeWires input region).length)
  apply congrArg (fun wire => items.renameWires wire)
  funext index
  simp [RetainedContextEmbedding.extend]

/-- Authoritative recursive compilation is stable when explicit anchor wires
that are unused throughout the compiled subtree are removed from its inherited
lexical context. -/
private theorem compileRegion?_map_of_noExplicitEndpoint
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (region : Fin input.val.regionCount)
      (source target : Concrete.Elaboration.WireContext input.val)
      (embedding : RetainedContextEmbedding input.val selection source target)
      (binders : Concrete.Elaboration.BinderContext input.val rels),
      (target.extend region).Exact region →
      (∀ (node : Fin input.val.nodeCount),
        input.val.Encloses region (input.val.nodes node).region →
        ∀ {wire : Fin input.val.wireCount},
          wire ∈ selection.val.explicitWires →
          ∀ port : CPort, ¬ input.val.EndpointOccurs wire ⟨node, port⟩) →
      Concrete.Elaboration.compileRegion? input.val fuel region target binders =
        (Concrete.Elaboration.compileRegion? input.val fuel region source
          binders).map (Region.renameWires embedding.index) := by
  intro rels fuel
  induction fuel generalizing rels with
  | zero =>
      intro region source target embedding binders targetExact noExplicit
      rfl
  | succ fuel ih =>
      intro region source target embedding binders targetExact noExplicit
      simp only [Concrete.Elaboration.compileRegion?]
      let sourceExtended := source.extend region
      let targetExtended := target.extend region
      let extendedEmbedding := embedding.extend region
      have occurrenceMap : ∀ occurrence,
          occurrence ∈ Concrete.Elaboration.localOccurrences input.val region →
          Concrete.Elaboration.compileOccurrenceWith? input.val
              (Concrete.Elaboration.compileRegion? input.val fuel)
              targetExtended binders occurrence =
            (Concrete.Elaboration.compileOccurrenceWith? input.val
              (Concrete.Elaboration.compileRegion? input.val fuel)
              sourceExtended binders occurrence).map
                (Item.renameWires extendedEmbedding.index) := by
        intro occurrence occurrenceMember
        cases occurrence with
        | node node =>
            simp only [Concrete.Elaboration.compileOccurrenceWith?]
            have nodeMap := Concrete.Elaboration.compileNode?_map sourceExtended
              targetExtended binders binders node node id id
              extendedEmbedding.index (fun relation => relation)
              (by cases input.val.nodes node <;> rfl)
              (by
                intro port
                apply Concrete.Elaboration.resolvePort?_map_of_embedding
                  sourceExtended targetExtended node node id
                  Function.injective_id extendedEmbedding.index
                  targetExact.nodup extendedEmbedding.get
                · intro wire occurs
                  exact occurs
                · intro wire occurs
                  exact ⟨wire, rfl, occurs⟩
                · intro wire occurs targetMember
                  by_cases sourceMember : wire ∈ sourceExtended
                  · exact sourceMember
                  · have explicit := extendedEmbedding.missing_explicit
                      targetMember sourceMember
                    have nodeRegion :=
                      (Concrete.Elaboration.mem_localOccurrences_node input.val
                        region node).1 occurrenceMember
                    exact False.elim (noExplicit node
                      (nodeRegion ▸ Diagram.Encloses.refl input.val region)
                      explicit port occurs)
                · exact input.property.wire_endpoints_are_disjoint)
              (by
                intro nodeRegion binder nodeEq
                cases binderResult : binders binder <;> simp [binderResult])
            simpa only [Item.renameRelations_id] using nodeMap
        | child child =>
            have direct :=
              (Concrete.Elaboration.mem_localOccurrences_child input.val
                region child).1 occurrenceMember
            have childExact := targetExact.extend_child input.property direct
            have childNoExplicit : ∀ (node : Fin input.val.nodeCount),
                input.val.Encloses child (input.val.nodes node).region →
                ∀ {wire : Fin input.val.wireCount},
                  wire ∈ selection.val.explicitWires →
                  ∀ port : CPort,
                    ¬ input.val.EndpointOccurs wire ⟨node, port⟩ := by
              intro node below wire explicit port
              exact noExplicit node
                (Concrete.Elaboration.checked_encloses_trans input.property
                  (directChild_encloses direct) below)
                explicit port
            cases childKind : input.val.regions child with
            | sheet =>
                simp [Concrete.Elaboration.compileOccurrenceWith?, childKind]
            | cut parent =>
                simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
                rw [ih child sourceExtended targetExtended extendedEmbedding
                  binders childExact childNoExplicit]
                cases Concrete.Elaboration.compileRegion? input.val fuel child
                    sourceExtended binders <;> rfl
            | bubble parent arity =>
                simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
                rw [ih child sourceExtended targetExtended extendedEmbedding
                  (binders.push child arity) childExact childNoExplicit]
                cases Concrete.Elaboration.compileRegion? input.val fuel child
                    sourceExtended (binders.push child arity) <;> rfl
      have sequenceMap := Concrete.Elaboration.compileOccurrencesWith?_map
        (Concrete.Elaboration.compileRegion? input.val fuel)
        (Concrete.Elaboration.compileRegion? input.val fuel)
        sourceExtended targetExtended binders binders id
        extendedEmbedding.index
        (Concrete.Elaboration.localOccurrences input.val region) occurrenceMap
      have sequenceMap' :
          Concrete.Elaboration.compileOccurrencesWith? input.val
              (Concrete.Elaboration.compileRegion? input.val fuel)
              targetExtended binders
              (Concrete.Elaboration.localOccurrences input.val region) =
            (Concrete.Elaboration.compileOccurrencesWith? input.val
              (Concrete.Elaboration.compileRegion? input.val fuel)
              sourceExtended binders
              (Concrete.Elaboration.localOccurrences input.val region)).map
                (ItemSeq.renameWires extendedEmbedding.index) := by
        simpa only [List.map_id_fun] using sequenceMap
      cases sourceItemsResult :
          Concrete.Elaboration.compileOccurrencesWith? input.val
            (Concrete.Elaboration.compileRegion? input.val fuel)
            sourceExtended binders
            (Concrete.Elaboration.localOccurrences input.val region) with
      | none =>
          rw [sourceItemsResult] at sequenceMap'
          simp only [Option.map_none] at sequenceMap'
          rw [sequenceMap']
          rfl
      | some items =>
          rw [sourceItemsResult] at sequenceMap'
          simp only [Option.map_some] at sequenceMap'
          rw [sequenceMap']
          exact congrArg some
            (finishRegion_renameWires input.val selection region source target
              embedding items)

/-- Kept occurrences compile in the retained anchor context, and the
authoritative full-context result is exactly their retained result renamed
through the canonical context inclusion. -/
structure KeptOccurrencesRestriction
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels) where
  items : ItemSeq
    (retainedContext input.val selection anchorLeaf.inheritedWires).length rels
  compiled : Concrete.Elaboration.compileOccurrencesWith? input.val
    (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
    (retainedContext input.val selection anchorLeaf.inheritedWires)
    anchorLeaf.binders (keptOccurrences input.val selection) = some items
  iso : ItemSeqIso (FiniteEquiv.refl _) rels keptItems
    (items.renameWires
      (retainedContextIndexMap input.val selection anchorLeaf.inheritedWires))

noncomputable def compileKeptOccurrences_restrict
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels}
    (keptCompiled :
      Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        anchorLeaf.binders (keptOccurrences input.val selection) =
          some keptItems) :
    KeptOccurrencesRestriction input selection anchorLeaf keptItems := by
  let sourceContext := retainedContext input.val selection
    anchorLeaf.inheritedWires
  let targetContext :=
    anchorLeaf.inheritedWires.extend selection.val.anchor
  let embedding := retainedContextEmbedding input.val selection
    anchorLeaf.inheritedWires
  have occurrenceMap : ∀ occurrence,
      occurrence ∈ keptOccurrences input.val selection →
      Concrete.Elaboration.compileOccurrenceWith? input.val
          (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
          targetContext anchorLeaf.binders occurrence =
        (Concrete.Elaboration.compileOccurrenceWith? input.val
          (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
          sourceContext anchorLeaf.binders occurrence).map
            (Item.renameWires embedding.index) := by
    intro occurrence kept
    cases occurrence with
    | node node =>
        simp only [Concrete.Elaboration.compileOccurrenceWith?]
        have nodeMap := Concrete.Elaboration.compileNode?_map sourceContext
          targetContext anchorLeaf.binders anchorLeaf.binders node node id id
          embedding.index (fun relation => relation)
          (by cases input.val.nodes node <;> rfl)
          (by
            intro port
            apply Concrete.Elaboration.resolvePort?_map_of_embedding
              sourceContext targetContext node node id Function.injective_id
              embedding.index anchorLeaf.wiresExact.nodup embedding.get
            · intro wire occurs
              exact occurs
            · intro wire occurs
              exact ⟨wire, rfl, occurs⟩
            · intro wire occurs targetMember
              by_cases sourceMember : wire ∈ sourceContext
              · exact sourceMember
              · have explicit := embedding.missing_explicit
                  targetMember sourceMember
                exact False.elim
                  (keptNode_noExplicitEndpoint input selection kept explicit
                    port occurs)
            · exact input.property.wire_endpoints_are_disjoint)
          (by
            intro nodeRegion binder nodeEq
            cases binderResult : anchorLeaf.binders binder <;>
              simp [binderResult])
        simpa only [Item.renameRelations_id] using nodeMap
    | child child =>
        have localMember :
            Concrete.Elaboration.LocalOccurrence.child child ∈
              Concrete.Elaboration.localOccurrences input.val
                selection.val.anchor :=
          (List.mem_filter.mp kept).1
        have direct :=
          (Concrete.Elaboration.mem_localOccurrences_child input.val
            selection.val.anchor child).1 localMember
        have childExact := anchorLeaf.wiresExact.extend_child
          input.property direct
        have childNoExplicit : ∀ (node : Fin input.val.nodeCount),
            input.val.Encloses child (input.val.nodes node).region →
            ∀ {wire : Fin input.val.wireCount},
              wire ∈ selection.val.explicitWires →
              ∀ port : CPort,
                ¬ input.val.EndpointOccurs wire ⟨node, port⟩ := by
          intro node below wire explicit port
          exact keptChild_descendant_noExplicitEndpoint input selection kept
            below explicit port
        cases childKind : input.val.regions child with
        | sheet =>
            simp [Concrete.Elaboration.compileOccurrenceWith?, childKind]
        | cut parent =>
            simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
            rw [compileRegion?_map_of_noExplicitEndpoint input selection
              anchorLeaf.fuel child sourceContext targetContext embedding
              anchorLeaf.binders childExact childNoExplicit]
            cases Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel
                child sourceContext anchorLeaf.binders <;> rfl
        | bubble parent arity =>
            simp only [Concrete.Elaboration.compileOccurrenceWith?, childKind]
            rw [compileRegion?_map_of_noExplicitEndpoint input selection
              anchorLeaf.fuel child sourceContext targetContext embedding
              (anchorLeaf.binders.push child arity) childExact childNoExplicit]
            cases Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel
                child sourceContext
                (anchorLeaf.binders.push child arity) <;> rfl
  have sequenceMap := Concrete.Elaboration.compileOccurrencesWith?_map
    (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
    (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
    sourceContext targetContext anchorLeaf.binders anchorLeaf.binders id
    embedding.index (keptOccurrences input.val selection) occurrenceMap
  have sequenceMap' :
      Concrete.Elaboration.compileOccurrencesWith? input.val
          (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
          targetContext anchorLeaf.binders
          (keptOccurrences input.val selection) =
        (Concrete.Elaboration.compileOccurrencesWith? input.val
          (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
          sourceContext anchorLeaf.binders
          (keptOccurrences input.val selection)).map
            (ItemSeq.renameWires embedding.index) := by
    simpa only [List.map_id_fun] using sequenceMap
  cases restrictedResult :
      Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
        sourceContext anchorLeaf.binders
        (keptOccurrences input.val selection) with
  | none =>
      rw [keptCompiled, restrictedResult] at sequenceMap'
      simp at sequenceMap'
  | some restrictedItems =>
      rw [keptCompiled, restrictedResult] at sequenceMap'
      simp only [Option.map_some] at sequenceMap'
      refine ⟨restrictedItems, ?_, ?_⟩
      · simpa only [sourceContext] using restrictedResult
      · have renamed : keptItems = restrictedItems.renameWires
            (retainedContextIndexMap input.val selection
              anchorLeaf.inheritedWires) := by
          exact Option.some.inj (by
            simpa only [embedding, retainedContextEmbedding] using sequenceMap')
        rw [renamed]
        exact ItemSeqIso.refl _

/-- Renaming wires preserves and reflects an already supplied intrinsic path.
This transports proof data only; it performs no path search. -/
private noncomputable def Region.ContextPath.unrenameWires
    (region : Region sourceWires rels)
    (wire : Fin sourceWires → Fin targetWires)
    {path : List Nat}
    (witness : Region.ContextPath (region.renameWires wire) path) :
    Region.ContextPath region path := by
  induction path generalizing sourceWires targetWires rels with
  | nil =>
      exact .here region
  | cons index rest induction =>
      cases region with
      | mk localWires items =>
          let extended := extendWireRenaming wire localWires
          change Region.ContextPath
            (Region.mk localWires (items.renameWires extended))
            (index :: rest) at witness
          cases witness with
          | @cut _ _ _ _ _ _ targetFocus targetAt targetChild targetIsCut
              targetNested =>
              let sourceIndex : Fin items.length := ⟨index, by
                simpa only [ItemSeq.renameWires_length] using
                  ItemSeq.focusAt?_index_lt _ _ targetFocus targetAt⟩
              let sourceResult := items.focusAt sourceIndex
              let sourceFocus := sourceResult.focus
              have sourceAt := sourceResult.atIndex
              have sourceItem := sourceResult.item_eq
              have targetItem : targetFocus.item =
                  sourceFocus.item.renameWires extended := by
                have targetGet := ItemSeq.focusAt?_item _ _ targetFocus targetAt
                have positionEq :
                    items.renameWiresPositionEquiv extended sourceIndex =
                      ⟨index, by
                        simpa only [ItemSeq.renameWires_length] using
                          ItemSeq.focusAt?_index_lt _ _ targetFocus targetAt⟩ := by
                  apply Fin.ext
                  rfl
                rw [← positionEq, ItemSeq.get_renameWires] at targetGet
                exact targetGet.trans (congrArg (Item.renameWires extended)
                  sourceItem.symm)
              cases sourceKind : sourceFocus.item with
              | atom relation arguments =>
                  rw [sourceKind, Item.renameWires] at targetItem
                  exact False.elim (by
                    rw [targetIsCut] at targetItem
                    contradiction)
              | identity arity arguments =>
                  rw [sourceKind, Item.renameWires] at targetItem
                  exact False.elim (by
                    rw [targetIsCut] at targetItem
                    contradiction)
              | cut sourceChild =>
                  have childEq : targetChild =
                      sourceChild.renameWires extended := by
                    rw [sourceKind, Item.renameWires, targetIsCut] at targetItem
                    exact Item.cut.inj targetItem
                  subst targetChild
                  exact .cut sourceFocus sourceAt sourceKind
                    (induction sourceChild extended targetNested)
              | bubble arity sourceChild =>
                  rw [sourceKind, Item.renameWires] at targetItem
                  exact False.elim (by
                    rw [targetIsCut] at targetItem
                    contradiction)
          | @bubble _ _ _ _ _ _ _ targetFocus targetAt targetChild
              targetIsBubble targetNested =>
              let sourceIndex : Fin items.length := ⟨index, by
                simpa only [ItemSeq.renameWires_length] using
                  ItemSeq.focusAt?_index_lt _ _ targetFocus targetAt⟩
              let sourceResult := items.focusAt sourceIndex
              let sourceFocus := sourceResult.focus
              have sourceAt := sourceResult.atIndex
              have sourceItem := sourceResult.item_eq
              have targetItem : targetFocus.item =
                  sourceFocus.item.renameWires extended := by
                have targetGet := ItemSeq.focusAt?_item _ _ targetFocus targetAt
                have positionEq :
                    items.renameWiresPositionEquiv extended sourceIndex =
                      ⟨index, by
                        simpa only [ItemSeq.renameWires_length] using
                          ItemSeq.focusAt?_index_lt _ _ targetFocus targetAt⟩ := by
                  apply Fin.ext
                  rfl
                rw [← positionEq, ItemSeq.get_renameWires] at targetGet
                exact targetGet.trans (congrArg (Item.renameWires extended)
                  sourceItem.symm)
              cases sourceKind : sourceFocus.item with
              | atom relation arguments =>
                  rw [sourceKind, Item.renameWires] at targetItem
                  exact False.elim (by
                    rw [targetIsBubble] at targetItem
                    contradiction)
              | identity arity arguments =>
                  rw [sourceKind, Item.renameWires] at targetItem
                  exact False.elim (by
                    rw [targetIsBubble] at targetItem
                    contradiction)
              | cut sourceChild =>
                  rw [sourceKind, Item.renameWires] at targetItem
                  exact False.elim (by
                    rw [targetIsBubble] at targetItem
                    contradiction)
              | bubble sourceArity sourceChild =>
                  have itemEq : Item.bubble sourceArity
                        (sourceChild.renameWires extended) =
                      Item.bubble _ targetChild := by
                    rw [sourceKind, Item.renameWires, targetIsBubble] at targetItem
                    exact targetItem.symm
                  cases itemEq
                  exact .bubble sourceFocus sourceAt sourceKind
                    (induction sourceChild extended targetNested)

/-- Exact proof-relevant transport of the supplied retained route into the
single retained anchor context used by the source factor. -/
structure SourceRouteAlignment
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (anchorLocal : Nat) where
  keptItems : ItemSeq
    (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels
  retainedItems : ItemSeq
    (retainedContext input.val selection anchorLeaf.inheritedWires).length rels
  retainedLength :
    (retainedContext input.val selection anchorLeaf.inheritedWires).length =
      anchorLeaf.inheritedWires.length + anchorLocal
  keptRoute : KeptRouteResult input selection anchorLeaf keptItems route
  retainedIso : RegionIso
    (FiniteEquiv.refl
      (Fin (anchorLeaf.inheritedWires.extend
        selection.val.anchor).length)) rels
    (Region.mk 0 keptItems)
    (Region.mk 0
      (retainedItems.renameWires
        (retainedContextIndexMap input.val selection
          anchorLeaf.inheritedWires)))

noncomputable def SourceRouteAlignment.alignment
    (result : SourceRouteAlignment input selection anchorLeaf route
      anchorLocal) :
    result.retainedIso.ContextPathAlignment result.keptRoute.witness :=
  result.retainedIso.alignContextPath result.keptRoute.witness

noncomputable def SourceRouteAlignment.retainedWitness
    (result : SourceRouteAlignment input selection anchorLeaf route
      anchorLocal) :
    Region.ContextPath (Region.mk 0 result.retainedItems)
      result.alignment.targetPath := by
  have renamed : Region.ContextPath
      ((Region.mk 0 result.retainedItems).renameWires
        (retainedContextIndexMap input.val selection
          anchorLeaf.inheritedWires)) result.alignment.targetPath := by
    simpa only [Region.renameWires,
      retainedContextIndexMap_extend_zero] using
        result.alignment.targetWitness
  exact Region.ContextPath.unrenameWires
    (Region.mk 0 result.retainedItems)
    (retainedContextIndexMap input.val selection anchorLeaf.inheritedWires)
    renamed

/-- The retained-route witness in the explicit inherited-plus-anchor-local
carrier used by `SourceFactorResult`. -/
noncomputable def SourceRouteAlignment.factoredWitness
    (result : SourceRouteAlignment input selection anchorLeaf route
      anchorLocal) :
    Region.ContextPath
      ((Region.mk 0 result.retainedItems).castWiresEq
        result.retainedLength)
      result.alignment.targetPath :=
  result.retainedWitness.castWiresEq result.retainedLength

noncomputable def SourceRouteAlignment.descendant
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (anchorLocal : Nat)
    (result : SourceRouteAlignment input selection anchorLeaf route
      anchorLocal) :
    DiagramContext
      (anchorLeaf.inheritedWires.length + anchorLocal)
      result.factoredWitness.toFocus.holeWires rels
      result.factoredWitness.toFocus.holeRels :=
  result.factoredWitness.toFocus.context

noncomputable def SourceRouteAlignment.remainder
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (anchorLocal : Nat)
    (result : SourceRouteAlignment input selection anchorLeaf route
      anchorLocal) :
    Region result.factoredWitness.toFocus.holeWires
      result.factoredWitness.toFocus.holeRels :=
  result.factoredWitness.toFocus.body

noncomputable def sourceFactorTargetRegion
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (anchorLocal : Nat)
    (selected : Region
      (anchorLeaf.inheritedWires.length + anchorLocal) rels)
    (routeAlignment : SourceRouteAlignment input selection anchorLeaf route
      anchorLocal) :
    Region anchorLeaf.inheritedWires.length rels :=
  Region.adjoinAt anchorLocal
    (ItemSeq.nil : ItemSeq
      (anchorLeaf.inheritedWires.length + anchorLocal) rels)
    ((Region.conjoin (rels := rels) selected
      (@DiagramContext.fill
        (anchorLeaf.inheritedWires.length + anchorLocal)
        routeAlignment.factoredWitness.toFocus.holeWires rels
        routeAlignment.factoredWitness.toFocus.holeRels
        routeAlignment.factoredWitness.toFocus.context
        routeAlignment.factoredWitness.toFocus.body)) :
      Region (anchorLeaf.inheritedWires.length + anchorLocal) rels)

/-- The selected fragment body compiled in the anchor's authoritative wire and
relation contexts, before the anchor-local carrier is factored. -/
noncomputable def extractedSelectedRegion
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {outer : Nat} {rels fragmentRels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (fragmentItems : ItemSeq fragmentContext.length fragmentRels) :
    Region anchorLeaf.inheritedWires.length rels :=
  let binderWitness :=
    IterationExtraction.ExtractionBinderWitness.terminal input selection layout
      fragmentBinders fragmentEnumeration anchorLeaf.binders
      anchorLeaf.bindersCover
  let preparedItems :=
    (fragmentItems.renameRelations binderWitness.relationMap).renameWires
      (IterationExtraction.extractionContextIndexMap input selection layout
        fragmentContext
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        fragmentExact anchorLeaf.wiresExact)
  Region.mk
    (Concrete.Elaboration.exactScopeWires input.val
      selection.val.anchor).length
    (preparedItems.castWiresEq
      (Concrete.Elaboration.WireContext.length_extend
        anchorLeaf.inheritedWires selection.val.anchor))

/-- Base-ready source factorization at the compiled selection anchor.  The
selected explicit wires are local to `selected`; the retained anchor wires and
the retained descendant context are each bound exactly once outside it. -/
structure SourceFactorResult
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {outer : Nat} {rels fragmentRels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (fragmentItems : ItemSeq fragmentContext.length fragmentRels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path) where
  anchorLocal : Nat
  selected : Region (anchorLeaf.inheritedWires.length + anchorLocal) rels
  route_alignment : SourceRouteAlignment input selection anchorLeaf route
    anchorLocal
  selected_local : ∃ selectedItems : ItemSeq
      ((anchorLeaf.inheritedWires.length + anchorLocal) +
        selection.val.explicitWires.length) rels,
    selected = Region.mk selection.val.explicitWires.length selectedItems
  source_iso : RegionIso
    (FiniteEquiv.finCast anchorLeaf.inheritedLength.symm) rels anchorBody
    (sourceFactorTargetRegion (rels := rels) input selection anchorLeaf route
      anchorLocal selected route_alignment)
  material_iso : RegionIso
    (FiniteEquiv.refl (Fin anchorLeaf.inheritedWires.length)) rels
    (extractedSelectedRegion input selection layout anchorLeaf fragmentContext
      fragmentBinders fragmentEnumeration fragmentExact fragmentItems)
    (Region.adjoinAt anchorLocal .nil selected)

noncomputable def SourceFactorResult.descendant
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {outer : Nat} {rels fragmentRels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (fragmentItems : ItemSeq fragmentContext.length fragmentRels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (result : SourceFactorResult input selection layout anchorLeaf
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route) :
    DiagramContext
      (anchorLeaf.inheritedWires.length + result.anchorLocal)
      result.route_alignment.factoredWitness.toFocus.holeWires rels
      result.route_alignment.factoredWitness.toFocus.holeRels :=
  result.route_alignment.descendant

noncomputable def SourceFactorResult.remainder
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {outer : Nat} {rels fragmentRels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (fragmentItems : ItemSeq fragmentContext.length fragmentRels)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (result : SourceFactorResult input selection layout anchorLeaf
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route) :
    Region result.route_alignment.factoredWitness.toFocus.holeWires
      result.route_alignment.factoredWitness.toFocus.holeRels :=
  result.route_alignment.remainder

/-- The result's descendant and remainder rebuild the exact routed retained
focus, with no independently indexed context or body. -/
theorem SourceFactorResult.routed_focus_eq
    (result : SourceFactorResult input selection layout anchorLeaf
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route) :
    result.descendant.fill result.remainder =
      (Region.mk 0 result.route_alignment.retainedItems).castWiresEq
        result.route_alignment.retainedLength :=
  by
    simpa only [SourceFactorResult.descendant,
      SourceFactorResult.remainder, SourceRouteAlignment.descendant,
      SourceRouteAlignment.remainder] using
        result.route_alignment.factoredWitness.toFocus.rebuild

noncomputable def sourceFactor_complete
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {outer : Nat} {rels fragmentRels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (fragmentFuel : Nat)
    (fragmentContext : Concrete.Elaboration.WireContext
      (input.val.extractDiagramRaw selection layout))
    (fragmentBinders : Concrete.Elaboration.BinderContext
      (input.val.extractDiagramRaw selection layout) fragmentRels)
    (fragmentEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (input.val.extractDiagramRaw selection layout) fragmentBinders
      layout.bodyContainer)
    (fragmentExact : fragmentContext.Exact layout.bodyContainer)
    (fragmentItems : ItemSeq fragmentContext.length fragmentRels)
    (fragmentCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (input.val.extractDiagramRaw selection layout)
      (Concrete.Elaboration.compileRegion?
        (input.val.extractDiagramRaw selection layout) fragmentFuel)
      fragmentContext fragmentBinders
      (Concrete.Elaboration.localOccurrences
        (input.val.extractDiagramRaw selection layout) layout.bodyContainer) =
      some fragmentItems)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    SourceFactorResult input selection layout anchorLeaf
      fragmentContext fragmentBinders fragmentEnumeration fragmentExact
      fragmentItems route := by
  obtain ⟨selectedItems, keptItems, selectedCompiled, keptCompiled,
      partitionIso⟩ := partition_complete input selection anchorLeaf
  obtain ⟨restrictedItems, restrictedCompiled, keptIso⟩ :=
    compileKeptOccurrences_restrict input selection anchorLeaf keptCompiled
  let keptRoute := keptRoute_complete input selection anchorLeaf
    keptItems keptCompiled route targetNotSelected
  let keptRegionIso : RegionIso
      (FiniteEquiv.refl
        (Fin (anchorLeaf.inheritedWires.extend
          selection.val.anchor).length)) rels
      (Region.mk 0 keptItems)
      (Region.mk 0
        (restrictedItems.renameWires
          (retainedContextIndexMap input.val selection
            anchorLeaf.inheritedWires))) :=
    by
      apply RegionIso.mk (FiniteEquiv.refl (Fin 0))
      have extendedRefl :
          extendWireEquiv
              (FiniteEquiv.refl
                (Fin (anchorLeaf.inheritedWires.extend
                  selection.val.anchor).length))
              (FiniteEquiv.refl (Fin 0)) =
            FiniteEquiv.refl
              (Fin ((anchorLeaf.inheritedWires.extend
                selection.val.anchor).length + 0)) := by
        apply FiniteEquiv.ext
        intro wire
        refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) wire
        · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
        · exact Fin.elim0 localIndex
      rw [extendedRefl]
      simpa using keptIso
  let routeAlignment : SourceRouteAlignment input selection anchorLeaf route
      (retainedAnchorWires input.val selection).length := {
    keptItems := keptItems
    retainedItems := restrictedItems
    retainedLength :=
      retainedContext_length input.val selection anchorLeaf.inheritedWires
    keptRoute := keptRoute
    retainedIso := keptRegionIso
  }
  let binderWitness :=
    IterationExtraction.ExtractionBinderWitness.terminal input selection layout
      fragmentBinders fragmentEnumeration anchorLeaf.binders
      anchorLeaf.bindersCover
  let preparedItems :=
    (fragmentItems.renameRelations binderWitness.relationMap).renameWires
      (IterationExtraction.extractionContextIndexMap input selection layout
        fragmentContext
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        fragmentExact anchorLeaf.wiresExact)
  let localEquiv := anchorLocalEquiv input.val selection
  let wireEquiv := anchorWireEquiv input.val selection
    anchorLeaf.inheritedWires
  let retainedLength := routeAlignment.retainedLength
  let factoredWitness := routeAlignment.factoredWitness
  let factorRetained : Fin
      (retainedContext input.val selection anchorLeaf.inheritedWires).length →
      Fin (anchorLeaf.inheritedWires.length +
        ((retainedAnchorWires input.val selection).length +
          selection.val.explicitWires.length)) := fun index =>
    Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
      (retainedAnchorWires input.val selection).length
      selection.val.explicitWires.length)
      (Fin.castAdd selection.val.explicitWires.length
        (Fin.cast retainedLength index))
  have retainedFactor :
      wireEquiv.symm.toFun ∘
          Fin.cast (Concrete.Elaboration.WireContext.length_extend
            anchorLeaf.inheritedWires selection.val.anchor) ∘
          retainedContextIndexMap input.val selection
            anchorLeaf.inheritedWires =
        factorRetained := by
    funext index
    apply wireEquiv.injective
    change wireEquiv
        (wireEquiv.symm
          (Fin.cast
            (Concrete.Elaboration.WireContext.length_extend
              anchorLeaf.inheritedWires selection.val.anchor)
            (retainedContextIndexMap input.val selection
              anchorLeaf.inheritedWires index))) =
      wireEquiv (factorRetained index)
    have cancel := wireEquiv.right_inv
      (Fin.cast
        (Concrete.Elaboration.WireContext.length_extend
          anchorLeaf.inheritedWires selection.val.anchor)
        (retainedContextIndexMap input.val selection
          anchorLeaf.inheritedWires index))
    change wireEquiv (wireEquiv.symm _) = _ at cancel
    rw [cancel]
    let lengthEq := Concrete.Elaboration.WireContext.length_extend
      anchorLeaf.inheritedWires selection.val.anchor
    let leftFull := Fin.cast lengthEq.symm
      (Fin.cast lengthEq
        (retainedContextIndexMap input.val selection
          anchorLeaf.inheritedWires index))
    let rightFull := Fin.cast lengthEq.symm
      (wireEquiv (factorRetained index))
    have factorGet :
        (anchorLeaf.inheritedWires.extend selection.val.anchor).get rightFull =
          (retainedContext input.val selection
            anchorLeaf.inheritedWires).get index := by
      let split := Fin.cast retainedLength index
      refine Fin.addCases (motive := fun splitIndex => split = splitIndex →
          (anchorLeaf.inheritedWires.extend selection.val.anchor).get
              rightFull =
            (retainedContext input.val selection
              anchorLeaf.inheritedWires).get index)
        (fun inherited splitEq => ?_)
        (fun retained splitEq => ?_) split rfl
      · have indexEq : index = Fin.cast retainedLength.symm
            (Fin.castAdd
              (retainedAnchorWires input.val selection).length inherited) := by
          apply Fin.ext
          simpa [split] using congrArg Fin.val splitEq
        subst index
        have factorEq : wireEquiv
              (factorRetained (Fin.cast retainedLength.symm
                (Fin.castAdd
                  (retainedAnchorWires input.val selection).length
                  inherited))) =
            Fin.castAdd
              (Concrete.Elaboration.exactScopeWires input.val
                selection.val.anchor).length inherited := by
          have inputEq : factorRetained
                (Fin.cast retainedLength.symm
                  (Fin.castAdd
                    (retainedAnchorWires input.val selection).length
                    inherited)) =
              Fin.castAdd
                ((retainedAnchorWires input.val selection).length +
                  selection.val.explicitWires.length) inherited := by
            apply Fin.ext
            rfl
          rw [inputEq]
          simp [wireEquiv, anchorWireEquiv]
        simp only [rightFull]
        rw [factorEq]
        simp only [retainedContext,
          Concrete.Elaboration.WireContext.extend,
          Concrete.Elaboration.get_append_castAdd]
      · have indexEq : index = Fin.cast retainedLength.symm
            (Fin.natAdd anchorLeaf.inheritedWires.length retained) := by
          apply Fin.ext
          simpa [split] using congrArg Fin.val splitEq
        subst index
        have factorEq : wireEquiv
              (factorRetained (Fin.cast retainedLength.symm
                (Fin.natAdd anchorLeaf.inheritedWires.length retained))) =
            Fin.natAdd anchorLeaf.inheritedWires.length
              (localEquiv (Fin.castAdd
                selection.val.explicitWires.length retained)) := by
          have inputEq : factorRetained
                (Fin.cast retainedLength.symm
                  (Fin.natAdd anchorLeaf.inheritedWires.length retained)) =
              Fin.natAdd anchorLeaf.inheritedWires.length
                (Fin.castAdd selection.val.explicitWires.length retained) := by
            apply Fin.ext
            rfl
          rw [inputEq]
          simp [wireEquiv, anchorWireEquiv, localEquiv]
        simp only [rightFull]
        rw [factorEq]
        simp only [retainedContext,
          Concrete.Elaboration.WireContext.extend,
          Concrete.Elaboration.get_append_natAdd]
        change (Concrete.Elaboration.exactScopeWires input.val
            selection.val.anchor).get
              (anchorLocalEquiv input.val selection
                (Fin.castAdd selection.val.explicitWires.length retained)) =
          (retainedAnchorWires input.val selection).get retained
        rw [anchorLocalEquiv_spec]
        simp only [Concrete.Elaboration.get_append_castAdd]
    have leftGet :
        (anchorLeaf.inheritedWires.extend selection.val.anchor).get leftFull =
          (retainedContext input.val selection
            anchorLeaf.inheritedWires).get index := by
      simpa only [leftFull, lengthEq, Fin.cast_cast] using
        retainedContextIndexMap_spec input.val selection
          anchorLeaf.inheritedWires index
    have fullIndexEq : leftFull = rightFull := by
      apply Fin.ext
      exact (List.getElem_inj anchorLeaf.wiresExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using leftGet.trans factorGet.symm)
    apply Fin.ext
    simpa only [leftFull, rightFull] using congrArg Fin.val fullIndexEq
  let factoredItems : ItemSeq
      ((anchorLeaf.inheritedWires.length +
        (retainedAnchorWires input.val selection).length) +
        selection.val.explicitWires.length) rels :=
    ((preparedItems.castWiresEq
      (Concrete.Elaboration.WireContext.length_extend
        anchorLeaf.inheritedWires selection.val.anchor)).renameWires
          wireEquiv.symm).castWiresEq
      (Nat.add_assoc anchorLeaf.inheritedWires.length
        (retainedAnchorWires input.val selection).length
        selection.val.explicitWires.length).symm
  let selected : Region
      (anchorLeaf.inheritedWires.length +
        (retainedAnchorWires input.val selection).length) rels :=
    Region.mk selection.val.explicitWires.length factoredItems
  have extractionIso :=
    IterationExtraction.extractionCompileSelectedItems_iso input selection
      layout fragmentFuel anchorLeaf.fuel fragmentContext
      (anchorLeaf.inheritedWires.extend selection.val.anchor) fragmentBinders
      anchorLeaf.binders fragmentEnumeration anchorLeaf.binderEnumeration
      anchorLeaf.bindersCover fragmentExact anchorLeaf.wiresExact
      fragmentItems selectedItems fragmentCompiled selectedCompiled
  have materialIso : RegionIso
      (FiniteEquiv.refl (Fin anchorLeaf.inheritedWires.length)) rels
      (extractedSelectedRegion input selection layout anchorLeaf fragmentContext
        fragmentBinders fragmentEnumeration fragmentExact fragmentItems)
      (Region.adjoinAt (retainedAnchorWires input.val selection).length .nil
        selected) := by
    have targetEq :
        Region.adjoinAt (retainedAnchorWires input.val selection).length .nil
            selected =
          Region.mk
            ((retainedAnchorWires input.val selection).length +
              selection.val.explicitWires.length)
            ((preparedItems.castWiresEq
              (Concrete.Elaboration.WireContext.length_extend
                anchorLeaf.inheritedWires selection.val.anchor)).renameWires
                  wireEquiv.symm) := by
      simp only [selected, factoredItems, Region.adjoinAt,
        ItemSeq.castWiresEq_eq_renameWires, ItemSeq.renameWires,
        ItemSeq.nil_append]
      apply congrArg (Region.mk
        ((retainedAnchorWires input.val selection).length +
          selection.val.explicitWires.length))
      rw [ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
      rw [ItemSeq.renameWires_comp]
      have adjoinCancel :
          Region.adjoinMaterialWire anchorLeaf.inheritedWires.length
              (retainedAnchorWires input.val selection).length
              selection.val.explicitWires.length ∘
            Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
              (retainedAnchorWires input.val selection).length
              selection.val.explicitWires.length).symm = id := by
        funext index
        apply Fin.ext
        rfl
      rw [adjoinCancel, ItemSeq.renameWires_id]
    rw [targetEq]
    simp only [extractedSelectedRegion, preparedItems, binderWitness]
    apply RegionIso.mk localEquiv.symm
    have renamed := ItemSeqIso.renameWiresEquiv
      (preparedItems.castWiresEq
        (Concrete.Elaboration.WireContext.length_extend
          anchorLeaf.inheritedWires selection.val.anchor)) wireEquiv.symm
    have completeEq :
        extendWireEquiv
            (FiniteEquiv.refl (Fin anchorLeaf.inheritedWires.length))
            localEquiv.symm = wireEquiv.symm := by
      dsimp only [wireEquiv, anchorWireEquiv]
      rw [extendWireEquiv_symm]
      apply FiniteEquiv.ext
      intro index
      rfl
    rw [completeEq]
    exact renamed
  let fullLength := Concrete.Elaboration.WireContext.length_extend
    anchorLeaf.inheritedWires selection.val.anchor
  have extractionCast : ItemSeqIso
      (FiniteEquiv.refl (Fin
        (anchorLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires input.val
            selection.val.anchor).length))) rels
      (selectedItems.renameWires (Fin.cast fullLength))
      (preparedItems.renameWires (Fin.cast fullLength)) := by
    apply ItemSeqIso.renameWires_commuting extractionIso
      (Fin.cast fullLength) (Fin.cast fullLength)
      (FiniteEquiv.refl _)
    funext index
    rfl
  have selectedFactorIso : ItemSeqIso wireEquiv.symm rels
      (selectedItems.renameWires (Fin.cast fullLength))
      ((preparedItems.renameWires (Fin.cast fullLength)).renameWires
        wireEquiv.symm) := by
    have renamed := ItemSeqIso.renameWiresEquiv
      (preparedItems.renameWires (Fin.cast fullLength)) wireEquiv.symm
    have combined := extractionCast.trans renamed
    simpa [FiniteEquiv.trans, FiniteEquiv.refl] using combined
  have keptCast : ItemSeqIso
      (FiniteEquiv.refl (Fin
        (anchorLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires input.val
            selection.val.anchor).length))) rels
      (keptItems.renameWires (Fin.cast fullLength))
      ((restrictedItems.renameWires
        (retainedContextIndexMap input.val selection
          anchorLeaf.inheritedWires)).renameWires (Fin.cast fullLength)) := by
    apply ItemSeqIso.renameWires_commuting keptIso
      (Fin.cast fullLength) (Fin.cast fullLength)
      (FiniteEquiv.refl _)
    funext index
    rfl
  have keptFactorTarget :
      (((restrictedItems.renameWires
          (retainedContextIndexMap input.val selection
            anchorLeaf.inheritedWires)).renameWires
            (Fin.cast fullLength)).renameWires wireEquiv.symm) =
        restrictedItems.renameWires factorRetained := by
    simp only [ItemSeq.renameWires_comp]
    simpa [Function.comp_def] using
      congrArg (fun rename => restrictedItems.renameWires rename)
        retainedFactor
  have keptFactorIso : ItemSeqIso wireEquiv.symm rels
      (keptItems.renameWires (Fin.cast fullLength))
      (restrictedItems.renameWires factorRetained) := by
    have renamed := ItemSeqIso.renameWiresEquiv
      ((restrictedItems.renameWires
        (retainedContextIndexMap input.val selection
          anchorLeaf.inheritedWires)).renameWires (Fin.cast fullLength))
      wireEquiv.symm
    have combined := keptCast.trans renamed
    rw [keptFactorTarget] at combined
    simpa [FiniteEquiv.trans, FiniteEquiv.refl] using combined
  have combinedFactorIso := ItemSeqIso.append selectedFactorIso keptFactorIso
  have partitionItems : ItemSeqIso
      (FiniteEquiv.refl
        (Fin (anchorLeaf.inheritedWires.extend
          selection.val.anchor).length)) rels
      anchorLeaf.items (selectedItems.append keptItems) := by
    have reversed := partitionIso.symm
    cases reversed with
    | mk localEquiv items =>
        have ambientSymm :
            (FiniteEquiv.refl
              (Fin (anchorLeaf.inheritedWires.extend
                selection.val.anchor).length)).symm =
              FiniteEquiv.refl
                (Fin (anchorLeaf.inheritedWires.extend
                  selection.val.anchor).length) := by
          apply FiniteEquiv.ext
          intro wire
          rfl
        rw [ambientSymm] at items
        have extendedRefl :
            extendWireEquiv
                (FiniteEquiv.refl
                  (Fin (anchorLeaf.inheritedWires.extend
                    selection.val.anchor).length))
                localEquiv =
              FiniteEquiv.refl
                (Fin (anchorLeaf.inheritedWires.extend
                  selection.val.anchor).length) := by
          apply FiniteEquiv.ext
          intro wire
          refine Fin.addCases (fun index => ?_) (fun index => ?_) wire
          · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
          · exact Fin.elim0 index
        rw [extendedRefl] at items
        exact items
  have partitionCast : ItemSeqIso
      (FiniteEquiv.refl (Fin
        (anchorLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires input.val
            selection.val.anchor).length))) rels
      (anchorLeaf.items.renameWires (Fin.cast fullLength))
      ((selectedItems.append keptItems).renameWires
        (Fin.cast fullLength)) := by
    apply ItemSeqIso.renameWires_commuting partitionItems
      (Fin.cast fullLength) (Fin.cast fullLength)
      (FiniteEquiv.refl _)
    funext index
    rfl
  have leafFactorItems : ItemSeqIso wireEquiv.symm rels
      (anchorLeaf.items.renameWires (Fin.cast fullLength))
      (((preparedItems.renameWires (Fin.cast fullLength)).renameWires
          wireEquiv.symm).append
        (restrictedItems.renameWires factorRetained)) := by
    have partitionCast' : ItemSeqIso
        (FiniteEquiv.refl (Fin
          (anchorLeaf.inheritedWires.length +
            (Concrete.Elaboration.exactScopeWires input.val
              selection.val.anchor).length))) rels
        (anchorLeaf.items.renameWires (Fin.cast fullLength))
        ((selectedItems.renameWires (Fin.cast fullLength)).append
          (keptItems.renameWires (Fin.cast fullLength))) := by
      simpa only [ItemSeq.renameWires_append] using partitionCast
    have combined := partitionCast'.trans combinedFactorIso
    simpa [FiniteEquiv.trans, FiniteEquiv.refl] using combined
  have renameNil {sourceWires targetWires : Nat}
      (rename : Fin sourceWires → Fin targetWires) :
      (ItemSeq.nil : ItemSeq sourceWires rels).renameWires rename =
        (ItemSeq.nil : ItemSeq targetWires rels) := by
    rfl
  let selectedBase :=
    (preparedItems.renameWires (Fin.cast fullLength)).renameWires
      wireEquiv.symm
  have selectedMapEq :
      Region.adjoinMaterialWire anchorLeaf.inheritedWires.length
          (retainedAnchorWires input.val selection).length
          selection.val.explicitWires.length ∘
        Region.conjoinLeftWire
          (anchorLeaf.inheritedWires.length +
            (retainedAnchorWires input.val selection).length)
          selection.val.explicitWires.length 0 ∘
        Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
          (retainedAnchorWires input.val selection).length
          selection.val.explicitWires.length).symm = id := by
    funext index
    refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
    · have castEq :
          Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
            (retainedAnchorWires input.val selection).length
            selection.val.explicitWires.length).symm
              (Fin.castAdd
                ((retainedAnchorWires input.val selection).length +
                  selection.val.explicitWires.length) inherited) =
            Fin.castAdd selection.val.explicitWires.length
              (Fin.castAdd
                (retainedAnchorWires input.val selection).length inherited) := by
        apply Fin.ext
        rfl
      simp only [Function.comp_apply, castEq, Region.conjoinLeftWire,
        Fin.addCases_left, Region.adjoinMaterialWire]
      apply Fin.ext
      rfl
    · refine Fin.addCases (fun retained => ?_) (fun explicitIndex => ?_)
        localIndex
      · have castEq :
            Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
              (retainedAnchorWires input.val selection).length
              selection.val.explicitWires.length).symm
                (Fin.natAdd anchorLeaf.inheritedWires.length
                  (Fin.castAdd selection.val.explicitWires.length retained)) =
              Fin.castAdd selection.val.explicitWires.length
                (Fin.natAdd anchorLeaf.inheritedWires.length retained) := by
          apply Fin.ext
          rfl
        simp only [Function.comp_apply, castEq, Region.conjoinLeftWire,
          Fin.addCases_left, Region.adjoinMaterialWire]
        apply Fin.ext
        rfl
      · have castEq :
            Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
              (retainedAnchorWires input.val selection).length
              selection.val.explicitWires.length).symm
                (Fin.natAdd anchorLeaf.inheritedWires.length
                  (Fin.natAdd
                    (retainedAnchorWires input.val selection).length
                    explicitIndex)) =
              Fin.natAdd
                (anchorLeaf.inheritedWires.length +
                  (retainedAnchorWires input.val selection).length)
                explicitIndex := by
          apply Fin.ext
          change anchorLeaf.inheritedWires.length +
              ((retainedAnchorWires input.val selection).length +
                explicitIndex.val) =
            (anchorLeaf.inheritedWires.length +
              (retainedAnchorWires input.val selection).length) +
                explicitIndex.val
          omega
        simp only [Function.comp_apply, castEq, Region.conjoinLeftWire,
          Fin.addCases_right, Region.adjoinMaterialWire]
        apply Fin.ext
        change (anchorLeaf.inheritedWires.length +
              (retainedAnchorWires input.val selection).length) +
                explicitIndex.val =
            anchorLeaf.inheritedWires.length +
              ((retainedAnchorWires input.val selection).length +
                explicitIndex.val)
        omega
  have selectedBlockEq :
      (((selectedBase.renameWires
          (Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
            (retainedAnchorWires input.val selection).length
            selection.val.explicitWires.length).symm)).renameWires
        (Region.conjoinLeftWire
          (anchorLeaf.inheritedWires.length +
            (retainedAnchorWires input.val selection).length)
          selection.val.explicitWires.length 0)).renameWires
        (Region.adjoinMaterialWire anchorLeaf.inheritedWires.length
          (retainedAnchorWires input.val selection).length
          selection.val.explicitWires.length)) = selectedBase := by
    calc
      _ = selectedBase.renameWires
          ((Region.adjoinMaterialWire anchorLeaf.inheritedWires.length
              (retainedAnchorWires input.val selection).length
              selection.val.explicitWires.length ∘
            Region.conjoinLeftWire
              (anchorLeaf.inheritedWires.length +
                (retainedAnchorWires input.val selection).length)
              selection.val.explicitWires.length 0) ∘
            Fin.cast (Nat.add_assoc anchorLeaf.inheritedWires.length
              (retainedAnchorWires input.val selection).length
              selection.val.explicitWires.length).symm) := by
              rw [ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
      _ = selectedBase.renameWires id := by
        apply congrArg (fun rename => selectedBase.renameWires rename)
        exact selectedMapEq
      _ = selectedBase := ItemSeq.renameWires_id selectedBase
  dsimp only [selectedBase] at selectedBlockEq
  have retainedMapEq :
      Region.adjoinMaterialWire anchorLeaf.inheritedWires.length
          (retainedAnchorWires input.val selection).length
          selection.val.explicitWires.length ∘
        Region.conjoinRightWire
          (anchorLeaf.inheritedWires.length +
            (retainedAnchorWires input.val selection).length)
          selection.val.explicitWires.length 0 ∘
        Fin.cast (congrArg (fun wires => wires + 0) retainedLength) =
      factorRetained := by
    funext index
    have castEq :
        Fin.cast (congrArg (fun wires => wires + 0) retainedLength) index =
          Fin.castAdd 0 (Fin.cast retainedLength index) := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [castEq]
    simp only [Region.conjoinRightWire,
      Fin.addCases_left, Region.adjoinMaterialWire, factorRetained]
    apply Fin.ext
    rfl
  have retainedBlockEq :
      (((restrictedItems.renameWires
          (Fin.cast (congrArg (fun wires => wires + 0)
            retainedLength))).renameWires
        (Region.conjoinRightWire
          (anchorLeaf.inheritedWires.length +
            (retainedAnchorWires input.val selection).length)
          selection.val.explicitWires.length 0)).renameWires
        (Region.adjoinMaterialWire anchorLeaf.inheritedWires.length
          (retainedAnchorWires input.val selection).length
          selection.val.explicitWires.length)) =
        restrictedItems.renameWires factorRetained := by
    calc
      _ = restrictedItems.renameWires
          ((Region.adjoinMaterialWire anchorLeaf.inheritedWires.length
              (retainedAnchorWires input.val selection).length
              selection.val.explicitWires.length ∘
            Region.conjoinRightWire
              (anchorLeaf.inheritedWires.length +
                (retainedAnchorWires input.val selection).length)
              selection.val.explicitWires.length 0) ∘
            Fin.cast (congrArg (fun wires => wires + 0)
              retainedLength)) := by
                rw [ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
      _ = restrictedItems.renameWires factorRetained := by
        apply congrArg (fun rename => restrictedItems.renameWires rename)
        exact retainedMapEq
  have sourceTargetEq :
      Region.adjoinAt (retainedAnchorWires input.val selection).length .nil
          (selected.conjoin
            (factoredWitness.toFocus.context.fill
              factoredWitness.toFocus.body)) =
        Region.mk
          ((retainedAnchorWires input.val selection).length +
            selection.val.explicitWires.length)
          (((preparedItems.renameWires (Fin.cast fullLength)).renameWires
              wireEquiv.symm).append
            (restrictedItems.renameWires factorRetained)) := by
    rw [factoredWitness.toFocus.rebuild]
    simp only [selected, factoredItems, Region.conjoin, Region.adjoinAt,
      Region.castWiresEq_mk, ItemSeq.nil_append,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.renameWires_append,
      renameNil, Nat.add_zero]
    apply congrArg (Region.mk
      ((retainedAnchorWires input.val selection).length +
        selection.val.explicitWires.length))
    congr 1
  let finished := Concrete.Elaboration.finishRegion input.val
    anchorLeaf.inheritedWires selection.val.anchor anchorLeaf.items
  let sourceItems : ItemSeq
      (outer + (Concrete.Elaboration.exactScopeWires input.val
        selection.val.anchor).length) rels :=
    (anchorLeaf.items.renameWires (Fin.cast fullLength)).castWiresEq
      (congrArg
        (fun inherited => inherited +
          (Concrete.Elaboration.exactScopeWires input.val
            selection.val.anchor).length)
        anchorLeaf.inheritedLength)
  let targetItems : ItemSeq
      (anchorLeaf.inheritedWires.length +
        ((retainedAnchorWires input.val selection).length +
          selection.val.explicitWires.length)) rels :=
    ((preparedItems.renameWires (Fin.cast fullLength)).renameWires
        wireEquiv.symm).append
      (restrictedItems.renameWires factorRetained)
  have sourceEq : anchorBody = Region.mk
      (Concrete.Elaboration.exactScopeWires input.val
        selection.val.anchor).length sourceItems := by
    simpa only [sourceItems, finished, Concrete.Elaboration.finishRegion,
      Region.castWiresEq_mk, ItemSeq.castWiresEq_eq_renameWires] using
        anchorLeaf.bodyComputation
  let sourceCastEquiv := extendWireEquiv
    (FiniteEquiv.finCast anchorLeaf.inheritedLength)
    (FiniteEquiv.refl (Fin
      (Concrete.Elaboration.exactScopeWires input.val
        selection.val.anchor).length))
  have sourceCastEq :
      Fin.cast
          (congrArg
            (fun inherited => inherited +
              (Concrete.Elaboration.exactScopeWires input.val
                selection.val.anchor).length)
            anchorLeaf.inheritedLength) =
        sourceCastEquiv := by
    funext index
    refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
    · apply Fin.ext
      simp only [sourceCastEquiv, extendWireEquiv_outer,
        FiniteEquiv.finCast]
      rfl
    · apply Fin.ext
      simp only [sourceCastEquiv, extendWireEquiv_local,
        FiniteEquiv.refl_apply]
      change anchorLeaf.inheritedWires.length + localIndex.val =
        outer + localIndex.val
      exact congrArg (fun inherited => inherited + localIndex.val)
        anchorLeaf.inheritedLength
  have sourceItemsEq : sourceItems =
      (anchorLeaf.items.renameWires (Fin.cast fullLength)).renameWires
        sourceCastEquiv := by
    dsimp only [sourceItems]
    rw [ItemSeq.castWiresEq_eq_renameWires]
    exact congrArg
      (fun rename =>
        (anchorLeaf.items.renameWires (Fin.cast fullLength)).renameWires
          rename)
      sourceCastEq
  have sourceCastIso : ItemSeqIso sourceCastEquiv.symm rels sourceItems
      (anchorLeaf.items.renameWires (Fin.cast fullLength)) := by
    have renamed := (ItemSeqIso.renameWiresEquiv
      (anchorLeaf.items.renameWires (Fin.cast fullLength))
      sourceCastEquiv).symm
    rw [sourceItemsEq]
    simpa only [Region.ContextPath.toFocus] using renamed
  have sourceFactorItems := sourceCastIso.trans leafFactorItems
  have presentationWireEq :
      sourceCastEquiv.symm.trans wireEquiv.symm =
        extendWireEquiv
          (FiniteEquiv.finCast anchorLeaf.inheritedLength.symm)
          localEquiv.symm := by
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
    · apply Fin.ext
      simp only [FiniteEquiv.trans_apply, sourceCastEquiv,
        extendWireEquiv_symm, extendWireEquiv_outer,
        FiniteEquiv.finCast, wireEquiv, anchorWireEquiv]
      dsimp only [FiniteEquiv.symm, FiniteEquiv.refl]
      rfl
    · apply Fin.ext
      simp only [FiniteEquiv.trans_apply, sourceCastEquiv,
        extendWireEquiv_symm, extendWireEquiv_local,
        wireEquiv, anchorWireEquiv]
      dsimp only [FiniteEquiv.symm, FiniteEquiv.refl, localEquiv]
      rfl
  rw [presentationWireEq] at sourceFactorItems
  have rawSourceIso : RegionIso
      (FiniteEquiv.finCast anchorLeaf.inheritedLength.symm) rels
      (Region.mk
        (Concrete.Elaboration.exactScopeWires input.val
          selection.val.anchor).length sourceItems)
      (Region.mk
        ((retainedAnchorWires input.val selection).length +
          selection.val.explicitWires.length) targetItems) :=
    .mk localEquiv.symm sourceFactorItems
  have sourceIso : RegionIso
      (FiniteEquiv.finCast anchorLeaf.inheritedLength.symm) rels anchorBody
      (Region.mk
        ((retainedAnchorWires input.val selection).length +
          selection.val.explicitWires.length) targetItems) :=
    Eq.mp (congrArg (fun source => RegionIso
      (FiniteEquiv.finCast anchorLeaf.inheritedLength.symm) rels source
      (Region.mk
        ((retainedAnchorWires input.val selection).length +
          selection.val.explicitWires.length) targetItems)) sourceEq.symm)
      rawSourceIso
  have sourceIso' : RegionIso
      (FiniteEquiv.finCast anchorLeaf.inheritedLength.symm) rels anchorBody
      (Region.adjoinAt
        (retainedAnchorWires input.val selection).length .nil
        (selected.conjoin
          (factoredWitness.toFocus.context.fill
            factoredWitness.toFocus.body))) :=
    Eq.mp (congrArg (fun target => RegionIso
      (FiniteEquiv.finCast anchorLeaf.inheritedLength.symm) rels anchorBody
      target) sourceTargetEq.symm) sourceIso
  exact {
    anchorLocal := (retainedAnchorWires input.val selection).length
    selected := selected
    route_alignment := routeAlignment
    selected_local := ⟨factoredItems, rfl⟩
    source_iso := by
      simpa only [sourceFactorTargetRegion,
        SourceRouteAlignment.descendant, SourceRouteAlignment.remainder]
        using sourceIso'
    material_iso := materialIso
  }

end VisualProof.Refinement.Implementation.IterationSourceFactor
