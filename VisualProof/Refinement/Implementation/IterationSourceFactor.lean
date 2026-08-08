import VisualProof.Refinement.Implementation.IterationExtractionSelected
import VisualProof.Refinement.Implementation.IterationRoute

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
theorem compileKeptOccurrences_restrict
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
    ∃ restrictedItems : ItemSeq
        (retainedContext input.val selection
          anchorLeaf.inheritedWires).length rels,
      Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val anchorLeaf.fuel)
        (retainedContext input.val selection anchorLeaf.inheritedWires)
        anchorLeaf.binders (keptOccurrences input.val selection) =
          some restrictedItems ∧
      ItemSeqIso (FiniteEquiv.refl _) rels keptItems
        (restrictedItems.renameWires
          (retainedContextIndexMap input.val selection
            anchorLeaf.inheritedWires)) := by
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
      · rfl
      · have renamed : keptItems = restrictedItems.renameWires
            (retainedContextIndexMap input.val selection
              anchorLeaf.inheritedWires) := by
          exact Option.some.inj (by
            simpa only [embedding, retainedContextEmbedding] using sequenceMap')
        rw [renamed]
        exact ItemSeqIso.refl _

end VisualProof.Refinement.Implementation.IterationSourceFactor
