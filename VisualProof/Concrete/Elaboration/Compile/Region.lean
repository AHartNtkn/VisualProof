import VisualProof.Concrete.Elaboration.Compile.Kernel

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

noncomputable def regionIso_of_cast
    {sourceOuter targetOuter sourceLocal targetLocal
      sourceExtended targetExtended : Nat}
    (sourceEq : sourceExtended = sourceOuter + sourceLocal)
    (targetEq : targetExtended = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceItems : ItemSeq sourceExtended rels)
    (targetItems : ItemSeq targetExtended rels)
    (hitems : ItemSeqIso
      (castFinEquiv sourceEq targetEq (extendWireEquiv ambient localEquiv))
      rels sourceItems targetItems) :
    RegionIso ambient rels
      (.mk sourceLocal (sourceItems.castWiresEq sourceEq))
      (.mk targetLocal (targetItems.castWiresEq targetEq)) := by
  subst sourceExtended
  subst targetExtended
  simpa using RegionIso.mk localEquiv hitems

private def descendantRegions (d : Diagram)
    (region : Fin d.regionCount) : List (Fin d.regionCount) :=
  filterFin fun candidate => decide (d.Encloses region candidate)

private theorem filter_sublist_filter {values : List α} {p q : α → Bool}
    (implication : ∀ value, p value = true → q value = true) :
    (values.filter p).Sublist (values.filter q) := by
  induction values with
  | nil => exact .slnil
  | cons head tail ih =>
      cases hp : p head with
      | false =>
          cases hq : q head with
          | false => simpa [hp, hq] using ih
          | true => simpa [hp, hq] using ih.cons head
      | true =>
          have hq := implication head hp
          simpa [hp, hq] using ih.cons_cons head

private theorem descendantRegions_length_lt_of_parent
    {d : Diagram} (hwf : d.WellFormed)
    {child parent : Fin d.regionCount}
    (hparent : (d.regions child).parent? = some parent) :
    (descendantRegions d child).length <
      (descendantRegions d parent).length := by
  have sublist : (descendantRegions d child).Sublist
      (descendantRegions d parent) := by
    have parentChild : d.Encloses parent child := by
      refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
      simp [Diagram.climb, hparent]
    apply filter_sublist_filter
    intro candidate candidateMember
    simp only [decide_eq_true_eq] at candidateMember ⊢
    exact checked_encloses_trans hwf parentChild candidateMember
  have distinct : descendantRegions d child ≠
      descendantRegions d parent := by
    intro equal
    have parentMember : parent ∈ descendantRegions d parent := by
      simp [descendantRegions, Diagram.Encloses.refl]
    have childMember : parent ∈ descendantRegions d child := by
      rw [equal]
      exact parentMember
    simp only [descendantRegions, mem_filterFin, decide_eq_true_eq]
      at childMember
    exact checked_direct_child_not_encloses_parent hwf hparent childMember
  have lengthLe := sublist.length_le
  have lengthNe : (descendantRegions d child).length ≠
      (descendantRegions d parent).length := by
    intro equal
    exact distinct (sublist.eq_of_length equal)
  omega

private def compileOccurrenceWith? (d : Diagram)
    (parent : Fin d.regionCount)
    (recurse : ∀ {nestedRels : RelCtx},
      (child : Fin d.regionCount) →
      (d.regions child).parent? = some parent →
      (context : WireContext d) →
      (binders : BinderContext d nestedRels) →
      Option (CompiledRegion d (.nested child context nestedRels binders)))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount)
    (direct : occurrence ∈ localOccurrences d parent) :
    Option (CompiledItem d context rels binders) :=
  match occurrence with
  | .node node => compileNode? d context binders node
  | .child child =>
      have hparent := (mem_localOccurrences_child d parent child).mp direct
      match d.regions child with
      | .sheet => none
      | .cut _ => do
          let body ← recurse child hparent context binders
          pure (.cut body)
      | .bubble _ arity => do
          let body ← recurse child hparent context (binders.push child arity)
          pure (.bubble arity body)

private def compileItemsWith? (d : Diagram)
    (parent : Fin d.regionCount)
    (recurse : ∀ {nestedRels : RelCtx},
      (child : Fin d.regionCount) →
      (d.regions child).parent? = some parent →
      (context : WireContext d) →
      (binders : BinderContext d nestedRels) →
      Option (CompiledRegion d (.nested child context nestedRels binders)))
    (context : WireContext d) (binders : BinderContext d rels) :
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount)) →
    (∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d parent) →
    Option (CompiledItems d context rels binders)
  | [], _ => some .nil
  | occurrence :: tail, direct => do
      let head ← compileOccurrenceWith? d parent recurse context binders
        occurrence (direct occurrence (by simp))
      let rest ← compileItemsWith? d parent recurse context binders tail
        (by
          intro candidate member
          exact direct candidate (by simp [member]))
      pure (.cons head rest)

namespace CompilerCall

/-- Compile exactly one root or nested call. Recursive descent follows only
direct children in the checked region hierarchy. -/
def compile? (d : Diagram) (hwf : d.WellFormed) :
    (call : CompilerCall d) → Option (CompiledRegion d call)
  | call => do
      let items ← compileItemsWith? d call.origin
        (fun child _hparent context binders =>
          compile? d hwf (.nested child context _ binders))
        call.fullContext call.binders (localOccurrences d call.origin)
        (fun _ member => member)
      pure (.mk items)
termination_by call => (descendantRegions d call.origin).length
decreasing_by
  exact descendantRegions_length_lt_of_parent hwf _hparent

end CompilerCall

/-- Compile one direct occurrence using the sole checked call compiler for
recursive children. -/
def compileOccurrence? (d : Diagram) (hwf : d.WellFormed)
    (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount)
    (direct : occurrence ∈ localOccurrences d parent) :
    Option (CompiledItem d context rels binders) :=
  compileOccurrenceWith? d parent
    (fun child _ context nestedBinders =>
      CompilerCall.compile? d hwf
        (.nested child context _ nestedBinders))
    context binders occurrence direct

/-- Compile a chosen direct-occurrence subsequence using the sole checked call
compiler for recursive children. -/
def compileItems? (d : Diagram) (hwf : d.WellFormed)
    (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    (direct : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d parent) :
    Option (CompiledItems d context rels binders) :=
  compileItemsWith? d parent
    (fun child _ context nestedBinders =>
      CompilerCall.compile? d hwf
        (.nested child context _ nestedBinders))
    context binders occurrences direct

/-- Compile an exact nested call. -/
def compileRegion? (d : Diagram) (hwf : d.WellFormed)
    (origin : Fin d.regionCount) (context : WireContext d)
    (binders : BinderContext d rels) :
    Option (CompiledRegion d (.nested origin context rels binders)) :=
  CompilerCall.compile? d hwf (.nested origin context rels binders)

/-- Compile an exact root call. -/
def compileRoot? (d : Diagram) (hwf : d.WellFormed)
    (ambient locals : WireContext d) :
    Option (CompiledRegion d (.root ambient locals)) :=
  CompilerCall.compile? d hwf (.root ambient locals)

theorem CompilerCall.compile?_root
    (hwf : d.WellFormed) (ambient locals : WireContext d) :
    (CompilerCall.root ambient locals).compile? d hwf =
      compileRoot? d hwf ambient locals := rfl

theorem CompilerCall.compile?_nested
    (hwf : d.WellFormed) (origin : Fin d.regionCount)
    (context : WireContext d)
    (binders : BinderContext d nestedRels) :
    (CompilerCall.nested origin context nestedRels binders).compile? d hwf =
      compileRegion? d hwf origin context binders := rfl

@[simp] theorem compileOccurrence?_node
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (node : Fin d.nodeCount)
    (direct : LocalOccurrence.node node ∈ localOccurrences d parent) :
    compileOccurrence? d hwf parent context binders (.node node) direct =
      compileNode? d context binders node := rfl

theorem compileOccurrence?_child_sheet
    (hwf : d.WellFormed) (parent child : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (direct : LocalOccurrence.child child ∈ localOccurrences d parent)
    (hchild : d.regions child = .sheet) :
    compileOccurrence? d hwf parent context binders (.child child) direct =
      none := by
  simp [compileOccurrence?, compileOccurrenceWith?, hchild]

theorem compileOccurrence?_child_cut
    (hwf : d.WellFormed) (parent child : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (direct : LocalOccurrence.child child ∈ localOccurrences d parent)
    (hchild : d.regions child = .cut parent) :
    compileOccurrence? d hwf parent context binders (.child child) direct =
      (do
        let body ← compileRegion? d hwf child context binders
        pure (.cut body)) := by
  simp only [compileOccurrence?, compileOccurrenceWith?]
  rw [hchild]
  rfl

theorem compileOccurrence?_child_bubble
    (hwf : d.WellFormed) (parent child : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (arity : Nat)
    (direct : LocalOccurrence.child child ∈ localOccurrences d parent)
    (hchild : d.regions child = .bubble parent arity) :
    compileOccurrence? d hwf parent context binders (.child child) direct =
      (do
        let body ← compileRegion? d hwf child context
          (binders.push child arity)
        pure (.bubble arity body)) := by
  simp only [compileOccurrence?, compileOccurrenceWith?]
  rw [hchild]
  rfl

theorem compileOccurrence?_child_cut_success
    (hwf : d.WellFormed) (parent child : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (direct : LocalOccurrence.child child ∈ localOccurrences d parent)
    (hchild : d.regions child = .cut parent)
    {item : CompiledItem d context rels binders}
    (compiled : compileOccurrence? d hwf parent context binders
      (.child child) direct = some item) :
    ∃ body : CompiledRegion d (.nested child context rels binders),
      compileRegion? d hwf child context binders = some body ∧
        item = .cut body := by
  rw [compileOccurrence?_child_cut hwf parent child context binders direct
    hchild] at compiled
  cases bodyCompiled : compileRegion? d hwf child context binders with
  | none => simp [bodyCompiled] at compiled
  | some body =>
      refine ⟨body, rfl, ?_⟩
      simpa [bodyCompiled] using compiled.symm

theorem compileOccurrence?_child_bubble_success
    (hwf : d.WellFormed) (parent child : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (arity : Nat)
    (direct : LocalOccurrence.child child ∈ localOccurrences d parent)
    (hchild : d.regions child = .bubble parent arity)
    {item : CompiledItem d context rels binders}
    (compiled : compileOccurrence? d hwf parent context binders
      (.child child) direct = some item) :
    ∃ body : CompiledRegion d
        (.nested child context (arity :: rels) (binders.push child arity)),
      compileRegion? d hwf child context (binders.push child arity) =
        some body ∧
      item = .bubble arity body := by
  rw [compileOccurrence?_child_bubble hwf parent child context binders arity
    direct hchild] at compiled
  cases bodyCompiled : compileRegion? d hwf child context
      (binders.push child arity) with
  | none => simp [bodyCompiled] at compiled
  | some body =>
      refine ⟨body, rfl, ?_⟩
      simpa [bodyCompiled] using compiled.symm

theorem compileOccurrence?_child_cut_body
    (hwf : d.WellFormed) (parent child : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (direct : LocalOccurrence.child child ∈ localOccurrences d parent)
    (hchild : d.regions child = .cut parent)
    {body : CompiledRegion d (.nested child context rels binders)}
    (compiled : compileOccurrence? d hwf parent context binders
      (.child child) direct = some (.cut body)) :
    compileRegion? d hwf child context binders = some body := by
  rw [compileOccurrence?_child_cut hwf parent child context binders direct
    hchild] at compiled
  cases result : compileRegion? d hwf child context binders with
  | none => simp [result] at compiled
  | some childBody =>
      simp [result] at compiled
      cases compiled
      rfl

theorem compileOccurrence?_child_bubble_body
    (hwf : d.WellFormed) (parent child : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (arity : Nat)
    (direct : LocalOccurrence.child child ∈ localOccurrences d parent)
    (hchild : d.regions child = .bubble parent arity)
    {body : CompiledRegion d
      (.nested child context (arity :: rels) (binders.push child arity))}
    (compiled : compileOccurrence? d hwf parent context binders
      (.child child) direct = some (.bubble arity body)) :
    compileRegion? d hwf child context (binders.push child arity) =
      some body := by
  rw [compileOccurrence?_child_bubble hwf parent child context binders arity
    direct hchild] at compiled
  cases result : compileRegion? d hwf child context
      (binders.push child arity) with
  | none => simp [result] at compiled
  | some childBody =>
      simp [result] at compiled
      cases compiled
      rfl

@[simp] theorem compileItems?_nil
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (direct : ∀ occurrence, occurrence ∈ [] →
      occurrence ∈ localOccurrences d parent) :
    compileItems? d hwf parent context binders [] direct = some .nil := rfl

theorem compileItems?_cons
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrence : LocalOccurrence d.regionCount d.nodeCount)
    (tail : List (LocalOccurrence d.regionCount d.nodeCount))
    (direct : ∀ candidate, candidate ∈ occurrence :: tail →
      candidate ∈ localOccurrences d parent) :
    compileItems? d hwf parent context binders (occurrence :: tail) direct =
      (do
        let head ← compileOccurrence? d hwf parent context binders occurrence
          (direct occurrence (by simp))
        let rest ← compileItems? d hwf parent context binders tail (by
          intro candidate member
          exact direct candidate (by simp [member]))
        pure (.cons head rest)) := rfl

/-- Compile two direct occurrence blocks independently, then concatenate their
sole compiler results. -/
theorem compileItems?_append
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (initial suffix : List (LocalOccurrence d.regionCount d.nodeCount))
    (direct : ∀ occurrence, occurrence ∈ initial ++ suffix →
      occurrence ∈ localOccurrences d parent)
    {initialItems suffixItems : CompiledItems d context rels binders}
    (initialCompiled : compileItems? d hwf parent context binders initial
      (fun occurrence member => direct occurrence
        (List.mem_append_left suffix member)) = some initialItems)
    (suffixCompiled : compileItems? d hwf parent context binders suffix
      (fun occurrence member => direct occurrence
        (List.mem_append_right initial member)) = some suffixItems) :
    compileItems? d hwf parent context binders (initial ++ suffix) direct =
      some (initialItems.append suffixItems) := by
  induction initial generalizing initialItems with
  | nil =>
      simp only [compileItems?_nil] at initialCompiled
      cases initialCompiled
      simpa using suffixCompiled
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at initialCompiled
      change (do
        let head ← compileOccurrence? d hwf parent context binders occurrence
          (direct occurrence (by simp))
        let rest ← compileItems? d hwf parent context binders
          (tail ++ suffix) (by
            intro candidate member
            exact direct candidate (by simp [member]))
        pure (.cons head rest)) = some (initialItems.append suffixItems)
      let headDirect : occurrence ∈ localOccurrences d parent :=
        direct occurrence (by simp)
      let tailDirect : ∀ candidate, candidate ∈ tail ++ suffix →
          candidate ∈ localOccurrences d parent := by
        intro candidate member
        exact direct candidate (by simp [member])
      cases headCompiled : compileOccurrence? d hwf parent context binders
          occurrence headDirect with
      | none => simp [headCompiled] at initialCompiled
      | some head =>
          cases tailCompiled : compileItems? d hwf parent context binders tail
              (fun candidate member => direct candidate (by simp [member])) with
          | none => simp [headCompiled, tailCompiled] at initialCompiled
          | some tailItems =>
              simp [headCompiled, tailCompiled] at initialCompiled
              cases initialCompiled
              have combined := ih tailDirect tailCompiled suffixCompiled
              change (do
                let rest ← compileItems? d hwf parent context binders
                  (tail ++ suffix) _
                pure (CompiledItems.cons head rest)) = _
              rw [combined]
              rfl

/-- A successful concatenated occurrence compilation uniquely factors into
the successful compiler results of its two blocks. -/
theorem compileItems?_append_inv
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (initial suffix : List (LocalOccurrence d.regionCount d.nodeCount))
    (direct : ∀ occurrence, occurrence ∈ initial ++ suffix →
      occurrence ∈ localOccurrences d parent)
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf parent context binders
      (initial ++ suffix) direct = some items) :
    ∃ initialItems suffixItems,
      compileItems? d hwf parent context binders initial
          (fun occurrence member => direct occurrence
            (List.mem_append_left suffix member)) = some initialItems ∧
      compileItems? d hwf parent context binders suffix
          (fun occurrence member => direct occurrence
            (List.mem_append_right initial member)) = some suffixItems ∧
      items = initialItems.append suffixItems := by
  induction initial generalizing items with
  | nil =>
      refine ⟨.nil, items, rfl, ?_, rfl⟩
      simpa using compiled
  | cons occurrence tail ih =>
      change (do
        let head ← compileOccurrence? d hwf parent context binders occurrence
          (direct occurrence (by simp))
        let rest ← compileItems? d hwf parent context binders
          (tail ++ suffix) (by
            intro candidate member
            exact direct candidate (by simp [member]))
        pure (CompiledItems.cons head rest)) = some items at compiled
      cases headCompiled : compileOccurrence? d hwf parent context binders
          occurrence (direct occurrence (by simp)) with
      | none => simp [headCompiled] at compiled
      | some head =>
          cases restCompiled : compileItems? d hwf parent context binders
              (tail ++ suffix) (by
                intro candidate member
                exact direct candidate (by simp [member])) with
          | none => simp [headCompiled, restCompiled] at compiled
          | some rest =>
              simp [headCompiled, restCompiled] at compiled
              subst items
              let tailDirect : ∀ candidate, candidate ∈ tail ++ suffix →
                  candidate ∈ localOccurrences d parent := by
                intro candidate member
                exact direct candidate (by simp [member])
              obtain ⟨tailItems, suffixItems, tailCompiled,
                  suffixCompiled, restEq⟩ := ih tailDirect restCompiled
              subst rest
              refine ⟨.cons head tailItems, suffixItems, ?_, ?_, rfl⟩
              · rw [compileItems?_cons]
                simp only [headCompiled]
                rw [tailCompiled]
                rfl
              · exact suffixCompiled

/-- Constructively transport one finite occurrence block when each head
compiler call transports. Recursive region transport remains the operation's
responsibility. -/
theorem compileItems?_map_success
    {source target : Diagram}
    (sourceWf : source.WellFormed) (targetWf : target.WellFormed)
    (sourceParent : Fin source.regionCount)
    (targetParent : Fin target.regionCount)
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (sourceOccurrences :
      List (LocalOccurrence source.regionCount source.nodeCount))
    (mapOccurrence : LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount)
    (sourceDirect : ∀ occurrence, occurrence ∈ sourceOccurrences →
      occurrence ∈ localOccurrences source sourceParent)
    (targetDirect : ∀ occurrence,
      occurrence ∈ sourceOccurrences.map mapOccurrence →
        occurrence ∈ localOccurrences target targetParent)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (mapHead : ∀ occurrence (member : occurrence ∈ sourceOccurrences)
        {sourceItem : CompiledItem source sourceContext sourceRels
          sourceBinders},
      compileOccurrence? source sourceWf sourceParent sourceContext
          sourceBinders occurrence (sourceDirect occurrence member) =
        some sourceItem →
      ∃ targetItem : CompiledItem target targetContext targetRels
          targetBinders,
        compileOccurrence? target targetWf targetParent targetContext
            targetBinders (mapOccurrence occurrence)
            (targetDirect _ (List.mem_map.mpr ⟨occurrence, member, rfl⟩)) =
          some targetItem ∧
        targetItem.erase =
          (sourceItem.erase.renameWires wireMap).renameRelations relationMap)
    {sourceItems : CompiledItems source sourceContext sourceRels
      sourceBinders}
    (sourceCompiled : compileItems? source sourceWf sourceParent
      sourceContext sourceBinders sourceOccurrences sourceDirect =
        some sourceItems) :
    ∃ targetItems : CompiledItems target targetContext targetRels
        targetBinders,
      compileItems? target targetWf targetParent targetContext targetBinders
          (sourceOccurrences.map mapOccurrence) targetDirect =
        some targetItems ∧
      targetItems.erase =
        (sourceItems.erase.renameWires wireMap).renameRelations relationMap := by
  induction sourceOccurrences generalizing sourceItems with
  | nil =>
      simp only [compileItems?_nil] at sourceCompiled ⊢
      cases sourceCompiled
      exact ⟨.nil, rfl, rfl⟩
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at sourceCompiled
      cases headCompiled : compileOccurrence? source sourceWf sourceParent
          sourceContext sourceBinders occurrence
          (sourceDirect occurrence (by simp)) with
      | none => simp [headCompiled] at sourceCompiled
      | some sourceHead =>
          cases tailCompiled : compileItems? source sourceWf sourceParent
              sourceContext sourceBinders tail (by
                intro candidate member
                exact sourceDirect candidate (by simp [member])) with
          | none => simp [headCompiled, tailCompiled] at sourceCompiled
          | some sourceTail =>
              simp [headCompiled, tailCompiled] at sourceCompiled
              subst sourceItems
              obtain ⟨targetHead, targetHeadCompiled, targetHeadErase⟩ :=
                mapHead occurrence (by simp) headCompiled
              obtain ⟨targetTail, targetTailCompiled, targetTailErase⟩ :=
                ih (sourceDirect := by
                    intro candidate member
                    exact sourceDirect candidate (by simp [member]))
                  (targetDirect := by
                    intro candidate member
                    exact targetDirect candidate (by
                      rw [List.map_cons]
                      exact List.mem_cons_of_mem _ member))
                  (mapHead := by
                    intro candidate member sourceItem compiled
                    exact mapHead candidate (by simp [member]) compiled)
                  tailCompiled
              refine ⟨.cons targetHead targetTail, ?_, ?_⟩
              · change compileItems? target targetWf targetParent
                  targetContext targetBinders
                    (mapOccurrence occurrence :: tail.map mapOccurrence) _ = _
                rw [compileItems?_cons]
                simp only [targetHeadCompiled, targetTailCompiled]
                rfl
              · simp [CompiledItems.erase, ItemSeq.renameWires,
                  ItemSeq.renameRelations, targetHeadErase, targetTailErase]

/-- Constructively transport one finite occurrence block when callers need
only target compilation.  This weaker boundary is used by operations that
intentionally remove unused lexical wires, where no total source-to-target
wire renaming exists. -/
theorem compileItems?_map_success_only
    {source target : Diagram}
    (sourceWf : source.WellFormed) (targetWf : target.WellFormed)
    (sourceParent : Fin source.regionCount)
    (targetParent : Fin target.regionCount)
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (sourceBinders : BinderContext source sourceRels)
    (targetBinders : BinderContext target targetRels)
    (sourceOccurrences :
      List (LocalOccurrence source.regionCount source.nodeCount))
    (mapOccurrence : LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount)
    (sourceDirect : ∀ occurrence, occurrence ∈ sourceOccurrences →
      occurrence ∈ localOccurrences source sourceParent)
    (targetDirect : ∀ occurrence,
      occurrence ∈ sourceOccurrences.map mapOccurrence →
        occurrence ∈ localOccurrences target targetParent)
    (mapHead : ∀ occurrence (member : occurrence ∈ sourceOccurrences)
        {sourceItem : CompiledItem source sourceContext sourceRels
          sourceBinders},
      compileOccurrence? source sourceWf sourceParent sourceContext
          sourceBinders occurrence (sourceDirect occurrence member) =
        some sourceItem →
      ∃ targetItem : CompiledItem target targetContext targetRels
          targetBinders,
        compileOccurrence? target targetWf targetParent targetContext
            targetBinders (mapOccurrence occurrence)
            (targetDirect _ (List.mem_map.mpr ⟨occurrence, member, rfl⟩)) =
          some targetItem)
    {sourceItems : CompiledItems source sourceContext sourceRels
      sourceBinders}
    (sourceCompiled : compileItems? source sourceWf sourceParent
      sourceContext sourceBinders sourceOccurrences sourceDirect =
        some sourceItems) :
    ∃ targetItems : CompiledItems target targetContext targetRels
        targetBinders,
      compileItems? target targetWf targetParent targetContext targetBinders
          (sourceOccurrences.map mapOccurrence) targetDirect =
        some targetItems := by
  induction sourceOccurrences generalizing sourceItems with
  | nil =>
      simp only [compileItems?_nil] at sourceCompiled ⊢
      cases sourceCompiled
      exact ⟨.nil, rfl⟩
  | cons occurrence tail induction =>
      rw [compileItems?_cons] at sourceCompiled
      cases headCompiled : compileOccurrence? source sourceWf sourceParent
          sourceContext sourceBinders occurrence
          (sourceDirect occurrence (by simp)) with
      | none => simp [headCompiled] at sourceCompiled
      | some sourceHead =>
          cases tailCompiled : compileItems? source sourceWf sourceParent
              sourceContext sourceBinders tail (by
                intro candidate member
                exact sourceDirect candidate (by simp [member])) with
          | none => simp [headCompiled, tailCompiled] at sourceCompiled
          | some sourceTail =>
              simp [headCompiled, tailCompiled] at sourceCompiled
              subst sourceItems
              obtain ⟨targetHead, targetHeadCompiled⟩ :=
                mapHead occurrence (by simp) headCompiled
              obtain ⟨targetTail, targetTailCompiled⟩ :=
                induction (sourceDirect := by
                    intro candidate member
                    exact sourceDirect candidate (by simp [member]))
                  (targetDirect := by
                    intro candidate member
                    exact targetDirect candidate (by
                      rw [List.map_cons]
                      exact List.mem_cons_of_mem _ member))
                  (mapHead := by
                    intro candidate member sourceItem compiled
                    exact mapHead candidate (by simp [member]) compiled)
                  tailCompiled
              refine ⟨.cons targetHead targetTail, ?_⟩
              change compileItems? target targetWf targetParent targetContext
                targetBinders
                  (mapOccurrence occurrence :: tail.map mapOccurrence) _ = _
              rw [compileItems?_cons]
              simp only [targetHeadCompiled, targetTailCompiled]
              rfl

/-- Constructively transport one finite occurrence block when each head is
intrinsically isomorphic. This is the semantic counterpart of
`compileItems?_map_success`; recursive-region meaning remains with the caller. -/
theorem compileItems?_map_iso_success
    {source target : Diagram}
    (sourceWf : source.WellFormed) (targetWf : target.WellFormed)
    (sourceParent : Fin source.regionCount)
    (targetParent : Fin target.regionCount)
    (sourceContext : WireContext source)
    (targetContext : WireContext target)
    (sourceBinders : BinderContext source rels)
    (targetBinders : BinderContext target rels)
    (sourceOccurrences :
      List (LocalOccurrence source.regionCount source.nodeCount))
    (mapOccurrence : LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount)
    (sourceDirect : ∀ occurrence, occurrence ∈ sourceOccurrences →
      occurrence ∈ localOccurrences source sourceParent)
    (targetDirect : ∀ occurrence,
      occurrence ∈ sourceOccurrences.map mapOccurrence →
        occurrence ∈ localOccurrences target targetParent)
    (wire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (mapHead : ∀ occurrence (member : occurrence ∈ sourceOccurrences)
        {sourceItem : CompiledItem source sourceContext rels sourceBinders},
      compileOccurrence? source sourceWf sourceParent sourceContext
          sourceBinders occurrence (sourceDirect occurrence member) =
        some sourceItem →
      Nonempty (Σ targetItem : CompiledItem target targetContext rels
          targetBinders,
        PSigma (fun _ : compileOccurrence? target targetWf targetParent
            targetContext targetBinders (mapOccurrence occurrence)
            (targetDirect _
              (List.mem_map.mpr ⟨occurrence, member, rfl⟩)) =
              some targetItem =>
          ItemIso wire rels sourceItem.erase targetItem.erase)))
    {sourceItems : CompiledItems source sourceContext rels sourceBinders}
    (sourceCompiled : compileItems? source sourceWf sourceParent
      sourceContext sourceBinders sourceOccurrences sourceDirect =
        some sourceItems) :
    Nonempty (Σ targetItems : CompiledItems target targetContext rels
        targetBinders,
      PSigma (fun _ : compileItems? target targetWf targetParent targetContext
          targetBinders (sourceOccurrences.map mapOccurrence) targetDirect =
            some targetItems =>
        ItemSeqIso wire rels sourceItems.erase targetItems.erase)) := by
  induction sourceOccurrences generalizing sourceItems with
  | nil =>
      simp only [compileItems?_nil] at sourceCompiled
      cases sourceCompiled
      refine ⟨⟨.nil, ⟨compileItems?_nil _ _ _ _ _, ?_⟩⟩⟩
      exact .permute (FiniteEquiv.refl (Fin 0)) (fun index => Fin.elim0 index)
  | cons occurrence tail induction =>
      rw [compileItems?_cons] at sourceCompiled
      cases headCompiled : compileOccurrence? source sourceWf sourceParent
          sourceContext sourceBinders occurrence
          (sourceDirect occurrence (by simp)) with
      | none => simp [headCompiled] at sourceCompiled
      | some sourceHead =>
          cases tailCompiled : compileItems? source sourceWf sourceParent
              sourceContext sourceBinders tail (by
                intro candidate member
                exact sourceDirect candidate (by simp [member])) with
          | none => simp [headCompiled, tailCompiled] at sourceCompiled
          | some sourceTail =>
              simp [headCompiled, tailCompiled] at sourceCompiled
              subst sourceItems
              let headResult := Classical.choice
                (mapHead occurrence (by simp) headCompiled)
              let tailResult := Classical.choice (induction
                (sourceDirect := by
                  intro candidate member
                  exact sourceDirect candidate (by simp [member]))
                (targetDirect := by
                  intro candidate member
                  exact targetDirect candidate (by
                    rw [List.map_cons]
                    exact List.mem_cons_of_mem _ member))
                (mapHead := by
                  intro candidate member sourceItem compiled
                  exact mapHead candidate (by simp [member]) compiled)
                tailCompiled)
              let targetItems := CompiledItems.cons headResult.fst
                tailResult.fst
              refine ⟨⟨targetItems, ⟨?_, ?_⟩⟩⟩
              · change compileItems? target targetWf targetParent
                  targetContext targetBinders
                    (mapOccurrence occurrence :: tail.map mapOccurrence) _ =
                  some targetItems
                rw [compileItems?_cons, headResult.snd.fst,
                  tailResult.snd.fst]
                rfl
              · exact (ItemSeqIso.singleton headResult.snd.snd).append
                  tailResult.snd.snd

theorem compileItems?_length
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {direct : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d parent}
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf parent context binders occurrences direct =
      some items) :
    items.length = occurrences.length := by
  induction occurrences generalizing items with
  | nil =>
      simp only [compileItems?_nil] at compiled
      cases compiled
      rfl
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hhead : compileOccurrence? d hwf parent context binders occurrence
          (direct occurrence (by simp)) with
      | none => simp [hhead] at compiled
      | some head =>
          cases htail : compileItems? d hwf parent context binders tail (by
              intro candidate member
              exact direct candidate (by simp [member])) with
          | none => simp [hhead, htail] at compiled
          | some rest =>
              simp [hhead, htail] at compiled
              cases compiled
              exact congrArg Nat.succ (ih htail)

theorem compileItems?_get
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {direct : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d parent}
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf parent context binders occurrences direct =
      some items)
    (index : Fin occurrences.length) :
    compileOccurrence? d hwf parent context binders (occurrences.get index)
        (direct _ (List.get_mem occurrences index)) =
      some (items.get (Fin.cast (compileItems?_length hwf parent context
        binders compiled).symm index)) := by
  induction occurrences generalizing items with
  | nil => exact Fin.elim0 index
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hhead : compileOccurrence? d hwf parent context binders occurrence
          (direct occurrence (by simp)) with
      | none => simp [hhead] at compiled
      | some head =>
          cases htail : compileItems? d hwf parent context binders tail (by
              intro candidate member
              exact direct candidate (by simp [member])) with
          | none => simp [hhead, htail] at compiled
          | some rest =>
              simp [hhead, htail] at compiled
              cases compiled
              refine Fin.cases ?_ (fun tailIndex => ?_) index
              · simpa only [List.get, CompiledItems.get] using hhead
              · have result := ih htail tailIndex
                simpa only [List.get, CompiledItems.get] using result

theorem compileItems?_cons_inv
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (head : CompiledItem d context rels binders)
    (tail : CompiledItems d context rels binders)
    (direct : ∀ occurrence,
      occurrence ∈ (CompiledItems.cons head tail).origins →
        occurrence ∈ localOccurrences d parent)
    (compiled : compileItems? d hwf parent context binders
      (CompiledItems.cons head tail).origins direct =
        some (CompiledItems.cons head tail)) :
    compileOccurrence? d hwf parent context binders head.origin
        (direct head.origin (by simp [CompiledItems.origins])) = some head ∧
      compileItems? d hwf parent context binders tail.origins
        (fun occurrence member => direct occurrence (by
          simp [CompiledItems.origins, member])) = some tail := by
  simp only [CompiledItems.origins] at compiled
  rw [compileItems?_cons] at compiled
  cases headResult : compileOccurrence? d hwf parent context binders head.origin
      (direct head.origin (by simp [CompiledItems.origins])) with
  | none => simp [headResult] at compiled
  | some actualHead =>
      cases tailResult : compileItems? d hwf parent context binders tail.origins
          (fun occurrence member => direct occurrence (by
            simp [CompiledItems.origins, member])) with
      | none => simp [headResult, tailResult] at compiled
      | some actualTail =>
          simp [headResult, tailResult] at compiled
          obtain ⟨rfl, rfl⟩ := compiled
          exact ⟨rfl, rfl⟩

/-- A successful item sequence with one distinguished element factors into
the exact prefix, selected occurrence, and suffix computations. -/
def compileItems?_selected_inv
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (before : CompiledItems d context rels binders)
    (selected : CompiledItem d context rels binders)
    (suffix : CompiledItems d context rels binders)
    (direct : ∀ occurrence,
      occurrence ∈ (before.append (.cons selected suffix)).origins →
        occurrence ∈ localOccurrences d parent)
    (compiled : compileItems? d hwf parent context binders
      (before.append (.cons selected suffix)).origins direct =
        some (before.append (.cons selected suffix))) :
    compileItems? d hwf parent context binders before.origins
        (fun occurrence member => direct occurrence (by
          rw [CompiledItems.origins_append]
          exact List.mem_append_left _ member)) = some before ∧
      compileOccurrence? d hwf parent context binders selected.origin
        (direct selected.origin (by
          rw [CompiledItems.origins_append]
          exact List.mem_append_right _ (by simp [CompiledItems.origins]))) =
          some selected ∧
      compileItems? d hwf parent context binders suffix.origins
        (fun occurrence member => direct occurrence (by
          rw [CompiledItems.origins_append]
          exact List.mem_append_right _ (by
            simp [CompiledItems.origins, member]))) = some suffix := by
  cases before with
  | nil =>
      have fact := compileItems?_cons_inv hwf parent context binders selected
        suffix direct compiled
      exact ⟨rfl, fact.1, fact.2⟩
  | cons head tail =>
      obtain ⟨headCompiled, restCompiled⟩ := compileItems?_cons_inv hwf
        parent context binders head (tail.append (.cons selected suffix))
        direct compiled
      let restDirect : ∀ occurrence,
          occurrence ∈ (tail.append (.cons selected suffix)).origins →
            occurrence ∈ localOccurrences d parent := by
        intro occurrence member
        exact direct occurrence (by
          change occurrence ∈ head.origin ::
            (tail.append (.cons selected suffix)).origins
          exact List.mem_cons_of_mem _ member)
      obtain ⟨tailCompiled, selectedCompiled, suffixCompiled⟩ :=
        compileItems?_selected_inv hwf parent context binders tail selected
          suffix restDirect restCompiled
      refine ⟨?_, selectedCompiled, suffixCompiled⟩
      change compileItems? d hwf parent context binders
        (head.origin :: tail.origins) _ = some (.cons head tail)
      rw [compileItems?_cons, headCompiled, tailCompiled]
      rfl

/-- A successful compiled sequence remains successful after either side of
its stable origin partition is selected.  This is a grammar property of the
sole compiler result; callers do not replay the omitted occurrences. -/
theorem compileItems?_partition_success
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (classifier : LocalOccurrence d.regionCount d.nodeCount → Bool)
    (items : CompiledItems d context rels binders)
    (direct : ∀ occurrence, occurrence ∈ items.origins →
      occurrence ∈ localOccurrences d parent)
    (compiled : compileItems? d hwf parent context binders items.origins
      direct = some items) :
    compileItems? d hwf parent context binders
        (items.partition classifier).retained.origins
        (fun occurrence member => direct occurrence
          ((items.partition_retained_stable classifier).mem member)) =
      some (items.partition classifier).retained ∧
    compileItems? d hwf parent context binders
        (items.partition classifier).material.origins
        (fun occurrence member => direct occurrence
          ((items.partition_material_stable classifier).mem member)) =
      some (items.partition classifier).material := by
  cases items with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail =>
      obtain ⟨headCompiled, tailCompiled⟩ :=
        compileItems?_cons_inv hwf parent context binders head tail direct
          compiled
      let tailDirect : ∀ occurrence, occurrence ∈ tail.origins →
          occurrence ∈ localOccurrences d parent := by
        intro occurrence member
        exact direct occurrence (by simp [CompiledItems.origins, member])
      have divided := compileItems?_partition_success hwf parent context
        binders classifier tail tailDirect tailCompiled
      cases classified : classifier head.origin with
      | false =>
          constructor
          · simp only [CompiledItems.partition, classified]
            change compileItems? d hwf parent context binders
              (head.origin :: (tail.partition classifier).retained.origins)
              _ = some (.cons head (tail.partition classifier).retained)
            rw [compileItems?_cons]
            have headCompiled' : compileOccurrence? d hwf parent context
                binders head.origin
                  (direct head.origin (by simp [CompiledItems.origins])) =
                some head := by
              simpa only using headCompiled
            rw [headCompiled', divided.1]
            rfl
          · simpa [CompiledItems.partition, classified] using divided.2
      | true =>
          constructor
          · simpa [CompiledItems.partition, classified] using divided.1
          · simp only [CompiledItems.partition, classified]
            change compileItems? d hwf parent context binders
              (head.origin :: (tail.partition classifier).material.origins)
              _ = some (.cons head (tail.partition classifier).material)
            rw [compileItems?_cons]
            have headCompiled' : compileOccurrence? d hwf parent context
                binders head.origin
                  (direct head.origin (by simp [CompiledItems.origins])) =
                some head := by
              simpa only using headCompiled
            rw [headCompiled', divided.2]
            rfl
theorem compileOccurrence?_origin
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    {context : WireContext d} {binders : BinderContext d rels}
    (occurrence : LocalOccurrence d.regionCount d.nodeCount)
    (direct : occurrence ∈ localOccurrences d parent)
    {item : CompiledItem d context rels binders}
    (compiled : compileOccurrence? d hwf parent context binders occurrence
      direct = some item) :
    item.origin = occurrence := by
  cases occurrence with
  | node node =>
      rw [compileOccurrence?_node] at compiled
      exact compileNode?_origin compiled
  | child child =>
      cases hchild : d.regions child with
      | sheet =>
          rw [compileOccurrence?_child_sheet hwf parent child context binders
            direct hchild] at compiled
          contradiction
      | cut childParent =>
          have childParentEq : childParent = parent := by
            have parentEq :=
              (mem_localOccurrences_child d parent child).mp direct
            simpa [hchild, CRegion.parent?] using parentEq
          subst childParent
          rw [compileOccurrence?_child_cut hwf parent child context binders
            direct hchild] at compiled
          cases hbody : compileRegion? d hwf child context binders with
          | none => simp [hbody] at compiled
          | some body =>
              simp [hbody] at compiled
              subst item
              rfl
      | bubble childParent arity =>
          have childParentEq : childParent = parent := by
            have parentEq :=
              (mem_localOccurrences_child d parent child).mp direct
            simpa [hchild, CRegion.parent?] using parentEq
          subst childParent
          rw [compileOccurrence?_child_bubble hwf parent child context binders
            arity direct hchild] at compiled
          cases hbody : compileRegion? d hwf child context
              (binders.push child arity) with
          | none => simp [hbody] at compiled
          | some body =>
              simp [hbody] at compiled
              subst item
              rfl

theorem compileItems?_origins
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {direct : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d parent}
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf parent context binders occurrences direct =
      some items) :
    items.origins = occurrences := by
  induction occurrences generalizing items with
  | nil =>
      simp only [compileItems?_nil] at compiled
      cases compiled
      rfl
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hitem : compileOccurrence? d hwf parent context binders occurrence
          (direct occurrence (by simp)) with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileItems? d hwf parent context binders tail (by
              intro candidate member
              exact direct candidate (by simp [member])) with
          | none => simp [hitem, htail] at compiled
          | some rest =>
              simp [hitem, htail] at compiled
              cases compiled
              rw [CompiledItems.origins_cons,
                compileOccurrence?_origin hwf parent occurrence _ hitem,
                ih htail]

theorem CompilerCall.compile?_eq_compileItems?
    (hwf : d.WellFormed) (call : CompilerCall d) :
    call.compile? d hwf = (do
      let items ← compileItems? d hwf call.origin call.fullContext
        call.binders (localOccurrences d call.origin) (fun _ member => member)
      pure (.mk items)) := by
  rw [CompilerCall.compile?]
  rfl

theorem compileItems?_congr_occurrences
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    {first second : List (LocalOccurrence d.regionCount d.nodeCount)}
    (equal : first = second)
    (firstDirect : ∀ occurrence, occurrence ∈ first →
      occurrence ∈ localOccurrences d parent)
    (secondDirect : ∀ occurrence, occurrence ∈ second →
      occurrence ∈ localOccurrences d parent) :
    compileItems? d hwf parent context binders first firstDirect =
      compileItems? d hwf parent context binders second secondDirect := by
  subst second
  congr

theorem CompilerCall.compile?_items_of_success
    (hwf : d.WellFormed) (call : CompilerCall d)
    {items : CompiledItems d call.fullContext call.rels call.binders}
    (compiled : call.compile? d hwf = some (.mk items)) :
    compileItems? d hwf call.origin call.fullContext call.binders
      (localOccurrences d call.origin) (fun _ member => member) = some items := by
  rw [CompilerCall.compile?_eq_compileItems? hwf] at compiled
  obtain ⟨resultItems, result, resultEq⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have itemsEq : resultItems = items := by
    cases call <;> cases resultEq <;> rfl
  subst resultItems
  exact result

/-- A successful nested-region call exposes the exact ordered item sequence
produced by that call. -/
theorem compileRegion?_items_of_success
    {d : Diagram} {rels : RelCtx}
    (hwf : d.WellFormed) (origin : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    {body : CompiledRegion d
      (@CompilerCall.nested d origin context rels binders)}
    (compiled : compileRegion? d hwf origin context binders = some body) :
    compileItems? d hwf origin (@WireContext.extend d context origin) binders
      (localOccurrences d origin) (fun _ member => member) =
        some (@CompiledRegion.items d
          (@CompilerCall.nested d origin context rels binders) body :
            CompiledItems d (@WireContext.extend d context origin) rels binders) := by
  cases body with
  | mk items =>
      exact CompilerCall.compile?_items_of_success hwf
        (.nested origin context rels binders) compiled

theorem compileRegion?_eq_compileItems?
    (hwf : d.WellFormed) (origin : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels) :
    compileRegion? d hwf origin context binders =
      (compileItems? d hwf origin (context.extend origin) binders
        (localOccurrences d origin) (fun _ member => member)).map
          (fun items => (CompiledRegion.mk items : CompiledRegion d
            (.nested origin context rels binders))) := by
  unfold compileRegion?
  rw [CompilerCall.compile?_eq_compileItems?]
  change (do
    let items ← compileItems? d hwf origin (context.extend origin) binders
      (localOccurrences d origin) (fun _ member => member)
    pure (CompiledRegion.mk items : CompiledRegion d
      (.nested origin context rels binders))) = _
  cases compileItems? d hwf origin (context.extend origin) binders
      (localOccurrences d origin) (fun _ member => member) <;> rfl

theorem compileRoot?_eq_compileItems?
    (hwf : d.WellFormed) (ambient locals : WireContext d) :
    compileRoot? d hwf ambient locals = (do
      let items ← compileItems? d hwf d.root (ambient ++ locals)
        BinderContext.empty (localOccurrences d d.root) (fun _ member => member)
      pure (CompiledRegion.mk items : CompiledRegion d
        (.root ambient locals))) := by
  unfold compileRoot?
  simpa only [CompilerCall.origin, CompilerCall.fullContext,
    CompilerCall.outerContext, CompilerCall.localContext,
    CompilerCall.rels, CompilerCall.binders] using
    CompilerCall.compile?_eq_compileItems? hwf
    (CompilerCall.root ambient locals)

theorem compileRoot?_localCount
    (hwf : d.WellFormed)
    {body : CompiledRegion d (.root ambient locals)}
    (_compiled : compileRoot? d hwf ambient locals = some body) :
    body.localCount = locals.length := rfl

theorem compileNode?_complete
    (hwf : d.WellFormed)
    {context : WireContext d} {binders : BinderContext d rels}
    {region : Fin d.regionCount}
    (hwires : context.Covers region) (hbinders : binders.Covers region)
    {node : Fin d.nodeCount} (hregion : (d.nodes node).region = region) :
    ∃ item, compileNode? d context binders node = some item := by
  cases hnode : d.nodes node with
  | atom nodeRegion binder =>
      have hnodeRegion : nodeRegion = region := by simpa [hnode] using hregion
      subst nodeRegion
      obtain ⟨parent, arity, hbubble⟩ :=
        BinderContext.checked_atom_binder_is_bubble hwf hnode
      obtain ⟨relation, hrelation⟩ :=
        BinderContext.checked_atom_binder_available hwf hbinders hnode hbubble
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf
        hwires (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [Diagram.RequiresPort, hnode, hbubble]
          exact ⟨index, rfl⟩)
      exact ⟨CompiledItem.node node (Item.atom relation arguments), by
        simp [compileNode?, hnode, hrelation, harguments]⟩
  | identity nodeRegion arity =>
      obtain ⟨arguments, harguments⟩ := checked_resolvePorts?_complete hwf
        hwires (node := node) hregion arity (fun index => .arg index) (by
          intro index
          simp [Diagram.RequiresPort, hnode]
          exact ⟨index, rfl⟩)
      exact ⟨CompiledItem.node node (Item.identity arity arguments), by
        simp [compileNode?, hnode, harguments]⟩

/-- Exact wire and binder contexts make the sole checked compiler total. -/
theorem CompilerCall.compile?_complete
    (hwf : d.WellFormed) (call : CompilerCall d)
    (hwires : call.fullContext.Exact call.origin)
    (hbinders : call.binders.Covers call.origin) :
    ∃ body, call.compile? d hwf = some body := by
  have occurrenceComplete : ∀ occurrence
      (direct : occurrence ∈ localOccurrences d call.origin),
      ∃ item, compileOccurrence? d hwf call.origin call.fullContext
        call.binders occurrence direct = some item := by
    intro occurrence direct
    cases occurrence with
    | node node =>
        have hregion :=
          (mem_localOccurrences_node d call.origin node).mp direct
        simpa only [compileOccurrence?_node] using
          compileNode?_complete hwf hwires.covers hbinders hregion
    | child child =>
        have hparent :=
          (mem_localOccurrences_child d call.origin child).mp direct
        cases hchild : d.regions child with
        | sheet =>
            have hchildRoot : child = d.root :=
              hwf.only_root_is_sheet child hchild
            subst child
            rw [hwf.root_is_sheet] at hparent
            simp [CRegion.parent?] at hparent
        | cut parent =>
            have hparentEq : parent = call.origin := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            have childWires := hwires.extend_child hwf hparent
            have childBinders :=
              BinderContext.covers_cut_child hbinders hchild
            obtain ⟨body, bodyCompiled⟩ :=
              CompilerCall.compile?_complete hwf
                (.nested child call.fullContext call.rels call.binders)
                childWires childBinders
            change compileRegion? d hwf child call.fullContext call.binders =
              some body at bodyCompiled
            refine ⟨CompiledItem.cut body, ?_⟩
            rw [compileOccurrence?_child_cut hwf call.origin child
              call.fullContext call.binders direct hchild, bodyCompiled]
            rfl
        | bubble parent arity =>
            have hparentEq : parent = call.origin := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            have childWires := hwires.extend_child hwf hparent
            have childBinders :=
              BinderContext.push_covers_bubble_child hbinders hchild
            obtain ⟨body, bodyCompiled⟩ :=
              CompilerCall.compile?_complete hwf
                (.nested child call.fullContext (arity :: call.rels)
                  (call.binders.push child arity)) childWires childBinders
            change compileRegion? d hwf child call.fullContext
              (call.binders.push child arity) = some body at bodyCompiled
            refine ⟨CompiledItem.bubble arity body, ?_⟩
            rw [compileOccurrence?_child_bubble hwf call.origin child
              call.fullContext call.binders arity direct hchild, bodyCompiled]
            rfl
  have compileItemsComplete : ∀
      (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
      (direct : ∀ occurrence, occurrence ∈ occurrences →
        occurrence ∈ localOccurrences d call.origin),
      ∃ items, compileItems? d hwf call.origin call.fullContext call.binders
        occurrences direct = some items := by
    intro occurrences direct
    induction occurrences with
    | nil =>
        exact ⟨.nil, compileItems?_nil hwf call.origin call.fullContext
          call.binders direct⟩
    | cons occurrence tail ih =>
        obtain ⟨head, headCompiled⟩ := occurrenceComplete occurrence
          (direct occurrence (by simp))
        have tailDirect : ∀ candidate, candidate ∈ tail →
            candidate ∈ localOccurrences d call.origin := by
          intro candidate member
          exact direct candidate (by simp [member])
        obtain ⟨rest, restCompiled⟩ := ih tailDirect
        refine ⟨.cons head rest, ?_⟩
        rw [compileItems?_cons hwf call.origin call.fullContext call.binders
          occurrence tail direct, headCompiled, restCompiled]
        rfl
  obtain ⟨items, itemsCompiled⟩ := compileItemsComplete
    (localOccurrences d call.origin) (fun _ member => member)
  refine ⟨.mk items, ?_⟩
  rw [CompilerCall.compile?_eq_compileItems?, itemsCompiled]
  rfl
termination_by (descendantRegions d call.origin).length
decreasing_by
  all_goals exact descendantRegions_length_lt_of_parent hwf hparent

theorem openRootWires_exact
    {d : OpenDiagram} (hwf : d.WellFormed) :
    WireContext.Exact d.rootWires d.diagram.root := by
  constructor
  · exact d.rootWires_nodup
  · intro wire
    rw [OpenDiagram.mem_rootWires_iff d hwf]
    constructor
    · intro hscope
      rw [hscope]
      exact Diagram.Encloses.refl d.diagram d.diagram.root
    · exact encloses_sheet_eq hwf.diagram_well_formed.root_is_sheet

theorem closedRootWires_exact (hwf : d.WellFormed) :
    WireContext.Exact
      (([] : WireContext d) ++ exactScopeWires d d.root) d.root := by
  simpa [WireContext.extend] using WireContext.root_exact hwf

theorem compileRoot?_complete
    (hwf : d.WellFormed)
    (ambient locals : WireContext d)
    (hwires : WireContext.Exact (ambient ++ locals) d.root) :
    ∃ body, compileRoot? d hwf ambient locals = some body := by
  exact CompilerCall.compile?_complete hwf (.root ambient locals) hwires
    (BinderContext.empty_covers_root hwf)

end VisualProof.Concrete.Elaboration
