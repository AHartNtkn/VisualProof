import VisualProof.Concrete.Elaboration.Compile.Kernel

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

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
      let nodes ← compileItemsWith? d call.origin
        (fun child _hparent context binders =>
          compile? d hwf (.nested child context _ binders))
        call.fullContext call.binders (localNodeOccurrences d call.origin)
        (fun _ member => List.mem_append_left _ member)
      let children ← compileItemsWith? d call.origin
        (fun child _hparent context binders =>
          compile? d hwf (.nested child context _ binders))
        call.fullContext call.binders (localChildOccurrences d call.origin)
        (fun _ member => List.mem_append_right _ member)
      pure (.mk nodes children)
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

theorem compileItems?_append
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels)
    (first second : List (LocalOccurrence d.regionCount d.nodeCount))
    (direct : ∀ occurrence, occurrence ∈ first ++ second →
      occurrence ∈ localOccurrences d parent)
    {firstItems secondItems : CompiledItems d context rels binders}
    (firstCompiled : compileItems? d hwf parent context binders first
      (fun occurrence member => direct occurrence
        (List.mem_append_left second member)) = some firstItems)
    (secondCompiled : compileItems? d hwf parent context binders second
      (fun occurrence member => direct occurrence
        (List.mem_append_right first member)) = some secondItems) :
    compileItems? d hwf parent context binders (first ++ second) direct =
      some (firstItems.append secondItems) := by
  induction first generalizing firstItems with
  | nil =>
      simp only [compileItems?_nil] at firstCompiled
      cases firstCompiled
      simpa using secondCompiled
  | cons head tail ih =>
      rw [compileItems?_cons] at firstCompiled
      change compileItems? d hwf parent context binders
        (head :: (tail ++ second)) _ = some (firstItems.append secondItems)
      rw [compileItems?_cons hwf parent context binders head
        (tail ++ second)]
      cases hhead : compileOccurrence? d hwf parent context binders head
          (direct head (by simp)) with
      | none => simp [hhead] at firstCompiled
      | some headItem =>
          cases htail : compileItems? d hwf parent context binders tail
              (fun occurrence member => direct occurrence (by simp [member])) with
          | none => simp [hhead, htail] at firstCompiled
          | some tailItems =>
              simp [hhead, htail] at firstCompiled
              obtain ⟨rfl, rfl⟩ := firstCompiled
              rw [ih (fun occurrence member =>
                direct occurrence (by simp [member])) htail secondCompiled]
              rfl

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

theorem CompilerCall.compile?_eq_compileBlocks?
    (hwf : d.WellFormed) (call : CompilerCall d) :
    call.compile? d hwf = (do
      let nodes ← compileItems? d hwf call.origin call.fullContext
        call.binders (localNodeOccurrences d call.origin)
          (fun _ member => List.mem_append_left _ member)
      let children ← compileItems? d hwf call.origin call.fullContext
        call.binders (localChildOccurrences d call.origin)
          (fun _ member => List.mem_append_right _ member)
      pure (.mk nodes children)) := by
  rw [CompilerCall.compile?]
  rfl

/-- A successful call with one direct bubble occurrence exposes that exact
child result. This is the canonical grammar inversion used by source
consumers following a checked singleton spine. -/
theorem CompilerCall.compile?_singleton_bubble
    (hwf : d.WellFormed) (call : CompilerCall d)
    (child : Fin d.regionCount) (arity : Nat)
    (nodes : localNodeOccurrences d call.origin = [])
    (children : localChildOccurrences d call.origin = [.child child])
    (region : d.regions child = .bubble call.origin arity)
    {body : CompiledRegion d call}
    (compiled : call.compile? d hwf = some body) :
    ∃ childBody : CompiledRegion d
        (.nested child call.fullContext (arity :: call.rels)
          (call.binders.push child arity)),
      compileRegion? d hwf child call.fullContext
          (call.binders.push child arity) = some childBody ∧
        body = .mk .nil (.cons (.bubble arity childBody) .nil) := by
  rw [CompilerCall.compile?_eq_compileBlocks?] at compiled
  simp only [nodes, children, compileItems?_nil] at compiled
  rw [compileItems?_cons] at compiled
  let direct : LocalOccurrence.child child ∈
      localOccurrences d call.origin := by
    simp [localOccurrences, children]
  cases hhead : compileOccurrence? d hwf call.origin call.fullContext
      call.binders (.child child) direct with
  | none =>
      simp [hhead] at compiled
  | some head =>
      have hsame := compileOccurrence?_child_bubble hwf call.origin child
        call.fullContext call.binders arity direct region
      rw [hhead] at hsame
      cases hchild : compileRegion? d hwf child call.fullContext
          (call.binders.push child arity) with
      | none => simp [hchild] at hsame
      | some childBody =>
          simp [hchild] at hsame
          subst head
          simp [hhead] at compiled
          exact ⟨childBody, rfl, compiled.symm⟩

theorem compileRegion?_eq_compileBlocks?
    (hwf : d.WellFormed) (origin : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels) :
    compileRegion? d hwf origin context binders = (do
      let nodes ← compileItems? d hwf origin
        (CompilerCall.nested origin context rels binders).fullContext binders
        (localNodeOccurrences d origin)
          (fun _ member => List.mem_append_left _ member)
      let children ← compileItems? d hwf origin
        (CompilerCall.nested origin context rels binders).fullContext binders
        (localChildOccurrences d origin)
          (fun _ member => List.mem_append_right _ member)
      pure (@CompiledRegion.mk d
        (.nested origin context rels binders) nodes children : CompiledRegion d
        (.nested origin context rels binders))) := by
  unfold compileRegion?
  simpa only [CompilerCall.origin, CompilerCall.fullContext,
    CompilerCall.outerContext, CompilerCall.localContext,
    CompilerCall.rels, CompilerCall.binders] using
      CompilerCall.compile?_eq_compileBlocks? hwf
        (CompilerCall.nested origin context rels binders)

theorem compileRoot?_eq_compileBlocks?
    (hwf : d.WellFormed) (ambient locals : WireContext d) :
    compileRoot? d hwf ambient locals = (do
      let nodes ← compileItems? d hwf d.root (ambient ++ locals)
        BinderContext.empty (localNodeOccurrences d d.root)
          (fun _ member => List.mem_append_left _ member)
      let children ← compileItems? d hwf d.root (ambient ++ locals)
        BinderContext.empty (localChildOccurrences d d.root)
          (fun _ member => List.mem_append_right _ member)
      pure (CompiledRegion.mk nodes children : CompiledRegion d
        (.root ambient locals))) := by
  unfold compileRoot?
  simpa only [CompilerCall.origin, CompilerCall.fullContext,
    CompilerCall.outerContext, CompilerCall.localContext,
    CompilerCall.rels, CompilerCall.binders] using
    CompilerCall.compile?_eq_compileBlocks? hwf
    (CompilerCall.root ambient locals)

theorem compileRoot?_localCount
    (hwf : d.WellFormed)
    {body : CompiledRegion d (.root ambient locals)}
    (_compiled : compileRoot? d hwf ambient locals = some body) :
    body.localCount = locals.length := rfl

private theorem compileNode?_complete
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
  obtain ⟨nodes, nodesCompiled⟩ := compileItemsComplete
    (localNodeOccurrences d call.origin)
      (fun _ member => List.mem_append_left _ member)
  obtain ⟨children, childrenCompiled⟩ := compileItemsComplete
    (localChildOccurrences d call.origin)
      (fun _ member => List.mem_append_right _ member)
  refine ⟨.mk nodes children, ?_⟩
  rw [CompilerCall.compile?_eq_compileBlocks?, nodesCompiled,
    childrenCompiled]
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
