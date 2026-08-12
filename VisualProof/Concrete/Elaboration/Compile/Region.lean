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

theorem CompilerCall.compile?_eq_compileItems?
    (hwf : d.WellFormed) (call : CompilerCall d) :
    call.compile? d hwf = (do
      let items ← compileItems? d hwf call.origin call.fullContext
        call.binders (localOccurrences d call.origin) (fun _ member => member)
      pure (.mk items)) := by
  rw [CompilerCall.compile?]
  rfl

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

end VisualProof.Concrete.Elaboration
