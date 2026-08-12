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
  have distinct : descendantRegions d child ≠ descendantRegions d parent := by
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
    (recurse : ∀ {nestedRels : RelCtx}
      (child : Fin d.regionCount),
      (d.regions child).parent? = some parent →
      (context : WireContext d) →
      (binders : BinderContext d nestedRels) →
      Option (CompiledRegion d
        (.nested child context nestedRels binders)))
    (context : WireContext d) (binders : BinderContext d rels) :
    (occurrence : LocalOccurrence d.regionCount d.nodeCount) →
    (direct : ∀ child, occurrence = .child child →
      (d.regions child).parent? = some parent) →
    Option (CompiledItem d context rels binders)
  | .node node, _ => compileNode? d context binders node
  | .child child, direct =>
      match d.regions child with
      | .sheet => none
      | .cut _ => do
          let body ← recurse child (direct child rfl) context binders
          pure (.cut body)
      | .bubble _ arity => do
          let body ← recurse child (direct child rfl) context
            (binders.push child arity)
          pure (.bubble arity body)

private def compileItemsWith? (d : Diagram)
    (parent : Fin d.regionCount)
    (recurse : ∀ {nestedRels : RelCtx}
      (child : Fin d.regionCount),
      (d.regions child).parent? = some parent →
      (context : WireContext d) →
      (binders : BinderContext d nestedRels) →
      Option (CompiledRegion d
        (.nested child context nestedRels binders)))
    (context : WireContext d) (binders : BinderContext d rels) :
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount)) →
    (direct : ∀ child, LocalOccurrence.child child ∈ occurrences →
      (d.regions child).parent? = some parent) →
    Option (CompiledItems d context rels binders)
  | [], _ => some .nil
  | occurrence :: tail, direct => do
      let head ← compileOccurrenceWith? d parent recurse context binders
        occurrence (fun child equality => direct child (by simp [equality]))
      let rest ← compileItemsWith? d parent recurse context binders tail
        (fun child member => direct child (by simp [member]))
      pure (.cons head rest)

/-- The sole nested compiler. Termination is justified privately by strict
direct-child descent in a well-formed diagram; no counter enters its API or
result type. -/
def compileRegion? (d : Diagram) (hwf : d.WellFormed) :
    (origin : Fin d.regionCount) → (context : WireContext d) →
      (binders : BinderContext d rels) →
      Option (CompiledRegion d (.nested origin context rels binders))
  | origin, context, binders => do
      let items ← compileItemsWith? d origin
        (fun child direct childContext childBinders => by
          have _direct := direct
          exact compileRegion? d hwf child childContext childBinders)
        (context.extend origin) binders (localOccurrences d origin)
        (fun child member => (mem_localOccurrences_child d origin child).mp member)
      pure (.mk items)
termination_by origin => (descendantRegions d origin).length
decreasing_by
  exact descendantRegions_length_lt_of_parent hwf direct

/-- Compile one occurrence using the fixed well-founded region compiler. -/
def compileOccurrence? (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels) :
    LocalOccurrence d.regionCount d.nodeCount →
      Option (CompiledItem d context rels binders)
  | .node node => compileNode? d context binders node
  | .child child =>
      match d.regions child with
      | .sheet => none
      | .cut _ => do
          let body ← compileRegion? d hwf child context binders
          pure (.cut body)
      | .bubble _ arity => do
          let body ← compileRegion? d hwf child context
            (binders.push child arity)
          pure (.bubble arity body)

/-- Compile an ordinary ordered occurrence list. -/
def compileItems? (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels) :
    List (LocalOccurrence d.regionCount d.nodeCount) →
      Option (CompiledItems d context rels binders)
  | [] => some .nil
  | occurrence :: tail => do
      let head ← compileOccurrence? d hwf context binders occurrence
      let rest ← compileItems? d hwf context binders tail
      pure (.cons head rest)

/-- Compile the exact root call. -/
def compileRoot? (d : Diagram) (hwf : d.WellFormed)
    (ambient locals : WireContext d) :
    Option (CompiledRegion d (.root ambient locals)) := do
  let items ← compileItems? d hwf (ambient ++ locals) BinderContext.empty
    (localOccurrences d d.root)
  pure (.mk items)

/-- Run the sole compiler at the exact call described by its signature. -/
def CompilerCall.compile? (hwf : d.WellFormed) :
    (call : CompilerCall d) → Option (CompiledRegion d call)
  | .root ambient locals => compileRoot? d hwf ambient locals
  | .nested origin context _ binders =>
      compileRegion? d hwf origin context binders

@[simp] theorem CompilerCall.compile?_root (hwf : d.WellFormed)
    (ambient locals : WireContext d) :
    (CompilerCall.root ambient locals).compile? hwf =
      compileRoot? d hwf ambient locals := rfl

@[simp] theorem CompilerCall.compile?_nested (hwf : d.WellFormed)
    {rels : RelCtx} (origin : Fin d.regionCount)
    (context : WireContext d) (binders : BinderContext d rels) :
    (CompilerCall.nested origin context rels binders).compile? hwf =
      compileRegion? d hwf origin context binders := rfl

@[simp] theorem compileOccurrence?_node (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels)
    (node : Fin d.nodeCount) :
    compileOccurrence? d hwf context binders (.node node) =
      compileNode? d context binders node := rfl

theorem compileOccurrence?_child_sheet (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels)
    (child : Fin d.regionCount) (shape : d.regions child = .sheet) :
    compileOccurrence? d hwf context binders (.child child) = none := by
  simp [compileOccurrence?, shape]

theorem compileOccurrence?_child_cut (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels)
    (child parent : Fin d.regionCount)
    (shape : d.regions child = .cut parent) :
    compileOccurrence? d hwf context binders (.child child) =
      (do
        let body ← compileRegion? d hwf child context binders
        pure (.cut body)) := by
  simp [compileOccurrence?, shape]

theorem compileOccurrence?_child_bubble (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels)
    (child parent : Fin d.regionCount) (arity : Nat)
    (shape : d.regions child = .bubble parent arity) :
    compileOccurrence? d hwf context binders (.child child) =
      (do
        let body ← compileRegion? d hwf child context
          (binders.push child arity)
        pure (.bubble arity body)) := by
  simp [compileOccurrence?, shape]

@[simp] theorem compileItems?_nil (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels) :
    compileItems? d hwf context binders [] = some .nil := rfl

@[simp] theorem compileItems?_cons (d : Diagram) (hwf : d.WellFormed)
    (context : WireContext d) (binders : BinderContext d rels)
    (head : LocalOccurrence d.regionCount d.nodeCount) (tail : List _) :
    compileItems? d hwf context binders (head :: tail) = (do
      let compiledHead ← compileOccurrence? d hwf context binders head
      let compiledTail ← compileItems? d hwf context binders tail
      pure (.cons compiledHead compiledTail)) := rfl

theorem compileOccurrence?_origin
    {item : CompiledItem d context rels binders}
    (compiled : compileOccurrence? d hwf context binders occurrence =
      some item) : item.origin = occurrence := by
  cases occurrence with
  | node node => exact compileNode?_origin compiled
  | child child =>
      cases shape : d.regions child with
      | sheet => simp [compileOccurrence?, shape] at compiled
      | cut parent =>
          simp only [compileOccurrence?, shape] at compiled
          cases bodyResult : compileRegion? d hwf child context binders with
          | none => simp [bodyResult] at compiled
          | some body =>
              simp [bodyResult] at compiled
              cases compiled
              rfl
      | bubble parent arity =>
          simp only [compileOccurrence?, shape] at compiled
          cases bodyResult : compileRegion? d hwf child context
              (binders.push child arity) with
          | none => simp [bodyResult] at compiled
          | some body =>
              simp [bodyResult] at compiled
              cases compiled
              rfl

theorem compileItems?_origins
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf context binders occurrences = some items) :
    items.origins = occurrences := by
  induction occurrences generalizing items with
  | nil =>
      simp only [compileItems?_nil] at compiled
      cases compiled
      rfl
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases headResult : compileOccurrence? d hwf context binders occurrence with
      | none => simp [headResult] at compiled
      | some head =>
          cases tailResult : compileItems? d hwf context binders tail with
          | none => simp [headResult, tailResult] at compiled
          | some rest =>
              simp [headResult, tailResult] at compiled
              cases compiled
              rw [CompiledItems.origins_cons,
                compileOccurrence?_origin headResult, ih tailResult]

theorem compileItems?_length
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf context binders occurrences = some items) :
    items.length = occurrences.length := by
  rw [CompiledItems.length_eq_origins_length,
    compileItems?_origins compiled]

theorem compileItems?_get
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf context binders occurrences = some items)
    (index : Fin occurrences.length) :
    compileOccurrence? d hwf context binders (occurrences.get index) =
      some (items.get (Fin.cast (compileItems?_length compiled).symm index)) := by
  induction occurrences generalizing items with
  | nil => exact Fin.elim0 index
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases headResult : compileOccurrence? d hwf context binders occurrence with
      | none => simp [headResult] at compiled
      | some head =>
          cases tailResult : compileItems? d hwf context binders tail with
          | none => simp [headResult, tailResult] at compiled
          | some rest =>
              simp [headResult, tailResult] at compiled
              cases compiled
              refine Fin.cases ?_ (fun tailIndex => ?_) index
              · simpa only [List.get, CompiledItems.get] using headResult
              · simpa only [List.get, CompiledItems.get] using
                  ih tailResult tailIndex

theorem compileItems?_complete
    (d : Diagram) (hwf : d.WellFormed) (context : WireContext d)
    (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    (success : ∀ occurrence, occurrence ∈ occurrences →
      ∃ item, compileOccurrence? d hwf context binders occurrence = some item) :
    ∃ items, compileItems? d hwf context binders occurrences = some items := by
  induction occurrences with
  | nil => exact ⟨.nil, rfl⟩
  | cons occurrence tail ih =>
      obtain ⟨head, headResult⟩ := success occurrence (by simp)
      obtain ⟨rest, tailResult⟩ := ih (by
        intro candidate member
        exact success candidate (by simp [member]))
      exact ⟨.cons head rest, by
        simp [compileItems?, headResult, tailResult]⟩

/-- Every well-formed node compiles in an exact wire context covered by its
lexical binder context. -/
theorem compileNode?_complete
    (hwf : d.WellFormed)
    {context : WireContext d} {binders : BinderContext d rels}
    {region : Fin d.regionCount}
    (exact : context.Exact region) (covers : binders.Covers region)
    {node : Fin d.nodeCount} (nodeRegion : (d.nodes node).region = region) :
    ∃ item, compileNode? d context binders node = some item := by
  cases nodeShape : d.nodes node with
  | atom actualRegion binder =>
      have actualRegionEq : actualRegion = region := by
        simpa [nodeShape] using nodeRegion
      subst actualRegion
      obtain ⟨parent, arity, bubble⟩ :=
        BinderContext.checked_atom_binder_is_bubble hwf nodeShape
      obtain ⟨relation, relationResult⟩ :=
        BinderContext.checked_atom_binder_available hwf covers nodeShape bubble
      obtain ⟨arguments, argumentsResult⟩ := checked_resolvePorts?_complete hwf
        exact.covers (node := node) nodeRegion arity (fun index => .arg index) (by
          intro index
          simp [Diagram.RequiresPort, nodeShape, bubble]
          exact ⟨index, rfl⟩)
      exact ⟨CompiledItem.node node (Item.atom relation arguments), by
        simp [compileNode?, nodeShape, relationResult, argumentsResult]⟩
  | identity actualRegion arity =>
      obtain ⟨arguments, argumentsResult⟩ := checked_resolvePorts?_complete hwf
        exact.covers (node := node) nodeRegion arity (fun index => .arg index) (by
          intro index
          simp [Diagram.RequiresPort, nodeShape]
          exact ⟨index, rfl⟩)
      exact ⟨CompiledItem.node node (Item.identity arity arguments), by
        simp [compileNode?, nodeShape, argumentsResult]⟩

private theorem compileItemsWith?_complete
    (d : Diagram) (parent : Fin d.regionCount)
    (recurse : ∀ {nestedRels : RelCtx}
      (child : Fin d.regionCount),
      (d.regions child).parent? = some parent →
      (context : WireContext d) →
      (binders : BinderContext d nestedRels) →
      Option (CompiledRegion d (.nested child context nestedRels binders)))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    (direct : ∀ child, LocalOccurrence.child child ∈ occurrences →
      (d.regions child).parent? = some parent)
    (success : ∀ (occurrence) (member : occurrence ∈ occurrences),
      ∃ item, compileOccurrenceWith? d parent recurse context binders occurrence
        (fun child equality => direct child (by
          simpa [← equality] using member)) = some item) :
    ∃ items, compileItemsWith? d parent recurse context binders occurrences
      direct = some items := by
  induction occurrences with
  | nil => exact ⟨.nil, rfl⟩
  | cons occurrence tail ih =>
      obtain ⟨head, headResult⟩ := success occurrence (by simp)
      obtain ⟨rest, tailResult⟩ := ih
        (fun child member => direct child (by simp [member])) (by
          intro candidate member
          exact success candidate (by simp [member]))
      exact ⟨.cons head rest, by
        simp [compileItemsWith?, headResult, tailResult]⟩

/-- Exact and covering call inputs produce the unique successful result of the
well-founded nested compiler. -/
private noncomputable def compileRegionComplete
    (hwf : d.WellFormed) :
    ∀ {rels : RelCtx} (region : Fin d.regionCount)
      (context : WireContext d) (binders : BinderContext d rels),
      (context.extend region).Exact region → binders.Covers region →
      {body // compileRegion? d hwf region context binders = some body}
  | rels, region, context, binders, exact, covers => by
      let extended := context.extend region
      have extendedExact : extended.Exact region := by
        simpa [extended] using exact
      let recurse := fun {nestedRels : RelCtx}
          (child : Fin d.regionCount)
          (_direct : (d.regions child).parent? = some region)
          (childContext : WireContext d)
          (childBinders : BinderContext d nestedRels) =>
        compileRegion? d hwf child childContext childBinders
      have direct : ∀ child,
          LocalOccurrence.child child ∈ localOccurrences d region →
          (d.regions child).parent? = some region := by
        intro child member
        exact (mem_localOccurrences_child d region child).mp member
      have occurrenceSuccess : ∀ (occurrence)
          (member : occurrence ∈ localOccurrences d region),
          ∃ item, compileOccurrenceWith? d region recurse extended binders
            occurrence (fun child equality => direct child (by
              simpa [← equality] using member)) = some item := by
        intro occurrence member
        cases occurrence with
        | node node =>
            have nodeRegion := (mem_localOccurrences_node d region node).mp member
            simpa [compileOccurrenceWith?, recurse] using
              compileNode?_complete hwf extendedExact covers nodeRegion
        | child child =>
            have childDirect := direct child member
            cases childShape : d.regions child with
            | sheet =>
                have childRoot : child = d.root :=
                  hwf.only_root_is_sheet child childShape
                subst child
                rw [hwf.root_is_sheet] at childDirect
                simp [CRegion.parent?] at childDirect
            | cut parent =>
                have parentEq : parent = region := by
                  simpa [childShape, CRegion.parent?] using childDirect
                subst parent
                have childExact := extendedExact.extend_child hwf childDirect
                have childCovers := BinderContext.covers_cut_child covers childShape
                obtain ⟨body, bodyResult⟩ := compileRegionComplete hwf child
                  extended binders childExact childCovers
                exact ⟨.cut body, by
                  simp [compileOccurrenceWith?, recurse, childShape, bodyResult]⟩
            | bubble parent arity =>
                have parentEq : parent = region := by
                  simpa [childShape, CRegion.parent?] using childDirect
                subst parent
                have childExact := extendedExact.extend_child hwf childDirect
                have childCovers :=
                  BinderContext.push_covers_bubble_child covers childShape
                obtain ⟨body, bodyResult⟩ := compileRegionComplete hwf child
                  extended (binders.push child arity) childExact childCovers
                exact ⟨.bubble arity body, by
                  simp [compileOccurrenceWith?, recurse, childShape, bodyResult]⟩
      let itemsExist := compileItemsWith?_complete d region recurse
        extended binders (localOccurrences d region) direct occurrenceSuccess
      let items := Classical.choose itemsExist
      have itemsResult := Classical.choose_spec itemsExist
      refine ⟨.mk items, ?_⟩
      rw [compileRegion?]
      change (do
        let compiledItems ← compileItemsWith? d region recurse extended binders
          (localOccurrences d region) direct
        pure (@CompiledRegion.mk d (.nested region context rels binders)
          compiledItems)) =
          some (@CompiledRegion.mk d (.nested region context rels binders) items)
      rw [itemsResult]
      rfl
termination_by _ region _ _ _ _ =>
  (descendantRegions d region).length
decreasing_by
  all_goals
    exact descendantRegions_length_lt_of_parent hwf childDirect

theorem compileRegion?_complete
    (hwf : d.WellFormed) {region : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    (exact : (context.extend region).Exact region)
    (covers : binders.Covers region) :
    ∃ body, compileRegion? d hwf region context binders = some body :=
  let result := compileRegionComplete hwf region context binders exact covers
  ⟨result.1, result.2⟩

theorem openRootWires_exact {d : OpenDiagram} (hwf : d.WellFormed) :
    WireContext.Exact d.rootWires d.diagram.root := by
  constructor
  · exact d.rootWires_nodup
  · intro wire
    rw [OpenDiagram.mem_rootWires_iff d hwf]
    constructor
    · intro scope
      rw [scope]
      exact Diagram.Encloses.refl d.diagram d.diagram.root
    · exact encloses_sheet_eq hwf.diagram_well_formed.root_is_sheet

theorem closedRootWires_exact (hwf : d.WellFormed) :
    WireContext.Exact (([] : WireContext d) ++ exactScopeWires d d.root)
      d.root := by
  simpa [WireContext.extend] using WireContext.root_exact hwf

theorem compileRoot?_complete (hwf : d.WellFormed)
    (ambient locals : WireContext d)
    (exact : WireContext.Exact (ambient ++ locals) d.root) :
    ∃ body, compileRoot? d hwf ambient locals = some body := by
  have covers : (BinderContext.empty : BinderContext d []).Covers d.root :=
    BinderContext.empty_covers_root hwf
  obtain ⟨items, itemsResult⟩ := compileItems?_complete d hwf
    (ambient ++ locals) BinderContext.empty (localOccurrences d d.root) (by
    intro occurrence member
    cases occurrence with
    | node node =>
        have nodeRegion := (mem_localOccurrences_node d d.root node).mp member
        simpa using compileNode?_complete hwf exact covers nodeRegion
    | child child =>
        have childDirect :=
          (mem_localOccurrences_child d d.root child).mp member
        cases childShape : d.regions child with
        | sheet =>
            have childRoot : child = d.root :=
              hwf.only_root_is_sheet child childShape
            subst child
            rw [hwf.root_is_sheet] at childDirect
            simp [CRegion.parent?] at childDirect
        | cut parent =>
            have parentEq : parent = d.root := by
              simpa [childShape, CRegion.parent?] using childDirect
            subst parent
            have childExact := exact.extend_child hwf childDirect
            have childCovers := BinderContext.covers_cut_child covers childShape
            obtain ⟨body, bodyResult⟩ := compileRegion?_complete hwf
              (region := child) (context := ambient ++ locals)
              (binders := BinderContext.empty) childExact childCovers
            exact ⟨.cut body, by
              simp [compileOccurrence?, childShape, bodyResult]⟩
        | bubble parent arity =>
            have parentEq : parent = d.root := by
              simpa [childShape, CRegion.parent?] using childDirect
            subst parent
            have childExact := exact.extend_child hwf childDirect
            have childCovers :=
              BinderContext.push_covers_bubble_child covers childShape
            obtain ⟨body, bodyResult⟩ := compileRegion?_complete hwf
              (region := child) (context := ambient ++ locals)
              (binders := BinderContext.empty.push child arity)
              childExact childCovers
            exact ⟨.bubble arity body, by
              simp [compileOccurrence?, childShape, bodyResult]⟩)
  refine ⟨.mk items, ?_⟩
  change (do
    let compiledItems ← compileItems? d hwf (ambient ++ locals)
      BinderContext.empty (localOccurrences d d.root)
    pure (@CompiledRegion.mk d (.root ambient locals) compiledItems)) =
      some (@CompiledRegion.mk d (.root ambient locals) items)
  rw [itemsResult]
  rfl

end VisualProof.Concrete.Elaboration
