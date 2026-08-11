import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.State

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-!
The compiled focus is a single structural zipper.  Its constructors either
select the current region, enter a child item, or skip an item.  Numeric
positions and intrinsic context paths are projections of this structure.
-/

mutual
  inductive CompiledRegionFocus (d : Diagram) :
      {origin : Fin d.regionCount} -> {wires : Nat} -> {rels : RelCtx} ->
        CompiledRegion d origin wires rels ->
        (site : Fin d.regionCount) -> Type
    | here (body : CompiledRegion d site wires rels) :
        CompiledRegionFocus d body site
    | child {origin site : Fin d.regionCount}
        {totalWires localWires : Nat} {rels : RelCtx}
        {items : CompiledItems d totalWires rels}
        {split : RegionWireSplit wires totalWires localWires}
        (nested : CompiledItemsFocus d items site) :
        CompiledRegionFocus d (.mk localWires items split) site

  inductive CompiledItemsFocus (d : Diagram) :
      {wires : Nat} -> {rels : RelCtx} -> CompiledItems d wires rels ->
        (site : Fin d.regionCount) -> Type
    | cut {site childOrigin : Fin d.regionCount}
        {body : CompiledRegion d childOrigin wires rels}
        (suffix : CompiledItems d wires rels)
        (nested : CompiledRegionFocus d body site) :
        CompiledItemsFocus d (.cons (.cut childOrigin body) suffix) site
    | bubble {site childOrigin : Fin d.regionCount} {arity : Nat}
        {body : CompiledRegion d childOrigin wires (arity :: rels)}
        (suffix : CompiledItems d wires rels)
        (nested : CompiledRegionFocus d body site) :
        CompiledItemsFocus d (.cons (.bubble childOrigin arity body) suffix) site
    | tail (head : CompiledItem d wires rels)
        {suffix : CompiledItems d wires rels}
        (nested : CompiledItemsFocus d suffix site) :
        CompiledItemsFocus d (.cons head suffix) site
end

mutual
  def CompiledRegionFocus.route :
      CompiledRegionFocus d body site -> List Nat
    | .here _ => []
    | .child nested => nested.index :: nested.childRoute

  def CompiledItemsFocus.childRoute :
      CompiledItemsFocus d items site -> List Nat
    | .cut _ nested => nested.route
    | .bubble _ nested => nested.route
    | .tail _ nested => nested.childRoute

  def CompiledItemsFocus.index :
      CompiledItemsFocus d items site -> Nat
    | .cut _ _ => 0
    | .bubble _ _ => 0
    | .tail _ nested => nested.index + 1
end

namespace CompiledItemsFocus

def intrinsicFocus (focus : CompiledItemsFocus d items site) :
    ItemSeq.Focus items.erase :=
  match focus with
  | .cut (body := body) suffix nested => {
      before := .nil
      item := .cut body.erase
      after := suffix.erase
      rebuild := rfl
    }
  | .bubble (arity := arity) (body := body) suffix nested => {
      before := .nil
      item := .bubble arity body.erase
      after := suffix.erase
      rebuild := rfl
    }
  | .tail head nested =>
      let direct := nested.intrinsicFocus
      {
        before := .cons head.erase direct.before
        item := direct.item
        after := direct.after
        rebuild := congrArg (ItemSeq.cons head.erase) direct.rebuild
      }

theorem intrinsicFocus_atIndex (focus : CompiledItemsFocus d items site) :
    items.erase.focusAt? focus.index = some focus.intrinsicFocus :=
  match focus with
  | .cut _ _ => rfl
  | .bubble _ _ => rfl
  | .tail head nested => by
      simp [CompiledItemsFocus.index, ItemSeq.focusAt?, intrinsicFocus,
        intrinsicFocus_atIndex nested]

end CompiledItemsFocus

private def Region.ContextPath.prependItem
    (head : Item totalWires rels)
    {tail : ItemSeq totalWires rels}
    (split : RegionWireSplit outerWires totalWires localWires)
    (path : Region.ContextPath
      (.mk localWires (tail.castWiresEq split.total_eq)) (index :: rest)) :
    Region.ContextPath
      (.mk localWires
        ((ItemSeq.cons head tail).castWiresEq split.total_eq))
      ((index + 1) :: rest) := by
  obtain ⟨totalEq⟩ := split
  subst totalWires
  simp [ItemSeq.castWiresEq] at path ⊢
  cases path with
  | cut focus atIndex isCut nested =>
      let lifted : ItemSeq.Focus
          (ItemSeq.cons head tail) := {
        before := .cons head focus.before
        item := focus.item
        after := focus.after
        rebuild := by
          simp only [ItemSeq.append]
          exact congrArg (ItemSeq.cons head) focus.rebuild
      }
      exact .cut lifted (by
        change (do
          let inner ← tail.focusAt? index
          pure {
            before := .cons head inner.before
            item := inner.item
            after := inner.after
            rebuild := congrArg (ItemSeq.cons head) inner.rebuild
          }) = some lifted
        rw [atIndex]
        rfl) isCut nested
  | bubble focus atIndex isBubble nested =>
      let lifted : ItemSeq.Focus
          (ItemSeq.cons head tail) := {
        before := .cons head focus.before
        item := focus.item
        after := focus.after
        rebuild := by
          simp only [ItemSeq.append]
          exact congrArg (ItemSeq.cons head) focus.rebuild
      }
      exact .bubble lifted (by
        change (do
          let inner ← tail.focusAt? index
          pure {
            before := .cons head inner.before
            item := inner.item
            after := inner.after
            rebuild := congrArg (ItemSeq.cons head) inner.rebuild
          }) = some lifted
        rw [atIndex]
        rfl) isBubble nested

mutual
  def CompiledRegionFocus.intrinsic
      (focus : CompiledRegionFocus d body site) :
      Region.ContextPath body.erase focus.route :=
    match focus with
    | .here body => .here body.erase
    | .child (origin := origin) (split := split) nested =>
        nested.intrinsic origin split

  private def CompiledItemsFocus.intrinsic
      {d : Diagram} {totalWires : Nat} {rels : RelCtx}
      {items : CompiledItems d totalWires rels}
      {site : Fin d.regionCount} :
      (focus : CompiledItemsFocus d items site) ->
      (origin : Fin d.regionCount) ->
      {outerWires localWires : Nat} ->
      (split : RegionWireSplit outerWires totalWires localWires) ->
      Region.ContextPath
        (CompiledRegion.erase
          (CompiledRegion.mk (origin := origin) localWires items split))
        (focus.index :: focus.childRoute)
    | .cut suffix nested, origin, _, _, split =>
        .cut
          ((CompiledItemsFocus.cut suffix nested).intrinsicFocus.castWiresEq
            split.total_eq)
          (ItemSeq.focusAt?_castWiresEq split.total_eq
            (CompiledItems.cons (.cut _ _) suffix).erase 0
            (CompiledItemsFocus.cut suffix nested).intrinsicFocus rfl)
          (by simp [CompiledItemsFocus.intrinsicFocus])
          (nested.intrinsic.castWiresEq split.total_eq)
    | .bubble suffix nested, origin, _, _, split =>
        .bubble
          ((CompiledItemsFocus.bubble suffix nested).intrinsicFocus.castWiresEq
            split.total_eq)
          (ItemSeq.focusAt?_castWiresEq split.total_eq
            (CompiledItems.cons (.bubble _ _ _) suffix).erase 0
            (CompiledItemsFocus.bubble suffix nested).intrinsicFocus rfl)
          (by simp [CompiledItemsFocus.intrinsicFocus])
          (nested.intrinsic.castWiresEq split.total_eq)
    | .tail head nested, origin, _, _, split =>
        Region.ContextPath.prependItem head.erase split
          (nested.intrinsic origin split)
end

def CompiledRegionFocus.depth
    (focus : CompiledRegionFocus d body site) : Nat := focus.route.length

def CompiledRegionFocus.endpoint
    (_focus : CompiledRegionFocus d body site) : Fin d.regionCount := site

def CompiledRegionFocus.sourceOccurrence :
    CompiledRegionFocus d body site ->
      Option (LocalOccurrence d.regionCount d.nodeCount)
  | .here _ => none
  | .child _ => some (.child site)

private theorem compileOccurrencesWith?_focus_of_child
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) ->
      (context : WireContext d) -> BinderContext d rels ->
      Option (CompiledRegion d region context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    {items : CompiledItems d context.length rels}
    (compiled : compileOccurrencesWith? d recurse context binders occurrences =
      some items)
    (child site : Fin d.regionCount)
    (member : LocalOccurrence.child child ∈ occurrences)
    (cutComplete : ∀ {parent : Fin d.regionCount}
      {body : CompiledRegion d child context.length rels},
      d.regions child = .cut parent ->
      recurse child context binders = some body ->
      Nonempty (CompiledRegionFocus d body site))
    (bubbleComplete : ∀ {parent : Fin d.regionCount} {arity : Nat}
      {body : CompiledRegion d child context.length (arity :: rels)},
      d.regions child = .bubble parent arity ->
      recurse child context (binders.push child arity) = some body ->
      Nonempty (CompiledRegionFocus d body site)) :
    Nonempty (CompiledItemsFocus d items site) := by
  induction occurrences generalizing items with
  | nil => simp at member
  | cons occurrence tail ih =>
      simp only [compileOccurrencesWith?] at compiled
      cases itemResult : compileOccurrenceWith? d recurse context binders
          occurrence with
      | none => simp [itemResult] at compiled
      | some item =>
          cases tailResult : compileOccurrencesWith? d recurse context binders
              tail with
          | none => simp [itemResult, tailResult] at compiled
          | some rest =>
              simp [itemResult, tailResult] at compiled
              subst items
              rcases List.mem_cons.mp member with head | tailMember
              · subst occurrence
                cases regionEq : d.regions child with
                | sheet =>
                    simp [compileOccurrenceWith?, regionEq] at itemResult
                | cut parent =>
                    cases bodyResult : recurse child context binders with
                    | none =>
                        simp [compileOccurrenceWith?, regionEq, bodyResult]
                          at itemResult
                    | some body =>
                        simp [compileOccurrenceWith?, regionEq, bodyResult]
                          at itemResult
                        subst item
                        obtain ⟨nested⟩ := cutComplete regionEq bodyResult
                        exact ⟨.cut rest nested⟩
                | bubble parent arity =>
                    cases bodyResult : recurse child context
                        (binders.push child arity) with
                    | none =>
                        simp [compileOccurrenceWith?, regionEq, bodyResult]
                          at itemResult
                    | some body =>
                        simp [compileOccurrenceWith?, regionEq, bodyResult]
                          at itemResult
                        subst item
                        obtain ⟨nested⟩ := bubbleComplete regionEq bodyResult
                        exact ⟨.bubble rest nested⟩
              · obtain ⟨nested⟩ := ih tailResult tailMember
                exact ⟨.tail item nested⟩

private theorem compileRegion?_focus
    (hwf : d.WellFormed)
    {fuel : Nat} {origin site : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    {body : CompiledRegion d origin context.length rels}
    (compiled : compileRegion? d fuel origin context binders = some body)
    (encloses : d.Encloses origin site) :
    Nonempty (CompiledRegionFocus d body site) := by
  induction fuel generalizing origin context rels binders body site with
  | zero => simp [compileRegion?] at compiled
  | succ fuel ih =>
      by_cases same : origin = site
      · subst site
        exact ⟨.here body⟩
      · obtain ⟨child, childParent, childEncloses⟩ :=
          exists_direct_child_enclosing hwf (Ne.symm same) encloses
        simp only [compileRegion?] at compiled
        let extended := context.extend origin
        cases itemsResult : compileOccurrencesWith? d (compileRegion? d fuel)
            extended binders (localOccurrences d origin) with
        | none => simp [extended, itemsResult] at compiled
        | some items =>
            simp [extended, itemsResult] at compiled
            subst body
            obtain ⟨nested⟩ := compileOccurrencesWith?_focus_of_child
              (compileRegion? d fuel) extended binders
              (localOccurrences d origin) itemsResult child site
              ((mem_localOccurrences_child d origin child).mpr childParent)
              (fun _ bodyResult => ih bodyResult childEncloses)
              (fun _ bodyResult => ih bodyResult childEncloses)
            exact ⟨.child (origin := origin) nested⟩

private theorem compileRoot?_focus
    (hwf : d.WellFormed)
    (ambient locals : WireContext d)
    {body : CompiledRegion d d.root ambient.length []}
    (compiled : compileRoot? d ambient locals = some body)
    (site : Fin d.regionCount) :
    Nonempty (CompiledRegionFocus d body site) := by
  by_cases same : d.root = site
  · subst site
    exact ⟨.here body⟩
  · obtain ⟨child, childParent, childEncloses⟩ :=
      exists_direct_child_enclosing hwf (Ne.symm same)
        (hwf.all_regions_reach_root site)
    simp only [compileRoot?] at compiled
    let rootWires := ambient ++ locals
    cases itemsResult : compileOccurrencesWith? d
        (compileRegion? d d.regionCount) rootWires BinderContext.empty
        (localOccurrences d d.root) with
    | none => simp [rootWires, itemsResult] at compiled
    | some items =>
        simp [rootWires, itemsResult] at compiled
        subst body
        obtain ⟨nested⟩ := compileOccurrencesWith?_focus_of_child
          (compileRegion? d d.regionCount) rootWires BinderContext.empty
          (localOccurrences d d.root) itemsResult child site
          ((mem_localOccurrences_child d d.root child).mpr childParent)
          (fun _ bodyResult =>
            compileRegion?_focus hwf bodyResult childEncloses)
          (fun _ bodyResult =>
            compileRegion?_focus hwf bodyResult childEncloses)
        exact ⟨.child (origin := d.root) nested⟩

namespace CheckedOpen

private theorem compilation_focus
    (checked : CheckedOpen)
    (site : Fin checked.val.diagram.regionCount) :
    Nonempty (CompiledRegionFocus checked.val.diagram
      checked.compilation site) := by
  obtain ⟨body, compiled, compilationEq, _⟩ :=
    checked.elaborate_body_computation
  subst body
  exact compileRoot?_focus checked.property.diagram_well_formed
    checked.val.exposedWires checked.val.hiddenWires compiled site

end CheckedOpen

structure CompiledSite (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) where
  focus : CompiledRegionFocus source.checked.val.diagram
    source.checked.compilation site

namespace CompiledSite

noncomputable def ofSource (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledSite source site where
  focus := Classical.choice
    (CheckedOpen.compilation_focus source.checked site)

def intrinsic (compiled : CompiledSite source site) :
    Region.ContextPath source.checked.elaborate.body compiled.focus.route :=
  compiled.focus.intrinsic

def context (compiled : CompiledSite source site) :
    DiagramContext source.checked.elaborate.externalClasses
      compiled.intrinsic.toFocus.holeWires []
      compiled.intrinsic.toFocus.holeRels :=
  compiled.intrinsic.toFocus.context

def body (compiled : CompiledSite source site) :
    Region compiled.intrinsic.toFocus.holeWires
      compiled.intrinsic.toFocus.holeRels :=
  compiled.intrinsic.toFocus.body

def cutDepth (compiled : CompiledSite source site) : Nat :=
  compiled.intrinsic.toFocus.context.cutDepth

def sourceOccurrence (compiled : CompiledSite source site) :
    Option (LocalOccurrence source.checked.val.diagram.regionCount
      source.checked.val.diagram.nodeCount) :=
  compiled.focus.sourceOccurrence

theorem rebuild (compiled : CompiledSite source site) :
    compiled.intrinsic.toFocus.context.fill compiled.intrinsic.toFocus.body =
      source.checked.elaborate.body :=
  compiled.intrinsic.toFocus.rebuild

end CompiledSite

end VisualProof.Concrete.Elaboration
