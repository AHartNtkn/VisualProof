import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.Elaboration.Compile.Tree
import VisualProof.Concrete.State
import VisualProof.Concrete.Subgraph.Selection

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

/-- One successful invocation of the sole source compiler at a focused
annotated body.  This is an endpoint frame, never an ancestor trace. -/
inductive RegionCallFrame (d : Diagram) :
    {origin : Fin d.regionCount} → {wires : Nat} → {rels : RelCtx} →
      CompiledRegion d origin wires rels → Type
  | root (ambient locals : WireContext d)
      {body : CompiledRegion d d.root ambient.length []}
      (compiled : compileRoot? d ambient locals = some body) :
      RegionCallFrame d body
  | nested (fuel : Nat) (origin : Fin d.regionCount)
      (context : WireContext d) (binders : BinderContext d rels)
      {body : CompiledRegion d origin context.length rels}
      (compiled : compileRegion? d fuel origin context binders = some body) :
      RegionCallFrame d body

/-- The hidden indices and annotated body at the endpoint of one focused
compiler call. -/
abbrev FocusedRegionCallFrame (d : Diagram)
    (site : Fin d.regionCount) :=
  Σ wires, Σ rels, Σ body : CompiledRegion d site wires rels,
    RegionCallFrame d body

mutual
  private noncomputable def CompiledRegionFocus.deriveRootCallFrame
      (ambient locals : WireContext d)
      {body : CompiledRegion d d.root ambient.length []}
      (focus : CompiledRegionFocus d body site)
      (compiled : compileRoot? d ambient locals = some body) :
      FocusedRegionCallFrame d site := by
    let endpoint := RegionCallFrame.root ambient locals compiled
    simp only [compileRoot?] at compiled
    let rootWires := ambient ++ locals
    cases itemsResult : compileOccurrencesWith? d
        (compileRegion? d d.regionCount) rootWires BinderContext.empty
        (localOccurrences d d.root) with
    | none => simp [rootWires, itemsResult] at compiled
    | some items =>
        simp [rootWires, itemsResult] at compiled
        cases compiled
        cases focus with
        | here body => exact ⟨_, _, _, endpoint⟩
        | child nested =>
            exact CompiledItemsFocus.deriveCallFrame d.regionCount rootWires
              BinderContext.empty (localOccurrences d d.root) nested itemsResult

  private noncomputable def CompiledRegionFocus.deriveNestedCallFrame
      (fuel : Nat) (origin : Fin d.regionCount) (context : WireContext d)
      (binders : BinderContext d rels)
      {body : CompiledRegion d origin context.length rels}
      (focus : CompiledRegionFocus d body site)
      (compiled : compileRegion? d fuel origin context binders = some body) :
      FocusedRegionCallFrame d site := by
    let endpoint := RegionCallFrame.nested fuel origin context binders compiled
    cases fuel with
    | zero => simp [compileRegion?] at compiled
    | succ fuel =>
        simp only [compileRegion?] at compiled
        let extended := context.extend origin
        cases itemsResult : compileOccurrencesWith? d
            (compileRegion? d fuel) extended binders
            (localOccurrences d origin) with
        | none => simp [extended, itemsResult] at compiled
        | some items =>
            simp [extended, itemsResult] at compiled
            cases compiled
            cases focus with
            | here body => exact ⟨_, _, _, endpoint⟩
            | child nested =>
                exact CompiledItemsFocus.deriveCallFrame fuel extended binders
                  (localOccurrences d origin) nested itemsResult

  private noncomputable def CompiledItemsFocus.deriveCallFrame
      (fuel : Nat) (context : WireContext d)
      (binders : BinderContext d rels)
      (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
      {items : CompiledItems d context.length rels}
      (focus : CompiledItemsFocus d items site)
      (compiled : compileOccurrencesWith? d (compileRegion? d fuel)
        context binders occurrences = some items) :
      FocusedRegionCallFrame d site := by
    cases occurrences with
    | nil =>
        simp only [compileOccurrencesWith?] at compiled
        cases compiled
        cases focus
    | cons occurrence tail =>
        simp only [compileOccurrencesWith?] at compiled
        cases itemResult : compileOccurrenceWith? d (compileRegion? d fuel)
            context binders occurrence with
        | none => simp [itemResult] at compiled
        | some item =>
            cases tailResult : compileOccurrencesWith? d
                (compileRegion? d fuel) context binders tail with
            | none => simp [itemResult, tailResult] at compiled
            | some suffix =>
                simp [itemResult, tailResult] at compiled
                cases compiled
                cases focus with
                | tail head nested =>
                    exact CompiledItemsFocus.deriveCallFrame fuel context
                      binders tail nested tailResult
                | cut suffix nested =>
                    rename_i childOrigin childBody
                    have occurrenceEq : occurrence = .child childOrigin :=
                      (compileOccurrenceWith?_origin
                        (recurse := compileRegion? d fuel) itemResult).symm
                    subst occurrence
                    simp only [compileOccurrenceWith?] at itemResult
                    cases regionEq : d.regions childOrigin with
                    | sheet =>
                        simp [regionEq] at itemResult
                    | cut parent =>
                        cases bodyResult : compileRegion? d fuel childOrigin
                            context binders with
                        | none =>
                            simp [regionEq, bodyResult] at itemResult
                        | some produced =>
                            simp [regionEq, bodyResult] at itemResult
                            cases itemResult
                            exact CompiledRegionFocus.deriveNestedCallFrame fuel
                              childOrigin context binders nested bodyResult
                    | bubble parent arity =>
                        cases bodyResult : compileRegion? d fuel childOrigin
                            context (binders.push childOrigin arity) with
                        | none =>
                            simp [regionEq, bodyResult] at itemResult
                        | some produced =>
                            simp [regionEq, bodyResult] at itemResult
                | bubble suffix nested =>
                    rename_i childOrigin childArity childBody
                    have occurrenceEq : occurrence = .child childOrigin :=
                      (compileOccurrenceWith?_origin
                        (recurse := compileRegion? d fuel) itemResult).symm
                    subst occurrence
                    simp only [compileOccurrenceWith?] at itemResult
                    cases regionEq : d.regions childOrigin with
                    | sheet =>
                        simp [regionEq] at itemResult
                    | cut parent =>
                        cases bodyResult : compileRegion? d fuel childOrigin
                            context binders with
                        | none =>
                            simp [regionEq, bodyResult] at itemResult
                        | some produced =>
                            simp [regionEq, bodyResult] at itemResult
                    | bubble parent arity =>
                        cases bodyResult : compileRegion? d fuel childOrigin
                            context (binders.push childOrigin arity) with
                        | none =>
                            simp [regionEq, bodyResult] at itemResult
                        | some produced =>
                            simp [regionEq, bodyResult] at itemResult
                            rcases itemResult with ⟨rfl, bodyEq⟩
                            cases bodyEq
                            exact CompiledRegionFocus.deriveNestedCallFrame fuel
                              childOrigin context
                              (binders.push childOrigin arity) nested
                              bodyResult
end

/-- The annotated direct items at one compiled region.  Wire and relation
indices are existential projections of the sole compiler tree. -/
structure CompiledRegionItems (d : Diagram)
    (origin : Fin d.regionCount) where
  wires : Nat
  rels : RelCtx
  items : CompiledItems d wires rels

def CompiledRegion.directItems
    (body : CompiledRegion d origin wires rels) :
    CompiledRegionItems d origin :=
  match body with
  | .mk _ items _ => ⟨_, _, items⟩

mutual
  def CompiledRegionFocus.focusedItems
      (focus : CompiledRegionFocus d body site) :
      CompiledRegionItems d site :=
    match focus with
    | .here body => body.directItems
    | .child nested => nested.focusedItems

  def CompiledItemsFocus.focusedItems
      (focus : CompiledItemsFocus d items site) :
      CompiledRegionItems d site :=
    match focus with
    | .cut _ nested => nested.focusedItems
    | .bubble _ nested => nested.focusedItems
    | .tail _ nested => nested.focusedItems
end

mutual
  private def CompiledRegion.originsValid
      (body : CompiledRegion d origin wires rels) : Prop :=
    match body with
    | .mk _ items _ =>
        items.origins = localOccurrences d origin ∧ items.originsValid

  private def CompiledItem.originsValid
      (item : CompiledItem d wires rels) : Prop :=
    match item with
    | .node _ _ => True
    | .cut _ body => body.originsValid
    | .bubble _ _ body => body.originsValid

  private def CompiledItems.originsValid
      (items : CompiledItems d wires rels) : Prop :=
    match items with
    | .nil => True
    | .cons head tail => head.originsValid ∧ tail.originsValid
end

private theorem compileNode?_originsValid
    {item : CompiledItem d context.length rels}
    (compiled : compileNode? d context binders node = some item) :
    item.originsValid := by
  cases hnode : d.nodes node with
  | atom region binder =>
      simp only [compileNode?, hnode] at compiled
      cases hrelation : binders binder with
      | none => simp [hrelation] at compiled
      | some relation =>
          cases relation with
          | mk arity relation =>
              cases harguments : resolvePorts? d context node arity with
              | none => simp [hrelation, harguments] at compiled
              | some arguments =>
                  simp [hrelation, harguments] at compiled
                  subst item
                  trivial
  | identity region arity =>
      simp only [compileNode?, hnode] at compiled
      cases harguments : resolvePorts? d context node arity with
      | none => simp [harguments] at compiled
      | some arguments =>
          simp [harguments] at compiled
          subst item
          trivial

private theorem compileOccurrenceWith?_originsValid
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (CompiledRegion d region context.length rels))
    (recurseValid : ∀ {rels : RelCtx}
      {region : Fin d.regionCount} {context : WireContext d}
      {binders : BinderContext d rels}
      {body : CompiledRegion d region context.length rels},
      recurse region context binders = some body → body.originsValid)
    {item : CompiledItem d context.length rels}
    (compiled : compileOccurrenceWith? d recurse context binders occurrence =
      some item) :
    item.originsValid := by
  cases occurrence with
  | node node =>
      exact compileNode?_originsValid (by
        simpa [compileOccurrenceWith?] using compiled)
  | child child =>
      cases hregion : d.regions child with
      | sheet => simp [compileOccurrenceWith?, hregion] at compiled
      | cut parent =>
          cases hbody : recurse child context binders with
          | none => simp [compileOccurrenceWith?, hregion, hbody] at compiled
          | some body =>
              simp [compileOccurrenceWith?, hregion, hbody] at compiled
              subst item
              exact recurseValid hbody
      | bubble parent arity =>
          cases hbody : recurse child context (binders.push child arity) with
          | none => simp [compileOccurrenceWith?, hregion, hbody] at compiled
          | some body =>
              simp [compileOccurrenceWith?, hregion, hbody] at compiled
              subst item
              exact recurseValid hbody

private theorem compileOccurrencesWith?_originsValid
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (CompiledRegion d region context.length rels))
    (recurseValid : ∀ {rels : RelCtx}
      {region : Fin d.regionCount} {context : WireContext d}
      {binders : BinderContext d rels}
      {body : CompiledRegion d region context.length rels},
      recurse region context binders = some body → body.originsValid)
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d context.length rels}
    (compiled : compileOccurrencesWith? d recurse context binders occurrences =
      some items) :
    items.originsValid := by
  induction occurrences generalizing items with
  | nil =>
      simp [compileOccurrencesWith?] at compiled
      subst items
      trivial
  | cons occurrence tail ih =>
      simp only [compileOccurrencesWith?] at compiled
      cases hitem : compileOccurrenceWith? d recurse context binders occurrence with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileOccurrencesWith? d recurse context binders tail with
          | none => simp [hitem, htail] at compiled
          | some rest =>
              simp [hitem, htail] at compiled
              subst items
              exact ⟨compileOccurrenceWith?_originsValid recurse recurseValid
                hitem, ih htail⟩

private theorem compileRegion?_originsValid
    {body : CompiledRegion d origin context.length rels}
    (compiled : compileRegion? d fuel origin context binders = some body) :
    body.originsValid := by
  induction fuel generalizing origin context rels binders body with
  | zero => simp [compileRegion?] at compiled
  | succ fuel ih =>
      simp only [compileRegion?] at compiled
      let extended := context.extend origin
      cases hitems : compileOccurrencesWith? d (compileRegion? d fuel)
          extended binders (localOccurrences d origin) with
      | none => simp [extended, hitems] at compiled
      | some items =>
          simp [extended, hitems] at compiled
          subst body
          exact ⟨compileOccurrencesWith?_origins
              (compileRegion? d fuel) hitems,
            compileOccurrencesWith?_originsValid (compileRegion? d fuel)
              (fun equation => ih equation) hitems⟩

private theorem compileRoot?_originsValid
    {body : CompiledRegion d d.root ambient.length []}
    (compiled : compileRoot? d ambient locals = some body) :
    body.originsValid := by
  simp only [compileRoot?] at compiled
  let rootWires := ambient ++ locals
  cases hitems : compileOccurrencesWith? d
      (compileRegion? d d.regionCount) rootWires BinderContext.empty
      (localOccurrences d d.root) with
  | none => simp [rootWires, hitems] at compiled
  | some items =>
      simp [rootWires, hitems] at compiled
      subst body
      exact ⟨compileOccurrencesWith?_origins
          (compileRegion? d d.regionCount) hitems,
        compileOccurrencesWith?_originsValid
          (compileRegion? d d.regionCount)
          (fun equation => compileRegion?_originsValid equation) hitems⟩

mutual
  private theorem CompiledRegionFocus.focusedItems_origins
      (focus : CompiledRegionFocus d body site)
      (valid : body.originsValid) :
      focus.focusedItems.items.origins = localOccurrences d site := by
    cases focus with
    | here body =>
        cases body
        exact valid.1
    | child nested => exact nested.focusedItems_origins valid.2

  private theorem CompiledItemsFocus.focusedItems_origins
      (focus : CompiledItemsFocus d items site)
      (valid : items.originsValid) :
      focus.focusedItems.items.origins = localOccurrences d site := by
    cases focus with
    | cut suffix nested => exact nested.focusedItems_origins valid.1
    | bubble suffix nested => exact nested.focusedItems_origins valid.1
    | tail head nested => exact nested.focusedItems_origins valid.2
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

private theorem compilation_originsValid (checked : CheckedOpen) :
    checked.compilation.originsValid := by
  obtain ⟨body, compiled, compilationEq, _⟩ :=
    checked.elaborate_body_computation
  subst body
  exact compileRoot?_originsValid compiled

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

/-- Recover the one actual compiler invocation whose annotated result is the
endpoint of the stored source focus. -/
noncomputable def callFrame (compiled : CompiledSite source site) :
    FocusedRegionCallFrame source.checked.val.diagram site :=
  CompiledRegionFocus.deriveRootCallFrame
    source.checked.val.exposedWires source.checked.val.hiddenWires
    compiled.focus (CheckedOpen.compilation_computation source.checked)

def directItems (compiled : CompiledSite source site) :
    CompiledRegionItems source.checked.val.diagram site :=
  compiled.focus.focusedItems

theorem directItems_origins (compiled : CompiledSite source site) :
    compiled.directItems.items.origins =
      localOccurrences source.checked.val.diagram site :=
  compiled.focus.focusedItems_origins
    (CheckedOpen.compilation_originsValid source.checked)

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

/-- Classify exactly the direct anchor occurrences named by a checked
selection.  A selected child root remains one atomic occurrence here. -/
def checkedSelectionAnchorClassifier (selection : CheckedSelection d) :
    LocalOccurrence d.regionCount d.nodeCount → Bool
  | .node node => decide (node ∈ selection.val.directNodes)
  | .child child => decide (child ∈ selection.val.childRoots)

@[simp] theorem checkedSelectionAnchorClassifier_node
    (selection : CheckedSelection d)
    (node : Fin d.nodeCount) :
    checkedSelectionAnchorClassifier selection (.node node) =
      decide (node ∈ selection.val.directNodes) := rfl

@[simp] theorem checkedSelectionAnchorClassifier_child
    (selection : CheckedSelection d)
    (child : Fin d.regionCount) :
    checkedSelectionAnchorClassifier selection (.child child) =
      decide (child ∈ selection.val.childRoots) := rfl

/-- Source-only selection compilation.  Every partition and intrinsic braid
is derived from this one annotated anchor zipper. -/
structure CompiledSelection (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) where
  anchor : CompiledSite source selection.val.anchor

namespace CompiledSelection

noncomputable def ofSource (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    CompiledSelection source selection where
  anchor := CompiledSite.ofSource source selection.val.anchor

def anchorItems (compiled : CompiledSelection source selection) :
    CompiledRegionItems source.checked.val.diagram selection.val.anchor :=
  compiled.anchor.directItems

def partition (compiled : CompiledSelection source selection) :
    CompiledItems.Partition compiled.anchorItems.items :=
  compiled.anchorItems.items.partition
    (checkedSelectionAnchorClassifier selection)

def retained (compiled : CompiledSelection source selection) :
    CompiledItems source.checked.val.diagram compiled.anchorItems.wires
      compiled.anchorItems.rels :=
  compiled.partition.retained

def material (compiled : CompiledSelection source selection) :
    CompiledItems source.checked.val.diagram compiled.anchorItems.wires
      compiled.anchorItems.rels :=
  compiled.partition.material

def intrinsic (compiled : CompiledSelection source selection) :
    ItemSeq compiled.anchorItems.wires compiled.anchorItems.rels :=
  compiled.anchorItems.items.erase

def retainedIntrinsic (compiled : CompiledSelection source selection) :
    ItemSeq compiled.anchorItems.wires compiled.anchorItems.rels :=
  compiled.retained.erase

def materialIntrinsic (compiled : CompiledSelection source selection) :
    ItemSeq compiled.anchorItems.wires compiled.anchorItems.rels :=
  compiled.material.erase

/-- The source-derived intrinsic factorization.  Its position equivalence is
the canonical stable-partition braid, never caller supplied. -/
noncomputable def factorization
    (compiled : CompiledSelection source selection) :
    ItemSeqIso (FiniteEquiv.refl (Fin compiled.anchorItems.wires))
      compiled.anchorItems.rels compiled.intrinsic
      (compiled.retainedIntrinsic.append compiled.materialIntrinsic) := by
  simpa [intrinsic, retainedIntrinsic, materialIntrinsic, retained, material,
    partition, CompiledItems.erase_append] using
      CompiledItems.partitionFactorization
        (checkedSelectionAnchorClassifier selection)
        compiled.anchorItems.items

noncomputable def positionMap
    (compiled : CompiledSelection source selection) :
    FiniteEquiv (Fin compiled.intrinsic.length)
      (Fin (compiled.retainedIntrinsic.append
        compiled.materialIntrinsic).length) :=
  match compiled.factorization with
  | .permute positions _ => positions

theorem anchor_origins (compiled : CompiledSelection source selection) :
    compiled.anchorItems.items.origins =
      localOccurrences source.checked.val.diagram selection.val.anchor :=
  compiled.anchor.directItems_origins

theorem retained_origins_eq_unselected
    (compiled : CompiledSelection source selection) :
    compiled.retained.origins =
      (localOccurrences source.checked.val.diagram selection.val.anchor).filter
        fun occurrence =>
          !checkedSelectionAnchorClassifier selection occurrence := by
  change (compiled.anchorItems.items.partition
    (checkedSelectionAnchorClassifier selection)).retained.origins = _
  rw [CompiledItems.partition_retained_origins, compiled.anchor_origins]

theorem material_origins_eq_selected
    (compiled : CompiledSelection source selection) :
    compiled.material.origins =
      (localOccurrences source.checked.val.diagram selection.val.anchor).filter
        (checkedSelectionAnchorClassifier selection) := by
  change (compiled.anchorItems.items.partition
    (checkedSelectionAnchorClassifier selection)).material.origins = _
  rw [CompiledItems.partition_material_origins, compiled.anchor_origins]

theorem mem_retained_origins
    (compiled : CompiledSelection source selection)
    (occurrence : LocalOccurrence source.checked.val.diagram.regionCount
      source.checked.val.diagram.nodeCount) :
    occurrence ∈ compiled.retained.origins ↔
      checkedSelectionAnchorClassifier selection occurrence = false ∧
        occurrence ∈ localOccurrences source.checked.val.diagram
          selection.val.anchor := by
  rw [compiled.retained_origins_eq_unselected]
  simp [and_comm]

theorem mem_material_origins
    (compiled : CompiledSelection source selection)
    (occurrence : LocalOccurrence source.checked.val.diagram.regionCount
      source.checked.val.diagram.nodeCount) :
    occurrence ∈ compiled.material.origins ↔
      checkedSelectionAnchorClassifier selection occurrence = true ∧
        occurrence ∈ localOccurrences source.checked.val.diagram
          selection.val.anchor := by
  rw [compiled.material_origins_eq_selected]
  simp [and_comm]

theorem retained_stable (compiled : CompiledSelection source selection) :
    List.Sublist compiled.retained.origins
      compiled.anchorItems.items.origins :=
  CompiledItems.partition_retained_stable
    (checkedSelectionAnchorClassifier selection)
    compiled.anchorItems.items

theorem material_stable (compiled : CompiledSelection source selection) :
    List.Sublist compiled.material.origins
      compiled.anchorItems.items.origins :=
  CompiledItems.partition_material_stable
    (checkedSelectionAnchorClassifier selection)
    compiled.anchorItems.items

theorem origins_factorization
    (compiled : CompiledSelection source selection) :
    compiled.anchorItems.items.origins.Perm
      (compiled.retained.origins ++ compiled.material.origins) :=
  CompiledItems.partition_origins_perm
    (checkedSelectionAnchorClassifier selection)
    compiled.anchorItems.items

theorem classified_once (compiled : CompiledSelection source selection) :
    (compiled.retained.origins ++ compiled.material.origins).Nodup := by
  have originalNodup : compiled.anchorItems.items.origins.Nodup := by
    rw [compiled.anchor_origins]
    exact localOccurrences_nodup source.checked.val.diagram selection.val.anchor
  exact compiled.origins_factorization.nodup originalNodup

theorem retained_material_disjoint
    (compiled : CompiledSelection source selection) :
    ∀ occurrence, occurrence ∈ compiled.retained.origins →
      occurrence ∉ compiled.material.origins := by
  intro occurrence retained material
  exact (List.nodup_append.mp compiled.classified_once).2.2
    occurrence retained occurrence material rfl

theorem node_mem_material_origins
    (compiled : CompiledSelection source selection)
    (node : Fin source.checked.val.diagram.nodeCount) :
    LocalOccurrence.node node ∈ compiled.material.origins ↔
      node ∈ selection.val.directNodes := by
  rw [compiled.mem_material_origins]
  constructor
  · intro classified
    simpa using classified.1
  · intro selected
    constructor
    · simpa using selected
    · exact (mem_localOccurrences_node source.checked.val.diagram
        selection.val.anchor node).2
          (selection.property.directNodes_at_anchor node selected)

theorem child_mem_material_origins
    (compiled : CompiledSelection source selection)
    (child : Fin source.checked.val.diagram.regionCount) :
    LocalOccurrence.child child ∈ compiled.material.origins ↔
      child ∈ selection.val.childRoots := by
  rw [compiled.mem_material_origins]
  constructor
  · intro classified
    simpa using classified.1
  · intro selected
    constructor
    · simpa using selected
    · exact (mem_localOccurrences_child source.checked.val.diagram
        selection.val.anchor child).2
          (selection.property.childRoots_direct child selected)

end CompiledSelection

end VisualProof.Concrete.Elaboration
