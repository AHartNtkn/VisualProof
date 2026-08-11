import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.State

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

inductive CompiledCutAt (d : Diagram) {wires : Nat} {rels : RelCtx} :
    CompiledItems d wires rels -> Nat -> (origin : Fin d.regionCount) ->
      CompiledRegion d wires rels -> Type
  | here (origin : Fin d.regionCount) (body : CompiledRegion d wires rels)
      (suffix : CompiledItems d wires rels) :
      CompiledCutAt d (.cons (.cut origin body) suffix) 0 origin body
  | tail (head : CompiledItem d wires rels) {items index origin body}
      (rest : CompiledCutAt d items index origin body) :
      CompiledCutAt d (.cons head items) (index + 1) origin body

inductive CompiledBubbleAt (d : Diagram) {wires : Nat} {rels : RelCtx} :
    CompiledItems d wires rels -> Nat -> (origin : Fin d.regionCount) ->
      (arity : Nat) -> CompiledRegion d wires (arity :: rels) -> Type
  | here (origin : Fin d.regionCount) (arity : Nat)
      (body : CompiledRegion d wires (arity :: rels))
      (suffix : CompiledItems d wires rels) :
      CompiledBubbleAt d (.cons (.bubble origin arity body) suffix) 0 origin
        arity body
  | tail (head : CompiledItem d wires rels) {items index origin arity body}
      (rest : CompiledBubbleAt d items index origin arity body) :
      CompiledBubbleAt d (.cons head items) (index + 1) origin arity body

inductive CompiledPath (d : Diagram) :
    (origin : Fin d.regionCount) -> {wires : Nat} -> {rels : RelCtx} ->
      CompiledRegion d wires rels ->
      (site : Fin d.regionCount) -> List Nat -> Type
  | here (origin : Fin d.regionCount) (body : CompiledRegion d wires rels) :
      CompiledPath d origin body origin []
  | cut {origin site childOrigin : Fin d.regionCount}
      {totalWires : Nat} {items : CompiledItems d totalWires rels}
      {localWires : Nat}
      {split : RegionWireSplit wires totalWires localWires}
      {index : Nat} {rest : List Nat}
      {childBody : CompiledRegion d totalWires rels}
      (direct : CompiledCutAt d items index childOrigin childBody)
      (nested : CompiledPath d childOrigin childBody site rest) :
      CompiledPath d origin (.mk localWires items split) site (index :: rest)
  | bubble {origin site childOrigin : Fin d.regionCount}
      {totalWires : Nat} {items : CompiledItems d totalWires rels}
      {localWires : Nat}
      {split : RegionWireSplit wires totalWires localWires}
      {index arity : Nat} {rest : List Nat}
      {childBody : CompiledRegion d totalWires (arity :: rels)}
      (direct : CompiledBubbleAt d items index childOrigin arity childBody)
      (nested : CompiledPath d childOrigin childBody site rest) :
      CompiledPath d origin (.mk localWires items split) site (index :: rest)

mutual
  private def CompiledRegion.findPath? (origin : Fin d.regionCount)
      (body : CompiledRegion d wires rels) (site : Fin d.regionCount) :
      Option (List Nat) :=
    if origin = site then some []
    else
      match body with
      | .mk _ items _ =>
          (items.findPath? site).map fun result => result.1 :: result.2

  private def CompiledItems.findPath? (items : CompiledItems d wires rels)
      (site : Fin d.regionCount) : Option (Nat × List Nat) :=
    match items with
    | .nil => none
    | .cons head tail =>
        let nested? :=
          match head with
          | .node _ _ => none
          | .cut childOrigin childBody =>
              (childBody.findPath? childOrigin site).map fun path => (0, path)
          | .bubble childOrigin _ childBody =>
              (childBody.findPath? childOrigin site).map fun path => (0, path)
        nested?.orElse fun _ =>
          (tail.findPath? site).map fun result => (result.1 + 1, result.2)
end

private theorem compileOccurrencesWith?_findPath?_isSome_of_child
    (recurse : ∀ {rels : RelCtx},
      (region : Fin d.regionCount) →
      (context : WireContext d) → BinderContext d rels →
      Option (CompiledRegion d context.length rels))
    (context : WireContext d) (binders : BinderContext d rels)
    (occurrences : List (LocalOccurrence d.regionCount d.nodeCount))
    {items : CompiledItems d context.length rels}
    (compiled : compileOccurrencesWith? d recurse context binders occurrences =
      some items)
    (child site : Fin d.regionCount)
    (member : LocalOccurrence.child child ∈ occurrences)
    (cutComplete : ∀ {parent : Fin d.regionCount}
      {body : CompiledRegion d context.length rels},
      d.regions child = .cut parent →
      recurse child context binders = some body →
      (body.findPath? child site).isSome)
    (bubbleComplete : ∀ {parent : Fin d.regionCount} {arity : Nat}
      {body : CompiledRegion d context.length (arity :: rels)},
      d.regions child = .bubble parent arity →
      recurse child context (binders.push child arity) = some body →
      (body.findPath? child site).isSome) :
    (items.findPath? site).isSome := by
  induction occurrences generalizing items with
  | nil => simp at member
  | cons occurrence tail ih =>
      simp only [compileOccurrencesWith?] at compiled
      cases itemResult : compileOccurrenceWith? d recurse context binders occurrence with
      | none => simp [itemResult] at compiled
      | some item =>
          cases tailResult : compileOccurrencesWith? d recurse context binders tail with
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
                        simp [compileOccurrenceWith?, regionEq, bodyResult] at itemResult
                    | some body =>
                        simp [compileOccurrenceWith?, regionEq, bodyResult] at itemResult
                        subst item
                        obtain ⟨path, pathEq⟩ := Option.isSome_iff_exists.mp
                          (cutComplete regionEq bodyResult)
                        simp [CompiledItems.findPath?, pathEq]
                | bubble parent arity =>
                    cases bodyResult : recurse child context
                        (binders.push child arity) with
                    | none =>
                        simp [compileOccurrenceWith?, regionEq, bodyResult] at itemResult
                    | some body =>
                        simp [compileOccurrenceWith?, regionEq, bodyResult] at itemResult
                        subst item
                        obtain ⟨path, pathEq⟩ := Option.isSome_iff_exists.mp
                          (bubbleComplete regionEq bodyResult)
                        simp [CompiledItems.findPath?, pathEq]
              · obtain ⟨result, resultEq⟩ := Option.isSome_iff_exists.mp
                  (ih tailResult tailMember)
                cases item with
                | node => simp [CompiledItems.findPath?, resultEq]
                | cut itemOrigin body =>
                    cases nested : body.findPath? itemOrigin site <;>
                      simp [CompiledItems.findPath?, nested, resultEq]
                | bubble itemOrigin arity body =>
                    cases nested : body.findPath? itemOrigin site <;>
                      simp [CompiledItems.findPath?, nested, resultEq]

private theorem compileRegion?_findPath?_isSome
    (hwf : d.WellFormed)
    {fuel : Nat} {origin site : Fin d.regionCount}
    {context : WireContext d} {binders : BinderContext d rels}
    {body : CompiledRegion d context.length rels}
    (compiled : compileRegion? d fuel origin context binders = some body)
    (encloses : d.Encloses origin site) :
    (body.findPath? origin site).isSome := by
  induction fuel generalizing origin context rels binders body site with
  | zero => simp [compileRegion?] at compiled
  | succ fuel ih =>
      by_cases same : origin = site
      · subst site
        cases body
        simp [CompiledRegion.findPath?]
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
            let split : RegionWireSplit context.length extended.length
                (exactScopeWires d origin).length := {
              total_eq := WireContext.length_extend context origin
            }
            have packageEq : finishRegion d context origin items =
                .mk (exactScopeWires d origin).length items split := by
              unfold finishRegion
              apply congrArg (CompiledRegion.mk
                (exactScopeWires d origin).length items)
              exact Subsingleton.elim _ _
            rw [packageEq]
            rw [CompiledRegion.findPath?]
            simp only [same, ↓reduceIte, Option.isSome_map]
            exact compileOccurrencesWith?_findPath?_isSome_of_child
              (compileRegion? d fuel) extended binders
              (localOccurrences d origin) itemsResult child site
              ((mem_localOccurrences_child d origin child).mpr childParent)
              (fun _ bodyResult => ih bodyResult childEncloses)
              (fun _ bodyResult => ih bodyResult childEncloses)

private theorem compileRoot?_findPath?_isSome
    (hwf : d.WellFormed)
    (ambient locals : WireContext d)
    {body : CompiledRegion d ambient.length []}
    (compiled : compileRoot? d ambient locals = some body)
    (site : Fin d.regionCount) :
    (body.findPath? d.root site).isSome := by
  by_cases same : d.root = site
  · subst site
    cases body
    simp [CompiledRegion.findPath?]
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
        let split : RegionWireSplit ambient.length rootWires.length
            locals.length := { total_eq := by simp [rootWires] }
        have packageEq : finishRoot ambient locals items =
            .mk locals.length items split := by
          unfold finishRoot
          apply congrArg (CompiledRegion.mk locals.length items)
          exact Subsingleton.elim _ _
        rw [packageEq]
        rw [CompiledRegion.findPath?]
        simp only [same, ↓reduceIte, Option.isSome_map]
        exact compileOccurrencesWith?_findPath?_isSome_of_child
          (compileRegion? d d.regionCount) rootWires BinderContext.empty
          (localOccurrences d d.root) itemsResult child site
          ((mem_localOccurrences_child d d.root child).mpr childParent)
          (fun _ bodyResult =>
            compileRegion?_findPath?_isSome hwf bodyResult childEncloses)
          (fun _ bodyResult =>
            compileRegion?_findPath?_isSome hwf bodyResult childEncloses)

mutual
  private theorem CompiledRegion.findPath?_sound
      (body : CompiledRegion d wires rels)
      (origin site : Fin d.regionCount) (path : List Nat)
      (found : body.findPath? origin site = some path) :
      Nonempty (CompiledPath d origin body site path) := by
    by_cases equality : origin = site
    · subst site
      cases body with
      | mk localWires items split =>
          simp [CompiledRegion.findPath?] at found
          subst path
          exact ⟨CompiledPath.here origin (.mk localWires items split)⟩
    · cases body with
      | mk localWires items split =>
          simp only [CompiledRegion.findPath?, equality, ↓reduceIte,
            ] at found
          cases itemResult : items.findPath? site with
          | none => simp [itemResult] at found
          | some result =>
              obtain ⟨index, rest⟩ := result
              simp [itemResult] at found
              subst path
              exact items.findPath?_sound localWires split origin site index rest
                itemResult

  private theorem CompiledItems.findPath?_sound
      (items : CompiledItems d totalWires rels)
      (localWires : Nat)
      (split : RegionWireSplit outerWires totalWires localWires)
      (origin site : Fin d.regionCount) (index : Nat) (rest : List Nat)
      (found : items.findPath? site = some (index, rest)) :
      Nonempty (CompiledPath d origin (.mk localWires items split) site
        (index :: rest)) := by
    cases items with
    | nil => simp [CompiledItems.findPath?] at found
    | cons head tail =>
        cases head with
        | node node item =>
            simp only [CompiledItems.findPath?, Option.orElse_none,
              ] at found
            cases tailResult : tail.findPath? site with
            | none => simp [tailResult] at found
            | some result =>
                obtain ⟨tailIndex, tailRest⟩ := result
                simp [tailResult] at found
                rw [← found.1, ← found.2]
                obtain ⟨nested⟩ := tail.findPath?_sound localWires split origin
                  site tailIndex tailRest tailResult
                cases nested with
                | cut direct inner =>
                    exact ⟨CompiledPath.cut (CompiledCutAt.tail (.node node item)
                      direct) inner⟩
                | bubble direct inner =>
                    exact ⟨CompiledPath.bubble (CompiledBubbleAt.tail
                      (.node node item) direct) inner⟩
        | cut childOrigin childBody =>
            cases childResult : childBody.findPath? childOrigin site with
            | some childPath =>
                simp [CompiledItems.findPath?, childResult] at found
                rw [← found.1, ← found.2]
                obtain ⟨nested⟩ := childBody.findPath?_sound childOrigin site
                  childPath childResult
                exact ⟨CompiledPath.cut
                  (CompiledCutAt.here childOrigin childBody tail) nested⟩
            | none =>
                simp only [CompiledItems.findPath?, childResult, Option.map_none,
                  Option.orElse_none] at found
                cases tailResult : tail.findPath? site with
                | none => simp [tailResult] at found
                | some result =>
                    obtain ⟨tailIndex, tailRest⟩ := result
                    simp [tailResult] at found
                    rw [← found.1, ← found.2]
                    obtain ⟨nested⟩ := tail.findPath?_sound localWires split
                      origin site tailIndex tailRest tailResult
                    cases nested with
                    | cut direct inner =>
                        exact ⟨CompiledPath.cut (CompiledCutAt.tail
                          (.cut childOrigin childBody) direct) inner⟩
                    | bubble direct inner =>
                        exact ⟨CompiledPath.bubble (CompiledBubbleAt.tail
                          (.cut childOrigin childBody) direct) inner⟩
        | bubble childOrigin arity childBody =>
            cases childResult : childBody.findPath? childOrigin site with
            | some childPath =>
                simp [CompiledItems.findPath?, childResult] at found
                rw [← found.1, ← found.2]
                obtain ⟨nested⟩ := childBody.findPath?_sound childOrigin site
                  childPath childResult
                exact ⟨CompiledPath.bubble
                  (CompiledBubbleAt.here childOrigin arity childBody tail) nested⟩
            | none =>
                simp only [CompiledItems.findPath?, childResult, Option.map_none,
                  Option.orElse_none] at found
                cases tailResult : tail.findPath? site with
                | none => simp [tailResult] at found
                | some result =>
                    obtain ⟨tailIndex, tailRest⟩ := result
                    simp [tailResult] at found
                    rw [← found.1, ← found.2]
                    obtain ⟨nested⟩ := tail.findPath?_sound localWires split
                      origin site tailIndex tailRest tailResult
                    cases nested with
                    | cut direct inner =>
                        exact ⟨CompiledPath.cut (CompiledCutAt.tail
                          (.bubble childOrigin arity childBody) direct) inner⟩
                    | bubble direct inner =>
                        exact ⟨CompiledPath.bubble (CompiledBubbleAt.tail
                          (.bubble childOrigin arity childBody) direct) inner⟩
end

namespace CompiledCutAt

def intrinsicFocus (focus : CompiledCutAt d items index origin body) :
    ItemSeq.Focus items.erase :=
  match focus with
  | .here _ body suffix => {
      before := .nil
      item := .cut body.erase
      after := suffix.erase
      rebuild := rfl
    }
  | .tail head rest =>
      let nested := rest.intrinsicFocus
      {
        before := .cons head.erase nested.before
        item := nested.item
        after := nested.after
        rebuild := congrArg (ItemSeq.cons head.erase) nested.rebuild
      }

@[simp] theorem intrinsicFocus_item
    (focus : CompiledCutAt d items index origin body) :
    focus.intrinsicFocus.item = .cut body.erase := by
  induction focus with
  | here => rfl
  | tail _ _ ih => exact ih

theorem intrinsicFocus_atIndex
    (focus : CompiledCutAt d items index origin body) :
    items.erase.focusAt? index = some focus.intrinsicFocus := by
  induction focus with
  | here => rfl
  | tail head rest ih => simp [ItemSeq.focusAt?, intrinsicFocus, ih]

end CompiledCutAt

namespace CompiledBubbleAt

def intrinsicFocus (focus : CompiledBubbleAt d items index origin arity body) :
    ItemSeq.Focus items.erase :=
  match focus with
  | .here _ arity body suffix => {
      before := .nil
      item := .bubble arity body.erase
      after := suffix.erase
      rebuild := rfl
    }
  | .tail head rest =>
      let nested := rest.intrinsicFocus
      {
        before := .cons head.erase nested.before
        item := nested.item
        after := nested.after
        rebuild := congrArg (ItemSeq.cons head.erase) nested.rebuild
      }

@[simp] theorem intrinsicFocus_item
    (focus : CompiledBubbleAt d items index origin arity body) :
    focus.intrinsicFocus.item = .bubble arity body.erase := by
  induction focus with
  | here => rfl
  | tail _ _ ih => exact ih

theorem intrinsicFocus_atIndex
    (focus : CompiledBubbleAt d items index origin arity body) :
    items.erase.focusAt? index = some focus.intrinsicFocus := by
  induction focus with
  | here => rfl
  | tail head rest ih => simp [ItemSeq.focusAt?, intrinsicFocus, ih]

end CompiledBubbleAt

namespace CompiledPath

def intrinsic : CompiledPath d origin body site path ->
    Region.ContextPath body.erase path
  | .here _ _ => .here _
  | .cut (split := split) direct nested =>
      .cut (direct.intrinsicFocus.castWiresEq split.total_eq)
        (ItemSeq.focusAt?_castWiresEq split.total_eq _ _ _
          direct.intrinsicFocus_atIndex)
        (by simp)
        (nested.intrinsic.castWiresEq split.total_eq)
  | .bubble (split := split) direct nested =>
      .bubble (direct.intrinsicFocus.castWiresEq split.total_eq)
        (ItemSeq.focusAt?_castWiresEq split.total_eq _ _ _
          direct.intrinsicFocus_atIndex)
        (by simp)
        (nested.intrinsic.castWiresEq split.total_eq)

def depth (_focus : CompiledPath d origin body site path) : Nat := path.length

def endpoint (_focus : CompiledPath d origin body site path) :
    Fin d.regionCount := site

def sourceOccurrence :
    CompiledPath d origin body site path ->
      Option (LocalOccurrence d.regionCount d.nodeCount)
  | .here _ _ => none
  | .cut _ nested => some (.child nested.endpoint)
  | .bubble _ nested => some (.child nested.endpoint)

end CompiledPath

namespace CheckedOpen

private theorem compilation_findPath?_isSome
    (checked : CheckedOpen)
    (site : Fin checked.val.diagram.regionCount) :
    (checked.compilation.findPath? checked.val.diagram.root site).isSome := by
  obtain ⟨body, compiled, compilationEq, _⟩ :=
    checked.elaborate_body_computation
  rw [compilationEq]
  exact compileRoot?_findPath?_isSome
    checked.property.diagram_well_formed checked.val.exposedWires
      checked.val.hiddenWires compiled site

end CheckedOpen

structure CompiledSite (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) where
  focus : (path : List Nat) ×'
    CompiledPath source.checked.val.diagram source.checked.val.diagram.root
      source.checked.compilation site path

namespace CompiledSite

noncomputable def ofSource (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledSite source site := by
  let pathIsSome := CheckedOpen.compilation_findPath?_isSome source.checked site
  let path :=
    (source.checked.compilation.findPath? source.checked.val.diagram.root site).get
      pathIsSome
  have pathSpec : source.checked.compilation.findPath?
      source.checked.val.diagram.root site = some path :=
    (Option.some_get pathIsSome).symm
  exact {
    focus := ⟨path, Classical.choice
      (source.checked.compilation.findPath?_sound
        source.checked.val.diagram.root site path pathSpec)⟩
  }

def intrinsic (compiled : CompiledSite source site) :
    Region.ContextPath source.checked.elaborate.body compiled.focus.1 :=
  compiled.focus.2.intrinsic

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
  compiled.focus.2.sourceOccurrence

theorem rebuild (compiled : CompiledSite source site) :
    compiled.intrinsic.toFocus.context.fill compiled.intrinsic.toFocus.body =
      source.checked.elaborate.body :=
  compiled.intrinsic.toFocus.rebuild

end CompiledSite

end VisualProof.Concrete.Elaboration
