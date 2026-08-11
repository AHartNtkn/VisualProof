import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.State
import VisualProof.Concrete.Subgraph.Selection

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-!
The compiled source focus is one structural zipper over the sole
signature-indexed compiler result. Exact endpoint inputs remain indices of the
selected result; intrinsic context, body, and rebuilding are projections of
that zipper.
-/

mutual
  inductive CompiledZipper (d : Diagram) :
      {sourceCall : CompilerCall d} ->
      CompiledRegion d sourceCall ->
      (site : Fin d.regionCount) ->
      (endpointCall : CompilerCall d) ->
      CompiledRegion d endpointCall -> Type
    | here {sourceCall : CompilerCall d}
        (source : CompiledRegion d sourceCall) :
        CompiledZipper d source sourceCall.origin sourceCall source
    | child {sourceCall endpointCall : CompilerCall d}
        {items : CompiledItems d sourceCall.childFuel sourceCall.fullContext
          sourceCall.rels sourceCall.binders}
        {site : Fin d.regionCount}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledItemsZipper d items site endpointCall endpoint) :
        CompiledZipper d (.mk items) site endpointCall endpoint

  inductive CompiledItemsZipper (d : Diagram) :
      {fuel : Nat} -> {context : WireContext d} -> {rels : RelCtx} ->
      {binders : BinderContext d rels} ->
      CompiledItems d fuel context rels binders ->
      (site : Fin d.regionCount) ->
      (endpointCall : CompilerCall d) ->
      CompiledRegion d endpointCall -> Type
    | cut {childFuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {body : CompiledRegion d
          (.nested childFuel origin context rels binders)}
        {suffix : CompiledItems d (childFuel + 1) context rels binders}
        {site : Fin d.regionCount} {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledZipper d body site endpointCall endpoint) :
        CompiledItemsZipper d (.cons (.cut body) suffix) site endpointCall
          endpoint
    | bubble {childFuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {arity : Nat}
        {body : CompiledRegion d
          (.nested childFuel origin context (arity :: rels)
            (binders.push origin arity))}
        {suffix : CompiledItems d (childFuel + 1) context rels binders}
        {site : Fin d.regionCount} {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledZipper d body site endpointCall endpoint) :
        CompiledItemsZipper d (.cons (.bubble arity body) suffix) site
          endpointCall endpoint
    | tail {fuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels}
        {head : CompiledItem d fuel context rels binders}
        {suffix : CompiledItems d fuel context rels binders}
        {site : Fin d.regionCount} {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledItemsZipper d suffix site endpointCall endpoint) :
        CompiledItemsZipper d (.cons head suffix) site endpointCall endpoint
end

/-- The one stored source focus: an exact endpoint result and its structural
selection from the root result. -/
structure CompiledFocus {d : Diagram} {sourceCall : CompilerCall d}
    (source : CompiledRegion d sourceCall) (site : Fin d.regionCount) where
  endpointCall : CompilerCall d
  endpoint : CompiledRegion d endpointCall
  zipper : CompiledZipper d source site endpointCall endpoint

/-- Intrinsic context and rebuilding obtained directly from one zipper. -/
structure CompiledIntrinsic (d : Diagram)
    {sourceWires : Nat} {sourceRels : RelCtx}
    (source : Region sourceWires sourceRels)
    (endpointCall : CompilerCall d)
    (endpoint : CompiledRegion d endpointCall) where
  context : DiagramContext sourceWires endpointCall.outerContext.length
    sourceRels endpointCall.rels
  rebuild : context.fill endpoint.erase = source

private theorem DiagramContext.castOuterWires_fill
    {source target holeWires : Nat} {outerRels holeRels : RelCtx}
    (equality : source = target)
    (context : DiagramContext source holeWires outerRels holeRels)
    (body : Region holeWires holeRels) :
    (equality ▸ context).fill body =
      (context.fill body).castWiresEq equality := by
  cases equality
  rfl

mutual
  def CompiledZipper.intrinsic
      {sourceCall endpointCall : CompilerCall d}
      {source : CompiledRegion d sourceCall}
      {site : Fin d.regionCount}
      {endpoint : CompiledRegion d endpointCall} :
      (focus : CompiledZipper d source site endpointCall endpoint) ->
        CompiledIntrinsic d source.erase endpointCall endpoint
    | .here _ => ⟨.hole, rfl⟩
    | .child nested => by
        simpa [CompiledRegion.erase, CompilerCall.finish,
          CompilerCall.castFullItems] using
            nested.intrinsic .nil sourceCall.outerContext.length
              sourceCall.localContext.length (by
                simp [CompilerCall.fullContext])

  def CompiledItemsZipper.intrinsic
      {fuel : Nat} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d fuel context rels binders}
      {site : Fin d.regionCount} {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall}
      (focus : CompiledItemsZipper d items site endpointCall endpoint)
      (before : ItemSeq context.length rels)
      (outerWires localWires : Nat)
      (split : context.length = outerWires + localWires) :
      CompiledIntrinsic d
        (.mk localWires ((before.append items.erase).castWiresEq split))
        endpointCall endpoint :=
    match focus with
    | .cut (body := body) (suffix := suffix) nested =>
        let selected := nested.intrinsic
        {
          context := .cut localWires (before.castWiresEq split)
            (suffix.erase.castWiresEq split) (split ▸ selected.context)
          rebuild := by
            have nestedEq :
                (split ▸ selected.context).fill endpoint.erase =
                  body.erase.castWiresEq split :=
              (DiagramContext.castOuterWires_fill split selected.context
                endpoint.erase).trans
                (congrArg (Region.castWiresEq split) selected.rebuild)
            simp only [DiagramContext.fill]
            calc
              _ = .mk localWires
                  ((before.castWiresEq split).append
                    (.cons (.cut (body.erase.castWiresEq split))
                      (suffix.erase.castWiresEq split))) := by
                exact congrArg (fun sequence => Region.mk localWires sequence)
                  (congrArg (fun item =>
                    (before.castWiresEq split).append
                      (.cons item (suffix.erase.castWiresEq split)))
                    (congrArg Item.cut nestedEq))
              _ = _ := by simp [CompiledItems.erase, CompiledItem.erase]
        }
    | .bubble (arity := arity) (body := body) (suffix := suffix) nested =>
        let selected := nested.intrinsic
        {
          context := .bubble localWires (before.castWiresEq split)
            (suffix.erase.castWiresEq split) arity
            (split ▸ selected.context)
          rebuild := by
            have nestedEq :
                (split ▸ selected.context).fill endpoint.erase =
                  body.erase.castWiresEq split :=
              (DiagramContext.castOuterWires_fill split selected.context
                endpoint.erase).trans
                (congrArg (Region.castWiresEq split) selected.rebuild)
            simp only [DiagramContext.fill]
            calc
              _ = .mk localWires
                  ((before.castWiresEq split).append
                    (.cons (.bubble arity (body.erase.castWiresEq split))
                      (suffix.erase.castWiresEq split))) := by
                exact congrArg (fun sequence => Region.mk localWires sequence)
                  (congrArg (fun item =>
                    (before.castWiresEq split).append
                      (.cons item (suffix.erase.castWiresEq split)))
                    (congrArg (Item.bubble arity) nestedEq))
              _ = _ := by simp [CompiledItems.erase, CompiledItem.erase]
        }
    | .tail (head := head) nested => by
        let castNilGeneric : ∀ {source target : Nat} {nilRels : RelCtx}
            (equality : source = target),
            (ItemSeq.nil : ItemSeq source nilRels).castWiresEq equality =
              (ItemSeq.nil : ItemSeq target nilRels) := by
          intro source target nilRels equality
          cases equality
          rfl
        have castNil :
            (ItemSeq.nil : ItemSeq context.length rels).castWiresEq split =
              (ItemSeq.nil : ItemSeq (outerWires + localWires) rels) :=
          castNilGeneric split
        simpa [CompiledItems.erase, ItemSeq.append_assoc, castNil,
          ItemSeq.append] using
            nested.intrinsic (before.append (.cons head.erase .nil))
              outerWires localWires split
end

def CompiledZipper.body {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
    {endpoint : CompiledRegion d endpointCall}
    (_focus : CompiledZipper d source site endpointCall endpoint) :
    Region endpointCall.outerContext.length endpointCall.rels :=
  endpoint.erase

def CompiledZipper.context {d : Diagram}
    {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source site endpointCall endpoint) :
    DiagramContext sourceCall.outerContext.length
      endpointCall.outerContext.length sourceCall.rels endpointCall.rels :=
  focus.intrinsic.context

/-- Ordinary intrinsic focus projected from the compiler zipper. -/
def CompiledZipper.toContextFocus
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source site endpointCall endpoint) :
    Region.ContextFocus source.erase where
  holeWires := endpointCall.outerContext.length
  holeRels := endpointCall.rels
  context := focus.context
  body := focus.body
  rebuild := focus.intrinsic.rebuild

@[simp] theorem CompiledZipper.toContextFocus_holeWires
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source site endpointCall endpoint) :
    focus.toContextFocus.holeWires = endpointCall.outerContext.length := rfl

@[simp] theorem CompiledZipper.toContextFocus_holeRels
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source site endpointCall endpoint) :
    focus.toContextFocus.holeRels = endpointCall.rels := rfl

@[simp] theorem CompiledZipper.toContextFocus_body
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source site endpointCall endpoint) :
    focus.toContextFocus.body = endpoint.erase := rfl

mutual
  private inductive CompiledRegion.OriginsValid (d : Diagram) :
      {call : CompilerCall d} → CompiledRegion d call → Prop
    | mk {call : CompilerCall d}
        {items : CompiledItems d call.childFuel call.fullContext
          call.rels call.binders}
        (origins : items.origins = localOccurrences d call.origin)
        (children : CompiledItems.OriginsValid d items) :
        CompiledRegion.OriginsValid d (.mk items)

  private inductive CompiledItem.OriginsValid (d : Diagram) :
      {fuel : Nat} → {context : WireContext d} → {rels : RelCtx} →
      {binders : BinderContext d rels} →
      CompiledItem d fuel context rels binders → Prop
    | node {fuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.nodeCount}
        {item : Item context.length rels} :
        CompiledItem.OriginsValid d
          (CompiledItem.node (fuel := fuel) (binders := binders) origin item)
    | cut {childFuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {body : CompiledRegion d
          (.nested childFuel origin context rels binders)}
        (bodyValid : CompiledRegion.OriginsValid d body) :
        CompiledItem.OriginsValid d (.cut body)
    | bubble {childFuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {arity : Nat}
        {body : CompiledRegion d
          (.nested childFuel origin context (arity :: rels)
            (binders.push origin arity))}
        (bodyValid : CompiledRegion.OriginsValid d body) :
        CompiledItem.OriginsValid d (.bubble arity body)

  private inductive CompiledItems.OriginsValid (d : Diagram) :
      {fuel : Nat} → {context : WireContext d} → {rels : RelCtx} →
      {binders : BinderContext d rels} →
      CompiledItems d fuel context rels binders → Prop
    | nil {fuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} :
        CompiledItems.OriginsValid d
          (CompiledItems.nil (fuel := fuel) (context := context)
            (rels := rels) (binders := binders))
    | cons {fuel : Nat} {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels}
        {head : CompiledItem d fuel context rels binders}
        {tail : CompiledItems d fuel context rels binders}
        (headValid : CompiledItem.OriginsValid d head)
        (tailValid : CompiledItems.OriginsValid d tail) :
        CompiledItems.OriginsValid d (.cons head tail)
end

private theorem compileNode?_originsValid
    {item : CompiledItem d fuel context rels binders}
    (compiled : compileNode? d fuel context binders node = some item) :
    CompiledItem.OriginsValid d item := by
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
                  exact .node
  | identity region arity =>
      simp only [compileNode?, hnode] at compiled
      cases harguments : resolvePorts? d context node arity with
      | none => simp [harguments] at compiled
      | some arguments =>
          simp [harguments] at compiled
          subst item
          exact .node

private theorem compileOccurrenceZero?_originsValid
    {item : CompiledItem d 0 context rels binders}
    (compiled : compileOccurrence? d 0 context binders occurrence =
      some item) : CompiledItem.OriginsValid d item := by
  cases occurrence with
  | node node => exact compileNode?_originsValid compiled
  | child child => simp at compiled

private theorem compileOccurrenceSucc?_originsValid
    (nestedValid : ∀ {nestedRels : RelCtx}
      {origin : Fin d.regionCount} {nestedContext : WireContext d}
      {nestedBinders : BinderContext d nestedRels}
      {body : CompiledRegion d
        (.nested childFuel origin nestedContext nestedRels nestedBinders)},
      compileRegion? d childFuel origin nestedContext nestedBinders =
      some body → CompiledRegion.OriginsValid d body)
    {item : CompiledItem d (childFuel + 1) context rels binders}
    (compiled : compileOccurrence? d (childFuel + 1) context binders
      occurrence = some item) : CompiledItem.OriginsValid d item := by
  cases occurrence with
  | node node => exact compileNode?_originsValid compiled
  | child child =>
      cases hregion : d.regions child with
      | sheet =>
          rw [compileOccurrence?_child_succ_sheet _ _ _ _ _ hregion]
            at compiled
          contradiction
      | cut parent =>
          rw [compileOccurrence?_child_succ_cut _ _ _ _ _ _ hregion]
            at compiled
          cases hbody : compileRegion? d childFuel child context binders with
          | none => simp [hbody] at compiled
          | some body =>
              simp [hbody] at compiled
              subst item
              exact .cut (nestedValid hbody)
      | bubble parent arity =>
          rw [compileOccurrence?_child_succ_bubble _ _ _ _ _ _ _ hregion]
            at compiled
          cases hbody : compileRegion? d childFuel child context
              (binders.push child arity) with
          | none => simp [hbody] at compiled
          | some body =>
              simp [hbody] at compiled
              subst item
              exact .bubble (nestedValid hbody)

private theorem compileItemsZero?_originsValid
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d 0 context rels binders}
    (compiled : compileItems? d 0 context binders occurrences = some items) :
    CompiledItems.OriginsValid d items := by
  induction occurrences generalizing items with
  | nil =>
      simp only [compileItems?_nil] at compiled
      cases compiled
      exact .nil
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hitem : compileOccurrence? d 0 context binders occurrence with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileItems? d 0 context binders tail with
          | none => simp [hitem, htail] at compiled
          | some rest =>
              simp [hitem, htail] at compiled
              subst items
              exact .cons (compileOccurrenceZero?_originsValid hitem)
                (ih htail)

private theorem compileItemsSucc?_originsValid
    (nestedValid : ∀ {nestedRels : RelCtx}
      {origin : Fin d.regionCount} {nestedContext : WireContext d}
      {nestedBinders : BinderContext d nestedRels}
      {body : CompiledRegion d
        (.nested childFuel origin nestedContext nestedRels nestedBinders)},
      compileRegion? d childFuel origin nestedContext nestedBinders =
      some body → CompiledRegion.OriginsValid d body)
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d (childFuel + 1) context rels binders}
    (compiled : compileItems? d (childFuel + 1) context binders occurrences =
      some items) : CompiledItems.OriginsValid d items := by
  induction occurrences generalizing items with
  | nil =>
      simp only [compileItems?_nil] at compiled
      cases compiled
      exact .nil
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hitem : compileOccurrence? d (childFuel + 1) context binders
          occurrence with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileItems? d (childFuel + 1) context binders tail with
          | none => simp [hitem, htail] at compiled
          | some rest =>
              simp [hitem, htail] at compiled
              subst items
              exact .cons
                (compileOccurrenceSucc?_originsValid nestedValid hitem)
                (ih htail)

private theorem compileRegion?_originsValid
    {body : CompiledRegion d
      (.nested childFuel origin context rels binders)}
    (compiled : compileRegion? d childFuel origin context binders = some body) :
    CompiledRegion.OriginsValid d body := by
  induction childFuel generalizing origin context rels binders with
  | zero =>
      rw [compileRegion?_eq_compileItems?] at compiled
      cases hitems : compileItems? d 0 (context.extend origin) binders
          (localOccurrences d origin) with
      | none => simp [hitems] at compiled
      | some items =>
          simp [hitems] at compiled
          subst body
          exact .mk (compileItems?_origins hitems)
            (compileItemsZero?_originsValid hitems)
  | succ childFuel ih =>
      rw [compileRegion?_eq_compileItems?] at compiled
      cases hitems : compileItems? d (childFuel + 1)
          (context.extend origin) binders (localOccurrences d origin) with
      | none => simp [hitems] at compiled
      | some items =>
          simp [hitems] at compiled
          subst body
          exact .mk (compileItems?_origins hitems)
            (compileItemsSucc?_originsValid
              (fun equation => ih equation) hitems)

private theorem compileItems?_originsValid
    {items : CompiledItems d fuel context rels binders}
    (compiled : compileItems? d fuel context binders occurrences =
      some items) : CompiledItems.OriginsValid d items := by
  cases fuel with
  | zero => exact compileItemsZero?_originsValid compiled
  | succ childFuel =>
      exact compileItemsSucc?_originsValid
        (fun equation => compileRegion?_originsValid equation) compiled

private theorem compileRoot?_originsValid
    {body : CompiledRegion d (.root ambient locals)}
    (compiled : compileRoot? d ambient locals = some body) :
    CompiledRegion.OriginsValid d body := by
  simp only [compileRoot?] at compiled
  cases hitems : compileItems? d d.regionCount (ambient ++ locals)
      BinderContext.empty (localOccurrences d d.root) with
  | none => simp [hitems] at compiled
  | some items =>
      simp [hitems] at compiled
      subst body
      exact .mk (compileItems?_origins hitems)
        (compileItems?_originsValid hitems)

mutual
  private def CompiledZipper.endpoint_origins
      {d : Diagram} {sourceCall endpointCall : CompilerCall d}
      {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
      {endpoint : CompiledRegion d endpointCall} :
      (focus : CompiledZipper d source site endpointCall endpoint) →
      CompiledRegion.OriginsValid d source →
      endpoint.items.origins = localOccurrences d site
    | .here _, valid => by
        cases valid with
        | mk origins _ => exact origins
    | .child nested, valid => by
        cases valid with
        | mk _ children => exact nested.endpoint_origins children

  private def CompiledItemsZipper.endpoint_origins
      {d : Diagram} {fuel : Nat} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d fuel context rels binders}
      {site : Fin d.regionCount} {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall} :
      (focus : CompiledItemsZipper d items site endpointCall endpoint) →
      CompiledItems.OriginsValid d items →
      endpoint.items.origins = localOccurrences d site
    | .cut nested, valid => by
        cases valid with
        | cons headValid _ =>
            cases headValid with
            | cut bodyValid => exact nested.endpoint_origins bodyValid
    | .bubble nested, valid => by
        cases valid with
        | cons headValid _ =>
            cases headValid with
            | bubble bodyValid => exact nested.endpoint_origins bodyValid
    | .tail nested, valid => by
        cases valid with
        | cons _ tailValid => exact nested.endpoint_origins tailValid
end

private theorem compileItems?_zipper_of_child
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {items : CompiledItems d fuel context rels binders}
    (compiled : compileItems? d fuel context binders occurrences = some items)
    (child site : Fin d.regionCount)
    (member : LocalOccurrence.child child ∈ occurrences)
    (cutComplete : ∀ {childFuel : Nat}
      {body : CompiledRegion d
        (.nested childFuel child context rels binders)},
      fuel = childFuel + 1 →
      compileRegion? d childFuel child context binders = some body →
      Nonempty (CompiledFocus body site))
    (bubbleComplete : ∀ {childFuel : Nat} {arity : Nat}
      {body : CompiledRegion d
        (.nested childFuel child context (arity :: rels)
          (binders.push child arity))},
      fuel = childFuel + 1 →
      compileRegion? d childFuel child context
        (binders.push child arity) = some body →
      Nonempty (CompiledFocus body site)) :
    Nonempty (Σ endpointCall, Σ endpoint : CompiledRegion d endpointCall,
      CompiledItemsZipper d items site endpointCall endpoint) := by
  induction occurrences generalizing items with
  | nil => simp at member
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      cases hitem : compileOccurrence? d fuel context binders occurrence with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileItems? d fuel context binders tail with
          | none => simp [hitem, htail] at compiled
          | some suffix =>
              simp [hitem, htail] at compiled
              subst items
              rcases List.mem_cons.mp member with head | tailMember
              · subst occurrence
                cases fuel with
                | zero => simp at hitem
                | succ childFuel =>
                    cases hregion : d.regions child with
                    | sheet =>
                        rw [compileOccurrence?_child_succ_sheet
                          _ _ _ _ _ hregion] at hitem
                        contradiction
                    | cut parent =>
                        rw [compileOccurrence?_child_succ_cut
                          _ _ _ _ _ _ hregion] at hitem
                        cases hbody : compileRegion? d childFuel child context
                            binders with
                        | none => simp [hbody] at hitem
                        | some body =>
                            simp [hbody] at hitem
                            subst item
                            obtain ⟨nested⟩ := cutComplete rfl hbody
                            exact ⟨⟨nested.endpointCall, nested.endpoint,
                              .cut nested.zipper⟩⟩
                    | bubble parent arity =>
                        rw [compileOccurrence?_child_succ_bubble
                          _ _ _ _ _ _ _ hregion] at hitem
                        cases hbody : compileRegion? d childFuel child context
                            (binders.push child arity) with
                        | none => simp [hbody] at hitem
                        | some body =>
                            simp [hbody] at hitem
                            subst item
                            obtain ⟨nested⟩ := bubbleComplete rfl hbody
                            exact ⟨⟨nested.endpointCall, nested.endpoint,
                              .bubble nested.zipper⟩⟩
              · obtain ⟨⟨endpointCall, endpoint, nested⟩⟩ :=
                    ih htail tailMember
                exact ⟨⟨endpointCall, endpoint, .tail nested⟩⟩

private theorem compileRegion?_focus
    (hwf : d.WellFormed)
    {body : CompiledRegion d
      (.nested childFuel origin context rels binders)}
    (compiled : compileRegion? d childFuel origin context binders = some body)
    (encloses : d.Encloses origin site) :
    Nonempty (CompiledFocus body site) := by
  induction childFuel generalizing origin context rels binders site with
  | zero =>
      by_cases same : origin = site
      · subst site
        exact ⟨⟨_, body, .here body⟩⟩
      · obtain ⟨child, childParent, childEncloses⟩ :=
          exists_direct_child_enclosing hwf (Ne.symm same) encloses
        rw [compileRegion?_eq_compileItems?] at compiled
        cases hitems : compileItems? d 0 (context.extend origin) binders
            (localOccurrences d origin) with
        | none => simp [hitems] at compiled
        | some items =>
            simp [hitems] at compiled
            subst body
            obtain ⟨⟨endpointCall, endpoint, nested⟩⟩ :=
              compileItems?_zipper_of_child hitems child site
                ((mem_localOccurrences_child d origin child).mpr childParent)
                (fun equality _ => by omega)
                (fun equality _ => by omega)
            exact ⟨⟨endpointCall, endpoint, .child nested⟩⟩
  | succ childFuel ih =>
      by_cases same : origin = site
      · subst site
        exact ⟨⟨_, body, .here body⟩⟩
      · obtain ⟨child, childParent, childEncloses⟩ :=
          exists_direct_child_enclosing hwf (Ne.symm same) encloses
        rw [compileRegion?_eq_compileItems?] at compiled
        cases hitems : compileItems? d (childFuel + 1)
            (context.extend origin) binders (localOccurrences d origin) with
        | none => simp [hitems] at compiled
        | some items =>
            simp [hitems] at compiled
            subst body
            obtain ⟨⟨endpointCall, endpoint, nested⟩⟩ :=
              compileItems?_zipper_of_child hitems child site
                ((mem_localOccurrences_child d origin child).mpr childParent)
                (fun equality bodyCompiled => by
                  have fuelEq := Nat.add_right_cancel equality
                  subst_vars
                  exact ih bodyCompiled childEncloses)
                (fun equality bodyCompiled => by
                  have fuelEq := Nat.add_right_cancel equality
                  subst_vars
                  exact ih bodyCompiled childEncloses)
            exact ⟨⟨endpointCall, endpoint, .child nested⟩⟩

private theorem compileRoot?_focus
    (hwf : d.WellFormed) (ambient locals : WireContext d)
    {body : CompiledRegion d (.root ambient locals)}
    (compiled : compileRoot? d ambient locals = some body)
    (site : Fin d.regionCount) : Nonempty (CompiledFocus body site) := by
  by_cases same : d.root = site
  · subst site
    exact ⟨⟨_, body, .here body⟩⟩
  · obtain ⟨child, childParent, childEncloses⟩ :=
      exists_direct_child_enclosing hwf (Ne.symm same)
        (hwf.all_regions_reach_root site)
    simp only [compileRoot?] at compiled
    cases hitems : compileItems? d d.regionCount (ambient ++ locals)
        BinderContext.empty (localOccurrences d d.root) with
    | none => simp [hitems] at compiled
    | some items =>
        simp [hitems] at compiled
        subst body
        obtain ⟨⟨endpointCall, endpoint, nested⟩⟩ :=
          compileItems?_zipper_of_child hitems child site
            ((mem_localOccurrences_child d d.root child).mpr childParent)
            (fun _ bodyCompiled =>
              compileRegion?_focus hwf bodyCompiled childEncloses)
            (fun _ bodyCompiled =>
              compileRegion?_focus hwf bodyCompiled childEncloses)
        exact ⟨⟨endpointCall, endpoint, .child nested⟩⟩

namespace CheckedOpen

private theorem compilation_focus
    (checked : CheckedOpen)
    (site : Fin checked.val.diagram.regionCount) :
    Nonempty (CompiledFocus checked.compilation site) :=
  compileRoot?_focus checked.property.diagram_well_formed
    checked.val.exposedWires checked.val.hiddenWires
    checked.compilation_computation site

private theorem compilation_originsValid (checked : CheckedOpen) :
    CompiledRegion.OriginsValid checked.val.diagram checked.compilation :=
  compileRoot?_originsValid checked.compilation_computation

end CheckedOpen

/-- A source site stores exactly one structural focus over the checked root
compilation. Every endpoint and intrinsic value is projected from this field. -/
structure CompiledSite (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) where
  focus : CompiledFocus source.checked.compilation site

namespace CompiledSite

noncomputable def ofSource (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledSite source site where
  focus := Classical.choice (CheckedOpen.compilation_focus source.checked site)

def endpointCall (compiled : CompiledSite source site) :
    CompilerCall source.checked.val.diagram :=
  compiled.focus.endpointCall

def endpoint (compiled : CompiledSite source site) :
    CompiledRegion source.checked.val.diagram compiled.endpointCall :=
  compiled.focus.endpoint

def zipper (compiled : CompiledSite source site) :
    CompiledZipper source.checked.val.diagram source.checked.compilation site
      compiled.endpointCall compiled.endpoint :=
  compiled.focus.zipper

def directItems (compiled : CompiledSite source site) :
    CompiledItems source.checked.val.diagram compiled.endpointCall.childFuel
      compiled.endpointCall.fullContext compiled.endpointCall.rels
      compiled.endpointCall.binders :=
  compiled.endpoint.items

theorem directItems_origins (compiled : CompiledSite source site) :
    compiled.directItems.origins =
      localOccurrences source.checked.val.diagram site :=
  compiled.zipper.endpoint_origins
    (CheckedOpen.compilation_originsValid source.checked)

def intrinsic (compiled : CompiledSite source site) :
    Region.ContextFocus source.checked.elaborate.body :=
  compiled.zipper.toContextFocus

def context (compiled : CompiledSite source site) :
    DiagramContext source.checked.val.exposedWires.length
      compiled.endpointCall.outerContext.length [] compiled.endpointCall.rels :=
  compiled.zipper.context

def body (compiled : CompiledSite source site) :
    Region compiled.endpointCall.outerContext.length compiled.endpointCall.rels :=
  compiled.endpoint.erase

def cutDepth (compiled : CompiledSite source site) : Nat :=
  compiled.context.cutDepth

def sourceOccurrence (compiled : CompiledSite source site) :
    Option (LocalOccurrence source.checked.val.diagram.regionCount
      source.checked.val.diagram.nodeCount) :=
  match compiled.endpointCall with
  | .root _ _ => none
  | .nested _ origin _ _ _ => some (.child origin)

theorem rebuild (compiled : CompiledSite source site) :
    compiled.context.fill compiled.body = source.checked.elaborate.body :=
  compiled.zipper.intrinsic.rebuild

end CompiledSite

/-- Classify exactly the direct anchor occurrences named by a checked
selection. A selected child root remains one atomic occurrence. -/
def checkedSelectionAnchorClassifier (selection : CheckedSelection d) :
    LocalOccurrence d.regionCount d.nodeCount → Bool
  | .node node => decide (node ∈ selection.val.directNodes)
  | .child child => decide (child ∈ selection.val.childRoots)

@[simp] theorem checkedSelectionAnchorClassifier_node
    (selection : CheckedSelection d) (node : Fin d.nodeCount) :
    checkedSelectionAnchorClassifier selection (.node node) =
      decide (node ∈ selection.val.directNodes) := rfl

@[simp] theorem checkedSelectionAnchorClassifier_child
    (selection : CheckedSelection d) (child : Fin d.regionCount) :
    checkedSelectionAnchorClassifier selection (.child child) =
      decide (child ∈ selection.val.childRoots) := rfl

/-- Selection compilation stores only the anchor's sole source focus. -/
structure CompiledSelection (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) where
  anchor : CompiledSite source selection.val.anchor

namespace CompiledSelection

noncomputable def ofSource (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    CompiledSelection source selection where
  anchor := CompiledSite.ofSource source selection.val.anchor

def anchorItems (compiled : CompiledSelection source selection) :
    CompiledItems source.checked.val.diagram
      compiled.anchor.endpointCall.childFuel
      compiled.anchor.endpointCall.fullContext
      compiled.anchor.endpointCall.rels compiled.anchor.endpointCall.binders :=
  compiled.anchor.directItems

def partition (compiled : CompiledSelection source selection) :
    CompiledItems.Partition compiled.anchorItems :=
  compiled.anchorItems.partition (checkedSelectionAnchorClassifier selection)

def retained (compiled : CompiledSelection source selection) :
    CompiledItems source.checked.val.diagram
      compiled.anchor.endpointCall.childFuel
      compiled.anchor.endpointCall.fullContext
      compiled.anchor.endpointCall.rels compiled.anchor.endpointCall.binders :=
  compiled.partition.retained

def material (compiled : CompiledSelection source selection) :
    CompiledItems source.checked.val.diagram
      compiled.anchor.endpointCall.childFuel
      compiled.anchor.endpointCall.fullContext
      compiled.anchor.endpointCall.rels compiled.anchor.endpointCall.binders :=
  compiled.partition.material

def intrinsic (compiled : CompiledSelection source selection) :
    ItemSeq compiled.anchor.endpointCall.fullContext.length
      compiled.anchor.endpointCall.rels :=
  compiled.anchorItems.erase

def retainedIntrinsic (compiled : CompiledSelection source selection) :
    ItemSeq compiled.anchor.endpointCall.fullContext.length
      compiled.anchor.endpointCall.rels :=
  compiled.retained.erase

def materialIntrinsic (compiled : CompiledSelection source selection) :
    ItemSeq compiled.anchor.endpointCall.fullContext.length
      compiled.anchor.endpointCall.rels :=
  compiled.material.erase

noncomputable def factorization
    (compiled : CompiledSelection source selection) :
    ItemSeqIso
      (FiniteEquiv.refl
        (Fin compiled.anchor.endpointCall.fullContext.length))
      compiled.anchor.endpointCall.rels compiled.intrinsic
      (compiled.retainedIntrinsic.append compiled.materialIntrinsic) := by
  simpa [intrinsic, retainedIntrinsic, materialIntrinsic, retained, material,
    partition, CompiledItems.erase_append] using
      CompiledItems.partitionFactorization
        (checkedSelectionAnchorClassifier selection) compiled.anchorItems

noncomputable def positionMap
    (compiled : CompiledSelection source selection) :
    FiniteEquiv (Fin compiled.intrinsic.length)
      (Fin (compiled.retainedIntrinsic.append
        compiled.materialIntrinsic).length) :=
  match compiled.factorization with
  | .permute positions _ => positions

theorem anchor_origins (compiled : CompiledSelection source selection) :
    compiled.anchorItems.origins =
      localOccurrences source.checked.val.diagram selection.val.anchor :=
  compiled.anchor.directItems_origins

theorem retained_origins_eq_unselected
    (compiled : CompiledSelection source selection) :
    compiled.retained.origins =
      (localOccurrences source.checked.val.diagram selection.val.anchor).filter
        fun occurrence =>
          !checkedSelectionAnchorClassifier selection occurrence := by
  change (compiled.anchorItems.partition
    (checkedSelectionAnchorClassifier selection)).retained.origins = _
  rw [CompiledItems.partition_retained_origins, compiled.anchor_origins]

theorem material_origins_eq_selected
    (compiled : CompiledSelection source selection) :
    compiled.material.origins =
      (localOccurrences source.checked.val.diagram selection.val.anchor).filter
        (checkedSelectionAnchorClassifier selection) := by
  change (compiled.anchorItems.partition
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
    List.Sublist compiled.retained.origins compiled.anchorItems.origins :=
  CompiledItems.partition_retained_stable
    (checkedSelectionAnchorClassifier selection) compiled.anchorItems

theorem material_stable (compiled : CompiledSelection source selection) :
    List.Sublist compiled.material.origins compiled.anchorItems.origins :=
  CompiledItems.partition_material_stable
    (checkedSelectionAnchorClassifier selection) compiled.anchorItems

theorem origins_factorization
    (compiled : CompiledSelection source selection) :
    compiled.anchorItems.origins.Perm
      (compiled.retained.origins ++ compiled.material.origins) :=
  CompiledItems.partition_origins_perm
    (checkedSelectionAnchorClassifier selection) compiled.anchorItems

theorem classified_once (compiled : CompiledSelection source selection) :
    (compiled.retained.origins ++ compiled.material.origins).Nodup := by
  have originalNodup : compiled.anchorItems.origins.Nodup := by
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
