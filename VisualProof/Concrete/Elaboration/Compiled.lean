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

private structure CompiledEndpointValidity (d : Diagram)
    (site : Fin d.regionCount) (call : CompilerCall d)
    (endpoint : CompiledRegion d call) : Prop where
  computation : call.compile? = some endpoint
  origin : call.origin = site
  fullContext_exact : call.fullContext.Exact site
  binders_covers : call.binders.Covers site
  origins : endpoint.items.origins = localOccurrences d site

mutual
  private def CompiledZipper.endpoint_validity
      {d : Diagram} {sourceCall endpointCall : CompilerCall d}
      {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
      {endpoint : CompiledRegion d endpointCall}
      (hwf : d.WellFormed) :
      (focus : CompiledZipper d source site endpointCall endpoint) →
      sourceCall.compile? = some source →
      sourceCall.fullContext.Exact sourceCall.origin →
      sourceCall.binders.Covers sourceCall.origin →
      CompiledEndpointValidity d site endpointCall endpoint
    | .here source, compiled, wires, binders => by
        have origins : source.items.origins =
            localOccurrences d sourceCall.origin := by
          rw [CompilerCall.compile?_eq_compileItems?] at compiled
          cases hitems : compileItems? d sourceCall.childFuel
              sourceCall.fullContext sourceCall.binders
              (localOccurrences d sourceCall.origin) with
          | none => simp [hitems] at compiled
          | some items =>
              simp [hitems] at compiled
              subst source
              exact compileItems?_origins hitems
        exact ⟨compiled, rfl, wires, binders, origins⟩
    | .child nested, compiled, wires, binders => by
        rw [CompilerCall.compile?_eq_compileItems?] at compiled
        cases hitems : compileItems? d sourceCall.childFuel
            sourceCall.fullContext sourceCall.binders
            (localOccurrences d sourceCall.origin) with
        | none => simp [hitems] at compiled
        | some items =>
            simp [hitems] at compiled
            subst items
            refine nested.endpoint_validity hwf sourceCall.origin wires binders
              ?_ ?_
            · intro occurrence member
              have origins := compileItems?_origins hitems
              simpa only [origins] using member
            · have origins := compileItems?_origins hitems
              rw [origins]
              exact hitems

  private def CompiledItemsZipper.endpoint_validity
      {d : Diagram} {fuel : Nat} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d fuel context rels binders}
      {site : Fin d.regionCount} {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall}
      (hwf : d.WellFormed) :
      (focus : CompiledItemsZipper d items site endpointCall endpoint) →
      (parent : Fin d.regionCount) →
      context.Exact parent → binders.Covers parent →
      (∀ occurrence, occurrence ∈ items.origins →
        occurrence ∈ localOccurrences d parent) →
      compileItems? d fuel context binders items.origins = some items →
      CompiledEndpointValidity d site endpointCall endpoint
    | .cut (childFuel := childFuel) (origin := origin)
        (suffix := suffix) nested,
        parent, wires, bindersCover, localOccurrencesValid, compiled => by
        simp only [CompiledItems.origins, CompiledItem.origin] at compiled
        rw [compileItems?_cons] at compiled
        cases hhead : compileOccurrence? d (childFuel + 1) context binders
            (.child origin) with
        | none => simp [hhead] at compiled
        | some head =>
            cases htail : compileItems? d (childFuel + 1) context binders
                suffix.origins with
            | none => simp [hhead, htail] at compiled
            | some rest =>
                simp [hhead, htail] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                obtain ⟨childParent, hregion, hbody⟩ :=
                  compileOccurrence?_child_cut_body hhead
                have hparent : (d.regions origin).parent? = some parent :=
                  (mem_localOccurrences_child d parent origin).mp
                    (localOccurrencesValid (.child origin)
                      (by simp [CompiledItem.origin]))
                have childParentEq : childParent = parent := by
                  apply Option.some.inj
                  simpa [hregion, CRegion.parent?] using hparent
                subst childParent
                apply nested.endpoint_validity hwf hbody
                · simpa [CompilerCall.fullContext, CompilerCall.localContext,
                    WireContext.extend] using
                    wires.extend_child hwf (by simp [hregion, CRegion.parent?])
                · exact BinderContext.covers_cut_child bindersCover hregion
    | .bubble (childFuel := childFuel) (origin := origin)
        (arity := arity) (suffix := suffix) nested,
        parent, wires, bindersCover, localOccurrencesValid, compiled => by
        simp only [CompiledItems.origins, CompiledItem.origin] at compiled
        rw [compileItems?_cons] at compiled
        cases hhead : compileOccurrence? d (childFuel + 1) context binders
            (.child origin) with
        | none => simp [hhead] at compiled
        | some head =>
            cases htail : compileItems? d (childFuel + 1) context binders
                suffix.origins with
            | none => simp [hhead, htail] at compiled
            | some rest =>
                simp [hhead, htail] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                obtain ⟨childParent, hregion, hbody⟩ :=
                  compileOccurrence?_child_bubble_body hhead
                have hparent : (d.regions origin).parent? = some parent :=
                  (mem_localOccurrences_child d parent origin).mp
                    (localOccurrencesValid (.child origin)
                      (by simp [CompiledItem.origin]))
                have childParentEq : childParent = parent := by
                  apply Option.some.inj
                  simpa [hregion, CRegion.parent?] using hparent
                subst childParent
                apply nested.endpoint_validity hwf hbody
                · simpa [CompilerCall.fullContext, CompilerCall.localContext,
                    WireContext.extend] using
                    wires.extend_child hwf (by simp [hregion, CRegion.parent?])
                · exact BinderContext.push_covers_bubble_child
                    bindersCover hregion
    | .tail (head := head) (suffix := suffix) nested,
        parent, wires, bindersCover, localOccurrencesValid, compiled => by
        simp only [CompiledItems.origins] at compiled
        rw [compileItems?_cons] at compiled
        cases hhead : compileOccurrence? d fuel context binders head.origin with
        | none => simp [hhead] at compiled
        | some compiledHead =>
            cases htail : compileItems? d fuel context binders
                suffix.origins with
            | none => simp [hhead, htail] at compiled
            | some rest =>
                simp [hhead, htail] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                exact nested.endpoint_validity hwf parent wires bindersCover
                  (fun occurrence member =>
                    localOccurrencesValid occurrence (by simp [member]))
                  htail
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

private def endpoint_validity (compiled : CompiledSite source site) :
    CompiledEndpointValidity source.checked.val.diagram site
      compiled.endpointCall compiled.endpoint :=
  compiled.zipper.endpoint_validity
    source.checked.property.diagram_well_formed
    (by simpa using source.checked.compilation_computation)
    (by
      simpa [CompilerCall.fullContext, OpenDiagram.rootWires] using
        openRootWires_exact source.checked.property)
    (by
      simpa using BinderContext.empty_covers_root
        source.checked.property.diagram_well_formed)

theorem endpoint_computation (compiled : CompiledSite source site) :
    compiled.endpointCall.compile? = some compiled.endpoint :=
  compiled.endpoint_validity.computation

theorem endpoint_origin (compiled : CompiledSite source site) :
    compiled.endpointCall.origin = site :=
  compiled.endpoint_validity.origin

theorem endpoint_fullContext_exact (compiled : CompiledSite source site) :
    compiled.endpointCall.fullContext.Exact site :=
  compiled.endpoint_validity.fullContext_exact

theorem endpoint_binders_covers (compiled : CompiledSite source site) :
    compiled.endpointCall.binders.Covers site :=
  compiled.endpoint_validity.binders_covers

def directItems (compiled : CompiledSite source site) :
    CompiledItems source.checked.val.diagram compiled.endpointCall.childFuel
      compiled.endpointCall.fullContext compiled.endpointCall.rels
      compiled.endpointCall.binders :=
  compiled.endpoint.items

theorem directItems_origins (compiled : CompiledSite source site) :
    compiled.directItems.origins =
      localOccurrences source.checked.val.diagram site :=
  compiled.endpoint_validity.origins

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
