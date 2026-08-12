import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.State
import VisualProof.Concrete.Subgraph.Selection

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-!
A compiled source focus is one structural zipper found in the sole
signature-indexed compiler result. Exact endpoint inputs remain indices of the
selected result; intrinsic context, body, and rebuilding are projections of
that zipper.
-/

mutual
  inductive CompiledZipper (d : Diagram) :
      {sourceCall : CompilerCall d} ->
      CompiledRegion d sourceCall ->
      (endpointCall : CompilerCall d) ->
      CompiledRegion d endpointCall -> Type
    | here {sourceCall : CompilerCall d}
        (source : CompiledRegion d sourceCall) :
        CompiledZipper d source sourceCall source
    | child {sourceCall endpointCall : CompilerCall d}
        {nodes children : CompiledItems d sourceCall.fullContext
          sourceCall.rels sourceCall.binders}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledItemsZipper d children endpointCall endpoint) :
        CompiledZipper d (.mk nodes children) endpointCall endpoint

  inductive CompiledItemsZipper (d : Diagram) :
      {context : WireContext d} -> {rels : RelCtx} ->
      {binders : BinderContext d rels} ->
      CompiledItems d context rels binders ->
      (endpointCall : CompilerCall d) ->
      CompiledRegion d endpointCall -> Type
    | cut {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {body : CompiledRegion d
          (.nested origin context rels binders)}
        {suffix : CompiledItems d context rels binders}
        {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledZipper d body endpointCall endpoint) :
        CompiledItemsZipper d (.cons (.cut body) suffix) endpointCall
          endpoint
    | bubble {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {arity : Nat}
        {body : CompiledRegion d
          (.nested origin context (arity :: rels)
            (binders.push origin arity))}
        {suffix : CompiledItems d context rels binders}
        {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledZipper d body endpointCall endpoint) :
        CompiledItemsZipper d (.cons (.bubble arity body) suffix)
          endpointCall endpoint
    | tail {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels}
        {head : CompiledItem d context rels binders}
        {suffix : CompiledItems d context rels binders}
        {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledItemsZipper d suffix endpointCall endpoint) :
        CompiledItemsZipper d (.cons head suffix) endpointCall endpoint
end

/-- The result of finding an exact endpoint and its structural selection in a
compiled region. -/
structure CompiledFocus {d : Diagram} {sourceCall : CompilerCall d}
    (source : CompiledRegion d sourceCall) where
  endpointCall : CompilerCall d
  endpoint : CompiledRegion d endpointCall
  zipper : CompiledZipper d source endpointCall endpoint

mutual
  /-- Canonically search the sole compiled region tree for a site. -/
  def CompiledRegion.focus?
      {d : Diagram} {sourceCall : CompilerCall d}
      (source : CompiledRegion d sourceCall) (site : Fin d.regionCount) :
      Option (CompiledFocus source) :=
    if _same : sourceCall.origin = site then
      some {
        endpointCall := sourceCall
        endpoint := source
        zipper := .here source
      }
    else
      match source with
      | .mk _nodes children =>
          (children.focus? site).map fun ⟨endpointCall, endpoint, zipper⟩ =>
            ⟨endpointCall, endpoint, .child zipper⟩

  private def CompiledItems.focus?
      {d : Diagram} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      (items : CompiledItems d context rels binders)
      (site : Fin d.regionCount) :
      Option (Σ endpointCall, Σ endpoint : CompiledRegion d endpointCall,
        CompiledItemsZipper d items endpointCall endpoint) :=
    match items with
    | .nil => none
    | .cons (.node _ _) tail =>
        match tail.focus? site with
        | none => none
        | some ⟨endpointCall, endpoint, zipper⟩ =>
            some ⟨endpointCall, endpoint, .tail zipper⟩
    | .cons (.cut body) tail =>
        match body.focus? site with
        | some focus =>
            some ⟨focus.endpointCall, focus.endpoint, .cut focus.zipper⟩
        | none =>
            match tail.focus? site with
            | none => none
            | some ⟨endpointCall, endpoint, zipper⟩ =>
                some ⟨endpointCall, endpoint, .tail zipper⟩
    | .cons (.bubble _ body) tail =>
        match body.focus? site with
        | some focus =>
            some ⟨focus.endpointCall, focus.endpoint, .bubble focus.zipper⟩
        | none =>
            match tail.focus? site with
            | none => none
            | some ⟨endpointCall, endpoint, zipper⟩ =>
                some ⟨endpointCall, endpoint, .tail zipper⟩
end

@[simp] theorem CompiledRegion.focus?_origin
    {d : Diagram} {sourceCall : CompilerCall d}
    (source : CompiledRegion d sourceCall) :
    source.focus? sourceCall.origin = some {
      endpointCall := sourceCall
      endpoint := source
      zipper := .here source
    } := by
  unfold CompiledRegion.focus?
  simp

theorem CompiledRegion.focus?_singleton_bubble_eq
    {d : Diagram} {parentCall : CompilerCall d}
    {child : Fin d.regionCount} {arity : Nat}
    {body : CompiledRegion d
      (.nested child parentCall.fullContext (arity :: parentCall.rels)
        (parentCall.binders.push child arity))}
    (site : Fin d.regionCount) (different : parentCall.origin ≠ site) :
    ((CompiledRegion.mk .nil (.cons (.bubble arity body) .nil) :
        CompiledRegion d parentCall).focus? site) =
      (body.focus? site).map fun focus => {
        endpointCall := focus.endpointCall
        endpoint := focus.endpoint
        zipper := .child (.bubble focus.zipper)
      } := by
  cases hbody : body.focus? site <;>
    simp [CompiledRegion.focus?, CompiledItems.focus?, different, hbody]

theorem CompiledRegion.focus?_singleton_bubble
    {d : Diagram} {parentCall : CompilerCall d}
    {child : Fin d.regionCount} {arity : Nat}
    {body : CompiledRegion d
      (.nested child parentCall.fullContext (arity :: parentCall.rels)
        (parentCall.binders.push child arity))}
    {site : Fin d.regionCount} {focus : CompiledFocus body}
    (different : parentCall.origin ≠ site)
    (found : body.focus? site = some focus) :
    ((CompiledRegion.mk .nil (.cons (.bubble arity body) .nil) :
        CompiledRegion d parentCall).focus? site) = some {
      endpointCall := focus.endpointCall
      endpoint := focus.endpoint
      zipper := .child (.bubble focus.zipper)
    } := by
  rw [CompiledRegion.focus?_singleton_bubble_eq site different, found]
  rfl

mutual
  /-- A successful canonical search identifies the requested region by the
  endpoint call's own origin. -/
  theorem CompiledRegion.focus?_endpoint_origin
      {d : Diagram} {sourceCall : CompilerCall d}
      {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
      {result : CompiledFocus source}
      (found : source.focus? site = some result) :
      result.endpointCall.origin = site := by
    unfold CompiledRegion.focus? at found
    split at found
    next same =>
      simp only [Option.some.injEq] at found
      subst result
      exact same
    next different =>
      cases source with
      | mk nodes children =>
          cases itemsFound : children.focus? site with
          | none => simp [itemsFound] at found
          | some packed =>
              obtain ⟨endpointCall, endpoint, zipper⟩ := packed
              simp [itemsFound] at found
              subst result
              exact CompiledItems.focus?_endpoint_origin itemsFound

  private theorem CompiledItems.focus?_endpoint_origin
      {d : Diagram} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d context rels binders}
      {site : Fin d.regionCount} {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall}
      {zipper : CompiledItemsZipper d items endpointCall endpoint}
      (found : items.focus? site = some ⟨endpointCall, endpoint, zipper⟩) :
      endpointCall.origin = site := by
    cases items with
    | nil => simp [CompiledItems.focus?] at found
    | cons item tail =>
        cases item with
        | node origin item =>
            unfold CompiledItems.focus? at found
            cases tailFound : tail.focus? site with
            | none => simp [tailFound] at found
            | some packed =>
                obtain ⟨tailCall, tailEndpoint, tailZipper⟩ := packed
                simp [tailFound] at found
                obtain ⟨rfl, rfl, rfl⟩ := found
                exact CompiledItems.focus?_endpoint_origin tailFound
        | cut body =>
            unfold CompiledItems.focus? at found
            cases bodyFound : body.focus? site with
            | some bodyFocus =>
                simp [bodyFound] at found
                obtain ⟨rfl, rfl, rfl⟩ := found
                exact CompiledRegion.focus?_endpoint_origin bodyFound
            | none =>
                cases tailFound : tail.focus? site with
                | none => simp [bodyFound, tailFound] at found
                | some packed =>
                    obtain ⟨tailCall, tailEndpoint, tailZipper⟩ := packed
                    simp [bodyFound, tailFound] at found
                    obtain ⟨rfl, rfl, rfl⟩ := found
                    exact CompiledItems.focus?_endpoint_origin tailFound
        | bubble arity body =>
            unfold CompiledItems.focus? at found
            cases bodyFound : body.focus? site with
            | some bodyFocus =>
                simp [bodyFound] at found
                obtain ⟨rfl, rfl, rfl⟩ := found
                exact CompiledRegion.focus?_endpoint_origin bodyFound
            | none =>
                cases tailFound : tail.focus? site with
                | none => simp [bodyFound, tailFound] at found
                | some packed =>
                    obtain ⟨tailCall, tailEndpoint, tailZipper⟩ := packed
                    simp [bodyFound, tailFound] at found
                    obtain ⟨rfl, rfl, rfl⟩ := found
                    exact CompiledItems.focus?_endpoint_origin tailFound
end

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
      {endpoint : CompiledRegion d endpointCall} :
      (focus : CompiledZipper d source endpointCall endpoint) ->
        CompiledIntrinsic d source.erase endpointCall endpoint
    | .here _ => ⟨.hole, rfl⟩
    | .child (nodes := nodes) nested => by
        simpa [CompiledRegion.erase, CompilerCall.finish,
          CompilerCall.castFullItems, ItemSeq.castWiresEq_append] using
            nested.intrinsic nodes.erase sourceCall.outerContext.length
              sourceCall.localContext.length sourceCall.fullContext_length

  def CompiledItemsZipper.intrinsic
      {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d context rels binders}
      {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall}
      (focus : CompiledItemsZipper d items endpointCall endpoint)
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
    {source : CompiledRegion d sourceCall}
    {endpoint : CompiledRegion d endpointCall}
    (_focus : CompiledZipper d source endpointCall endpoint) :
    Region endpointCall.outerContext.length endpointCall.rels :=
  endpoint.erase

def CompiledZipper.context {d : Diagram}
    {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source endpointCall endpoint) :
    DiagramContext sourceCall.outerContext.length
      endpointCall.outerContext.length sourceCall.rels endpointCall.rels :=
  focus.intrinsic.context

/-- Ordinary intrinsic focus projected from the compiler zipper. -/
def CompiledZipper.toContextFocus
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source endpointCall endpoint) :
    Region.ContextFocus source.erase where
  holeWires := endpointCall.outerContext.length
  holeRels := endpointCall.rels
  context := focus.context
  body := focus.body
  rebuild := focus.intrinsic.rebuild

@[simp] theorem CompiledZipper.toContextFocus_holeWires
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source endpointCall endpoint) :
    focus.toContextFocus.holeWires = endpointCall.outerContext.length := rfl

@[simp] theorem CompiledZipper.toContextFocus_holeRels
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source endpointCall endpoint) :
    focus.toContextFocus.holeRels = endpointCall.rels := rfl

@[simp] theorem CompiledZipper.toContextFocus_body
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source endpointCall endpoint) :
    focus.toContextFocus.body = endpoint.erase := rfl

private theorem compileOccurrence?_origin
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

private theorem compileItems?_origins
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

private structure CompiledEndpointValidity (d : Diagram)
    (wellFormed : d.WellFormed)
    (call : CompilerCall d)
    (endpoint : CompiledRegion d call) where
  computation : call.compile? d wellFormed = some endpoint
  fullContext_exact : call.fullContext.Exact call.origin
  binders_covers : call.binders.Covers call.origin
  binder_enumeration : BinderContext.Enumeration d call.binders call.origin
  node_origins : endpoint.nodeItems.origins =
    localNodeOccurrences d call.origin
  child_origins : endpoint.childItems.origins =
    localChildOccurrences d call.origin
  origins : endpoint.items.origins = localOccurrences d call.origin

mutual
  private def CompiledZipper.endpoint_validity
      {d : Diagram} {sourceCall endpointCall : CompilerCall d}
      {source : CompiledRegion d sourceCall}
      {endpoint : CompiledRegion d endpointCall}
      (hwf : d.WellFormed) :
      (focus : CompiledZipper d source endpointCall endpoint) →
      sourceCall.compile? d hwf = some source →
      sourceCall.fullContext.Exact sourceCall.origin →
      sourceCall.binders.Covers sourceCall.origin →
      BinderContext.Enumeration d sourceCall.binders sourceCall.origin →
      CompiledEndpointValidity d hwf endpointCall endpoint
    | .here source, compiled, wires, binders, enumeration => by
        have blockOrigins :
            source.nodeItems.origins = localNodeOccurrences d sourceCall.origin ∧
            source.childItems.origins =
              localChildOccurrences d sourceCall.origin := by
          rw [CompilerCall.compile?_eq_compileBlocks? hwf] at compiled
          cases hnodes : compileItems? d hwf sourceCall.origin
              sourceCall.fullContext sourceCall.binders
              (localNodeOccurrences d sourceCall.origin)
              (fun _ member => List.mem_append_left _ member) with
          | none => simp [hnodes] at compiled
          | some nodes =>
              cases hchildren : compileItems? d hwf sourceCall.origin
                  sourceCall.fullContext sourceCall.binders
                  (localChildOccurrences d sourceCall.origin)
                  (fun _ member => List.mem_append_right _ member) with
              | none => simp [hnodes, hchildren] at compiled
              | some children =>
                  simp [hnodes, hchildren] at compiled
                  subst source
                  exact ⟨
                    compileItems?_origins hwf sourceCall.origin
                      sourceCall.fullContext sourceCall.binders hnodes,
                    compileItems?_origins hwf sourceCall.origin
                      sourceCall.fullContext sourceCall.binders hchildren⟩
        have origins : source.items.origins =
            localOccurrences d sourceCall.origin := by
          simp only [CompiledRegion.items,
            CompiledItems.origins_append, localOccurrences,
            blockOrigins.1, blockOrigins.2]
        exact ⟨compiled, wires, binders, enumeration,
          blockOrigins.1, blockOrigins.2, origins⟩
    | .child (nodes := nodes) nested, compiled, wires, binders,
        enumeration => by
        rw [CompilerCall.compile?_eq_compileBlocks? hwf] at compiled
        cases hnodes : compileItems? d hwf sourceCall.origin
            sourceCall.fullContext sourceCall.binders
            (localNodeOccurrences d sourceCall.origin)
            (fun _ member => List.mem_append_left _ member) with
        | none => simp [hnodes] at compiled
        | some compiledNodes =>
            cases hchildren : compileItems? d hwf sourceCall.origin
                sourceCall.fullContext sourceCall.binders
                (localChildOccurrences d sourceCall.origin)
                (fun _ member => List.mem_append_right _ member) with
            | none => simp [hnodes, hchildren] at compiled
            | some children =>
                simp [hnodes, hchildren] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                have origins := compileItems?_origins hwf sourceCall.origin
                  sourceCall.fullContext sourceCall.binders hchildren
                refine nested.endpoint_validity hwf sourceCall.origin wires
                  binders enumeration ?_ ?_
                · intro occurrence member
                  exact List.mem_append_right _
                    (by simpa only [origins] using member)
                · simpa only [origins] using hchildren

  private def CompiledItemsZipper.endpoint_validity
      {d : Diagram} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d context rels binders}
      {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall}
      (hwf : d.WellFormed) :
      (focus : CompiledItemsZipper d items endpointCall endpoint) →
      (parent : Fin d.regionCount) →
      context.Exact parent → binders.Covers parent →
      BinderContext.Enumeration d binders parent →
      (localOccurrencesValid : ∀ occurrence, occurrence ∈ items.origins →
        occurrence ∈ localOccurrences d parent) →
      compileItems? d hwf parent context binders items.origins
        localOccurrencesValid = some items →
      CompiledEndpointValidity d hwf endpointCall endpoint
    | .cut (origin := origin) (suffix := suffix) nested,
        parent, wires, bindersCover, enumeration, localOccurrencesValid,
        compiled => by
        simp only [CompiledItems.origins, CompiledItem.origin] at compiled
        rw [compileItems?_cons] at compiled
        let headDirect :
            LocalOccurrence.child origin ∈ localOccurrences d parent :=
          localOccurrencesValid (.child origin)
            (by simp [CompiledItem.origin])
        let tailDirect : ∀ occurrence, occurrence ∈ suffix.origins →
            occurrence ∈ localOccurrences d parent := by
          intro occurrence member
          exact localOccurrencesValid occurrence (by simp [member])
        cases hhead : compileOccurrence? d hwf parent context binders
            (.child origin) headDirect with
        | none => simp [hhead] at compiled
        | some head =>
            cases htail : compileItems? d hwf parent context binders
                suffix.origins tailDirect with
            | none => simp [hhead, htail] at compiled
            | some rest =>
                simp [hhead, htail] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                have hparent : (d.regions origin).parent? = some parent :=
                  (mem_localOccurrences_child d parent origin).mp headDirect
                cases hregion : d.regions origin with
                | sheet =>
                    rw [compileOccurrence?_child_sheet hwf parent origin
                      context binders headDirect hregion] at hhead
                    contradiction
                | cut childParent =>
                    have childParentEq : childParent = parent := by
                      simpa [hregion, CRegion.parent?] using hparent
                    subst childParent
                    rw [compileOccurrence?_child_cut hwf parent origin context
                      binders headDirect hregion] at hhead
                    cases hbody : compileRegion? d hwf origin context binders with
                    | none => simp [hbody] at hhead
                    | some childBody =>
                        simp [hbody] at hhead
                        subst childBody
                        apply nested.endpoint_validity hwf hbody
                        · simpa [CompilerCall.fullContext,
                            CompilerCall.localContext, WireContext.extend] using
                            wires.extend_child hwf hparent
                        · exact BinderContext.covers_cut_child bindersCover
                            hregion
                        · exact enumeration.cutChild hwf hregion
                | bubble childParent arity =>
                    have childParentEq : childParent = parent := by
                      simpa [hregion, CRegion.parent?] using hparent
                    subst childParent
                    rw [compileOccurrence?_child_bubble hwf parent origin
                      context binders arity headDirect hregion] at hhead
                    cases hbody : compileRegion? d hwf origin context
                        (binders.push origin arity) with
                    | none => simp [hbody] at hhead
                    | some childBody => simp [hbody] at hhead
    | .bubble (origin := origin) (arity := arity) (suffix := suffix) nested,
        parent, wires, bindersCover, enumeration, localOccurrencesValid,
        compiled => by
        simp only [CompiledItems.origins, CompiledItem.origin] at compiled
        rw [compileItems?_cons] at compiled
        let headDirect :
            LocalOccurrence.child origin ∈ localOccurrences d parent :=
          localOccurrencesValid (.child origin)
            (by simp [CompiledItem.origin])
        let tailDirect : ∀ occurrence, occurrence ∈ suffix.origins →
            occurrence ∈ localOccurrences d parent := by
          intro occurrence member
          exact localOccurrencesValid occurrence (by simp [member])
        cases hhead : compileOccurrence? d hwf parent context binders
            (.child origin) headDirect with
        | none => simp [hhead] at compiled
        | some head =>
            cases htail : compileItems? d hwf parent context binders
                suffix.origins tailDirect with
            | none => simp [hhead, htail] at compiled
            | some rest =>
                simp [hhead, htail] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                have hparent : (d.regions origin).parent? = some parent :=
                  (mem_localOccurrences_child d parent origin).mp headDirect
                cases hregion : d.regions origin with
                | sheet =>
                    rw [compileOccurrence?_child_sheet hwf parent origin
                      context binders headDirect hregion] at hhead
                    contradiction
                | cut childParent =>
                    have childParentEq : childParent = parent := by
                      simpa [hregion, CRegion.parent?] using hparent
                    subst childParent
                    rw [compileOccurrence?_child_cut hwf parent origin context
                      binders headDirect hregion] at hhead
                    cases hbody : compileRegion? d hwf origin context binders with
                    | none => simp [hbody] at hhead
                    | some childBody => simp [hbody] at hhead
                | bubble childParent actualArity =>
                    have childParentEq : childParent = parent := by
                      simpa [hregion, CRegion.parent?] using hparent
                    have arityEq : actualArity = arity := by
                      rw [compileOccurrence?_child_bubble hwf parent origin
                        context binders actualArity headDirect
                        (childParentEq ▸ hregion)] at hhead
                      cases hbody : compileRegion? d hwf origin context
                          (binders.push origin actualArity) with
                      | none => simp [hbody] at hhead
                      | some childBody =>
                          simp [hbody] at hhead
                          exact hhead.1
                    subst childParent
                    subst actualArity
                    rw [compileOccurrence?_child_bubble hwf parent origin
                      context binders arity headDirect hregion] at hhead
                    cases hbody : compileRegion? d hwf origin context
                        (binders.push origin arity) with
                    | none => simp [hbody] at hhead
                    | some childBody =>
                        simp [hbody] at hhead
                        subst childBody
                        apply nested.endpoint_validity hwf hbody
                        · simpa [CompilerCall.fullContext,
                            CompilerCall.localContext, WireContext.extend] using
                            wires.extend_child hwf hparent
                        · exact BinderContext.push_covers_bubble_child
                            bindersCover hregion
                        · exact enumeration.bubbleChild hwf hregion
    | .tail (head := head) (suffix := suffix) nested,
        parent, wires, bindersCover, enumeration, localOccurrencesValid,
        compiled => by
        simp only [CompiledItems.origins] at compiled
        rw [compileItems?_cons] at compiled
        let headDirect : head.origin ∈ localOccurrences d parent :=
          localOccurrencesValid head.origin (by simp)
        let tailDirect : ∀ occurrence, occurrence ∈ suffix.origins →
            occurrence ∈ localOccurrences d parent := by
          intro occurrence member
          exact localOccurrencesValid occurrence (by simp [member])
        cases hhead : compileOccurrence? d hwf parent context binders
            head.origin headDirect with
        | none => simp [hhead] at compiled
        | some compiledHead =>
            cases htail : compileItems? d hwf parent context binders
                suffix.origins tailDirect with
            | none => simp [hhead, htail] at compiled
            | some rest =>
                simp [hhead, htail] at compiled
                obtain ⟨rfl, rfl⟩ := compiled
                exact nested.endpoint_validity hwf parent wires bindersCover
                  enumeration tailDirect htail
end

private theorem compileItems?_focus?_isSome_of_child
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    {context : WireContext d} {binders : BinderContext d rels}
    {occurrences : List (LocalOccurrence d.regionCount d.nodeCount)}
    {direct : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ localOccurrences d parent}
    {items : CompiledItems d context rels binders}
    (compiled : compileItems? d hwf parent context binders occurrences direct =
      some items)
    (child site : Fin d.regionCount)
    (member : LocalOccurrence.child child ∈ occurrences)
    (cutComplete : ∀
      {body : CompiledRegion d (.nested child context rels binders)},
      compileRegion? d hwf child context binders = some body →
      (body.focus? site).isSome = true)
    (bubbleComplete : ∀ {arity : Nat}
      {body : CompiledRegion d
        (.nested child context (arity :: rels) (binders.push child arity))},
      compileRegion? d hwf child context (binders.push child arity) =
        some body →
      (body.focus? site).isSome = true) :
    (items.focus? site).isSome = true := by
  induction occurrences generalizing items with
  | nil => simp at member
  | cons occurrence tail ih =>
      rw [compileItems?_cons] at compiled
      let headDirect : occurrence ∈ localOccurrences d parent :=
        direct occurrence (by simp)
      let tailDirect : ∀ candidate, candidate ∈ tail →
          candidate ∈ localOccurrences d parent := by
        intro candidate candidateMember
        exact direct candidate (by simp [candidateMember])
      cases hitem : compileOccurrence? d hwf parent context binders occurrence
          headDirect with
      | none => simp [hitem] at compiled
      | some item =>
          cases htail : compileItems? d hwf parent context binders tail
              tailDirect with
          | none => simp [hitem, htail] at compiled
          | some suffix =>
              simp [hitem, htail] at compiled
              subst items
              rcases List.mem_cons.mp member with head | tailMember
              · subst occurrence
                have childParent :=
                  (mem_localOccurrences_child d parent child).mp headDirect
                cases hregion : d.regions child with
                | sheet =>
                    rw [compileOccurrence?_child_sheet hwf parent child context
                      binders headDirect hregion] at hitem
                    contradiction
                | cut actualParent =>
                    have parentEq : actualParent = parent := by
                      simpa [hregion, CRegion.parent?] using childParent
                    subst actualParent
                    rw [compileOccurrence?_child_cut hwf parent child context
                      binders headDirect hregion] at hitem
                    cases hbody : compileRegion? d hwf child context binders with
                    | none => simp [hbody] at hitem
                    | some body =>
                        simp [hbody] at hitem
                        subst item
                        obtain ⟨focus, hfocus⟩ :=
                          Option.isSome_iff_exists.mp (cutComplete hbody)
                        unfold CompiledItems.focus?
                        rw [hfocus]
                        rfl
                | bubble actualParent arity =>
                    have parentEq : actualParent = parent := by
                      simpa [hregion, CRegion.parent?] using childParent
                    subst actualParent
                    rw [compileOccurrence?_child_bubble hwf parent child context
                      binders arity headDirect hregion] at hitem
                    cases hbody : compileRegion? d hwf child context
                        (binders.push child arity) with
                    | none => simp [hbody] at hitem
                    | some body =>
                        simp [hbody] at hitem
                        subst item
                        obtain ⟨focus, hfocus⟩ :=
                          Option.isSome_iff_exists.mp (bubbleComplete hbody)
                        unfold CompiledItems.focus?
                        rw [hfocus]
                        rfl
              · obtain ⟨focus, hfocus⟩ := Option.isSome_iff_exists.mp
                    (ih htail tailMember)
                cases item <;> unfold CompiledItems.focus?
                · rw [hfocus]
                  rfl
                · split
                  · rfl
                  · rw [hfocus]
                    rfl
                · split
                  · rfl
                  · rw [hfocus]
                    rfl

private theorem CompilerCall.compile?_focus?_isSome
    (hwf : d.WellFormed) (call : CompilerCall d)
    {body : CompiledRegion d call}
    (compiled : call.compile? d hwf = some body)
    (site : Fin d.regionCount) (encloses : d.Encloses call.origin site) :
    (body.focus? site).isSome = true := by
  let motive : CompilerCall d → Prop := fun call =>
    ∀ {body : CompiledRegion d call},
      call.compile? d hwf = some body →
      ∀ (site : Fin d.regionCount), d.Encloses call.origin site →
        (body.focus? site).isSome = true
  have allCalls : ∀ current, motive current :=
    CompilerCall.compile?.induct d hwf motive (by
      intro current
      dsimp only
      intro childIH body bodyCompiled site siteEnclosed
      by_cases same : current.origin = site
      · subst site
        unfold CompiledRegion.focus?
        simp
      · obtain ⟨child, childParent, childEncloses⟩ :=
          exists_direct_child_enclosing hwf (Ne.symm same) siteEnclosed
        rw [CompilerCall.compile?_eq_compileBlocks? hwf] at bodyCompiled
        cases hnodes : compileItems? d hwf current.origin current.fullContext
            current.binders (localNodeOccurrences d current.origin)
            (fun _ member => List.mem_append_left _ member) with
        | none => simp [hnodes] at bodyCompiled
        | some nodes =>
            cases hchildren : compileItems? d hwf current.origin
                current.fullContext current.binders
                (localChildOccurrences d current.origin)
                (fun _ member => List.mem_append_right _ member) with
            | none => simp [hnodes, hchildren] at bodyCompiled
            | some children =>
                simp [hnodes, hchildren] at bodyCompiled
                subst body
                have found := compileItems?_focus?_isSome_of_child hwf
                  current.origin hchildren child site
                  ((mem_localChildOccurrences_child d current.origin child).mpr
                    childParent)
                  (fun childCompiled =>
                    childIH child childParent current.fullContext current.binders
                      childCompiled site childEncloses)
                  (fun childCompiled =>
                    childIH child childParent current.fullContext _ childCompiled
                      site childEncloses)
                unfold CompiledRegion.focus?
                simpa [same] using found)
  exact allCalls call compiled site encloses

private theorem compileRoot?_focus?_isSome
    (hwf : d.WellFormed) (ambient locals : WireContext d)
    {body : CompiledRegion d (.root ambient locals)}
    (compiled : compileRoot? d hwf ambient locals = some body)
    (site : Fin d.regionCount) : (body.focus? site).isSome = true :=
  CompilerCall.compile?_focus?_isSome hwf (.root ambient locals) compiled site
    (hwf.all_regions_reach_root site)
namespace CheckedOpen

theorem compilation_focus?_isSome
    (checked : CheckedOpen)
    (site : Fin checked.val.diagram.regionCount) :
    (checked.compilation.focus? site).isSome = true :=
  compileRoot?_focus?_isSome checked.property.diagram_well_formed
    checked.val.exposedWires checked.val.hiddenWires
    checked.compilation_computation site

end CheckedOpen

namespace CompiledSite

def focus (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledFocus source.checked.compilation :=
  (source.checked.compilation.focus? site).get
    (CheckedOpen.compilation_focus?_isSome source.checked site)

def endpointCall (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompilerCall source.checked.val.diagram :=
  (focus source site).endpointCall

def endpoint (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledRegion source.checked.val.diagram (endpointCall source site) :=
  (focus source site).endpoint

def zipper (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledZipper source.checked.val.diagram source.checked.compilation
      (endpointCall source site) (endpoint source site) :=
  (focus source site).zipper

private def endpoint_validity (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledEndpointValidity source.checked.val.diagram
      source.checked.property.diagram_well_formed
      (endpointCall source site) (endpoint source site) :=
  (zipper source site).endpoint_validity
    source.checked.property.diagram_well_formed
    (by simpa using source.checked.compilation_computation)
    (by
      simpa [CompilerCall.fullContext, OpenDiagram.rootWires] using
        openRootWires_exact source.checked.property)
    (by
      simpa using BinderContext.empty_covers_root
        source.checked.property.diagram_well_formed)
    (by
      simpa using BinderContext.Enumeration.empty
        source.checked.val.diagram)

theorem endpoint_computation (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (endpointCall source site).compile? source.checked.val.diagram
      source.checked.property.diagram_well_formed =
        some (endpoint source site) :=
  (endpoint_validity source site).computation

theorem endpoint_origin (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (endpointCall source site).origin = site :=
  CompiledRegion.focus?_endpoint_origin
    (Option.some_get
      (CheckedOpen.compilation_focus?_isSome source.checked site)).symm

theorem endpoint_fullContext_exact (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (endpointCall source site).fullContext.Exact site :=
  by
    simpa only [endpoint_origin source site] using
      (endpoint_validity source site).fullContext_exact

theorem endpoint_binders_covers (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (endpointCall source site).binders.Covers site :=
  by
    simpa only [endpoint_origin source site] using
      (endpoint_validity source site).binders_covers

def endpoint_binder_enumeration (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    BinderContext.Enumeration source.checked.val.diagram
      (endpointCall source site).binders site := by
  simpa only [endpoint_origin source site] using
    (endpoint_validity source site).binder_enumeration

def directItems (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledItems source.checked.val.diagram
      (endpointCall source site).fullContext (endpointCall source site).rels
      (endpointCall source site).binders :=
  (endpoint source site).items

def directNodeItems (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledItems source.checked.val.diagram
      (endpointCall source site).fullContext (endpointCall source site).rels
      (endpointCall source site).binders :=
  (endpoint source site).nodeItems

def directChildItems (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledItems source.checked.val.diagram
      (endpointCall source site).fullContext (endpointCall source site).rels
      (endpointCall source site).binders :=
  (endpoint source site).childItems

theorem directNodeItems_origins (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (directNodeItems source site).origins =
      localNodeOccurrences source.checked.val.diagram site := by
  simpa only [endpoint_origin source site] using
    (endpoint_validity source site).node_origins

theorem directChildItems_origins (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (directChildItems source site).origins =
      localChildOccurrences source.checked.val.diagram site := by
  simpa only [endpoint_origin source site] using
    (endpoint_validity source site).child_origins

theorem directItems_origins (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (directItems source site).origins =
      localOccurrences source.checked.val.diagram site :=
  by
    simpa only [endpoint_origin source site] using
      (endpoint_validity source site).origins

def intrinsic (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    Region.ContextFocus source.checked.elaborate.body :=
  (zipper source site).toContextFocus

def context (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    DiagramContext source.checked.val.exposedWires.length
      (endpointCall source site).outerContext.length []
      (endpointCall source site).rels :=
  (zipper source site).context

def body (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    Region (endpointCall source site).outerContext.length
      (endpointCall source site).rels :=
  (endpoint source site).erase

def cutDepth (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) : Nat :=
  (context source site).cutDepth

def sourceOccurrence (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    Option (LocalOccurrence source.checked.val.diagram.regionCount
      source.checked.val.diagram.nodeCount) :=
  match endpointCall source site with
  | .root _ _ => none
  | .nested origin _ _ _ => some (.child origin)

theorem rebuild (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (context source site).fill (body source site) =
      source.checked.elaborate.body :=
  (zipper source site).intrinsic.rebuild

theorem focus_root (source : State arity) :
    focus source source.checked.val.diagram.root = {
      endpointCall := .root source.checked.val.exposedWires
        source.checked.val.hiddenWires
      endpoint := source.checked.compilation
      zipper := .here source.checked.compilation
    } := by
  unfold focus
  unfold CompiledRegion.focus?
  simp [CompilerCall.origin]

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

namespace CompiledSelection

def anchorItems (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    CompiledItems source.checked.val.diagram
      (CompiledSite.endpointCall source selection.val.anchor).fullContext
      (CompiledSite.endpointCall source selection.val.anchor).rels
      (CompiledSite.endpointCall source selection.val.anchor).binders :=
  CompiledSite.directItems source selection.val.anchor

def partition (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    CompiledItems.Partition (anchorItems source selection) :=
  (anchorItems source selection).partition
    (checkedSelectionAnchorClassifier selection)

def retained (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    CompiledItems source.checked.val.diagram
      (CompiledSite.endpointCall source selection.val.anchor).fullContext
      (CompiledSite.endpointCall source selection.val.anchor).rels
      (CompiledSite.endpointCall source selection.val.anchor).binders :=
  (partition source selection).retained

def material (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    CompiledItems source.checked.val.diagram
      (CompiledSite.endpointCall source selection.val.anchor).fullContext
      (CompiledSite.endpointCall source selection.val.anchor).rels
      (CompiledSite.endpointCall source selection.val.anchor).binders :=
  (partition source selection).material

def intrinsic (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    ItemSeq (CompiledSite.endpointCall source
      selection.val.anchor).fullContext.length
      (CompiledSite.endpointCall source selection.val.anchor).rels :=
  (anchorItems source selection).erase

def retainedIntrinsic (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    ItemSeq (CompiledSite.endpointCall source
      selection.val.anchor).fullContext.length
      (CompiledSite.endpointCall source selection.val.anchor).rels :=
  (retained source selection).erase

def materialIntrinsic (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    ItemSeq (CompiledSite.endpointCall source
      selection.val.anchor).fullContext.length
      (CompiledSite.endpointCall source selection.val.anchor).rels :=
  (material source selection).erase

noncomputable def factorization
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    ItemSeqIso
      (FiniteEquiv.refl
        (Fin (CompiledSite.endpointCall source
          selection.val.anchor).fullContext.length))
      (CompiledSite.endpointCall source selection.val.anchor).rels
      (intrinsic source selection)
      ((retainedIntrinsic source selection).append
        (materialIntrinsic source selection)) := by
  simpa [intrinsic, retainedIntrinsic, materialIntrinsic, retained, material,
    partition, CompiledItems.erase_append] using
      CompiledItems.partitionFactorization
        (checkedSelectionAnchorClassifier selection)
        (anchorItems source selection)

noncomputable def positionMap
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    FiniteEquiv (Fin (intrinsic source selection).length)
      (Fin ((retainedIntrinsic source selection).append
        (materialIntrinsic source selection)).length) :=
  match factorization source selection with
  | .permute positions _ => positions

theorem anchor_origins (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    (anchorItems source selection).origins =
      localOccurrences source.checked.val.diagram selection.val.anchor :=
  CompiledSite.directItems_origins source selection.val.anchor

theorem retained_origins_eq_unselected
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    (retained source selection).origins =
      (localOccurrences source.checked.val.diagram selection.val.anchor).filter
        fun occurrence =>
          !checkedSelectionAnchorClassifier selection occurrence := by
  change ((anchorItems source selection).partition
    (checkedSelectionAnchorClassifier selection)).retained.origins = _
  rw [CompiledItems.partition_retained_origins, anchor_origins]

theorem material_origins_eq_selected
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    (material source selection).origins =
      (localOccurrences source.checked.val.diagram selection.val.anchor).filter
        (checkedSelectionAnchorClassifier selection) := by
  change ((anchorItems source selection).partition
    (checkedSelectionAnchorClassifier selection)).material.origins = _
  rw [CompiledItems.partition_material_origins, anchor_origins]

theorem mem_retained_origins
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (occurrence : LocalOccurrence source.checked.val.diagram.regionCount
      source.checked.val.diagram.nodeCount) :
    occurrence ∈ (retained source selection).origins ↔
      checkedSelectionAnchorClassifier selection occurrence = false ∧
        occurrence ∈ localOccurrences source.checked.val.diagram
          selection.val.anchor := by
  rw [retained_origins_eq_unselected]
  cases occurrence <;>
    simp [localOccurrences, localNodeOccurrences, localChildOccurrences,
      and_comm]

theorem mem_material_origins
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (occurrence : LocalOccurrence source.checked.val.diagram.regionCount
      source.checked.val.diagram.nodeCount) :
    occurrence ∈ (material source selection).origins ↔
      checkedSelectionAnchorClassifier selection occurrence = true ∧
        occurrence ∈ localOccurrences source.checked.val.diagram
          selection.val.anchor := by
  rw [material_origins_eq_selected]
  cases occurrence <;>
    simp [localOccurrences, localNodeOccurrences, localChildOccurrences,
      and_comm]

theorem retained_stable (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    List.Sublist (retained source selection).origins
      (anchorItems source selection).origins :=
  CompiledItems.partition_retained_stable
    (checkedSelectionAnchorClassifier selection) (anchorItems source selection)

theorem material_stable (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    List.Sublist (material source selection).origins
      (anchorItems source selection).origins :=
  CompiledItems.partition_material_stable
    (checkedSelectionAnchorClassifier selection) (anchorItems source selection)

theorem origins_factorization
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    (anchorItems source selection).origins.Perm
      ((retained source selection).origins ++
        (material source selection).origins) :=
  CompiledItems.partition_origins_perm
    (checkedSelectionAnchorClassifier selection) (anchorItems source selection)

theorem classified_once (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    ((retained source selection).origins ++
      (material source selection).origins).Nodup := by
  have originalNodup : (anchorItems source selection).origins.Nodup := by
    rw [anchor_origins]
    exact localOccurrences_nodup source.checked.val.diagram selection.val.anchor
  exact (origins_factorization source selection).nodup originalNodup

theorem retained_material_disjoint
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    ∀ occurrence, occurrence ∈ (retained source selection).origins →
      occurrence ∉ (material source selection).origins := by
  intro occurrence retained material
  exact (List.nodup_append.mp (classified_once source selection)).2.2
    occurrence retained occurrence material rfl

theorem node_mem_material_origins
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (node : Fin source.checked.val.diagram.nodeCount) :
    LocalOccurrence.node node ∈ (material source selection).origins ↔
      node ∈ selection.val.directNodes := by
  rw [mem_material_origins]
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
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (child : Fin source.checked.val.diagram.regionCount) :
    LocalOccurrence.child child ∈ (material source selection).origins ↔
      child ∈ selection.val.childRoots := by
  rw [mem_material_origins]
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
