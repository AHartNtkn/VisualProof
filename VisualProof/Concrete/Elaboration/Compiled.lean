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
      (site : Fin d.regionCount) ->
      (endpointCall : CompilerCall d) ->
      CompiledRegion d endpointCall -> Type
    | here {sourceCall : CompilerCall d}
        (source : CompiledRegion d sourceCall) :
        CompiledZipper d source sourceCall.origin sourceCall source
    | child {sourceCall endpointCall : CompilerCall d}
        {items : CompiledItems d sourceCall.fullContext
          sourceCall.rels sourceCall.binders}
        {site : Fin d.regionCount}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledItemsZipper d items site endpointCall endpoint) :
        CompiledZipper d (.mk items) site endpointCall endpoint

  inductive CompiledItemsZipper (d : Diagram) :
      {context : WireContext d} -> {rels : RelCtx} ->
      {binders : BinderContext d rels} ->
      CompiledItems d context rels binders ->
      (site : Fin d.regionCount) ->
      (endpointCall : CompilerCall d) ->
      CompiledRegion d endpointCall -> Type
    | cut {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {body : CompiledRegion d
          (.nested origin context rels binders)}
        (before : CompiledItems d context rels binders)
        (suffix : CompiledItems d context rels binders)
        {items : CompiledItems d context rels binders}
        {site : Fin d.regionCount} {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledZipper d body site endpointCall endpoint) :
        (rebuild : before.append (.cons (.cut body) suffix) = items) →
        CompiledItemsZipper d items site endpointCall endpoint
    | bubble {context : WireContext d} {rels : RelCtx}
        {binders : BinderContext d rels} {origin : Fin d.regionCount}
        {arity : Nat}
        {body : CompiledRegion d
          (.nested origin context (arity :: rels)
            (binders.push origin arity))}
        (before : CompiledItems d context rels binders)
        (suffix : CompiledItems d context rels binders)
        {items : CompiledItems d context rels binders}
        {site : Fin d.regionCount} {endpointCall : CompilerCall d}
        {endpoint : CompiledRegion d endpointCall}
        (nested : CompiledZipper d body site endpointCall endpoint) :
        (rebuild : before.append (.cons (.bubble arity body) suffix) = items) →
        CompiledItemsZipper d items site endpointCall endpoint
end

/-- The result of finding an exact endpoint and its structural selection in a
compiled region. -/
structure CompiledFocus {d : Diagram} {sourceCall : CompilerCall d}
    (source : CompiledRegion d sourceCall) (site : Fin d.regionCount) where
  endpointCall : CompilerCall d
  endpoint : CompiledRegion d endpointCall
  zipper : CompiledZipper d source site endpointCall endpoint

mutual
  /-- Canonically search the sole compiled region tree for a site. -/
  def CompiledRegion.focus?
      {d : Diagram} {sourceCall : CompilerCall d}
      (source : CompiledRegion d sourceCall) (site : Fin d.regionCount) :
      Option (CompiledFocus source site) :=
    if same : sourceCall.origin = site then
      some (same ▸ {
        endpointCall := sourceCall
        endpoint := source
        zipper := .here source
      })
    else
      match source with
      | .mk items =>
          (items.focus? site).map fun ⟨endpointCall, endpoint, zipper⟩ =>
            ⟨endpointCall, endpoint, .child zipper⟩

  /-- Structural worker for the canonical compiled-region focus search. It is
  exposed only so source-derived transformations can invert the exact search
  decision while following the one returned zipper. -/
  def CompiledItems.focus?
      {d : Diagram} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      (items : CompiledItems d context rels binders)
      (site : Fin d.regionCount) :
      Option (Σ endpointCall, Σ endpoint : CompiledRegion d endpointCall,
        CompiledItemsZipper d items site endpointCall endpoint) :=
    match items with
    | .nil => none
    | .cons (.node origin item) tail =>
        match tail.focus? site with
        | none => none
        | some ⟨endpointCall, endpoint, .cut before suffix nested rebuild⟩ =>
            some ⟨endpointCall, endpoint,
              .cut (.cons (.node origin item) before) suffix nested
                (congrArg (CompiledItems.cons (.node origin item)) rebuild)⟩
        | some ⟨endpointCall, endpoint,
            .bubble before suffix nested rebuild⟩ =>
            some ⟨endpointCall, endpoint,
              .bubble (.cons (.node origin item) before) suffix nested
                (congrArg (CompiledItems.cons (.node origin item)) rebuild)⟩
    | .cons (.cut body) tail =>
        match body.focus? site with
        | some focus =>
            some ⟨focus.endpointCall, focus.endpoint,
              .cut .nil tail focus.zipper rfl⟩
        | none =>
            match tail.focus? site with
            | none => none
            | some ⟨endpointCall, endpoint,
                .cut before suffix nested rebuild⟩ =>
                some ⟨endpointCall, endpoint,
                  .cut (.cons (.cut body) before) suffix nested
                    (congrArg (CompiledItems.cons (.cut body)) rebuild)⟩
            | some ⟨endpointCall, endpoint,
                .bubble before suffix nested rebuild⟩ =>
                some ⟨endpointCall, endpoint,
                  .bubble (.cons (.cut body) before) suffix nested
                    (congrArg (CompiledItems.cons (.cut body)) rebuild)⟩
    | .cons (.bubble arity body) tail =>
        match body.focus? site with
        | some focus =>
            some ⟨focus.endpointCall, focus.endpoint,
              .bubble .nil tail focus.zipper rfl⟩
        | none =>
            match tail.focus? site with
            | none => none
            | some ⟨endpointCall, endpoint,
                .cut before suffix nested rebuild⟩ =>
                some ⟨endpointCall, endpoint,
                  .cut (.cons (.bubble arity body) before) suffix nested
                    (congrArg (CompiledItems.cons (.bubble arity body)) rebuild)⟩
            | some ⟨endpointCall, endpoint,
                .bubble before suffix nested rebuild⟩ =>
                some ⟨endpointCall, endpoint,
                  .bubble (.cons (.bubble arity body) before) suffix nested
                    (congrArg (CompiledItems.cons (.bubble arity body)) rebuild)⟩
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

theorem CompiledRegion.focus?_singleton_bubble
    {d : Diagram} {parentCall : CompilerCall d}
    {origin : Fin d.regionCount} {arity : Nat}
    {body : CompiledRegion d (.nested origin parentCall.fullContext
      (arity :: parentCall.rels) (parentCall.binders.push origin arity))}
    {site : Fin d.regionCount}
    (different : parentCall.origin ≠ site) :
    (CompiledRegion.mk (.cons (.bubble arity body) .nil) :
      CompiledRegion d parentCall).focus? site =
        (body.focus? site).map fun focus => {
          endpointCall := focus.endpointCall
          endpoint := focus.endpoint
          zipper := .child (.bubble .nil .nil focus.zipper rfl)
        } := by
  rw [CompiledRegion.focus?]
  simp only [different, ↓reduceDIte]
  cases hfocus : body.focus? site <;>
    simp [CompiledItems.focus?, hfocus]

theorem CompiledRegion.focus?_same_outerContext
    {d : Diagram} {call : CompilerCall d}
    {region : CompiledRegion d call} {site : Fin d.regionCount}
    {focus : CompiledFocus region site}
    (same : call.origin = site)
    (found : region.focus? site = some focus) :
    focus.endpointCall.outerContext = call.outerContext := by
  subst site
  rw [CompiledRegion.focus?_origin] at found
  cases found
  rfl

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
            nested.intrinsic sourceCall.outerContext.length
              sourceCall.localContext.length (by
                simp [CompilerCall.fullContext])

  def CompiledItemsZipper.intrinsic
      {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d context rels binders}
      {site : Fin d.regionCount} {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall}
      (focus : CompiledItemsZipper d items site endpointCall endpoint)
      (outerWires localWires : Nat)
      (split : context.length = outerWires + localWires) :
      CompiledIntrinsic d
        (.mk localWires (items.erase.castWiresEq split))
        endpointCall endpoint :=
    match focus with
    | .cut (body := body) before suffix nested rebuild => by
        subst items
        let selected := nested.intrinsic
        exact {
          context := .cut localWires (before.erase.castWiresEq split)
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
                  ((before.erase.castWiresEq split).append
                    (.cons (.cut (body.erase.castWiresEq split))
                      (suffix.erase.castWiresEq split))) := by
                exact congrArg (fun sequence => Region.mk localWires sequence)
                  (congrArg (fun item =>
                    (before.erase.castWiresEq split).append
                      (.cons item (suffix.erase.castWiresEq split)))
                    (congrArg Item.cut nestedEq))
              _ = _ := by simp [CompiledItems.erase, CompiledItem.erase,
                CompiledItems.erase_append]
        }
    | .bubble (arity := arity) (body := body) before suffix nested rebuild => by
        subst items
        let selected := nested.intrinsic
        exact {
          context := .bubble localWires (before.erase.castWiresEq split)
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
                  ((before.erase.castWiresEq split).append
                    (.cons (.bubble arity (body.erase.castWiresEq split))
                      (suffix.erase.castWiresEq split))) := by
                exact congrArg (fun sequence => Region.mk localWires sequence)
                  (congrArg (fun item =>
                    (before.erase.castWiresEq split).append
                      (.cons item (suffix.erase.castWiresEq split)))
                    (congrArg (Item.bubble arity) nestedEq))
              _ = _ := by simp [CompiledItems.erase, CompiledItem.erase,
                CompiledItems.erase_append]
        }
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
    (wellFormed : d.WellFormed)
    (sourceSite site : Fin d.regionCount) (call : CompilerCall d)
    (endpoint : CompiledRegion d call) where
  computation : call.compile? d wellFormed = some endpoint
  origin : call.origin = site
  fullContext_exact : call.fullContext.Exact site
  binders_covers : call.binders.Covers site
  binders_enumeration : BinderContext.Enumeration d call.binders site
  origins : endpoint.items.origins = localOccurrences d site
  encloses : d.Encloses sourceSite site

private structure CompiledItemsEndpointValidity (d : Diagram)
    (wellFormed : d.WellFormed) (parent : Fin d.regionCount)
    {context : WireContext d} {rels : RelCtx}
    {binders : BinderContext d rels}
    (items : CompiledItems d context rels binders)
    (site : Fin d.regionCount) (call : CompilerCall d)
    (endpoint : CompiledRegion d call)
    extends CompiledEndpointValidity d wellFormed parent site call endpoint where
  selectedChild : Fin d.regionCount
  selectedChild_mem : LocalOccurrence.child selectedChild ∈ items.origins
  selectedChild_parent : (d.regions selectedChild).parent? = some parent
  selectedChild_encloses : d.Encloses selectedChild site

mutual
  private def CompiledZipper.endpoint_validity
      {d : Diagram} {sourceCall endpointCall : CompilerCall d}
      {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
      {endpoint : CompiledRegion d endpointCall}
      (hwf : d.WellFormed) :
      (focus : CompiledZipper d source site endpointCall endpoint) →
      sourceCall.compile? d hwf = some source →
      sourceCall.fullContext.Exact sourceCall.origin →
      sourceCall.binders.Covers sourceCall.origin →
      BinderContext.Enumeration d sourceCall.binders sourceCall.origin →
      CompiledEndpointValidity d hwf sourceCall.origin site endpointCall endpoint
    | .here source, compiled, wires, binders, enumeration => by
        cases source with
        | mk items =>
            have hitems := sourceCall.compile?_items_of_success hwf compiled
            have origins := compileItems?_origins hwf sourceCall.origin
              sourceCall.fullContext sourceCall.binders hitems
            exact ⟨compiled, rfl, wires, binders, enumeration, origins,
              Diagram.Encloses.refl d sourceCall.origin⟩
    | .child nested, compiled, wires, binders, enumeration => by
        have hitems := sourceCall.compile?_items_of_success hwf compiled
        have origins := compileItems?_origins hwf sourceCall.origin
          sourceCall.fullContext sourceCall.binders hitems
        let validity := nested.endpoint_validity hwf sourceCall.origin wires
          binders enumeration
          (fun occurrence member => by simpa only [origins] using member)
          (by simpa only [origins] using hitems)
        exact validity.toCompiledEndpointValidity

  private def compileItems?_selected
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
      compileOccurrence? d hwf parent context binders selected.origin
        (direct selected.origin (by
          simp [CompiledItems.origins_append, CompiledItems.origins])) =
        some selected := by
    cases before with
    | nil =>
        exact (compileItems?_cons_inv hwf parent context binders selected
          suffix direct compiled).1
    | cons head tail =>
        obtain ⟨_, restCompiled⟩ := compileItems?_cons_inv hwf parent context
          binders head (tail.append (.cons selected suffix)) direct compiled
        exact compileItems?_selected hwf parent context binders tail selected
          suffix (fun occurrence member => direct occurrence (by
            change occurrence ∈ head.origin ::
              (tail.append (.cons selected suffix)).origins
            exact List.mem_cons_of_mem _ member))
          restCompiled

  private def CompiledItemsZipper.endpoint_validity
      {d : Diagram} {context : WireContext d} {rels : RelCtx}
      {binders : BinderContext d rels}
      {items : CompiledItems d context rels binders}
      {site : Fin d.regionCount} {endpointCall : CompilerCall d}
      {endpoint : CompiledRegion d endpointCall}
      (hwf : d.WellFormed) :
      (focus : CompiledItemsZipper d items site endpointCall endpoint) →
      (parent : Fin d.regionCount) →
      context.Exact parent → binders.Covers parent →
      BinderContext.Enumeration d binders parent →
      (localOccurrencesValid : ∀ occurrence, occurrence ∈ items.origins →
        occurrence ∈ localOccurrences d parent) →
      compileItems? d hwf parent context binders items.origins
        localOccurrencesValid = some items →
      CompiledItemsEndpointValidity d hwf parent items site endpointCall endpoint
    | .cut (origin := origin) (body := body) before suffix nested rebuild,
        parent, wires, bindersCover, enumeration, localOccurrencesValid,
        compiled => by
        subst items
        let headDirect :
            LocalOccurrence.child origin ∈ localOccurrences d parent :=
          localOccurrencesValid (.child origin)
            (by simp [CompiledItems.origins_append, CompiledItems.origins,
              CompiledItem.origin])
        have hhead := compileItems?_selected hwf parent context binders before
          (.cut body) suffix localOccurrencesValid compiled
        have hhead' : compileOccurrence? d hwf parent context binders
            (.child origin) headDirect = some (.cut body) := by
          simpa only [CompiledItem.origin] using hhead
        have hparent := (mem_localOccurrences_child d parent origin).mp headDirect
        have hregion : d.regions origin = .cut parent := by
          cases regionEq : d.regions origin with
          | sheet => rw [compileOccurrence?_child_sheet hwf parent origin
              context binders headDirect regionEq] at hhead'; contradiction
          | cut childParent =>
              have : childParent = parent := by
                simpa [regionEq, CRegion.parent?] using hparent
              subst childParent; rfl
          | bubble childParent arity =>
              have : childParent = parent := by
                simpa [regionEq, CRegion.parent?] using hparent
              subst childParent
              rw [compileOccurrence?_child_bubble hwf parent origin context
                binders arity headDirect regionEq] at hhead'
              cases hbody : compileRegion? d hwf origin context
                (binders.push origin arity) <;> simp [hbody] at hhead'
        have hbody := compileOccurrence?_child_cut_body hwf parent origin
          context binders headDirect hregion hhead'
        let childValidity := nested.endpoint_validity hwf hbody
          (by simpa [CompilerCall.fullContext, CompilerCall.localContext,
              WireContext.extend] using wires.extend_child hwf hparent)
          (BinderContext.covers_cut_child bindersCover hregion)
          (enumeration.cutChild hwf hregion)
        exact {
          toCompiledEndpointValidity := { childValidity with
            encloses := checked_encloses_trans hwf (by
              refine ⟨⟨1, by have := origin.isLt; omega⟩, ?_⟩
              change (match (d.regions origin).parent? with
                | none => none | some directParent => d.climb 0 directParent) =
                  some parent
              rw [hparent]
              rfl) childValidity.encloses }
          selectedChild := origin
          selectedChild_mem := by simp [CompiledItems.origins_append,
            CompiledItems.origins, CompiledItem.origin]
          selectedChild_parent := hparent
          selectedChild_encloses := childValidity.encloses }
    | .bubble (origin := origin) (arity := arity) (body := body) before suffix
        nested rebuild,
        parent, wires, bindersCover, enumeration, localOccurrencesValid,
        compiled => by
        subst items
        let headDirect :
            LocalOccurrence.child origin ∈ localOccurrences d parent :=
          localOccurrencesValid (.child origin)
            (by simp [CompiledItems.origins_append, CompiledItems.origins,
              CompiledItem.origin])
        have hhead := compileItems?_selected hwf parent context binders before
          (.bubble arity body) suffix localOccurrencesValid compiled
        have hhead' : compileOccurrence? d hwf parent context binders
            (.child origin) headDirect = some (.bubble arity body) := by
          simpa only [CompiledItem.origin] using hhead
        have hparent := (mem_localOccurrences_child d parent origin).mp headDirect
        have hregion : d.regions origin = .bubble parent arity := by
          cases regionEq : d.regions origin with
          | sheet => rw [compileOccurrence?_child_sheet hwf parent origin
              context binders headDirect regionEq] at hhead'; contradiction
          | cut childParent =>
              have : childParent = parent := by
                simpa [regionEq, CRegion.parent?] using hparent
              subst childParent
              rw [compileOccurrence?_child_cut hwf parent origin context
                binders headDirect regionEq] at hhead'
              cases hbody : compileRegion? d hwf origin context binders <;>
                simp [hbody] at hhead'
          | bubble childParent actualArity =>
              have hp : childParent = parent := by
                simpa [regionEq, CRegion.parent?] using hparent
              have ha : actualArity = arity := by
                subst childParent
                rw [compileOccurrence?_child_bubble hwf parent origin context
                  binders actualArity headDirect regionEq] at hhead'
                cases hbody : compileRegion? d hwf origin context
                  (binders.push origin actualArity) <;> simp [hbody] at hhead'
                exact hhead'.1
              subst childParent; subst actualArity; rfl
        have hbody := compileOccurrence?_child_bubble_body hwf parent origin
          context binders arity headDirect hregion hhead'
        let childValidity := nested.endpoint_validity hwf hbody
          (by simpa [CompilerCall.fullContext, CompilerCall.localContext,
              WireContext.extend] using wires.extend_child hwf hparent)
          (BinderContext.push_covers_bubble_child bindersCover hregion)
          (enumeration.bubbleChild hwf hregion)
        exact {
          toCompiledEndpointValidity := { childValidity with
            encloses := checked_encloses_trans hwf (by
              refine ⟨⟨1, by have := origin.isLt; omega⟩, ?_⟩
              change (match (d.regions origin).parent? with
                | none => none | some directParent => d.climb 0 directParent) =
                  some parent
              rw [hparent]
              rfl) childValidity.encloses }
          selectedChild := origin
          selectedChild_mem := by simp [CompiledItems.origins_append,
            CompiledItems.origins, CompiledItem.origin]
          selectedChild_parent := hparent
          selectedChild_encloses := childValidity.encloses }
end

/-- A valid compiled zipper ends at a region enclosed by its source call.
This is a projection of the single endpoint-validity fold, not a second
navigation of the compiled tree. -/
theorem CompiledZipper.endpoint_encloses
    {d : Diagram} {sourceCall endpointCall : CompilerCall d}
    {source : CompiledRegion d sourceCall} {site : Fin d.regionCount}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledZipper d source site endpointCall endpoint)
    (hwf : d.WellFormed)
    (compiled : sourceCall.compile? d hwf = some source)
    (wires : sourceCall.fullContext.Exact sourceCall.origin)
    (binders : sourceCall.binders.Covers sourceCall.origin)
    (enumeration : BinderContext.Enumeration d sourceCall.binders
      sourceCall.origin) :
    d.Encloses sourceCall.origin site :=
  (focus.endpoint_validity hwf compiled wires binders enumeration).encloses

/-- The selected branch of an item zipper starts at one actual direct child
that encloses its endpoint. -/
theorem CompiledItemsZipper.selected_child
    {d : Diagram} {context : WireContext d} {rels : RelCtx}
    {binders : BinderContext d rels}
    {items : CompiledItems d context rels binders}
    {site : Fin d.regionCount} {endpointCall : CompilerCall d}
    {endpoint : CompiledRegion d endpointCall}
    (focus : CompiledItemsZipper d items site endpointCall endpoint)
    (hwf : d.WellFormed) (parent : Fin d.regionCount)
    (wires : context.Exact parent) (covers : binders.Covers parent)
    (enumeration : BinderContext.Enumeration d binders parent)
    (direct : ∀ occurrence, occurrence ∈ items.origins →
      occurrence ∈ localOccurrences d parent)
    (compiled : compileItems? d hwf parent context binders items.origins
      direct = some items) :
    ∃ child, LocalOccurrence.child child ∈ items.origins ∧
      (d.regions child).parent? = some parent ∧
      d.Encloses child site := by
  let validity := focus.endpoint_validity hwf parent wires covers enumeration
    direct compiled
  exact ⟨validity.selectedChild, validity.selectedChild_mem,
    validity.selectedChild_parent,
    validity.selectedChild_encloses⟩

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
                rcases focus with ⟨endpointCall, endpoint, zipper⟩
                cases item <;> unfold CompiledItems.focus?
                · cases zipper <;> simp [hfocus]
                · split
                  · rfl
                  · cases zipper <;> simp [hfocus]
                · split
                  · rfl
                  · cases zipper <;> simp [hfocus]

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
        rw [CompilerCall.compile?_eq_compileItems? hwf] at bodyCompiled
        obtain ⟨items, hitems, hbody⟩ :=
          Option.bind_eq_some_iff.mp bodyCompiled
        cases hbody
        have found := compileItems?_focus?_isSome_of_child hwf
          current.origin hitems child site
          ((mem_localOccurrences_child d current.origin child).mpr childParent)
          (fun childCompiled =>
            childIH child childParent current.fullContext current.binders
              childCompiled site childEncloses)
          (fun childCompiled =>
            childIH child childParent current.fullContext _ childCompiled
              site childEncloses)
        unfold CompiledRegion.focus?
        simpa [same] using found)
  exact allCalls call compiled site encloses

/-- Failure of the canonical compiled-tree search rules out enclosure. -/
theorem CompiledRegion.not_encloses_of_focus?_eq_none
    (hwf : d.WellFormed) (call : CompilerCall d)
    {body : CompiledRegion d call}
    (compiled : call.compile? d hwf = some body)
    (site : Fin d.regionCount) (absent : body.focus? site = none) :
    ¬ d.Encloses call.origin site := by
  intro encloses
  have found := CompilerCall.compile?_focus?_isSome hwf call compiled site
    encloses
  rw [absent] at found
  contradiction

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
    CompiledFocus source.checked.compilation site :=
  (source.checked.compilation.focus? site).get
    (CheckedOpen.compilation_focus?_isSome source.checked site)

theorem focus_computation (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    source.checked.compilation.focus? site = some (focus source site) :=
  (Option.some_get
    (CheckedOpen.compilation_focus?_isSome source.checked site)).symm

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
    CompiledZipper source.checked.val.diagram source.checked.compilation site
      (endpointCall source site) (endpoint source site) :=
  (focus source site).zipper

private def endpoint_validity (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledEndpointValidity source.checked.val.diagram
      source.checked.property.diagram_well_formed
      source.checked.val.diagram.root site
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
  (endpoint_validity source site).origin

theorem endpoint_fullContext_exact (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (endpointCall source site).fullContext.Exact site :=
  (endpoint_validity source site).fullContext_exact

theorem endpoint_binders_covers (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (endpointCall source site).binders.Covers site :=
  (endpoint_validity source site).binders_covers

noncomputable def endpoint_binders_enumeration (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    BinderContext.Enumeration source.checked.val.diagram
      (endpointCall source site).binders site :=
  (endpoint_validity source site).binders_enumeration

def directItems (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledItems source.checked.val.diagram
      (endpointCall source site).fullContext (endpointCall source site).rels
      (endpointCall source site).binders :=
  (endpoint source site).items

theorem directItems_origins (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    (directItems source site).origins =
      localOccurrences source.checked.val.diagram site :=
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
  simp only [List.mem_filter, Bool.not_eq_true']
  simp only [and_comm]

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
  simp only [List.mem_filter]
  simp only [and_comm]

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
