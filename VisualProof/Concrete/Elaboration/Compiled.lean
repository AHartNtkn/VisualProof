import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.State
import VisualProof.Concrete.Subgraph.Selection

namespace VisualProof.Concrete.Elaboration

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

/-! One structural focus over the sole symbolic compiler result. -/

mutual
  inductive CompiledZipper (d : Diagram) :
      CompiledRegion d → CompiledRegion d → Type
    | here (source : CompiledRegion d) : CompiledZipper d source source
    | child {origin : Fin d.regionCount} {nodes children : CompiledItems d}
        {endpoint : CompiledRegion d}
        (nested : CompiledItemsZipper d children endpoint) :
        CompiledZipper d (.mk origin nodes children) endpoint

  inductive CompiledItemsZipper (d : Diagram) :
      CompiledItems d → CompiledRegion d → Type
    | cut {body endpoint : CompiledRegion d} {suffix : CompiledItems d}
        (nested : CompiledZipper d body endpoint) :
        CompiledItemsZipper d (.cons (.cut body) suffix) endpoint
    | bubble {arity : Nat} {body endpoint : CompiledRegion d}
        {suffix : CompiledItems d}
        (nested : CompiledZipper d body endpoint) :
        CompiledItemsZipper d (.cons (.bubble arity body) suffix) endpoint
    | tail {head : CompiledItem d} {suffix : CompiledItems d}
        {endpoint : CompiledRegion d}
        (nested : CompiledItemsZipper d suffix endpoint) :
        CompiledItemsZipper d (.cons head suffix) endpoint
end

/-! A focus derives its lexical compiler environment and intrinsic hole in
one pass over the same zipper. -/

structure CompiledEnvironment (region : CompiledRegion d) where
  outer : WireContext d
  locals : WireContext d
  rels : RelCtx
  binders : BinderContext d rels
  valid : region.Valid
  exact : (outer ++ locals).Exact region.origin
  covers : binders.Covers region.origin
  enumeration : BinderContext.Enumeration d binders region.origin

namespace CompiledEnvironment

def fullContext {d : Diagram} {region : CompiledRegion d}
    (environment : CompiledEnvironment region) : WireContext d :=
  environment.outer ++ environment.locals

noncomputable def body {d : Diagram} {region : CompiledRegion d}
    (environment : CompiledEnvironment region)
    (hwf : d.WellFormed) : Region environment.outer.length environment.rels :=
  region.erase environment.valid hwf environment.outer environment.locals
    environment.rels environment.binders environment.exact environment.covers

end CompiledEnvironment

structure CompiledHole {d : Diagram} {sourceWires : Nat}
    {sourceRels : RelCtx}
    (sourceBody : Region sourceWires sourceRels)
    (endpoint : CompiledRegion d) (hwf : d.WellFormed) where
  environment : CompiledEnvironment endpoint
  context : DiagramContext sourceWires environment.outer.length
    sourceRels environment.rels
  rebuild : context.fill (environment.body hwf) = sourceBody

private def DiagramContext.castOuterWires
    {source target holeWires : Nat} {outerRels holeRels : RelCtx}
    (equality : source = target)
    (context : DiagramContext source holeWires outerRels holeRels) :
    DiagramContext target holeWires outerRels holeRels := by
  cases equality
  exact context

private theorem DiagramContext.castOuterWires_fill
    {source target holeWires : Nat} {outerRels holeRels : RelCtx}
    (equality : source = target)
    (context : DiagramContext source holeWires outerRels holeRels)
    (body : Region holeWires holeRels) :
    (DiagramContext.castOuterWires equality context).fill body =
      (context.fill body).castWiresEq equality := by
  cases equality
  rfl

structure CompiledFocus (source : CompiledRegion d)
    (site : Fin d.regionCount) where
  endpoint : CompiledRegion d
  endpoint_origin : endpoint.origin = site
  zipper : CompiledZipper d source endpoint

private structure CompiledItemsFocus (items : CompiledItems d)
    (site : Fin d.regionCount) where
  endpoint : CompiledRegion d
  endpoint_origin : endpoint.origin = site
  zipper : CompiledItemsZipper d items endpoint

mutual
  def CompiledRegion.focus? (source : CompiledRegion d)
      (site : Fin d.regionCount) : Option (CompiledFocus source site) :=
    if _same : source.origin = site then
      some ⟨source, _same, .here source⟩
    else
      match source with
      | .mk _ _ children =>
          (children.focus? site).map fun focused =>
            ⟨focused.endpoint, focused.endpoint_origin,
              .child focused.zipper⟩

  private def CompiledItems.focus? (items : CompiledItems d)
      (site : Fin d.regionCount) :
      Option (CompiledItemsFocus items site) :=
    match items with
    | .nil => none
    | .cons (.atom _ _ _ _) tail =>
        (tail.focus? site).map fun focused =>
          ⟨focused.endpoint, focused.endpoint_origin,
            .tail focused.zipper⟩
    | .cons (.identity _ _ _) tail =>
        (tail.focus? site).map fun focused =>
          ⟨focused.endpoint, focused.endpoint_origin,
            .tail focused.zipper⟩
    | .cons (.cut body) tail =>
        match body.focus? site with
        | some focused => some ⟨focused.endpoint, focused.endpoint_origin,
            .cut focused.zipper⟩
        | none =>
            (tail.focus? site).map fun focused =>
              ⟨focused.endpoint, focused.endpoint_origin,
                .tail focused.zipper⟩
    | .cons (.bubble _ body) tail =>
        match body.focus? site with
        | some focused => some ⟨focused.endpoint, focused.endpoint_origin,
            .bubble focused.zipper⟩
        | none =>
            (tail.focus? site).map fun focused =>
              ⟨focused.endpoint, focused.endpoint_origin,
                .tail focused.zipper⟩
end

@[simp] theorem CompiledRegion.focus?_origin (source : CompiledRegion d) :
    source.focus? source.origin = some ⟨source, rfl, .here source⟩ := by
  simp [CompiledRegion.focus?]

/-- Canonical search through one administrative bubble. -/
theorem CompiledRegion.focus?_singleton_bubble
    {origin site : Fin d.regionCount} {arity : Nat}
    (body : CompiledRegion d) (different : origin ≠ site) :
    (CompiledRegion.mk origin .nil (.cons (.bubble arity body) .nil)).focus?
        site =
      (body.focus? site).map fun focused =>
        ⟨focused.endpoint, focused.endpoint_origin,
          CompiledZipper.child
            (CompiledItemsZipper.bubble focused.zipper)⟩ := by
  rw [CompiledRegion.focus?]
  simp only [CompiledRegion.origin, different]
  rw [CompiledItems.focus?]
  cases body.focus? site <;> simp [CompiledItems.focus?]

mutual
  theorem CompiledRegion.focus?_isSome_of_valid
      (source : CompiledRegion d) (valid : source.Valid)
      (hwf : d.WellFormed) (site : Fin d.regionCount)
      (encloses : d.Encloses source.origin site) :
      (source.focus? site).isSome := by
    by_cases same : source.origin = site
    · simp [CompiledRegion.focus?, same]
    · obtain ⟨child, parent, childEncloses⟩ :=
        exists_direct_child_enclosing hwf (Ne.symm same) encloses
      cases source with
      | mk origin nodes children =>
          have childMember : LocalOccurrence.child child ∈ children.origins := by
            rw [valid.2.1]
            exact (mem_localChildOccurrences_child d origin child).2 parent
          have childSome := CompiledItems.focus?_isSome_of_child
            children valid.2.2.2 hwf childMember childEncloses
          simp only [CompiledRegion.focus?, same]
          simpa using childSome

  private theorem CompiledItems.focus?_isSome_of_child
      (items : CompiledItems d) (valid : items.ValidAt parent)
      (hwf : d.WellFormed)
      (member : LocalOccurrence.child child ∈ items.origins)
      (encloses : d.Encloses child site) :
      (items.focus? site).isSome := by
    cases items with
    | nil => simp at member
    | cons head tail =>
        have headValid := valid.1
        have tailValid := valid.2
        simp only [CompiledItems.origins_cons, List.mem_cons] at member
        rcases member with headOrigin | tailMember
        · cases head with
          | atom origin binder arity ports => contradiction
          | identity origin arity ports => contradiction
          | cut body =>
              have originEq : body.origin = child :=
                LocalOccurrence.child.inj headOrigin.symm
              subst child
              have bodySome := CompiledRegion.focus?_isSome_of_valid
                body headValid.2 hwf site encloses
              simp only [CompiledItems.focus?]
              cases found : body.focus? site <;> simp_all
          | bubble arity body =>
              have originEq : body.origin = child :=
                LocalOccurrence.child.inj headOrigin.symm
              subst child
              have bodySome := CompiledRegion.focus?_isSome_of_valid
                body headValid.2 hwf site encloses
              simp only [CompiledItems.focus?]
              cases found : body.focus? site <;> simp_all
        · have tailSome := CompiledItems.focus?_isSome_of_child
            tail tailValid hwf tailMember encloses
          cases head with
          | atom =>
              simpa only [CompiledItems.focus?, Option.isSome_map] using tailSome
          | identity =>
              simpa only [CompiledItems.focus?, Option.isSome_map] using tailSome
          | cut body =>
              simp only [CompiledItems.focus?]
              cases body.focus? site <;> simp_all
          | bubble arity body =>
              simp only [CompiledItems.focus?]
              cases body.focus? site <;> simp_all
end

mutual
  noncomputable def CompiledZipper.intrinsic
      {source endpoint : CompiledRegion d} :
      (zipper : CompiledZipper d source endpoint) →
      (sourceEnvironment : CompiledEnvironment source) →
      (hwf : d.WellFormed) →
      CompiledHole (sourceEnvironment.body hwf) endpoint hwf
    | .here _, sourceEnvironment, _ =>
        ⟨sourceEnvironment, .hole, rfl⟩
    | .child (nodes := nodes) nested, sourceEnvironment, hwf => by
        let nodesErased := nodes.erase sourceEnvironment.valid.2.2.1 hwf
          sourceEnvironment.fullContext sourceEnvironment.rels
          sourceEnvironment.binders sourceEnvironment.exact
          sourceEnvironment.covers
        let selected := nested.intrinsic sourceEnvironment.valid.2.2.2 hwf
          sourceEnvironment.fullContext sourceEnvironment.rels
          sourceEnvironment.binders sourceEnvironment.exact
          sourceEnvironment.covers sourceEnvironment.enumeration nodesErased
          sourceEnvironment.outer.length
          sourceEnvironment.locals.length (by
            simp [CompiledEnvironment.fullContext])
        exact {
          environment := selected.environment
          context := selected.context
          rebuild := by
            simpa [CompiledEnvironment.body, CompiledRegion.erase,
              CompiledEnvironment.fullContext, nodesErased] using
              selected.rebuild
        }

  noncomputable def CompiledItemsZipper.intrinsic
      {items : CompiledItems d} {endpoint : CompiledRegion d} :
      (zipper : CompiledItemsZipper d items endpoint) →
      (valid : items.ValidAt parent) → (hwf : d.WellFormed) →
      (context : WireContext d) → (rels : RelCtx) →
      (binders : BinderContext d rels) →
      (exact : context.Exact parent) → (covers : binders.Covers parent) →
      (enumeration : BinderContext.Enumeration d binders parent) →
      (before : ItemSeq context.length rels) →
      (outerWires localWires : Nat) →
      (split : context.length = outerWires + localWires) →
      CompiledHole
        (.mk localWires
          ((before.append (items.erase valid hwf context rels binders exact
            covers)).castWiresEq split)) endpoint hwf
    | .cut (body := body) (suffix := suffix) nested, valid, hwf, context,
        rels, binders, exact, covers, enumeration, before, outerWires, localWires,
        split => by
        have parentShape : (d.regions body.origin).parent? = some parent := by
          simp [valid.1.1, CRegion.parent?]
        let bodyEnvironment : CompiledEnvironment body := {
          outer := context
          locals := exactScopeWires d body.origin
          rels := rels
          binders := binders
          valid := valid.1.2
          exact := exact.extend_child hwf parentShape
          covers := BinderContext.covers_cut_child covers valid.1.1
          enumeration := enumeration.cutChild hwf valid.1.1
        }
        let selected := nested.intrinsic bodyEnvironment hwf
        let suffixErased := suffix.erase valid.2 hwf context rels binders exact
          covers
        exact {
          environment := selected.environment
          context := .cut localWires (before.castWiresEq split)
            (suffixErased.castWiresEq split)
            (DiagramContext.castOuterWires split selected.context)
          rebuild := by
            have nestedEq :
                (DiagramContext.castOuterWires split selected.context).fill
                    (selected.environment.body hwf) =
                  (bodyEnvironment.body hwf).castWiresEq split :=
              (DiagramContext.castOuterWires_fill split selected.context
                (selected.environment.body hwf)).trans
                (congrArg (Region.castWiresEq split) selected.rebuild)
            simp only [DiagramContext.fill]
            calc
              _ = .mk localWires
                  ((before.castWiresEq split).append
                    (.cons (.cut ((bodyEnvironment.body hwf).castWiresEq split))
                      (suffixErased.castWiresEq split))) := by
                exact congrArg (fun sequence => Region.mk localWires sequence)
                  (congrArg (fun item =>
                    (before.castWiresEq split).append
                      (.cons item (suffixErased.castWiresEq split)))
                    (congrArg Item.cut nestedEq))
              _ = _ := by
                rw [CompiledItems.erase]
                simp only [ItemSeq.castWiresEq_append,
                  ItemSeq.castWiresEq_cons, suffixErased]
                rw [CompiledItem.erase]
                simp only [Item.castWiresEq_cut]
                rfl
        }
    | .bubble (arity := arity) (body := body) (suffix := suffix) nested,
        valid, hwf, context, rels, binders, exact, covers, enumeration, before,
        outerWires, localWires, split => by
        have parentShape : (d.regions body.origin).parent? = some parent := by
          simp [valid.1.1, CRegion.parent?]
        let bodyEnvironment : CompiledEnvironment body := {
          outer := context
          locals := exactScopeWires d body.origin
          rels := arity :: rels
          binders := binders.push body.origin arity
          valid := valid.1.2
          exact := exact.extend_child hwf parentShape
          covers := BinderContext.push_covers_bubble_child covers valid.1.1
          enumeration := enumeration.bubbleChild hwf valid.1.1
        }
        let selected := nested.intrinsic bodyEnvironment hwf
        let suffixErased := suffix.erase valid.2 hwf context rels binders exact
          covers
        exact {
          environment := selected.environment
          context := .bubble localWires (before.castWiresEq split)
            (suffixErased.castWiresEq split) arity
            (DiagramContext.castOuterWires split selected.context)
          rebuild := by
            have nestedEq :
                (DiagramContext.castOuterWires split selected.context).fill
                    (selected.environment.body hwf) =
                  (bodyEnvironment.body hwf).castWiresEq split :=
              (DiagramContext.castOuterWires_fill split selected.context
                (selected.environment.body hwf)).trans
                (congrArg (Region.castWiresEq split) selected.rebuild)
            simp only [DiagramContext.fill]
            calc
              _ = .mk localWires
                  ((before.castWiresEq split).append
                    (.cons (.bubble arity
                      ((bodyEnvironment.body hwf).castWiresEq split))
                      (suffixErased.castWiresEq split))) := by
                exact congrArg (fun sequence => Region.mk localWires sequence)
                  (congrArg (fun item =>
                    (before.castWiresEq split).append
                      (.cons item (suffixErased.castWiresEq split)))
                    (congrArg (Item.bubble arity) nestedEq))
              _ = _ := by
                rw [CompiledItems.erase]
                simp only [ItemSeq.castWiresEq_append,
                  ItemSeq.castWiresEq_cons, suffixErased]
                rw [CompiledItem.erase]
                simp only [Item.castWiresEq_bubble]
                rfl
        }
    | .tail (head := head) nested, valid, hwf, context, rels, binders,
        exact, covers, enumeration, before, outerWires, localWires, split => by
        let headErased := head.erase valid.1 hwf context rels binders exact
          covers
        rw [CompiledItems.erase]
        simpa only [ItemSeq.append_assoc, ItemSeq.append] using
          nested.intrinsic valid.2 hwf context rels binders exact covers
            enumeration
            (before.append (.cons headErased .nil)) outerWires localWires split
end

private theorem CompiledRegion.items_origins_of_valid
    (region : CompiledRegion d) (valid : region.Valid) :
    region.items.origins = localOccurrences d region.origin := by
  cases region with
  | mk origin nodes children =>
      rw [CompiledRegion.items_mk, CompiledItems.origins_append,
        valid.1, valid.2.1]
      rfl

namespace CompiledSite

/-- The canonical source-derived focus at a concrete region. -/
noncomputable def focus (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    CompiledFocus source.checked.compilation site :=
  (source.checked.compilation.focus? site).get <|
    CompiledRegion.focus?_isSome_of_valid source.checked.compilation
      source.checked.compilation_valid
      source.checked.property.diagram_well_formed site (by
        obtain ⟨steps, reachesRoot⟩ :=
          source.checked.property.diagram_well_formed.all_regions_reach_root site
        simpa only [VisualProof.Concrete.CheckedOpen.compilation_origin] using
          (show source.diagram.val.Encloses source.diagram.val.root site from
            ⟨steps, reachesRoot⟩))

@[simp] theorem focus_computation (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    source.checked.compilation.focus? site = some (focus source site) :=
  (Option.some_get <|
    CompiledRegion.focus?_isSome_of_valid source.checked.compilation
      source.checked.compilation_valid
      source.checked.property.diagram_well_formed site (by
        obtain ⟨steps, reachesRoot⟩ :=
          source.checked.property.diagram_well_formed.all_regions_reach_root site
        simpa only [VisualProof.Concrete.CheckedOpen.compilation_origin] using
          (show source.diagram.val.Encloses source.diagram.val.root site from
            ⟨steps, reachesRoot⟩))).symm

noncomputable def endpoint (source : State arity)
    (site : Fin source.diagram.val.regionCount) : CompiledRegion source.diagram.val :=
  (focus source site).endpoint

def endpoint_origin (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    (endpoint source site).origin = site :=
  (focus source site).endpoint_origin

/-- Canonical lexical environment of the checked open root. -/
def rootEnvironment (source : State arity) :
    CompiledEnvironment source.checked.compilation where
  outer := source.checked.val.exposedWires
  locals := source.checked.val.hiddenWires
  rels := []
  binders := BinderContext.empty
  valid := source.checked.compilation_valid
  exact := by
    simpa only [VisualProof.Concrete.CheckedOpen.compilation_origin,
      OpenDiagram.rootWires] using
      openRootWires_exact source.checked.property
  covers := by
    simpa only [VisualProof.Concrete.CheckedOpen.compilation_origin] using
      BinderContext.empty_covers_root
        source.checked.property.diagram_well_formed
  enumeration := by
    simpa only [VisualProof.Concrete.CheckedOpen.compilation_origin] using
      BinderContext.Enumeration.empty source.diagram.val

noncomputable def intrinsic (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    CompiledHole ((rootEnvironment source).body
      source.checked.property.diagram_well_formed) (endpoint source site)
      source.checked.property.diagram_well_formed :=
  (focus source site).zipper.intrinsic (rootEnvironment source)
    source.checked.property.diagram_well_formed

noncomputable def environment (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    CompiledEnvironment (endpoint source site) :=
  (intrinsic source site).environment

noncomputable def outerContext (source : State arity)
    (site : Fin source.diagram.val.regionCount) : WireContext source.diagram.val :=
  (environment source site).outer

noncomputable def localContext (source : State arity)
    (site : Fin source.diagram.val.regionCount) : WireContext source.diagram.val :=
  (environment source site).locals

noncomputable def fullContext (source : State arity)
    (site : Fin source.diagram.val.regionCount) : WireContext source.diagram.val :=
  (environment source site).fullContext

noncomputable def rels (source : State arity)
    (site : Fin source.diagram.val.regionCount) : RelCtx :=
  (environment source site).rels

noncomputable def binders (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    BinderContext source.diagram.val (rels source site) :=
  (environment source site).binders

noncomputable def body (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    Region (outerContext source site).length (rels source site) :=
  (environment source site).body
    source.checked.property.diagram_well_formed

noncomputable def context (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    DiagramContext source.checked.val.exposedWires.length
      (outerContext source site).length
      [] (rels source site) :=
  (intrinsic source site).context

theorem rebuild (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    (context source site).fill (body source site) =
      source.checked.elaborate.body := by
  simpa [context, body, intrinsic, rootEnvironment,
    CompiledEnvironment.body, VisualProof.Concrete.CheckedOpen.elaborate] using
    (intrinsic source site).rebuild

noncomputable def directItems (source : State arity)
    (site : Fin source.diagram.val.regionCount) : CompiledItems source.diagram.val :=
  (endpoint source site).items

theorem directItems_origins (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    (directItems source site).origins =
      localOccurrences source.diagram.val site := by
  have valid := (environment source site).valid
  have atOrigin : (endpoint source site).items.origins =
      localOccurrences source.diagram.val (endpoint source site).origin :=
    CompiledRegion.items_origins_of_valid _ valid
  exact atOrigin.trans (congrArg _ (endpoint_origin source site))

theorem fullContext_exact (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    (fullContext source site).Exact site := by
  have exact := (environment source site).exact
  rw [endpoint_origin source site] at exact
  simpa [fullContext, CompiledEnvironment.fullContext] using exact

theorem binders_covers (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    (binders source site).Covers site := by
  have covers := (environment source site).covers
  rw [endpoint_origin source site] at covers
  simpa [binders] using covers

/-- The inverse lexical interface derived by the same structural focus fold:
each relation position names its unique concrete bubble owner. -/
noncomputable def binders_enumeration (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    BinderContext.Enumeration source.diagram.val (binders source site) site := by
  have enumeration := (environment source site).enumeration
  rw [endpoint_origin source site] at enumeration
  simpa [binders] using enumeration

@[simp] theorem body_localCount (source : State arity)
    (site : Fin source.diagram.val.regionCount) :
    (body source site).localCount = (localContext source site).length :=
  CompiledRegion.erase_localCount _ (environment source site).valid
    source.checked.property.diagram_well_formed _ _ _ _
    (environment source site).exact (environment source site).covers

end CompiledSite

end VisualProof.Concrete.Elaboration
