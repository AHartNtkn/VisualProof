import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.State
import VisualProof.Diagram.Replacement

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open Elaboration

/-- A source compiler computation focused at one concrete region.  The
intrinsic path belongs to the already compiled source body; the concrete wire
and binder contexts are the exact inputs of the focused source compiler call. -/
structure RegionSiteCompilation
    (diagram : Concrete.Diagram)
    (site : Fin diagram.regionCount)
    {outerWires : Nat} {outerRels : RelCtx}
    (body : Region outerWires outerRels) where
  path : List Nat
  witness : Region.ContextPath body path
  siteRels : RelCtx
  siteContext : WireContext diagram
  siteBinders : BinderContext diagram siteRels
  siteFuel : Nat
  siteBody : Region siteContext.length siteRels
  site_compiled : compileRegion? diagram siteFuel site siteContext
    siteBinders = some siteBody
  fullWires : WireContext diagram
  fullWires_exact : fullWires.Exact site
  binder_covers : siteBinders.Covers site
  focus_wires : witness.toFocus.holeWires = siteContext.length
  focus_rels : witness.toFocus.holeRels = siteRels
  focus_body : HEq witness.toFocus.body siteBody

noncomputable def RegionSiteCompilation.ofRegion
    {diagram : Concrete.Diagram}
    (wellFormed : diagram.WellFormed)
    {site current : Fin diagram.regionCount}
    {context : WireContext diagram}
    {binders : BinderContext diagram rels}
    {fuel : Nat} {body : Region context.length rels}
    (compiled : compileRegion? diagram fuel current context binders =
      some body)
    (fullWires : (context.extend current).Exact current)
    (binderCovers : binders.Covers current)
    (encloses : diagram.Encloses current site) :
    RegionSiteCompilation diagram site body := by
  by_cases atSite : current = site
  · subst current
    exact {
      path := []
      witness := .here body
      siteRels := rels
      siteContext := context
      siteBinders := binders
      siteFuel := fuel
      siteBody := body
      site_compiled := compiled
      fullWires := context.extend site
      fullWires_exact := fullWires
      binder_covers := binderCovers
      focus_wires := rfl
      focus_rels := rfl
      focus_body := .rfl
    }
  · let childExistence := exists_direct_child_enclosing wellFormed
      (ancestor := current) (descendant := site)
      (fun equality => atSite equality.symm) encloses
    let child := Classical.choose childExistence
    have childData := Classical.choose_spec childExistence
    have childParent : (diagram.regions child).parent? = some current :=
      childData.1
    have childEncloses : diagram.Encloses child site := childData.2
    cases fuel with
    | zero => simp [compileRegion?] at compiled
    | succ childFuel =>
        simp only [compileRegion?] at compiled
        let extended := context.extend current
        cases itemsResult : compileOccurrencesWith? diagram
            (compileRegion? diagram childFuel) extended binders
            (localOccurrences diagram current) with
        | none => simp [extended, itemsResult] at compiled
        | some items =>
            simp [extended, itemsResult] at compiled
            subst body
            have childMem : LocalOccurrence.child child ∈
                localOccurrences diagram current :=
              (mem_localOccurrences_child diagram current child).2 childParent
            let occurrenceExistence := indexOf?_complete childMem
            let occurrenceIndex := Classical.choose occurrenceExistence
            have occurrenceFound := Classical.choose_spec occurrenceExistence
            have occurrenceEq :
                (localOccurrences diagram current).get occurrenceIndex =
                  .child child := indexOf?_sound occurrenceFound
            let itemIndex : Fin items.length := Fin.cast
              (compileOccurrencesWith?_length
                (compileRegion? diagram childFuel) extended binders
                itemsResult).symm occurrenceIndex
            have compiledItem := compileOccurrencesWith?_get
              (compileRegion? diagram childFuel) extended binders itemsResult
              occurrenceIndex
            rw [occurrenceEq] at compiledItem
            let focused := items.focusAt itemIndex
            have focusedItem : focused.focus.item = items.get itemIndex :=
              focused.item_eq
            cases childKind : diagram.regions child with
            | sheet =>
                simp [childKind, CRegion.parent?] at childParent
            | cut parent =>
                have parentEq : parent = current := by
                  simpa [childKind, CRegion.parent?] using childParent
                subst parent
                simp only [compileOccurrenceWith?, childKind] at compiledItem
                cases childCompilation : compileRegion? diagram childFuel child
                    extended binders with
                | none => simp [childCompilation] at compiledItem
                | some childBody =>
                    simp [childCompilation] at compiledItem
                    have itemEq : items.get itemIndex = .cut childBody := by
                      simpa [itemIndex] using compiledItem.symm
                    have focusedCut : focused.focus.item = .cut childBody :=
                      focusedItem.trans itemEq
                    let nested := RegionSiteCompilation.ofRegion wellFormed
                      childCompilation
                        (fullWires.extend_child wellFormed childParent)
                        (BinderContext.covers_cut_child binderCovers childKind)
                        childEncloses
                    let wireEq := WireContext.length_extend context current
                    let castFocus := focused.focus.castWiresEq wireEq
                    let castNested := nested.witness.castWiresEq wireEq
                    have castAt :
                        (items.castWiresEq wireEq).focusAt?
                            occurrenceIndex.val = some castFocus := by
                      have := ItemSeq.focusAt?_castWiresEq wireEq items
                        occurrenceIndex.val focused.focus focused.atIndex
                      simpa [itemIndex] using this
                    have castCut : castFocus.item =
                        .cut (childBody.castWiresEq wireEq) := by
                      simp [castFocus, focusedCut]
                    let witness : Region.ContextPath
                        (finishRegion diagram context current items)
                        (occurrenceIndex.val :: nested.path) :=
                      .cut castFocus castAt castCut castNested
                    exact {
                      path := occurrenceIndex.val :: nested.path
                      witness := witness
                      siteRels := nested.siteRels
                      siteContext := nested.siteContext
                      siteBinders := nested.siteBinders
                      siteFuel := nested.siteFuel
                      siteBody := nested.siteBody
                      site_compiled := nested.site_compiled
                      fullWires := nested.fullWires
                      fullWires_exact := nested.fullWires_exact
                      binder_covers := nested.binder_covers
                      focus_wires := by
                        change castNested.toFocus.holeWires =
                          nested.siteContext.length
                        simpa [castNested] using nested.focus_wires
                      focus_rels := by
                        change castNested.toFocus.holeRels = nested.siteRels
                        simpa [castNested] using nested.focus_rels
                      focus_body := by
                        change HEq castNested.toFocus.body nested.siteBody
                        exact (Region.ContextPath.castWiresEq_toFocus_body_heq
                          wireEq nested.witness).trans nested.focus_body
                    }
            | bubble parent arity =>
                have parentEq : parent = current := by
                  simpa [childKind, CRegion.parent?] using childParent
                subst parent
                simp only [compileOccurrenceWith?, childKind] at compiledItem
                let childBinders := binders.push child arity
                cases childCompilation : compileRegion? diagram childFuel child
                    extended childBinders with
                | none => simp [childBinders, childCompilation] at compiledItem
                | some childBody =>
                    simp [childBinders, childCompilation] at compiledItem
                    have itemEq : items.get itemIndex =
                        .bubble arity childBody := by
                      simpa [itemIndex] using compiledItem.symm
                    have focusedBubble : focused.focus.item =
                        .bubble arity childBody := focusedItem.trans itemEq
                    let nested := RegionSiteCompilation.ofRegion wellFormed
                      childCompilation
                        (fullWires.extend_child wellFormed childParent)
                        (BinderContext.push_covers_bubble_child binderCovers
                          childKind)
                        childEncloses
                    let wireEq := WireContext.length_extend context current
                    let castFocus := focused.focus.castWiresEq wireEq
                    let castNested := nested.witness.castWiresEq wireEq
                    have castAt :
                        (items.castWiresEq wireEq).focusAt?
                            occurrenceIndex.val = some castFocus := by
                      have := ItemSeq.focusAt?_castWiresEq wireEq items
                        occurrenceIndex.val focused.focus focused.atIndex
                      simpa [itemIndex] using this
                    have castBubble : castFocus.item =
                        .bubble arity (childBody.castWiresEq wireEq) := by
                      simp [castFocus, focusedBubble]
                    let witness : Region.ContextPath
                        (finishRegion diagram context current items)
                        (occurrenceIndex.val :: nested.path) :=
                      .bubble castFocus castAt castBubble castNested
                    exact {
                      path := occurrenceIndex.val :: nested.path
                      witness := witness
                      siteRels := nested.siteRels
                      siteContext := nested.siteContext
                      siteBinders := nested.siteBinders
                      siteFuel := nested.siteFuel
                      siteBody := nested.siteBody
                      site_compiled := nested.site_compiled
                      fullWires := nested.fullWires
                      fullWires_exact := nested.fullWires_exact
                      binder_covers := nested.binder_covers
                      focus_wires := by
                        change castNested.toFocus.holeWires =
                          nested.siteContext.length
                        simpa [castNested] using nested.focus_wires
                      focus_rels := by
                        change castNested.toFocus.holeRels = nested.siteRels
                        simpa [castNested] using nested.focus_rels
                      focus_body := by
                        change HEq castNested.toFocus.body nested.siteBody
                        exact (Region.ContextPath.castWiresEq_toFocus_body_heq
                          wireEq nested.witness).trans nested.focus_body
                    }
termination_by fuel

/-- Focus a non-root concrete site inside one exact successful root compiler
computation.  The first path step is derived from the root occurrence stream;
all remaining steps reuse `RegionSiteCompilation.ofRegion`. -/
noncomputable def RegionSiteCompilation.ofRootDescendant
    {diagram : Concrete.Diagram}
    (wellFormed : diagram.WellFormed)
    {site : Fin diagram.regionCount}
    {ambient locals : WireContext diagram}
    {body : Region ambient.length []}
    (compiled : compileRoot? diagram ambient locals = some body)
    (rootWires : (ambient ++ locals).Exact diagram.root)
    (rootBinders : (BinderContext.empty : BinderContext diagram []).Covers
      diagram.root)
    (notRoot : site ≠ diagram.root) :
    RegionSiteCompilation diagram site body := by
  simp only [compileRoot?] at compiled
  let rootContext := ambient ++ locals
  cases itemsResult : compileOccurrencesWith? diagram
      (compileRegion? diagram diagram.regionCount) rootContext
      BinderContext.empty (localOccurrences diagram diagram.root) with
  | none => simp [rootContext, itemsResult] at compiled
  | some items =>
      simp [rootContext, itemsResult] at compiled
      subst body
      let childExistence := exists_direct_child_enclosing wellFormed
        (ancestor := diagram.root) (descendant := site) notRoot
        (wellFormed.all_regions_reach_root site)
      let child := Classical.choose childExistence
      have childData := Classical.choose_spec childExistence
      have childParent : (diagram.regions child).parent? = some diagram.root :=
        childData.1
      have childEncloses : diagram.Encloses child site := childData.2
      have childMem : LocalOccurrence.child child ∈
          localOccurrences diagram diagram.root :=
        (mem_localOccurrences_child diagram diagram.root child).2 childParent
      let occurrenceExistence := indexOf?_complete childMem
      let occurrenceIndex := Classical.choose occurrenceExistence
      have occurrenceFound := Classical.choose_spec occurrenceExistence
      have occurrenceEq :
          (localOccurrences diagram diagram.root).get occurrenceIndex =
            .child child := indexOf?_sound occurrenceFound
      let itemIndex : Fin items.length := Fin.cast
        (compileOccurrencesWith?_length
          (compileRegion? diagram diagram.regionCount) rootContext
          BinderContext.empty itemsResult).symm occurrenceIndex
      have compiledItem := compileOccurrencesWith?_get
        (compileRegion? diagram diagram.regionCount) rootContext
        BinderContext.empty itemsResult occurrenceIndex
      rw [occurrenceEq] at compiledItem
      let focused := items.focusAt itemIndex
      have focusedItem : focused.focus.item = items.get itemIndex :=
        focused.item_eq
      cases childKind : diagram.regions child with
      | sheet => simp [childKind, CRegion.parent?] at childParent
      | cut parent =>
          have parentEq : parent = diagram.root := by
            simpa [childKind, CRegion.parent?] using childParent
          subst parent
          simp only [compileOccurrenceWith?, childKind] at compiledItem
          cases childCompilation : compileRegion? diagram diagram.regionCount
              child rootContext BinderContext.empty with
          | none => simp [childCompilation] at compiledItem
          | some childBody =>
              simp [childCompilation] at compiledItem
              have itemEq : items.get itemIndex = .cut childBody := by
                simpa [itemIndex] using compiledItem.symm
              have focusedCut : focused.focus.item = .cut childBody :=
                focusedItem.trans itemEq
              let nested := RegionSiteCompilation.ofRegion wellFormed
                childCompilation
                  (rootWires.extend_child wellFormed childParent)
                  (BinderContext.covers_cut_child rootBinders childKind)
                  childEncloses
              let wireEq : rootContext.length = ambient.length + locals.length :=
                by simp [rootContext]
              let castFocus := focused.focus.castWiresEq wireEq
              let castNested := nested.witness.castWiresEq wireEq
              have castAt :
                  (items.castWiresEq wireEq).focusAt? occurrenceIndex.val =
                    some castFocus := by
                have := ItemSeq.focusAt?_castWiresEq wireEq items
                  occurrenceIndex.val focused.focus focused.atIndex
                simpa [itemIndex] using this
              have castCut : castFocus.item =
                  .cut (childBody.castWiresEq wireEq) := by
                simp [castFocus, focusedCut]
              let witness : Region.ContextPath
                  (finishRoot ambient locals items)
                  (occurrenceIndex.val :: nested.path) :=
                .cut castFocus castAt castCut castNested
              exact {
                path := occurrenceIndex.val :: nested.path
                witness := witness
                siteRels := nested.siteRels
                siteContext := nested.siteContext
                siteBinders := nested.siteBinders
                siteFuel := nested.siteFuel
                siteBody := nested.siteBody
                site_compiled := nested.site_compiled
                fullWires := nested.fullWires
                fullWires_exact := nested.fullWires_exact
                binder_covers := nested.binder_covers
                focus_wires := by
                  change castNested.toFocus.holeWires =
                    nested.siteContext.length
                  simpa [castNested] using nested.focus_wires
                focus_rels := by
                  change castNested.toFocus.holeRels = nested.siteRels
                  simpa [castNested] using nested.focus_rels
                focus_body := by
                  change HEq castNested.toFocus.body nested.siteBody
                  exact (Region.ContextPath.castWiresEq_toFocus_body_heq
                    wireEq nested.witness).trans nested.focus_body
              }
      | bubble parent arity =>
          have parentEq : parent = diagram.root := by
            simpa [childKind, CRegion.parent?] using childParent
          subst parent
          simp only [compileOccurrenceWith?, childKind] at compiledItem
          let childBinders := BinderContext.empty.push child arity
          cases childCompilation : compileRegion? diagram diagram.regionCount
              child rootContext childBinders with
          | none => simp [childBinders, childCompilation] at compiledItem
          | some childBody =>
              simp [childBinders, childCompilation] at compiledItem
              have itemEq : items.get itemIndex = .bubble arity childBody := by
                simpa [itemIndex] using compiledItem.symm
              have focusedBubble : focused.focus.item =
                  .bubble arity childBody := focusedItem.trans itemEq
              let nested := RegionSiteCompilation.ofRegion wellFormed
                childCompilation
                  (rootWires.extend_child wellFormed childParent)
                  (BinderContext.push_covers_bubble_child rootBinders childKind)
                  childEncloses
              let wireEq : rootContext.length = ambient.length + locals.length :=
                by simp [rootContext]
              let castFocus := focused.focus.castWiresEq wireEq
              let castNested := nested.witness.castWiresEq wireEq
              have castAt :
                  (items.castWiresEq wireEq).focusAt? occurrenceIndex.val =
                    some castFocus := by
                have := ItemSeq.focusAt?_castWiresEq wireEq items
                  occurrenceIndex.val focused.focus focused.atIndex
                simpa [itemIndex] using this
              have castBubble : castFocus.item =
                  .bubble arity (childBody.castWiresEq wireEq) := by
                simp [castFocus, focusedBubble]
              let witness : Region.ContextPath
                  (finishRoot ambient locals items)
                  (occurrenceIndex.val :: nested.path) :=
                .bubble castFocus castAt castBubble castNested
              exact {
                path := occurrenceIndex.val :: nested.path
                witness := witness
                siteRels := nested.siteRels
                siteContext := nested.siteContext
                siteBinders := nested.siteBinders
                siteFuel := nested.siteFuel
                siteBody := nested.siteBody
                site_compiled := nested.site_compiled
                fullWires := nested.fullWires
                fullWires_exact := nested.fullWires_exact
                binder_covers := nested.binder_covers
                focus_wires := by
                  change castNested.toFocus.holeWires =
                    nested.siteContext.length
                  simpa [castNested] using nested.focus_wires
                focus_rels := by
                  change castNested.toFocus.holeRels = nested.siteRels
                  simpa [castNested] using nested.focus_rels
                focus_body := by
                  change HEq castNested.toFocus.body nested.siteBody
                  exact (Region.ContextPath.castWiresEq_toFocus_body_heq
                    wireEq nested.witness).trans nested.focus_body
              }

/-- The exact successful compiler call that owns a concrete site.  The root
uses the sheet compiler; every proper descendant uses the recursive region
compiler. -/
inductive ExactSiteCompilation (diagram : Concrete.Diagram) :
    (site : Fin diagram.regionCount) →
    (siteRels : RelCtx) →
    (siteContext : WireContext diagram) →
    (siteBinders : BinderContext diagram siteRels) →
    (siteBody : Region siteContext.length siteRels) → Type
  | root
      (ambient locals : WireContext diagram)
      (body : Region ambient.length [])
      (compiled : compileRoot? diagram ambient locals = some body) :
      ExactSiteCompilation diagram diagram.root [] ambient
        BinderContext.empty body
  | region
      (site : Fin diagram.regionCount)
      (siteRels : RelCtx)
      (siteContext : WireContext diagram)
      (siteBinders : BinderContext diagram siteRels)
      (fuel : Nat)
      (body : Region siteContext.length siteRels)
      (compiled : compileRegion? diagram fuel site siteContext siteBinders =
        some body) :
      ExactSiteCompilation diagram site siteRels siteContext siteBinders body

/-- Source-only compilation evidence for one concrete insertion site.  It
contains the source compiler derivation and its intrinsic abstract focus, and
contains no generated target or target-selected route. -/
structure CompiledSite (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) where
  path : List Nat
  witness : Region.ContextPath source.checked.elaborate.body path
  siteRels : RelCtx
  siteContext : WireContext source.checked.val.diagram
  siteBinders : BinderContext source.checked.val.diagram siteRels
  siteBody : Region siteContext.length siteRels
  compilation : ExactSiteCompilation source.checked.val.diagram site siteRels
    siteContext siteBinders siteBody
  fullWires : WireContext source.checked.val.diagram
  fullWires_exact : fullWires.Exact site
  binder_covers : siteBinders.Covers site
  focus_wires : witness.toFocus.holeWires = siteContext.length
  focus_rels : witness.toFocus.holeRels = siteRels
  focus_body : HEq witness.toFocus.body siteBody

/-- The source endpoint identified by the intrinsic compiler path. -/
noncomputable def CompiledSite.occurrence
    (compiled : CompiledSite source site) :
    Occurrence compiled.witness.toFocus.body source.checked.elaborate where
  interface := source.checked.elaborate
  context := compiled.witness.toFocus.context
  host_iso := by
    rw [compiled.witness.toFocus.rebuild]
    exact OpenDiagramIso.refl source.checked.elaborate

/-- The same source endpoint after the execution state's arity cast. -/
noncomputable def CompiledSite.canonicalOccurrence
    (compiled : CompiledSite source site) :
    Occurrence compiled.witness.toFocus.body
      (source.checked.elaborate.castArity source.boundary_length) :=
  compiled.occurrence.castArity source.boundary_length

/-- Compile one source site exactly once, beginning with the source root
computation and deriving all path data from that computation. -/
noncomputable def CompiledSite.ofSource (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) :
    CompiledSite source site := by
  let rootExistence :=
    CheckedOpen.elaborate_body_computation source.checked
  let rootBody := Classical.choose rootExistence
  have rootData := Classical.choose_spec rootExistence
  have rootCompiled := rootData.1
  have rootBodyEq := rootData.2
  have rootCompiledSource : compileRoot? source.checked.val.diagram
      source.checked.val.exposedWires source.checked.val.hiddenWires =
        some source.checked.elaborate.body := by
    calc
      _ = some rootBody := rootCompiled
      _ = some source.checked.elaborate.body :=
        congrArg some rootBodyEq.symm
  by_cases atRoot : site = source.checked.val.diagram.root
  · subst site
    exact {
      path := []
      witness := .here source.checked.elaborate.body
      siteRels := []
      siteContext := source.checked.val.exposedWires
      siteBinders := BinderContext.empty
      siteBody := source.checked.elaborate.body
      compilation := .root source.checked.val.exposedWires
        source.checked.val.hiddenWires source.checked.elaborate.body
          rootCompiledSource
      fullWires := source.checked.val.exposedWires ++
        source.checked.val.hiddenWires
      fullWires_exact := openRootWires_exact source.checked.property
      binder_covers := BinderContext.empty_covers_root
        source.checked.property.diagram_well_formed
      focus_wires := rfl
      focus_rels := rfl
      focus_body := .rfl
    }
  · let nested := RegionSiteCompilation.ofRootDescendant
      source.checked.property.diagram_well_formed rootCompiledSource
        (openRootWires_exact source.checked.property)
        (BinderContext.empty_covers_root
          source.checked.property.diagram_well_formed)
        atRoot
    exact {
      path := nested.path
      witness := nested.witness
      siteRels := nested.siteRels
      siteContext := nested.siteContext
      siteBinders := nested.siteBinders
      siteBody := nested.siteBody
      compilation := .region site nested.siteRels nested.siteContext
        nested.siteBinders nested.siteFuel nested.siteBody nested.site_compiled
      fullWires := nested.fullWires
      fullWires_exact := nested.fullWires_exact
      binder_covers := nested.binder_covers
      focus_wires := nested.focus_wires
      focus_rels := nested.focus_rels
      focus_body := nested.focus_body
    }

end VisualProof.Concrete
