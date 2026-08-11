import VisualProof.Concrete.Elaboration.Compile
import VisualProof.Concrete.State
import VisualProof.Diagram.Replacement

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open Elaboration

/-- The exact initial call from which a source compiler route descends. -/
inductive ConcreteCompilerStart (diagram : Concrete.Diagram)
  | openRoot (ambient locals : WireContext diagram)
  | region (origin : Fin diagram.regionCount) (context : WireContext diagram)

/-- A source compiler route indexed by its exact terminal concrete context.
The open-root constructors retain the exceptional ambient/local split, while
recursive steps extend the context by the current region's local wires. -/
inductive ConcreteCompilerRoute (diagram : Concrete.Diagram) :
    ConcreteCompilerStart diagram →
      (site : Fin diagram.regionCount) → WireContext diagram → Type
  | root (ambient locals : WireContext diagram) :
      ConcreteCompilerRoute diagram (.openRoot ambient locals)
        diagram.root ambient
  | rootStep {ambient locals : WireContext diagram}
      {child site : Fin diagram.regionCount} {siteContext : WireContext diagram}
      (parent : (diagram.regions child).parent? = some diagram.root)
      (nested : ConcreteCompilerRoute diagram
        (.region child (ambient ++ locals)) site siteContext) :
      ConcreteCompilerRoute diagram (.openRoot ambient locals)
        site siteContext
  | regionHere (region : Fin diagram.regionCount)
      (context : WireContext diagram) :
      ConcreteCompilerRoute diagram (.region region context) region context
  | regionStep {origin child site : Fin diagram.regionCount}
      {context siteContext : WireContext diagram}
      (parent : (diagram.regions child).parent? = some origin)
      (nested : ConcreteCompilerRoute diagram
        (.region child (context.extend origin)) site siteContext) :
      ConcreteCompilerRoute diagram (.region origin context) site siteContext

namespace ConcreteCompilerRoute

/-- Source-only evidence that a concrete compiler route follows the intrinsic
item-index path selected from its source occurrence streams.  Cut steps retain
the current binder context, while bubble steps push the concrete child binder. -/
inductive Derivation {diagram : Concrete.Diagram} :
    {start : ConcreteCompilerStart diagram} →
    {site : Fin diagram.regionCount} →
    {siteContext : WireContext diagram} →
    ConcreteCompilerRoute diagram start site siteContext →
    {startRels : RelCtx} →
    BinderContext diagram startRels →
    List Nat →
    {siteRels : RelCtx} →
    BinderContext diagram siteRels → Type
  | root (ambient locals : WireContext diagram) :
      Derivation (.root ambient locals) BinderContext.empty []
        BinderContext.empty
  | regionHere (region : Fin diagram.regionCount)
      (context : WireContext diagram) {rels : RelCtx}
      (binders : BinderContext diagram rels) :
      Derivation (.regionHere region context) binders [] binders
  | rootStepCut
      {ambient locals : WireContext diagram}
      {child site : Fin diagram.regionCount}
      {siteContext : WireContext diagram}
      (parent : (diagram.regions child).parent? = some diagram.root)
      (childKind : diagram.regions child = .cut diagram.root)
      (index : Fin (localOccurrences diagram diagram.root).length)
      (occurrence : (localOccurrences diagram diagram.root).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (ambient ++ locals)) site siteContext}
      (nested : Derivation nestedRoute BinderContext.empty path siteBinders) :
      Derivation (.rootStep parent nestedRoute) BinderContext.empty
        (index.val :: path) siteBinders
  | rootStepBubble
      {ambient locals : WireContext diagram}
      {child site : Fin diagram.regionCount}
      {siteContext : WireContext diagram} {arity : Nat}
      (parent : (diagram.regions child).parent? = some diagram.root)
      (childKind : diagram.regions child = .bubble diagram.root arity)
      (index : Fin (localOccurrences diagram diagram.root).length)
      (occurrence : (localOccurrences diagram diagram.root).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (ambient ++ locals)) site siteContext}
      (nested : Derivation nestedRoute
        (BinderContext.empty.push child arity) path siteBinders) :
      Derivation (.rootStep parent nestedRoute) BinderContext.empty
        (index.val :: path) siteBinders
  | regionStepCut
      {origin child site : Fin diagram.regionCount}
      {context siteContext : WireContext diagram}
      {startRels : RelCtx} (startBinders : BinderContext diagram startRels)
      (parent : (diagram.regions child).parent? = some origin)
      (childKind : diagram.regions child = .cut origin)
      (index : Fin (localOccurrences diagram origin).length)
      (occurrence : (localOccurrences diagram origin).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (context.extend origin)) site siteContext}
      (nested : Derivation nestedRoute startBinders path siteBinders) :
      Derivation (.regionStep parent nestedRoute) startBinders
        (index.val :: path) siteBinders
  | regionStepBubble
      {origin child site : Fin diagram.regionCount}
      {context siteContext : WireContext diagram}
      {startRels : RelCtx} (startBinders : BinderContext diagram startRels)
      {arity : Nat}
      (parent : (diagram.regions child).parent? = some origin)
      (childKind : diagram.regions child = .bubble origin arity)
      (index : Fin (localOccurrences diagram origin).length)
      (occurrence : (localOccurrences diagram origin).get index =
        .child child)
      {path : List Nat} {siteRels : RelCtx}
      {siteBinders : BinderContext diagram siteRels}
      {nestedRoute : ConcreteCompilerRoute diagram
        (.region child (context.extend origin)) site siteContext}
      (nested : Derivation nestedRoute (startBinders.push child arity)
        path siteBinders) :
      Derivation (.regionStep parent nestedRoute) startBinders
        (index.val :: path) siteBinders

end ConcreteCompilerRoute

/-- A source compiler computation focused at one concrete region.  The
intrinsic path belongs to the already compiled source body; the concrete wire
and binder contexts are the exact inputs of the focused source compiler call. -/
structure RegionSiteCompilation
    (diagram : Concrete.Diagram)
    (start : ConcreteCompilerStart diagram)
    {outerWires : Nat} {outerRels : RelCtx}
    (startBinders : BinderContext diagram outerRels)
    (site : Fin diagram.regionCount)
    (body : Region outerWires outerRels) where
  path : List Nat
  witness : Region.ContextPath body path
  siteRels : RelCtx
  siteContext : WireContext diagram
  route : ConcreteCompilerRoute diagram start site siteContext
  siteBinders : BinderContext diagram siteRels
  derivation : route.Derivation startBinders path siteBinders
  siteFuel : Nat
  siteBody : Region siteContext.length siteRels
  site_compiled : compileRegion? diagram siteFuel site siteContext
    siteBinders = some siteBody
  siteLocals : WireContext diagram
  siteLocals_eq : siteLocals = exactScopeWires diagram site
  fullWires : WireContext diagram
  fullWires_eq : fullWires = siteContext ++ siteLocals
  fullWires_exact : fullWires.Exact site
  siteBody_localCount : siteBody.localCount = siteLocals.length
  binder_covers : siteBinders.Covers site
  binder_enumeration : BinderContext.Enumeration diagram siteBinders site
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
    (binderEnumeration : BinderContext.Enumeration diagram binders current)
    (encloses : diagram.Encloses current site) :
    RegionSiteCompilation diagram (.region current context) binders site
      body := by
  by_cases atSite : current = site
  · subst current
    exact {
      route := .regionHere site context
      path := []
      witness := .here body
      siteRels := rels
      siteContext := context
      siteBinders := binders
      derivation := .regionHere site context binders
      siteFuel := fuel
      siteBody := body
      site_compiled := compiled
      siteLocals := exactScopeWires diagram site
      siteLocals_eq := rfl
      fullWires := context.extend site
      fullWires_eq := rfl
      fullWires_exact := fullWires
      siteBody_localCount := compileRegion?_localCount compiled
      binder_covers := binderCovers
      binder_enumeration := binderEnumeration
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
                        (binderEnumeration.cutChild wellFormed childKind)
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
                      route := .regionStep childParent nested.route
                      path := occurrenceIndex.val :: nested.path
                      witness := witness
                      siteRels := nested.siteRels
                      siteContext := nested.siteContext
                      siteBinders := nested.siteBinders
                      derivation := .regionStepCut binders childParent childKind
                        occurrenceIndex occurrenceEq nested.derivation
                      siteFuel := nested.siteFuel
                      siteBody := nested.siteBody
                      site_compiled := nested.site_compiled
                      siteLocals := nested.siteLocals
                      siteLocals_eq := nested.siteLocals_eq
                      fullWires := nested.fullWires
                      fullWires_eq := nested.fullWires_eq
                      fullWires_exact := nested.fullWires_exact
                      siteBody_localCount := nested.siteBody_localCount
                      binder_covers := nested.binder_covers
                      binder_enumeration := nested.binder_enumeration
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
                        (binderEnumeration.bubbleChild wellFormed childKind)
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
                      route := .regionStep childParent nested.route
                      path := occurrenceIndex.val :: nested.path
                      witness := witness
                      siteRels := nested.siteRels
                      siteContext := nested.siteContext
                      siteBinders := nested.siteBinders
                      derivation := .regionStepBubble binders childParent
                        childKind occurrenceIndex occurrenceEq
                        nested.derivation
                      siteFuel := nested.siteFuel
                      siteBody := nested.siteBody
                      site_compiled := nested.site_compiled
                      siteLocals := nested.siteLocals
                      siteLocals_eq := nested.siteLocals_eq
                      fullWires := nested.fullWires
                      fullWires_eq := nested.fullWires_eq
                      fullWires_exact := nested.fullWires_exact
                      siteBody_localCount := nested.siteBody_localCount
                      binder_covers := nested.binder_covers
                      binder_enumeration := nested.binder_enumeration
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
    RegionSiteCompilation diagram (.openRoot ambient locals)
      BinderContext.empty site body := by
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
                  ((BinderContext.Enumeration.empty diagram).cutChild
                    wellFormed childKind)
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
                route := .rootStep childParent nested.route
                path := occurrenceIndex.val :: nested.path
                witness := witness
                siteRels := nested.siteRels
                siteContext := nested.siteContext
                siteBinders := nested.siteBinders
                derivation := .rootStepCut childParent childKind
                  occurrenceIndex occurrenceEq nested.derivation
                siteFuel := nested.siteFuel
                siteBody := nested.siteBody
                site_compiled := nested.site_compiled
                siteLocals := nested.siteLocals
                siteLocals_eq := nested.siteLocals_eq
                fullWires := nested.fullWires
                fullWires_eq := nested.fullWires_eq
                fullWires_exact := nested.fullWires_exact
                siteBody_localCount := nested.siteBody_localCount
                binder_covers := nested.binder_covers
                binder_enumeration := nested.binder_enumeration
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
                  ((BinderContext.Enumeration.empty diagram).bubbleChild
                    wellFormed childKind)
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
                route := .rootStep childParent nested.route
                path := occurrenceIndex.val :: nested.path
                witness := witness
                siteRels := nested.siteRels
                siteContext := nested.siteContext
                siteBinders := nested.siteBinders
                derivation := .rootStepBubble childParent childKind
                  occurrenceIndex occurrenceEq nested.derivation
                siteFuel := nested.siteFuel
                siteBody := nested.siteBody
                site_compiled := nested.site_compiled
                siteLocals := nested.siteLocals
                siteLocals_eq := nested.siteLocals_eq
                fullWires := nested.fullWires
                fullWires_eq := nested.fullWires_eq
                fullWires_exact := nested.fullWires_exact
                siteBody_localCount := nested.siteBody_localCount
                binder_covers := nested.binder_covers
                binder_enumeration := nested.binder_enumeration
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
    (siteLocals : WireContext diagram) →
    (siteBody : Region siteContext.length siteRels) → Type
  | root
      (ambient locals : WireContext diagram)
      (body : Region ambient.length [])
      (compiled : compileRoot? diagram ambient locals = some body) :
      ExactSiteCompilation diagram diagram.root [] ambient
        BinderContext.empty locals body
  | region
      (site : Fin diagram.regionCount)
      (siteRels : RelCtx)
      (siteContext : WireContext diagram)
      (siteBinders : BinderContext diagram siteRels)
      (fuel : Nat)
      (body : Region siteContext.length siteRels)
      (compiled : compileRegion? diagram fuel site siteContext siteBinders =
        some body) :
      ExactSiteCompilation diagram site siteRels siteContext siteBinders
        (exactScopeWires diagram site) body

/-- Source-only compilation evidence for one concrete insertion site.  It
contains the source compiler derivation, its concrete parent chain, and its
intrinsic abstract focus, with no generated target or target-selected data. -/
structure CompiledSite (source : State arity)
    (site : Fin source.checked.val.diagram.regionCount) where
  path : List Nat
  witness : Region.ContextPath source.checked.elaborate.body path
  siteRels : RelCtx
  siteContext : WireContext source.checked.val.diagram
  route : ConcreteCompilerRoute source.checked.val.diagram
    (.openRoot source.checked.val.exposedWires
      source.checked.val.hiddenWires) site siteContext
  siteBinders : BinderContext source.checked.val.diagram siteRels
  derivation : route.Derivation BinderContext.empty path siteBinders
  siteBody : Region siteContext.length siteRels
  siteLocals : WireContext source.checked.val.diagram
  compilation : ExactSiteCompilation source.checked.val.diagram site siteRels
    siteContext siteBinders siteLocals siteBody
  siteLocals_eq : siteLocals =
    if site = source.checked.val.diagram.root then
      source.checked.val.hiddenWires
    else
      exactScopeWires source.checked.val.diagram site
  fullWires : WireContext source.checked.val.diagram
  fullWires_eq : fullWires = siteContext ++ siteLocals
  fullWires_exact : fullWires.Exact site
  siteBody_localCount : siteBody.localCount = siteLocals.length
  binder_covers : siteBinders.Covers site
  binder_enumeration : BinderContext.Enumeration
    source.checked.val.diagram siteBinders site
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
      route := .root source.checked.val.exposedWires
        source.checked.val.hiddenWires
      path := []
      witness := .here source.checked.elaborate.body
      siteRels := []
      siteContext := source.checked.val.exposedWires
      siteBinders := BinderContext.empty
      derivation := .root source.checked.val.exposedWires
        source.checked.val.hiddenWires
      siteBody := source.checked.elaborate.body
      compilation := .root source.checked.val.exposedWires
        source.checked.val.hiddenWires source.checked.elaborate.body
          rootCompiledSource
      siteLocals := source.checked.val.hiddenWires
      siteLocals_eq := by simp
      fullWires := source.checked.val.exposedWires ++
        source.checked.val.hiddenWires
      fullWires_eq := rfl
      fullWires_exact := openRootWires_exact source.checked.property
      siteBody_localCount := compileRoot?_localCount rootCompiledSource
      binder_covers := BinderContext.empty_covers_root
        source.checked.property.diagram_well_formed
      binder_enumeration := BinderContext.Enumeration.empty
        source.checked.val.diagram
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
      route := nested.route
      path := nested.path
      witness := nested.witness
      siteRels := nested.siteRels
      siteContext := nested.siteContext
      siteBinders := nested.siteBinders
      derivation := nested.derivation
      siteBody := nested.siteBody
      siteLocals := exactScopeWires source.checked.val.diagram site
      compilation := .region site nested.siteRels nested.siteContext
        nested.siteBinders nested.siteFuel nested.siteBody nested.site_compiled
      siteLocals_eq := by
        rw [if_neg atRoot]
      fullWires := nested.fullWires
      fullWires_eq := by
        calc
          nested.fullWires = nested.siteContext ++ nested.siteLocals :=
            nested.fullWires_eq
          _ = nested.siteContext ++
              exactScopeWires source.checked.val.diagram site :=
            congrArg (List.append nested.siteContext) nested.siteLocals_eq
      fullWires_exact := nested.fullWires_exact
      siteBody_localCount := by
        rw [← nested.siteLocals_eq]
        exact nested.siteBody_localCount
      binder_covers := nested.binder_covers
      binder_enumeration := nested.binder_enumeration
      focus_wires := nested.focus_wires
      focus_rels := nested.focus_rels
      focus_body := nested.focus_body
    }

end VisualProof.Concrete
