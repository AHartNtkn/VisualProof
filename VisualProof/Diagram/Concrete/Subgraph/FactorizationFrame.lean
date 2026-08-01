import VisualProof.Diagram.Concrete.Subgraph.FactorizationPrelude
import VisualProof.Diagram.ContextOuter
namespace VisualProof
open ConcreteElaboration
open FactorizationInternal

/--
Compiler path context; `siteBody` is hole output before enclosing frame fill. -/
structure RegionFrame
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (outer : WireContext diagram) where
  visible : WireContext diagram
  siteBody : Region definitions visible.sigs
  context : DiagramContext definitions visible.sigs outer.sigs

namespace RegionFrame
private def RootProjection
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {outer : WireContext diagram}
    (site scope : RegionFrame definitions diagram outer) : Prop :=
  ∃ inner :
      DiagramContext definitions site.visible.sigs scope.visible.sigs,
    scope.siteBody = inner.fill site.siteBody ∧
    (∀ body : Region definitions site.visible.sigs,
      site.context.fill body =
        scope.context.fill (inner.fill body)) ∧
    site.context.cutDepth =
      scope.context.cutDepth + inner.cutDepth

end RegionFrame
/-- Bind exactly one region's locally scoped wires around a generated context. -/
def bindContextFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
      DiagramContext definitions holeCtx
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig) →
      DiagramContext definitions holeCtx
        (outerIds.map fun wire => (diagram.wires wire).sig)
  | [], inner => inner
  | head :: tail, inner =>
      bindContextFor diagram outerIds tail
        (.bind (diagram.wires head).sig inner)

private theorem cast_bind
    {sourceOuter targetOuter : List Sig}
    (same : sourceOuter = targetOuter)
    (sig : Sig)
    (inner :
      DiagramContext definitions holeCtx (sig :: sourceOuter)) :
    same ▸
        (DiagramContext.bind sig inner :
          DiagramContext definitions holeCtx sourceOuter) =
      DiagramContext.bind sig
        ((congrArg (List.cons sig) same) ▸ inner) := by
  cases same
  rfl

/--
The compiler's ordered local binder fold is exactly the context-level
`bindMany` block over the corresponding ordered signature list.
-/
theorem bindContextFor_eq_bindMany
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig)) :
    bindContextFor diagram outerIds localIds inner =
      DiagramContext.bindMany
        (localIds.map fun wire => (diagram.wires wire).sig)
        ((@List.map_append _ _
          (fun wire => (diagram.wires wire).sig)
          localIds outerIds) ▸ inner) := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simp only [bindContextFor, List.map_cons,
        DiagramContext.bindMany]
      rw [induction (.bind (diagram.wires head).sig inner)]
      apply congrArg
      exact
        cast_bind
          (@List.map_append _ _
            (fun wire => (diagram.wires wire).sig)
            tail outerIds)
          (diagram.wires head).sig inner

private theorem cast_bindContextFor_hole
    (same : leftHole = rightHole)
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (inner :
      DiagramContext definitions leftHole
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig)) :
    same ▸ bindContextFor diagram outerIds localIds inner =
      bindContextFor diagram outerIds localIds (same ▸ inner) := by
  cases same
  rfl

private theorem cast_surround_cut_hole
    (same : leftHole = rightHole)
    (leading suffix : ItemSeq definitions outer)
    (inner : DiagramContext definitions leftHole outer) :
    same ▸
        (DiagramContext.surround leading (.cut inner) suffix) =
      DiagramContext.surround leading (.cut (same ▸ inner)) suffix := by
  cases same
  rfl

private theorem cast_bindMany_hole
    (bound outer : List Sig)
    (same : source = bound ++ outer) :
    same ▸
        (DiagramContext.bindMany bound
          (same ▸
            (.hole :
              DiagramContext definitions source source))) =
      DiagramContext.bindMany bound
        (.hole :
          DiagramContext definitions
            (bound ++ outer) (bound ++ outer)) := by
  cases same
  rfl

/--
The compiler's site case stops immediately outside exactly the site's ordered
local-signature binder block.
-/
theorem bindContextFor_hole_stopsAboveBindMany
    (diagram : ConcreteDiagram definitionCount)
    (outer : ConcreteElaboration.WireContext diagram)
    (site : diagram.RegionId) :
    DiagramContext.StopsAboveBindMany
      ((diagram.wiresAt site).map
        (fun wire => (diagram.wires wire).sig))
      (.hole : DiagramContext definitions outer.sigs outer.sigs)
      ((ConcreteElaboration.WireContext.sigs_extend outer site) ▸
        bindContextFor diagram outer.ids (diagram.wiresAt site)
          (.hole :
            DiagramContext definitions
              (outer.extend site).sigs (outer.extend site).sigs)) := by
  apply DiagramContext.StopsAboveBindMany.hole
  let mapAppend :=
    @List.map_append _ _
      (fun wire => (diagram.wires wire).sig)
      (diagram.wiresAt site) outer.ids
  have sigsProofExact :
      ConcreteElaboration.WireContext.sigs_extend outer site =
        mapAppend :=
    Subsingleton.elim _ _
  rw [sigsProofExact]
  calc
    _ =
        mapAppend ▸
          DiagramContext.bindMany
            ((diagram.wiresAt site).map
              (fun wire => (diagram.wires wire).sig))
            (mapAppend ▸
              (.hole :
                DiagramContext definitions
                  ((diagram.wiresAt site ++ outer.ids).map
                    (fun wire => (diagram.wires wire).sig))
                  ((diagram.wiresAt site ++ outer.ids).map
                    (fun wire => (diagram.wires wire).sig)))) :=
      congrArg
        (fun context :
            DiagramContext definitions
              ((diagram.wiresAt site ++ outer.ids).map
                (fun wire => (diagram.wires wire).sig))
              outer.sigs =>
          (mapAppend ▸ context :
            DiagramContext definitions
              ((diagram.wiresAt site).map
                  (fun wire => (diagram.wires wire).sig) ++
                outer.sigs)
              outer.sigs))
        (bindContextFor_eq_bindMany diagram outer.ids
          (diagram.wiresAt site) _)
    _ = _ :=
      cast_bindMany_hole
        ((diagram.wiresAt site).map
          (fun wire => (diagram.wires wire).sig))
        outer.sigs mapAppend

theorem DiagramContext.StopsAboveBindMany.bindContextFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    {stopped :
      DiagramContext definitions stoppedHole
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig)}
    {full :
      DiagramContext definitions (bound ++ stoppedHole)
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig)}
    (decomposition : StopsAboveBindMany bound stopped full) :
    StopsAboveBindMany bound
      (bindContextFor diagram outerIds localIds stopped)
      (bindContextFor diagram outerIds localIds full) := by
  induction localIds with
  | nil => exact decomposition
  | cons head tail induction =>
      apply induction
      exact .bind decomposition

theorem DiagramContext.StopsAboveBindMany.bindContextFor_cast
    (same : fullHole = bound ++ stoppedHole)
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (full :
      DiagramContext definitions fullHole
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig))
    (stopped :
      DiagramContext definitions stoppedHole
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig))
    (decomposition :
      StopsAboveBindMany bound stopped (same ▸ full)) :
    StopsAboveBindMany bound
      (VisualProof.bindContextFor diagram outerIds localIds stopped)
      (same ▸ VisualProof.bindContextFor diagram outerIds localIds full) := by
  rw [cast_bindContextFor_hole]
  exact decomposition.bindContextFor diagram outerIds localIds

/-- Compile the unbound conjunction owned by one concrete region. -/
def compileRegionBody?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (region : diagram.RegionId)
    (outer : WireContext diagram) :
    Option (Region definitions (outer.extend region).sigs) := do
  let extended := outer.extend region
  let nodes ← compileNodes? definitions diagram extended
    (diagram.nodesAt region)
  let children ← compileChildrenWith? definitions diagram
    (compileRegion? definitions diagram fuel) extended
    (diagram.childrenOf region)
  pure (.mk (nodes.append children))

/--
Compile siblings around the enclosure-selected child; it is never caller input. -/
def compileSiblingFrame?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer) :
    ItemSeq definitions outer.sigs →
      List diagram.RegionId →
      Option (RegionFrame definitions diagram outer)
  | _, [] => none
  | leading, child :: tail =>
      if equality : child = target then do
        let suffix ← compileChildrenWith? definitions diagram
          (compileRegion? definitions diagram fuel) outer tail
        pure
          { visible := nested.visible
            siteBody := nested.siteBody
            context := .surround leading (.cut nested.context) suffix }
      else do
        let body ← compileRegion? definitions diagram fuel child outer
        compileSiblingFrame? definitions diagram fuel outer target nested
          (leading.append (.cons (.cut body) .nil)) tail

/--
Follow the unique checked enclosure path; compile complete siblings ordinarily. -/
def compileRegionFrame?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    (fuel : Nat) →
      (region : diagram.RegionId) →
      (outer : WireContext diagram) →
      Option (RegionFrame definitions diagram outer)
  | 0, _, _ => none
  | fuel + 1, region, outer =>
      let extended := outer.extend region
      if atSite : region = site then do
        let siteBody ← compileRegionBody? definitions diagram fuel
          region outer
        pure
          { visible := extended
            siteBody := siteBody
            context :=
              bindContextFor diagram outer.ids
                (diagram.wiresAt region) .hole }
      else do
        let nodes ← compileNodes? definitions diagram extended
          (diagram.nodesAt region)
        let child ← (diagram.childrenOf region).find?
          (fun candidate => decide (diagram.Encloses candidate site))
        let nested ← compileRegionFrame? definitions diagram site fuel
          child extended
        let around ←
          compileSiblingFrame? definitions diagram fuel extended child nested
          nodes (diagram.childrenOf region)
        pure
          { visible := around.visible
            siteBody := around.siteBody
            context :=
              bindContextFor diagram outer.ids
                (diagram.wiresAt region) around.context }

private theorem liftOuter_bindContextFor_local
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId)
    (localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig))
    {sig : Sig}
    (value :
      Var (outerIds.map fun wire => (diagram.wires wire).sig) sig) :
    DiagramContext.liftOuter
        (bindContextFor diagram outerIds localIds inner) value =
      DiagramContext.liftOuter inner
        (ConcreteElaboration.appendRightVar diagram localIds value) := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simpa [bindContextFor, DiagramContext.liftOuter,
        ConcreteElaboration.appendRightVar] using
        induction (.bind (diagram.wires head).sig inner)

private theorem bindContextFor_injective_local
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length)
    (outerIds : List diagram.WireId)
    (localIds : List diagram.WireId) :
    Function.Injective
      (bindContextFor (definitions := definitions) diagram outerIds
        localIds :
        DiagramContext definitions holeCtx
            ((localIds ++ outerIds).map fun wire =>
              (diagram.wires wire).sig) →
          DiagramContext definitions holeCtx
            (outerIds.map fun wire => (diagram.wires wire).sig)) := by
  induction localIds with
  | nil =>
      intro left right same
      exact same
  | cons head tail induction =>
      intro left right same
      have boundSame := induction same
      injection boundSame

private theorem compileSiblingFrame?_liftOuter_origin
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer)
    (nestedLaw :
      ∀ {sig : Sig} (value : Var outer.sigs sig),
        WireContext.origin diagram nested.visible.ids
            (DiagramContext.liftOuter nested.context value) =
          WireContext.origin diagram outer.ids value) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      {frame : RegionFrame definitions diagram outer},
      compileSiblingFrame? definitions diagram fuel outer target nested
          leading children =
        some frame →
      ∀ {sig : Sig} (value : Var outer.sigs sig),
        WireContext.origin diagram frame.visible.ids
            (DiagramContext.liftOuter frame.context value) =
          WireContext.origin diagram outer.ids value := by
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro frame accepted
      simp [compileSiblingFrame?] at accepted
  | cons child tail induction =>
      intro frame accepted sig value
      unfold compileSiblingFrame? at accepted
      by_cases same : child = target
      · simp only [same, ↓reduceDIte] at accepted
        obtain ⟨suffix, _suffixCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp accepted
        have frameExact :
            ({ visible := nested.visible
               siteBody := nested.siteBody
               context := .surround leading (.cut nested.context) suffix } :
              RegionFrame definitions diagram outer) =
              frame :=
          Option.some.inj frameEquation
        subst frame
        exact nestedLaw value
      · simp only [same, ↓reduceDIte] at accepted
        obtain ⟨body, _bodyCompiled, recursive⟩ :=
          Option.bind_eq_some_iff.mp accepted
        exact induction
          (leading.append (.cons (.cut body) .nil)) recursive value

private theorem compileRegionFrame?_liftOuter_origin
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : WireContext diagram)
      {frame : RegionFrame definitions diagram outer},
      compileRegionFrame? definitions diagram site fuel region outer =
        some frame →
      ∀ {sig : Sig} (value : Var outer.sigs sig),
        WireContext.origin diagram frame.visible.ids
            (DiagramContext.liftOuter frame.context value) =
          WireContext.origin diagram outer.ids value := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame accepted
      simp [compileRegionFrame?] at accepted
  | succ childFuel induction =>
      intro region outer frame accepted sig value
      unfold compileRegionFrame? at accepted
      by_cases atSite : region = site
      · subst region
        simp only [↓reduceDIte] at accepted
        obtain ⟨body, _bodyCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp accepted
        have frameExact :
            ({ visible := outer.extend site
               siteBody := body
               context := bindContextFor diagram outer.ids
                 (diagram.wiresAt site) .hole } :
              RegionFrame definitions diagram outer) =
              frame :=
          Option.some.inj frameEquation
        subst frame
        change
          WireContext.origin diagram (outer.extend site).ids
              (DiagramContext.liftOuter
                (bindContextFor diagram outer.ids
                  (diagram.wiresAt site) .hole) value) =
            WireContext.origin diagram outer.ids value
        rw [liftOuter_bindContextFor_local]
        change
          WireContext.origin diagram
              (diagram.wiresAt site ++ outer.ids)
              (ConcreteElaboration.appendRightVar diagram
                (diagram.wiresAt site) value) =
            WireContext.origin diagram outer.ids value
        exact
          ConcreteElaboration.origin_appendRightVar diagram
            (diagram.wiresAt site) value
      · simp only [atSite, ↓reduceDIte] at accepted
        obtain ⟨nodes, _nodesCompiled, afterNodes⟩ :=
          Option.bind_eq_some_iff.mp accepted
        obtain ⟨child, _childFound, afterChild⟩ :=
          Option.bind_eq_some_iff.mp afterNodes
        obtain ⟨nested, nestedCompiled, afterNested⟩ :=
          Option.bind_eq_some_iff.mp afterChild
        obtain ⟨around, aroundCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp afterNested
        have nestedLaw :
            ∀ {nestedSig : Sig}
              (nestedValue :
                Var (outer.extend region).sigs nestedSig),
              WireContext.origin diagram nested.visible.ids
                  (DiagramContext.liftOuter nested.context nestedValue) =
                WireContext.origin diagram (outer.extend region).ids
                  nestedValue :=
          induction child (outer.extend region) nestedCompiled
        have aroundLaw :
            ∀ {aroundSig : Sig}
              (aroundValue :
                Var (outer.extend region).sigs aroundSig),
              WireContext.origin diagram around.visible.ids
                  (DiagramContext.liftOuter around.context aroundValue) =
                WireContext.origin diagram (outer.extend region).ids
                  aroundValue :=
          compileSiblingFrame?_liftOuter_origin definitions diagram childFuel
            (outer.extend region) child nested nestedLaw nodes
            (diagram.childrenOf region) aroundCompiled
        have frameExact :
            ({ visible := around.visible
               siteBody := around.siteBody
               context := bindContextFor diagram outer.ids
                 (diagram.wiresAt region) around.context } :
              RegionFrame definitions diagram outer) =
              frame :=
          Option.some.inj frameEquation
        subst frame
        change
          WireContext.origin diagram around.visible.ids
              (DiagramContext.liftOuter
                (bindContextFor diagram outer.ids
                  (diagram.wiresAt region) around.context) value) =
            WireContext.origin diagram outer.ids value
        rw [liftOuter_bindContextFor_local]
        calc
          _ =
              WireContext.origin diagram (outer.extend region).ids
                (ConcreteElaboration.appendRightVar diagram
                  (diagram.wiresAt region) value) :=
            aroundLaw
              (ConcreteElaboration.appendRightVar diagram
                (diagram.wiresAt region) value)
          _ = _ :=
            ConcreteElaboration.origin_appendRightVar diagram
              (diagram.wiresAt region) value

/--
The inner context exposed by a strict frame step embeds the complete extended
outer context with the same concrete-wire origins. This is the structural
variable projection receipt paired with the existing body factorization.
-/
theorem compileRegionFrame?_strict_inner_liftOuter_origin
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId)
    (fuel : Nat)
    (region : diagram.RegionId)
    (outer : WireContext diagram)
    (frame : RegionFrame definitions diagram outer)
    (inner : DiagramContext definitions frame.visible.sigs
      (outer.extend region).sigs)
    (notSite : region ≠ site)
    (compiled :
      compileRegionFrame? definitions diagram site fuel region outer =
        some frame)
    (decomposition :
      frame.context =
        bindContextFor diagram outer.ids (diagram.wiresAt region) inner) :
    ∀ {sig : Sig} (value : Var (outer.extend region).sigs sig),
      WireContext.origin diagram frame.visible.ids
          (DiagramContext.liftOuter inner value) =
        WireContext.origin diagram (outer.extend region).ids value := by
  cases fuel with
  | zero => simp [compileRegionFrame?] at compiled
  | succ childFuel =>
      unfold compileRegionFrame? at compiled
      simp only [notSite, ↓reduceDIte] at compiled
      obtain ⟨nodes, _nodesCompiled, afterNodes⟩ :=
        Option.bind_eq_some_iff.mp compiled
      obtain ⟨child, _childFound, afterChild⟩ :=
        Option.bind_eq_some_iff.mp afterNodes
      obtain ⟨nested, nestedCompiled, afterNested⟩ :=
        Option.bind_eq_some_iff.mp afterChild
      obtain ⟨around, aroundCompiled, frameEquation⟩ :=
        Option.bind_eq_some_iff.mp afterNested
      have frameExact :
          ({ visible := around.visible
             siteBody := around.siteBody
             context := bindContextFor diagram outer.ids
               (diagram.wiresAt region) around.context } :
            RegionFrame definitions diagram outer) =
            frame :=
        Option.some.inj frameEquation
      subst frame
      have contextExact :
          bindContextFor diagram outer.ids (diagram.wiresAt region)
              around.context =
            bindContextFor diagram outer.ids (diagram.wiresAt region)
              inner := by
        exact decomposition
      have innerExact : around.context = inner :=
        bindContextFor_injective_local diagram outer.ids
          (diagram.wiresAt region) contextExact
      subst inner
      have nestedLaw :
          ∀ {nestedSig : Sig}
            (nestedValue : Var (outer.extend region).sigs nestedSig),
            WireContext.origin diagram nested.visible.ids
                (DiagramContext.liftOuter nested.context nestedValue) =
              WireContext.origin diagram (outer.extend region).ids
                nestedValue :=
        compileRegionFrame?_liftOuter_origin definitions diagram site
          childFuel child (outer.extend region) nestedCompiled
      have aroundLaw :
          ∀ {aroundSig : Sig}
            (aroundValue : Var (outer.extend region).sigs aroundSig),
            WireContext.origin diagram around.visible.ids
                (DiagramContext.liftOuter around.context aroundValue) =
              WireContext.origin diagram (outer.extend region).ids
                aroundValue :=
        compileSiblingFrame?_liftOuter_origin definitions diagram childFuel
          (outer.extend region) child nested nestedLaw nodes
          (diagram.childrenOf region) aroundCompiled
      intro sig value
      exact aroundLaw value

namespace RegionFrame
/-- One accepted root factorization retaining its generated scope-to-site path. -/
def GeneratedRelativeFrame
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    (site scope : diagram.RegionId) {rootOuter : WireContext diagram}
    (siteFrame scopeFrame : RegionFrame definitions diagram rootOuter) : Prop :=
  ∃ (outer : WireContext diagram) (fuel : Nat)
    (relative : RegionFrame definitions diagram outer)
    (relativeVisible : relative.visible = siteFrame.visible),
    ContextAbove diagram outer scope ∧ compileRegionFrame? definitions diagram
      site fuel scope outer = some relative ∧
    congrArg WireContext.sigs relativeVisible ▸ relative.siteBody =
        siteFrame.siteBody ∧
    ∃ inner : DiagramContext definitions relative.visible.sigs
        (outer.extend scope).sigs,
      relative.context = bindContextFor diagram outer.ids
          (diagram.wiresAt scope) inner ∧
      ∃ scopeVisible : scopeFrame.visible = outer.extend scope,
        congrArg WireContext.sigs scopeVisible ▸ scopeFrame.siteBody =
            inner.fill relative.siteBody ∧
        ∃ rootInner : DiagramContext definitions siteFrame.visible.sigs
            scopeFrame.visible.sigs,
          scopeFrame.siteBody = rootInner.fill siteFrame.siteBody ∧
          (∀ body : Region definitions siteFrame.visible.sigs,
            siteFrame.context.fill body =
              scopeFrame.context.fill (rootInner.fill body)) ∧
          siteFrame.context.cutDepth = scopeFrame.context.cutDepth +
            rootInner.cutDepth

end RegionFrame
def finishBodyFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId) :
    (localIds : List diagram.WireId) →
      Region definitions
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig) →
      Region definitions
        (outerIds.map fun wire => (diagram.wires wire).sig)
  | [], body => body
  | head :: tail, body =>
      finishBodyFor diagram outerIds tail
        (.mk (.cons (.bind (diagram.wires head).sig body) .nil))

theorem bindContextFor_fill
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId)
    (localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig))
    (body : Region definitions holeCtx) :
    (bindContextFor diagram outerIds localIds inner).fill body =
      finishBodyFor diagram outerIds localIds (inner.fill body) := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simpa [bindContextFor, DiagramContext.fill, finishBodyFor] using
        induction (.bind (diagram.wires head).sig inner)

@[simp] private theorem bindContextFor_cutDepth
    (diagram : ConcreteDiagram definitionCount)
    (outerIds : List diagram.WireId)
    (localIds : List diagram.WireId)
    (inner : DiagramContext definitions holeCtx
      ((localIds ++ outerIds).map fun wire =>
        (diagram.wires wire).sig)) :
    (bindContextFor diagram outerIds localIds inner).cutDepth =
      inner.cutDepth := by
  induction localIds with
  | nil => rfl
  | cons head tail induction =>
      simpa [bindContextFor, DiagramContext.cutDepth] using
        induction (.bind (diagram.wires head).sig inner)

theorem finishBodyFor_eq_finishRegion
    (diagram : ConcreteDiagram definitionCount)
    (outer : WireContext diagram)
    (region : diagram.RegionId)
    (body : Region definitions (outer.extend region).sigs) :
    finishBodyFor diagram outer.ids (diagram.wiresAt region) body =
      finishRegion diagram outer region body :=
  by
    unfold ConcreteElaboration.finishRegion
    change Region definitions
      ((diagram.wiresAt region ++ outer.ids).map fun wire =>
        (diagram.wires wire).sig) at body
    generalize diagram.wiresAt region = localIds at body ⊢
    induction localIds with
    | nil => rfl
    | cons head tail induction =>
        simp only [finishBodyFor]
        exact induction _

theorem compileSiblingFrame?_sound
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target : diagram.RegionId)
    (nested frame : RegionFrame definitions diagram outer)
    (leading : ItemSeq definitions outer.sigs)
    (children : List diagram.RegionId)
    (nestedCompiled :
      compileRegion? definitions diagram fuel target outer =
        some (nested.context.fill nested.siteBody))
    (accepted :
      compileSiblingFrame? definitions diagram fuel outer target nested
        leading children = some frame) :
    ∃ compiledChildren,
      compileChildrenWith? definitions diagram
          (compileRegion? definitions diagram fuel) outer children =
        some compiledChildren ∧
      (.mk (leading.append compiledChildren) :
          Region definitions outer.sigs) =
        frame.context.fill frame.siteBody := by
  induction children generalizing leading frame with
  | nil =>
      simp [compileSiblingFrame?] at accepted
  | cons child tail induction =>
      unfold compileSiblingFrame? at accepted
      split at accepted
      · rename_i equality
        subst child
        cases suffixEquation :
            compileChildrenWith? definitions diagram
              (compileRegion? definitions diagram fuel) outer tail with
        | none =>
            simp [suffixEquation] at accepted
        | some suffix =>
            have frameEquality :
                ({ visible := nested.visible
                   siteBody := nested.siteBody
                   context :=
                     DiagramContext.surround leading
                       (.cut nested.context) suffix } :
                  RegionFrame definitions diagram outer) = frame :=
              Option.some.inj (by simpa [suffixEquation] using accepted)
            subst frame
            refine
              ⟨.cons (.cut (nested.context.fill nested.siteBody)) suffix,
                ?_, ?_⟩
            · simp [compileChildrenWith?, nestedCompiled, suffixEquation]
            · simp [DiagramContext.fill, Region.surround,
                ItemSeq.append]
      · rename_i different
        cases bodyEquation :
            compileRegion? definitions diagram fuel child outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have recursive :
                compileSiblingFrame? definitions diagram fuel outer
                    target nested
                    (leading.append (.cons (.cut body) .nil)) tail =
                  some frame := by
              simpa [bodyEquation] using accepted
            obtain ⟨compiledTail, tailCompiled, filled⟩ :=
              induction frame
                (leading.append (.cons (.cut body) .nil))
                recursive
            refine
              ⟨.cons (.cut body) compiledTail, ?_, ?_⟩
            · simp [compileChildrenWith?, bodyEquation, tailCompiled]
            · simpa [ItemSeq.append_assoc] using filled

private theorem compileSiblingFrame?_projects
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target : diagram.RegionId)
    (siteNested scopeNested : RegionFrame definitions diagram outer)
    (decomposed : RegionFrame.RootProjection siteNested scopeNested) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      (siteFrame scopeFrame : RegionFrame definitions diagram outer),
      compileSiblingFrame? definitions diagram fuel outer target siteNested
          leading children = some siteFrame →
      compileSiblingFrame? definitions diagram fuel outer target scopeNested
          leading children = some scopeFrame →
      RegionFrame.RootProjection siteFrame scopeFrame := by
  rcases decomposed with
    ⟨inner, scopeBody, replace, cutDepth⟩
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro siteFrame scopeFrame siteAccepted _
      simp [compileSiblingFrame?] at siteAccepted
  | cons child tail induction =>
      intro siteFrame scopeFrame siteAccepted scopeAccepted
      by_cases same : child = target
      · subst child
        cases suffixEquation :
            compileChildrenWith? definitions diagram
              (compileRegion? definitions diagram fuel) outer tail with
        | none =>
            simp [compileSiblingFrame?, suffixEquation] at siteAccepted
        | some suffix =>
            have siteEquality :
                ({ visible := siteNested.visible
                   siteBody := siteNested.siteBody
                   context :=
                     .surround leading (.cut siteNested.context) suffix } :
                  RegionFrame definitions diagram outer) =
                siteFrame :=
              Option.some.inj
                (by simpa [compileSiblingFrame?, suffixEquation] using
                  siteAccepted)
            have scopeEquality :
                ({ visible := scopeNested.visible
                   siteBody := scopeNested.siteBody
                   context :=
                     .surround leading (.cut scopeNested.context) suffix } :
                  RegionFrame definitions diagram outer) =
                scopeFrame :=
              Option.some.inj
                (by simpa [compileSiblingFrame?, suffixEquation] using
                  scopeAccepted)
            subst siteFrame
            subst scopeFrame
            refine ⟨inner, scopeBody, ?_, ?_⟩
            · intro body
              simp only [DiagramContext.fill, Region.surround]
              rw [replace body]
            · simp only [DiagramContext.cutDepth]
              rw [cutDepth]
              omega
      · cases bodyEquation :
            compileRegion? definitions diagram fuel child outer with
        | none =>
            simp [compileSiblingFrame?, same, bodyEquation] at siteAccepted
        | some body =>
            exact
              induction
                (leading.append (.cons (.cut body) .nil))
                siteFrame scopeFrame
                (by simpa [compileSiblingFrame?, same, bodyEquation] using
                  siteAccepted)
                (by simpa [compileSiblingFrame?, same, bodyEquation] using
                  scopeAccepted)

theorem compileRegion?_of_compileRegionBody?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (region : diagram.RegionId)
    (outer : WireContext diagram)
    (body : Region definitions (outer.extend region).sigs)
    (compiled :
      compileRegionBody? definitions diagram fuel region outer = some body) :
    compileRegion? definitions diagram (fuel + 1) region outer =
      some (finishRegion diagram outer region body) := by
  unfold compileRegionBody? at compiled
  unfold compileRegion?
  cases nodesEquation :
      compileNodes? definitions diagram (outer.extend region)
        (diagram.nodesAt region) with
  | none =>
      simp [nodesEquation] at compiled
  | some nodes =>
      cases childrenEquation :
          compileChildrenWith? definitions diagram
            (compileRegion? definitions diagram fuel)
            (outer.extend region) (diagram.childrenOf region) with
      | none =>
          simp [nodesEquation, childrenEquation] at compiled
      | some children =>
          have bodyEquality :
              (.mk (nodes.append children) :
                Region definitions (outer.extend region).sigs) = body :=
            Option.some.inj
              (by simpa [nodesEquation, childrenEquation] using compiled)
          subst body
          simp [nodesEquation, childrenEquation]

theorem compileRegionFrame?_sound
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId)
    (fuel : Nat)
    (region : diagram.RegionId)
    (outer : WireContext diagram)
    (frame : RegionFrame definitions diagram outer)
    (accepted :
      compileRegionFrame? definitions diagram site fuel region outer =
        some frame) :
    compileRegion? definitions diagram fuel region outer =
      some (frame.context.fill frame.siteBody) := by
  induction fuel generalizing region outer frame with
  | zero =>
      simp [compileRegionFrame?] at accepted
  | succ fuel induction =>
      unfold compileRegionFrame? at accepted
      simp only [] at accepted
      split at accepted
      · rename_i atSite
        subst region
        cases bodyEquation :
            compileRegionBody? definitions diagram fuel site outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have frameEquality :
                ({ visible := outer.extend site
                   siteBody := body
                   context :=
                     bindContextFor diagram outer.ids
                       (diagram.wiresAt site) .hole } :
                  RegionFrame definitions diagram outer) = frame :=
              Option.some.inj (by simpa [bodyEquation] using accepted)
            subst frame
            rw [compileRegion?_of_compileRegionBody? definitions diagram
              fuel site outer body bodyEquation]
            congr 1
            exact
              (finishBodyFor_eq_finishRegion diagram outer site body).symm
                |>.trans
                  (by
                    change
                      finishBodyFor diagram outer.ids
                          (diagram.wiresAt site) body =
                        finishBodyFor diagram outer.ids
                          (diagram.wiresAt site)
                          (DiagramContext.fill .hole body)
                    rfl)
                |>.trans
                  (bindContextFor_fill diagram outer.ids
                    (diagram.wiresAt site) .hole body).symm
      · rename_i notAtSite
        cases nodesEquation :
            compileNodes? definitions diagram (outer.extend region)
              (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at accepted
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at accepted
            | some child =>
                cases nestedEquation :
                    compileRegionFrame? definitions diagram site fuel child
                      (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation]
                      at accepted
                | some nested =>
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram fuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at accepted
                    | some around =>
                        have frameEquality :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            frame :=
                          Option.some.inj
                            (by simpa [nodesEquation, childEquation,
                                nestedEquation, aroundEquation] using
                              accepted)
                        subst frame
                        have nestedCompiled :
                            compileRegion? definitions diagram fuel child
                                (outer.extend region) =
                              some
                                (nested.context.fill nested.siteBody) :=
                          induction child (outer.extend region) nested
                            nestedEquation
                        obtain ⟨compiledChildren, childrenEquation,
                            aroundFilled⟩ :=
                          compileSiblingFrame?_sound definitions diagram fuel
                            (outer.extend region) child nested around nodes
                            (diagram.childrenOf region) nestedCompiled
                            aroundEquation
                        unfold compileRegion?
                        simp [nodesEquation, childrenEquation]
                        congr 1
                        exact
                          (congrArg (finishRegion diagram outer region)
                              aroundFilled)
                            |>.trans
                              (finishBodyFor_eq_finishRegion diagram outer
                                region
                                (around.context.fill around.siteBody)).symm
                            |>.trans
                              (bindContextFor_fill diagram outer.ids
                                (diagram.wiresAt region) around.context
                                around.siteBody).symm

private def CoversStrictlyAbove
    (diagram : ConcreteDiagram definitionCount)
    (site : diagram.RegionId)
    (context : WireContext diagram) : Prop :=
  ∀ wire,
    diagram.Encloses (diagram.wires wire).scope site →
    (diagram.wires wire).scope ≠ site →
    wire ∈ context.ids

private def CoversAt
    (diagram : ConcreteDiagram definitionCount)
    (site : diagram.RegionId)
    (context : WireContext diagram) : Prop :=
  ∀ wire,
    diagram.Encloses (diagram.wires wire).scope site →
    wire ∈ context.ids

private theorem climb_succ_predecessor
    (diagram : ConcreteDiagram definitionCount)
    (steps : Nat)
    (descendant ancestor : diagram.RegionId)
    (climbed :
      diagram.climb (steps + 1) descendant = some ancestor) :
    ∃ child,
      diagram.climb steps descendant = some child ∧
        diagram.regions child = .cut ancestor := by
  induction steps generalizing descendant with
  | zero =>
      cases regionData : diagram.regions descendant with
      | sheet =>
          simp [ConcreteDiagram.climb, regionData] at climbed
      | cut parent =>
          have parentEquality : parent = ancestor := by
            apply Option.some.inj
            simpa [ConcreteDiagram.climb, regionData] using climbed
          subst parent
          exact ⟨descendant, rfl, regionData⟩
  | succ steps induction =>
      cases regionData : diagram.regions descendant with
      | sheet =>
          simp [ConcreteDiagram.climb, regionData] at climbed
      | cut parent =>
          have parentClimbed :
              diagram.climb (steps + 1) parent = some ancestor := by
            simpa [ConcreteDiagram.climb, regionData,
              Nat.succ_eq_add_one, Nat.add_assoc] using climbed
          obtain ⟨child, before, childData⟩ :=
            induction parent parentClimbed
          refine ⟨child, ?_, childData⟩
          simpa [ConcreteDiagram.climb, regionData,
            Nat.succ_eq_add_one, Nat.add_assoc] using before

private theorem enclosing_child_exists
    (diagram : ConcreteDiagram definitionCount)
    (region site : diagram.RegionId)
    (encloses : diagram.Encloses region site)
    (different : region ≠ site) :
    ∃ child,
      child ∈ diagram.childrenOf region ∧
        diagram.Encloses child site := by
  obtain ⟨⟨steps, bound⟩, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram region site).mp encloses
  cases steps with
  | zero =>
      have same : site = region := by
        simpa using Option.some.inj climbed
      exact (different same.symm).elim
  | succ steps =>
      obtain ⟨child, before, childData⟩ :=
        climb_succ_predecessor diagram steps site region
          (by simpa [Nat.succ_eq_add_one] using climbed)
      have childMember : child ∈ diagram.childrenOf region := by
        simp [ConcreteDiagram.childrenOf,
          ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
          childData]
      have childEncloses : diagram.Encloses child site := by
        apply
          (ConcreteElaboration.encloses_iff_exists
            diagram child site).mpr
        exact ⟨⟨steps, by omega⟩, before⟩
      exact ⟨child, childMember, childEncloses⟩

private theorem compileChildrenWith?_at
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : WireContext diagram) →
      Option (Region definitions context.sigs))
    (context : WireContext diagram)
    (children : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      compileChildrenWith? definitions diagram recurse context children =
        some items)
    (child : diagram.RegionId)
    (member : child ∈ children) :
    ∃ body, recurse child context = some body := by
  induction children generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      cases headEquation : recurse head context with
      | none =>
          simp [compileChildrenWith?, headEquation] at compiled
      | some headBody =>
          cases tailEquation :
              compileChildrenWith? definitions diagram recurse context
                tail with
          | none =>
              simp [compileChildrenWith?, headEquation, tailEquation]
                at compiled
          | some tailItems =>
              rcases member with same | tailMember
              · subst child
                exact ⟨headBody, headEquation⟩
              · exact induction tailItems tailEquation tailMember

private theorem compileSiblingFrame?_complete_of_children
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer)
    (leading : ItemSeq definitions outer.sigs)
    (children : List diagram.RegionId)
    (compiledChildren : ItemSeq definitions outer.sigs)
    (targetMember : target ∈ children)
    (nestedCompiled :
      compileRegion? definitions diagram fuel target outer =
        some (nested.context.fill nested.siteBody))
    (childrenCompiled :
      compileChildrenWith? definitions diagram
          (compileRegion? definitions diagram fuel) outer children =
        some compiledChildren) :
    ∃ frame,
      compileSiblingFrame? definitions diagram fuel outer target nested
          leading children =
        some frame ∧
      frame.visible = nested.visible := by
  induction children generalizing leading compiledChildren with
  | nil => simp at targetMember
  | cons child tail induction =>
      cases bodyEquation :
          compileRegion? definitions diagram fuel child outer with
      | none =>
          simp [compileChildrenWith?, bodyEquation] at childrenCompiled
      | some body =>
          cases tailEquation :
              compileChildrenWith? definitions diagram
                (compileRegion? definitions diagram fuel) outer tail with
          | none =>
              simp [compileChildrenWith?, bodyEquation, tailEquation]
                at childrenCompiled
          | some tailItems =>
              by_cases same : child = target
              · subst child
                let frame : RegionFrame definitions diagram outer :=
                  { visible := nested.visible
                    siteBody := nested.siteBody
                    context :=
                      .surround leading (.cut nested.context) tailItems }
                refine ⟨frame, ?_, rfl⟩
                change
                  compileSiblingFrame? definitions diagram fuel outer target
                      nested leading (target :: tail) =
                    some frame
                simp [compileSiblingFrame?, tailEquation, frame]
              · have targetTail : target ∈ tail := by
                  have targetNeChild : target ≠ child := Ne.symm same
                  simpa [targetNeChild] using targetMember
                obtain ⟨frame, frameCompiled, visibleEquality⟩ :=
                  induction
                    (leading.append (.cons (.cut body) .nil))
                    tailItems targetTail tailEquation
                exact ⟨frame, by
                  simp [compileSiblingFrame?, same, bodyEquation,
                    frameCompiled], visibleEquality⟩

/--
Recover the ordinary compiled region body from the three accepted branches of
an ancestor frame compilation.
-/
theorem compileRegionBody?_of_frame_branch
    {diagram : ConcreteDiagram definitions.length}
    {site region selected : diagram.RegionId}
    {fuel : Nat}
    {outer : WireContext diagram}
    {nodes : ItemSeq definitions (outer.extend region).sigs}
    {nested around :
      RegionFrame definitions diagram (outer.extend region)}
    (nodesCompiled :
      compileNodes? definitions diagram (outer.extend region)
          (diagram.nodesAt region) =
        some nodes)
    (nestedCompiled :
      compileRegionFrame? definitions diagram site fuel selected
          (outer.extend region) =
        some nested)
    (aroundCompiled :
      compileSiblingFrame? definitions diagram fuel
          (outer.extend region) selected nested nodes
          (diagram.childrenOf region) =
        some around) :
    compileRegionBody? definitions diagram fuel region outer =
      some (around.context.fill around.siteBody) := by
  have nestedBodyCompiled :=
    compileRegionFrame?_sound definitions diagram site fuel selected
      (outer.extend region) nested nestedCompiled
  obtain ⟨children, childrenCompiled, bodyExact⟩ :=
    compileSiblingFrame?_sound definitions diagram fuel
      (outer.extend region) selected nested around nodes
      (diagram.childrenOf region) nestedBodyCompiled aroundCompiled
  simp only [compileRegionBody?, nodesCompiled, childrenCompiled,
    Option.bind_some]
  exact congrArg some bodyExact

private theorem encloses_child_split_local
    (diagram : ConcreteDiagram definitionCount)
    (ancestor child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent)
    (encloses : diagram.Encloses ancestor child) :
    ancestor = child ∨ diagram.Encloses ancestor parent := by
  obtain ⟨⟨steps, bound⟩, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram ancestor child).mp encloses
  cases steps with
  | zero => exact .inl (by simpa using climbed.symm)
  | succ steps =>
      right
      apply
        (ConcreteElaboration.encloses_iff_exists
          diagram ancestor parent).mpr
      exact
        ⟨⟨steps, by omega⟩, by
          simpa [ConcreteDiagram.climb, childData] using climbed⟩

private theorem factor_climb_add
    (diagram : ConcreteDiagram definitionCount)
    (first second : Nat)
    (region : diagram.RegionId) :
    diagram.climb (first + second) region =
      (diagram.climb first region).bind (diagram.climb second) := by
  induction first generalizing region with
  | zero => simp
  | succ first induction =>
      cases regionData : diagram.regions region with
      | sheet =>
          simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
            induction parent

private theorem factor_climb_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          have rootData : diagram.regions diagram.root = .sheet :=
            wellFormed.root_is_sheet
          have impossible :
              diagram.climb (right + 1) diagram.root = none := by
            simp [ConcreteDiagram.climb, rootData]
          rw [impossible] at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          have rootData : diagram.regions diagram.root = .sheet :=
            wellFormed.root_is_sheet
          have impossible :
              diagram.climb (left + 1) diagram.root = none := by
            simp [ConcreteDiagram.climb, rootData]
          rw [impossible] at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              apply congrArg Nat.succ
              apply induction
              · simpa [ConcreteDiagram.climb, regionData] using leftClimb
              · simpa [ConcreteDiagram.climb, regionData] using rightClimb

private theorem factor_reaches_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (region : diagram.RegionId) :
    ∃ steps : Fin (diagram.regionCount + 1),
      diagram.climb steps region = some diagram.root := by
  exact
    (ConcreteElaboration.encloses_iff_exists
      diagram diagram.root region).mp
      (of_decide_eq_true
        ((List.all_eq_true.mp wellFormed.all_regions_reach_root)
          region (Data.Finite.mem_allFin region)))

private theorem factor_encloses_trans
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {outer middle inner : diagram.RegionId}
    (outerMiddle : diagram.Encloses outer middle)
    (middleInner : diagram.Encloses middle inner) :
    diagram.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram outer middle).mp outerMiddle
  obtain ⟨middleSteps, middleClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram middle inner).mp middleInner
  obtain ⟨rootSteps, outerRoot⟩ :=
    factor_reaches_root definitions diagram wellFormed outer
  have composed :
      diagram.climb (middleSteps.val + outerSteps.val) inner =
        some outer := by
    rw [factor_climb_add diagram middleSteps.val outerSteps.val inner,
      middleClimb]
    exact outerClimb
  have composedRoot :
      diagram.climb
          ((middleSteps.val + outerSteps.val) + rootSteps.val) inner =
        some diagram.root := by
    rw [factor_climb_add diagram
      (middleSteps.val + outerSteps.val) rootSteps.val inner, composed]
    exact outerRoot
  obtain ⟨canonicalSteps, canonicalRoot⟩ :=
    factor_reaches_root definitions diagram wellFormed inner
  have sameDepth :=
    factor_climb_root_unique definitions diagram wellFormed
      composedRoot canonicalRoot
  apply
    (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
  exact
    ⟨⟨middleSteps.val + outerSteps.val, by omega⟩, composed⟩

/-- Enclosure is antisymmetric in every checked concrete region tree. -/
theorem factor_encloses_antisymm
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {left right : diagram.RegionId}
    (leftRight : diagram.Encloses left right)
    (rightLeft : diagram.Encloses right left) :
    left = right := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram left right).mp
      leftRight
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram right left).mp
      rightLeft
  obtain ⟨rootSteps, rootClimb⟩ :=
    factor_reaches_root definitions diagram wellFormed left
  have loop :
      diagram.climb (rightSteps.val + leftSteps.val) left = some left := by
    rw [factor_climb_add diagram rightSteps.val leftSteps.val left, rightClimb]
    exact leftClimb
  have longerRoot :
      diagram.climb
          ((rightSteps.val + leftSteps.val) + rootSteps.val) left =
        some diagram.root := by
    rw [factor_climb_add diagram
      (rightSteps.val + leftSteps.val) rootSteps.val left, loop]
    exact rootClimb
  have sameDepth :=
    factor_climb_root_unique definitions diagram wellFormed
      longerRoot rootClimb
  have rightZero : rightSteps.val = 0 := by omega
  rw [rightZero] at rightClimb
  simpa [ConcreteDiagram.climb] using rightClimb

private theorem factor_encloses_comparable
    (diagram : ConcreteDiagram definitionCount)
    {left right descendant : diagram.RegionId}
    (leftEncloses : diagram.Encloses left descendant)
    (rightEncloses : diagram.Encloses right descendant) :
    diagram.Encloses left right ∨ diagram.Encloses right left := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram left descendant).mp
      leftEncloses
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram right descendant).mp
      rightEncloses
  by_cases before : leftSteps.val ≤ rightSteps.val
  · right
    let remaining := rightSteps.val - leftSteps.val
    apply
      (ConcreteElaboration.encloses_iff_exists diagram right left).mpr
    refine ⟨⟨remaining, Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) rightSteps.isLt⟩, ?_⟩
    have composed :=
      factor_climb_add diagram leftSteps.val remaining descendant
    have sum : leftSteps.val + remaining = rightSteps.val := by omega
    rw [sum, leftClimb, rightClimb] at composed
    exact composed.symm
  · left
    let remaining := leftSteps.val - rightSteps.val
    apply
      (ConcreteElaboration.encloses_iff_exists diagram left right).mpr
    refine ⟨⟨remaining, Nat.lt_of_le_of_lt
      (Nat.sub_le _ _) leftSteps.isLt⟩, ?_⟩
    have composed :=
      factor_climb_add diagram rightSteps.val remaining descendant
    have sum : rightSteps.val + remaining = leftSteps.val := by omega
    rw [sum, rightClimb, leftClimb] at composed
    exact composed.symm

/--
The selected child on a checked region path encloses every intermediate scope
that still encloses the selected site.
-/
theorem selected_child_encloses_scope
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region child scope site : diagram.RegionId}
    (regionScope : diagram.Encloses region scope)
    (scopeStrict : scope ≠ region)
    (childData : diagram.regions child = .cut region)
    (childSite : diagram.Encloses child site)
    (scopeSite : diagram.Encloses scope site) :
    diagram.Encloses child scope := by
  rcases factor_encloses_comparable diagram childSite scopeSite with
    childScope | scopeChild
  · exact childScope
  · rcases encloses_child_split_local diagram scope child region
        childData scopeChild with scopeIsChild | scopeRegion
    · subst scope
      exact ConcreteDiagram.encloses_refl diagram child
    · have same :=
        factor_encloses_antisymm definitions diagram wellFormed
          regionScope scopeRegion
      exact (scopeStrict same.symm).elim

theorem find?_enclosing_scope
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (children : List diagram.RegionId)
    (child scope site : diagram.RegionId)
    (foundSite :
      children.find?
          (fun candidate => decide (diagram.Encloses candidate site)) =
        some child)
    (childScope : diagram.Encloses child scope)
    (scopeSite : diagram.Encloses scope site) :
    children.find?
        (fun candidate => decide (diagram.Encloses candidate scope)) =
      some child := by
  induction children with
  | nil => simp at foundSite
  | cons head tail induction =>
      by_cases headSite : diagram.Encloses head site
      · have same : head = child := by
          simpa [headSite] using foundSite
        subst child
        simp [childScope]
      · have headScope : ¬diagram.Encloses head scope := by
          intro encloses
          exact headSite
            (factor_encloses_trans definitions diagram wellFormed
              encloses scopeSite)
        simp [headSite, headScope] at foundSite ⊢
        exact induction foundSite

private theorem extend_covers_child
    (diagram : ConcreteDiagram definitionCount)
    (parent child : diagram.RegionId)
    (outer : WireContext diagram)
    (childData : diagram.regions child = .cut parent)
    (covers : CoversStrictlyAbove diagram parent outer) :
    CoversStrictlyAbove diagram child (outer.extend parent) := by
  intro wire encloses strict
  rcases
      encloses_child_split_local diagram
        (diagram.wires wire).scope child parent childData encloses with
    same | above
  · exact (strict same).elim
  · by_cases atParent : (diagram.wires wire).scope = parent
    · simp [WireContext.extend, ConcreteDiagram.wiresAt,
        ConcreteDiagram.wiresList, Data.Finite.mem_allFin, atParent]
    · exact List.mem_append_right _ (covers wire above atParent)

private theorem compileRegionBody?_complete_of_compileRegion?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (region : diagram.RegionId)
    (outer : WireContext diagram)
    (compiled :
      ∃ body,
        compileRegion? definitions diagram (fuel + 1) region outer =
          some body) :
    ∃ body,
      compileRegionBody? definitions diagram fuel region outer =
        some body := by
  rcases compiled with ⟨body, compiled⟩
  unfold compileRegion? at compiled
  unfold compileRegionBody?
  cases nodesEquation :
      compileNodes? definitions diagram (outer.extend region)
        (diagram.nodesAt region) with
  | none =>
      simp [nodesEquation] at compiled
  | some nodes =>
      cases childrenEquation :
          compileChildrenWith? definitions diagram
            (compileRegion? definitions diagram fuel)
            (outer.extend region) (diagram.childrenOf region) with
      | none =>
          simp [nodesEquation, childrenEquation] at compiled
      | some children =>
          exact ⟨.mk (nodes.append children), by
            simp [nodesEquation, childrenEquation]⟩

private theorem compileRegionFrame?_complete_of_region
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : WireContext diagram)
      (body : Region definitions outer.sigs),
      diagram.Encloses region site →
      CoversStrictlyAbove diagram region outer →
      compileRegion? definitions diagram fuel region outer = some body →
      ∃ frame,
        compileRegionFrame? definitions diagram site fuel region outer =
          some frame ∧
        CoversAt diagram site frame.visible := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer body _ _ compiled
      simp [compileRegion?] at compiled
  | succ fuel induction =>
      intro region outer body encloses covers compiled
      by_cases atSite : region = site
      · subst region
        obtain ⟨siteBody, bodyCompiled⟩ :=
          compileRegionBody?_complete_of_compileRegion? definitions diagram
            fuel site outer ⟨body, compiled⟩
        let frame : RegionFrame definitions diagram outer :=
          { visible := outer.extend site
            siteBody := siteBody
            context :=
              bindContextFor diagram outer.ids
                (diagram.wiresAt site) .hole }
        refine ⟨frame, by
          simp [compileRegionFrame?, bodyCompiled, frame], ?_⟩
        intro wire wireEncloses
        by_cases localScope : (diagram.wires wire).scope = site
        · simp [frame, WireContext.extend, ConcreteDiagram.wiresAt,
            ConcreteDiagram.wiresList, Data.Finite.mem_allFin, localScope]
        · exact
            List.mem_append_right _
              (covers wire wireEncloses localScope)
      · let extended := outer.extend region
        cases nodesEquation :
            compileNodes? definitions diagram extended
              (diagram.nodesAt region) with
        | none =>
            simp only [compileRegion?] at compiled
            rw [nodesEquation] at compiled
            simp at compiled
        | some nodes =>
            cases childrenEquation :
                compileChildrenWith? definitions diagram
                  (compileRegion? definitions diagram fuel) extended
                  (diagram.childrenOf region) with
            | none =>
                simp only [compileRegion?] at compiled
                rw [nodesEquation, childrenEquation] at compiled
                simp at compiled
            | some children =>
                obtain ⟨pathChild, pathMember, pathEncloses⟩ :=
                  enclosing_child_exists diagram region site encloses atSite
                cases childEquation :
                    (diagram.childrenOf region).find?
                      (fun candidate =>
                        decide (diagram.Encloses candidate site)) with
                | none =>
                    have rejects :=
                      (List.find?_eq_none.mp childEquation)
                        pathChild pathMember
                    simp [pathEncloses] at rejects
                | some child =>
                    have childMember :
                        child ∈ diagram.childrenOf region :=
                      List.mem_of_find?_eq_some childEquation
                    have childEncloses :
                        diagram.Encloses child site :=
                      of_decide_eq_true
                        (List.find?_some
                          (p := fun candidate =>
                            decide (diagram.Encloses candidate site))
                          childEquation)
                    have childData :
                        diagram.regions child = .cut region := by
                      have filtered :=
                        (List.mem_filter.mp childMember).2
                      cases data : diagram.regions child with
                      | sheet => simp [data] at filtered
                      | cut parent =>
                          have same : parent = region := by
                            exact eq_of_beq
                              (by simpa [data] using filtered)
                          exact congrArg CRegion.cut same
                    have childCovers :
                        CoversStrictlyAbove diagram child extended :=
                      extend_covers_child diagram region child outer
                        childData covers
                    obtain ⟨childBody, childCompiled⟩ :=
                      compileChildrenWith?_at definitions diagram
                        (compileRegion? definitions diagram fuel)
                        extended (diagram.childrenOf region) children
                        childrenEquation child childMember
                    obtain ⟨nested, nestedCompiled, nestedCovers⟩ :=
                      induction child extended childBody childEncloses
                        childCovers childCompiled
                    have nestedRegionCompiled :=
                      compileRegionFrame?_sound definitions diagram site
                        fuel child extended nested nestedCompiled
                    obtain ⟨around, aroundCompiled, aroundVisible⟩ :=
                      compileSiblingFrame?_complete_of_children
                        definitions diagram fuel extended child nested nodes
                        (diagram.childrenOf region) children childMember
                        nestedRegionCompiled childrenEquation
                    let frame : RegionFrame definitions diagram outer :=
                      { visible := around.visible
                        siteBody := around.siteBody
                        context :=
                          bindContextFor diagram outer.ids
                            (diagram.wiresAt region)
                            around.context }
                    unfold extended at nodesEquation nestedCompiled aroundCompiled
                    refine ⟨frame, by
                      simp [compileRegionFrame?, atSite, nodesEquation,
                        childEquation, nestedCompiled, aroundCompiled,
                        frame], ?_⟩
                    simpa [frame, aroundVisible] using nestedCovers

private theorem cast_trans
    {α : Sort u} {motive : α → Sort v}
    {left middle right : α}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (value : motive left) :
    (leftMiddle.trans middleRight) ▸ value =
      middleRight ▸ (leftMiddle ▸ value) := by
  cases leftMiddle
  cases middleRight
  rfl

private theorem cast_symm_of_cast_eq
    {α : Sort u} {motive : α → Sort v}
    {left right : α} (same : left = right)
    {leftValue : motive left} {rightValue : motive right}
    (casted : same ▸ leftValue = rightValue) :
    same.symm ▸ rightValue = leftValue := by
  cases same
  exact casted.symm

private theorem compileSiblingFrame?_site_eq
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      (frame : RegionFrame definitions diagram outer),
      compileSiblingFrame? definitions diagram fuel outer target nested
          leading children =
        some frame →
      ∃ visibleEquality : frame.visible = nested.visible,
        congrArg WireContext.sigs visibleEquality ▸ frame.siteBody =
          nested.siteBody := by
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro frame accepted
      simp [compileSiblingFrame?] at accepted
  | cons child tail induction =>
      intro frame accepted
      unfold compileSiblingFrame? at accepted
      split at accepted
      · cases suffixEquation :
          compileChildrenWith? definitions diagram
            (compileRegion? definitions diagram fuel) outer tail with
        | none =>
            simp [suffixEquation] at accepted
        | some suffix =>
            have frameEquality :
                ({ visible := nested.visible
                   siteBody := nested.siteBody
                   context :=
                     .surround leading (.cut nested.context) suffix } :
                  RegionFrame definitions diagram outer) =
                  frame :=
              Option.some.inj (by
                simpa [suffixEquation] using accepted)
            subst frame
            exact ⟨rfl, rfl⟩
      · cases bodyEquation :
          compileRegion? definitions diagram fuel child outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            exact induction
              (leading.append (.cons (.cut body) .nil))
              frame (by simpa [bodyEquation] using accepted)

private theorem compileRegionFrame?_site_origin
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : WireContext diagram)
      (frame : RegionFrame definitions diagram outer),
      compileRegionFrame? definitions diagram site fuel region outer =
          some frame →
      ∃ (siteOuter : WireContext diagram) (siteFuel : Nat)
        (nodes children :
          ItemSeq definitions (siteOuter.extend site).sigs)
        (visibleEquality : frame.visible = siteOuter.extend site),
          compileNodes? definitions diagram (siteOuter.extend site)
              (diagram.nodesAt site) =
            some nodes ∧
          compileChildrenWith? definitions diagram
              (compileRegion? definitions diagram siteFuel)
              (siteOuter.extend site) (diagram.childrenOf site) =
            some children ∧
          congrArg WireContext.sigs visibleEquality ▸ frame.siteBody =
            .mk (nodes.append children) := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame accepted
      simp [compileRegionFrame?] at accepted
  | succ fuel induction =>
      intro region outer frame accepted
      unfold compileRegionFrame? at accepted
      simp only [] at accepted
      split at accepted
      · rename_i atSite
        subst region
        cases bodyEquation :
            compileRegionBody? definitions diagram fuel site outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have frameEquality :
                ({ visible := outer.extend site
                   siteBody := body
                   context :=
                     bindContextFor diagram outer.ids
                       (diagram.wiresAt site) .hole } :
                  RegionFrame definitions diagram outer) =
                  frame :=
              Option.some.inj (by
                simpa [bodyEquation] using accepted)
            subst frame
            unfold compileRegionBody? at bodyEquation
            cases nodesEquation :
                compileNodes? definitions diagram (outer.extend site)
                  (diagram.nodesAt site) with
            | none =>
                simp [nodesEquation] at bodyEquation
            | some nodes =>
                cases childrenEquation :
                    compileChildrenWith? definitions diagram
                      (compileRegion? definitions diagram fuel)
                      (outer.extend site) (diagram.childrenOf site) with
                | none =>
                    simp [nodesEquation, childrenEquation] at bodyEquation
                | some children =>
                    have bodyEquality :
                        (.mk (nodes.append children) :
                          Region definitions (outer.extend site).sigs) =
                          body :=
                      Option.some.inj (by
                        simpa [nodesEquation, childrenEquation] using
                          bodyEquation)
                    subst body
                    exact
                      ⟨outer, fuel, nodes, children, rfl,
                        nodesEquation, childrenEquation, rfl⟩
      · cases nodesEquation :
          compileNodes? definitions diagram (outer.extend region)
            (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at accepted
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at accepted
            | some child =>
                cases nestedEquation :
                    compileRegionFrame? definitions diagram site fuel child
                      (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation]
                      at accepted
                | some nested =>
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram fuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at accepted
                    | some around =>
                        have frameEquality :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            frame :=
                          Option.some.inj (by
                            simpa [nodesEquation, childEquation,
                              nestedEquation, aroundEquation] using
                              accepted)
                        subst frame
                        obtain ⟨siteOuter, siteFuel, siteNodes,
                            siteChildren, visibleEquality,
                            siteNodesEquation, siteChildrenEquation,
                            siteBodyEquality⟩ :=
                          induction child (outer.extend region) nested
                            nestedEquation
                        obtain ⟨aroundVisible, aroundBody⟩ :=
                          compileSiblingFrame?_site_eq definitions diagram
                            fuel (outer.extend region) child nested nodes
                            (diagram.childrenOf region) around
                            aroundEquation
                        exact
                          ⟨siteOuter, siteFuel, siteNodes, siteChildren,
                            aroundVisible.trans visibleEquality,
                            siteNodesEquation, siteChildrenEquation,
                            (cast_trans
                                (congrArg WireContext.sigs aroundVisible)
                                (congrArg WireContext.sigs visibleEquality)
                                around.siteBody).trans
                              ((congrArg
                                  (fun body =>
                                    congrArg WireContext.sigs
                                        visibleEquality ▸ body)
                                  aroundBody).trans
                                siteBodyEquality)⟩

private theorem compileRegionFrame?_generated_relative_at
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (site scope : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : WireContext diagram)
      (siteFrame : RegionFrame definitions diagram outer),
      ContextAbove diagram outer region →
      diagram.Encloses region scope →
      diagram.Encloses scope site →
      compileRegionFrame? definitions diagram site fuel region outer =
          some siteFrame →
      ∃ scopeFrame : RegionFrame definitions diagram outer,
        compileRegionFrame? definitions diagram scope fuel region outer =
            some scopeFrame ∧
        RegionFrame.GeneratedRelativeFrame site scope
          siteFrame scopeFrame := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer siteFrame _ _ _ accepted
      simp [compileRegionFrame?] at accepted
  | succ fuel induction =>
      intro region outer siteFrame above regionScope scopeSite accepted
      unfold compileRegionFrame? at accepted
      simp only [] at accepted
      split at accepted
      · rename_i atSite
        subst region
        have sameScope : scope = site :=
          factor_encloses_antisymm definitions diagram wellFormed
            scopeSite regionScope
        subst scope
        cases bodyEquation :
            compileRegionBody? definitions diagram fuel site outer with
        | none => simp [bodyEquation] at accepted
        | some body =>
            let relative : RegionFrame definitions diagram outer :=
              { visible := outer.extend site
                siteBody := body
                context := bindContextFor diagram outer.ids
                  (diagram.wiresAt site) .hole }
            have frameEquality : relative = siteFrame :=
              Option.some.inj
                (by simpa [bodyEquation, relative] using accepted)
            subst siteFrame
            have generated :
                compileRegionFrame? definitions diagram site (fuel + 1)
                    site outer =
                  some relative := by
              simp [compileRegionFrame?, bodyEquation, relative]
            refine ⟨relative, generated, ?_⟩
            exact
              ⟨outer, fuel + 1, relative, rfl, above, generated, rfl, .hole,
                rfl, rfl, rfl, ⟨.hole, rfl, fun _ => rfl,
                  by simp [DiagramContext.cutDepth]⟩⟩
      · rename_i notAtSite
        cases nodesEquation :
            compileNodes? definitions diagram (outer.extend region)
              (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at accepted
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at accepted
            | some child =>
                cases nestedEquation :
                    compileRegionFrame? definitions diagram site fuel child
                      (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation] at accepted
                | some nested =>
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram fuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at accepted
                    | some around =>
                        have frameEquality :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            siteFrame :=
                          Option.some.inj
                            (by simpa [nodesEquation, childEquation,
                                nestedEquation, aroundEquation] using
                              accepted)
                        subst siteFrame
                        have childMember :
                            child ∈ diagram.childrenOf region :=
                          List.mem_of_find?_eq_some childEquation
                        have childSite : diagram.Encloses child site :=
                          of_decide_eq_true
                            (List.find?_some
                              (p := fun candidate =>
                                decide (diagram.Encloses candidate site))
                              childEquation)
                        have childData :
                            diagram.regions child = .cut region := by
                          have filtered :=
                            (List.mem_filter.mp childMember).2
                          cases data : diagram.regions child with
                          | sheet => simp [data] at filtered
                          | cut parent =>
                              have same : parent = region :=
                                eq_of_beq (by simpa [data] using filtered)
                              exact congrArg CRegion.cut same
                        have nestedCompiled :=
                          compileRegionFrame?_sound definitions diagram site
                            fuel child (outer.extend region) nested
                            nestedEquation
                        obtain ⟨compiledChildren, childrenEquation,
                            aroundFilled⟩ :=
                          compileSiblingFrame?_sound definitions diagram fuel
                            (outer.extend region) child nested around nodes
                            (diagram.childrenOf region) nestedCompiled
                            aroundEquation
                        by_cases atScope : region = scope
                        · subst scope
                          let scopeBody :
                              Region definitions
                                (outer.extend region).sigs :=
                            .mk (nodes.append compiledChildren)
                          let scopeFrame :
                              RegionFrame definitions diagram outer :=
                            { visible := outer.extend region
                              siteBody := scopeBody
                              context :=
                                bindContextFor diagram outer.ids
                                  (diagram.wiresAt region) .hole }
                          let relative :
                              RegionFrame definitions diagram outer :=
                            { visible := around.visible
                              siteBody := around.siteBody
                              context :=
                                bindContextFor diagram outer.ids
                                  (diagram.wiresAt region) around.context }
                          have scopeGenerated :
                              compileRegionFrame? definitions diagram region
                                  (fuel + 1) region outer =
                                some scopeFrame := by
                            simp [compileRegionFrame?, compileRegionBody?,
                              nodesEquation, childrenEquation, scopeFrame,
                              scopeBody]
                          have relativeGenerated :
                              compileRegionFrame? definitions diagram site
                                  (fuel + 1) region outer =
                                some relative := by
                            simp [compileRegionFrame?, notAtSite, nodesEquation,
                              childEquation, nestedEquation, aroundEquation,
                              relative]
                          have projection :
                              RegionFrame.RootProjection relative scopeFrame := by
                            refine ⟨around.context, ?_, ?_, ?_⟩
                            · exact aroundFilled
                            · intro body
                              dsimp [relative, scopeFrame]
                              calc
                                _ = finishBodyFor diagram outer.ids
                                      (diagram.wiresAt region)
                                      (around.context.fill body) :=
                                  bindContextFor_fill diagram outer.ids
                                    (diagram.wiresAt region)
                                    around.context body
                                _ = _ :=
                                  (bindContextFor_fill diagram outer.ids
                                    (diagram.wiresAt region)
                                    (DiagramContext.hole :
                                      DiagramContext definitions
                                        (outer.extend region).sigs
                                        (outer.extend region).sigs)
                                    (around.context.fill body)).symm
                            · dsimp [relative, scopeFrame]
                              calc
                                _ = around.context.cutDepth :=
                                  bindContextFor_cutDepth diagram outer.ids
                                    (diagram.wiresAt region) around.context
                                _ = (DiagramContext.hole :
                                      DiagramContext definitions
                                        (outer.extend region).sigs
                                        (outer.extend region).sigs
                                    ).cutDepth + around.context.cutDepth := by
                                  simp [DiagramContext.cutDepth]
                                _ = _ :=
                                  congrArg
                                    (fun depth =>
                                      depth + around.context.cutDepth)
                                    (bindContextFor_cutDepth diagram outer.ids
                                      (diagram.wiresAt region)
                                      (DiagramContext.hole :
                                        DiagramContext definitions
                                          (outer.extend region).sigs
                                          (outer.extend region).sigs)).symm
                          refine ⟨scopeFrame, scopeGenerated, ?_⟩
                          exact
                            ⟨outer, fuel + 1, relative, rfl,
                              above, relativeGenerated, rfl, around.context, rfl,
                              rfl, aroundFilled, projection⟩
                        · have childScope :
                              diagram.Encloses child scope :=
                            selected_child_encloses_scope definitions diagram
                              wellFormed regionScope (Ne.symm atScope) childData
                              childSite scopeSite
                          have scopeChildEquation :=
                            find?_enclosing_scope definitions diagram
                              wellFormed (diagram.childrenOf region) child
                              scope site childEquation childScope scopeSite
                          obtain ⟨nestedScope, nestedScopeGenerated,
                              nestedRelative⟩ :=
                            induction child (outer.extend region) nested
                              (extend_above_child definitions diagram wellFormed outer
                                region child above childData)
                              childScope scopeSite nestedEquation
                          obtain ⟨relativeOuter, relativeFuel, relative,
                              relativeVisible, relativeAbove, relativeGenerated,
                              relativeBody, relativeInner, relativeContext,
                              nestedScopeVisible, nestedScopeBody,
                              nestedRootInner, nestedRootScopeBody,
                              nestedReplace, nestedDepth⟩ := nestedRelative
                          have nestedProjection :
                              RegionFrame.RootProjection nested nestedScope :=
                            ⟨nestedRootInner, nestedRootScopeBody,
                              nestedReplace, nestedDepth⟩
                          have nestedScopeCompiled :=
                            compileRegionFrame?_sound definitions diagram scope
                              fuel child (outer.extend region) nestedScope
                              nestedScopeGenerated
                          obtain ⟨aroundScope, aroundScopeGenerated, _⟩ :=
                            compileSiblingFrame?_complete_of_children
                              definitions diagram fuel (outer.extend region)
                              child nestedScope nodes
                              (diagram.childrenOf region) compiledChildren
                              childMember nestedScopeCompiled childrenEquation
                          obtain ⟨rootInner, scopeBodyEquality,
                              replaceEquality, depthEquality⟩ :=
                            compileSiblingFrame?_projects definitions diagram
                              fuel (outer.extend region) child nested
                              nestedScope nestedProjection nodes
                              (diagram.childrenOf region) around aroundScope
                              aroundEquation aroundScopeGenerated
                          obtain ⟨aroundVisible, aroundBody⟩ :=
                            compileSiblingFrame?_site_eq definitions diagram
                              fuel (outer.extend region) child nested nodes
                              (diagram.childrenOf region) around aroundEquation
                          obtain ⟨aroundScopeVisible, aroundScopeBody⟩ :=
                            compileSiblingFrame?_site_eq definitions diagram
                              fuel (outer.extend region) child nestedScope nodes
                              (diagram.childrenOf region) aroundScope
                              aroundScopeGenerated
                          have relativeVisible' :
                              relative.visible = around.visible :=
                            relativeVisible.trans aroundVisible.symm
                          have relativeBody' :
                              congrArg WireContext.sigs relativeVisible' ▸
                                  relative.siteBody =
                                around.siteBody := by
                            exact
                              (cast_trans
                                  (congrArg WireContext.sigs relativeVisible)
                                  (congrArg WireContext.sigs
                                    aroundVisible.symm)
                                  relative.siteBody).trans
                                ((congrArg
                                    (fun body =>
                                      congrArg WireContext.sigs
                                          aroundVisible.symm ▸ body)
                                    relativeBody).trans
                                  (cast_symm_of_cast_eq
                                    (congrArg WireContext.sigs aroundVisible)
                                    aroundBody))
                          have scopeVisible' :
                              aroundScope.visible =
                                relativeOuter.extend scope :=
                            aroundScopeVisible.trans nestedScopeVisible
                          have scopeBody' :
                              congrArg WireContext.sigs scopeVisible' ▸
                                  aroundScope.siteBody =
                                relativeInner.fill relative.siteBody :=
                            (cast_trans
                                (congrArg WireContext.sigs aroundScopeVisible)
                                (congrArg WireContext.sigs nestedScopeVisible)
                                aroundScope.siteBody).trans
                              ((congrArg
                                  (fun body =>
                                    congrArg WireContext.sigs
                                        nestedScopeVisible ▸ body)
                                  aroundScopeBody).trans nestedScopeBody)
                          let scopeFrame :
                              RegionFrame definitions diagram outer :=
                            { visible := aroundScope.visible
                              siteBody := aroundScope.siteBody
                              context :=
                                bindContextFor diagram outer.ids
                                  (diagram.wiresAt region)
                                  aroundScope.context }
                          have scopeGenerated :
                              compileRegionFrame? definitions diagram scope
                                  (fuel + 1) region outer =
                                some scopeFrame := by
                            simp [compileRegionFrame?, atScope, nodesEquation,
                              scopeChildEquation, nestedScopeGenerated,
                              aroundScopeGenerated, scopeFrame]
                          have projection :
                              RegionFrame.RootProjection
                                ({ visible := around.visible
                                   siteBody := around.siteBody
                                   context :=
                                     bindContextFor diagram outer.ids
                                       (diagram.wiresAt region)
                                       around.context } :
                                  RegionFrame definitions diagram outer)
                                scopeFrame := by
                            refine ⟨rootInner, scopeBodyEquality, ?_, ?_⟩
                            · intro body
                              dsimp [scopeFrame]
                              calc
                                _ = finishBodyFor diagram outer.ids
                                      (diagram.wiresAt region)
                                      (around.context.fill body) :=
                                  bindContextFor_fill diagram outer.ids
                                    (diagram.wiresAt region)
                                    around.context body
                                _ = finishBodyFor diagram outer.ids
                                      (diagram.wiresAt region)
                                      (aroundScope.context.fill
                                        (rootInner.fill body)) :=
                                  congrArg
                                    (finishBodyFor diagram outer.ids
                                      (diagram.wiresAt region))
                                    (replaceEquality body)
                                _ = _ :=
                                  (bindContextFor_fill diagram outer.ids
                                    (diagram.wiresAt region)
                                    aroundScope.context
                                    (rootInner.fill body)).symm
                            · dsimp [scopeFrame]
                              calc
                                _ = around.context.cutDepth :=
                                  bindContextFor_cutDepth diagram outer.ids
                                    (diagram.wiresAt region) around.context
                                _ = aroundScope.context.cutDepth +
                                      rootInner.cutDepth := depthEquality
                                _ = _ :=
                                  congrArg
                                    (fun depth => depth + rootInner.cutDepth)
                                    (bindContextFor_cutDepth diagram outer.ids
                                      (diagram.wiresAt region)
                                      aroundScope.context).symm
                          refine ⟨scopeFrame, scopeGenerated, ?_⟩
                          exact
                            ⟨relativeOuter, relativeFuel, relative,
                              relativeVisible', relativeAbove, relativeGenerated,
                              relativeBody', relativeInner, relativeContext,
                              scopeVisible', scopeBody', projection⟩

/-- The root-specialized frame produced for an explicit checked base site. -/
abbrev SiteFrame
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (_site : base.val.RegionId) :=
  RegionFrame definitions base.val (WireContext.empty base.val)

/-- Execute the ordinary compiler while retaining the path to `site`. -/
private def compileSiteFrame?
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId) :
    Option (SiteFrame base site) :=
  compileRegionFrame? definitions base.val site
    (base.val.regionCount + 1) base.val.root
    (WireContext.empty base.val)

private theorem empty_covers_strictly_above_root
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions) :
    CoversStrictlyAbove base.val base.val.root
      (WireContext.empty base.val) := by
  intro wire encloses strict
  obtain ⟨⟨steps, bound⟩, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists base.val
      (base.val.wires wire).scope base.val.root).mp encloses
  cases steps with
  | zero =>
      exact (strict (by simpa using climbed.symm)).elim
  | succ steps =>
      rw [ConcreteDiagram.climb, base.property.root_is_sheet] at climbed
      simp at climbed

private theorem compileSiteFrame?_complete
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId) :
    ∃ frame,
      compileSiteFrame? base site = some frame ∧
        CoversAt base.val site frame.visible := by
  have rootEncloses : base.val.Encloses base.val.root site :=
    of_decide_eq_true
      ((List.all_eq_true.mp base.property.all_regions_reach_root)
        site (Data.Finite.mem_allFin site))
  have rootCompiled :=
    elaborateWith_compiles definitions base.val base.property
  unfold ConcreteElaboration.compileRoot? at rootCompiled
  obtain ⟨frame, generated, covers⟩ :=
    compileRegionFrame?_complete_of_region definitions base.val site
      (base.val.regionCount + 1) base.val.root
      (WireContext.empty base.val) (elaborate base)
      rootEncloses (empty_covers_strictly_above_root base) rootCompiled
  exact ⟨frame, generated, covers⟩

/--
Executable structural receipt for one explicit insertion site. Public
construction requires an exact successful site-frame compiler equation.
-/
structure SiteCompilation
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId) where
  private mk ::
  frame : SiteFrame base site
  private frame_compiles :
    compileSiteFrame? base site = some frame

/-- Run the site-frame compiler and retain its exact successful equation. -/
def compileSite?
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId) :
    Option (SiteCompilation base site) :=
  match accepted : compileSiteFrame? base site with
  | none => none
  | some frame => some (SiteCompilation.mk frame accepted)

/-- Every checked explicit site has an executable generated site receipt. -/
theorem compileSite_complete
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId) :
    ∃ compiled, compileSite? base site = some compiled := by
  obtain ⟨frame, generated, _⟩ :=
    compileSiteFrame?_complete base site
  refine ⟨SiteCompilation.mk frame generated, ?_⟩
  unfold compileSite?
  split
  · rename_i rejected
    rw [generated] at rejected
    contradiction
  · rename_i acceptedFrame accepted
    have same : acceptedFrame = frame :=
      Option.some.inj (accepted.symm.trans generated)
    subst acceptedFrame
    congr

namespace SiteCompilation

/--
Package a canonical site receipt from an already-proved exact root-frame
compiler equation. This does not execute `compileSite?` or search for a site.
-/
def ofFrame
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (frame : SiteFrame base site)
    (generated :
      compileRegionFrame? definitions base.val site
          (base.val.regionCount + 1) base.val.root
          (WireContext.empty base.val) =
        some frame) :
    SiteCompilation base site :=
  SiteCompilation.mk frame generated

/-- The executable site compiler has one proof-independent receipt per input. -/
theorem unique
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (left right : SiteCompilation base site) :
    left = right := by
  have sameFrame : left.frame = right.frame :=
    Option.some.inj (left.frame_compiles.symm.trans right.frame_compiles)
  cases left
  cases right
  simp_all

/--
The canonical structural stop immediately outside a compiled site's ordered
local binder block.  The certificate is tied to the retained generated frame:
after its visible hole context is identified with the site's local signatures
followed by `siteOuter`, the existing `frame.context` has exactly one
`bindMany` suffix at the hole.
-/
structure AboveScopeDecomposition
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) where
  siteOuter : ConcreteElaboration.WireContext base.val
  above : DiagramContext definitions siteOuter.sigs []
  visibleExact :
    compiled.frame.visible = siteOuter.extend site
  contextDecomposition :
    DiagramContext.StopsAboveBindMany
      ((base.val.wiresAt site).map
        (fun wire => (base.val.wires wire).sig))
      above
      (((congrArg ConcreteElaboration.WireContext.sigs visibleExact).trans
          (ConcreteElaboration.WireContext.sigs_extend siteOuter site)) ▸
        compiled.frame.context)

private theorem extend_injective
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {left right : ConcreteElaboration.WireContext base.val}
    (same : left.extend site = right.extend site) :
    left = right := by
  cases left with
  | mk leftIds =>
      cases right with
      | mk rightIds =>
          congr 1
          exact List.append_cancel_left
            (congrArg ConcreteElaboration.WireContext.ids same)

/--
Any two certificates over the same retained generated frame select the same
stopped context, including its typed site-outer boundary.
-/
structure AboveScopeDecomposition.Alignment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (left right : AboveScopeDecomposition compiled) : Type where
  siteOuterExact : left.siteOuter = right.siteOuter
  aboveExact :
    congrArg ConcreteElaboration.WireContext.sigs siteOuterExact ▸
        left.above =
      right.above

def AboveScopeDecomposition.alignment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (left right : AboveScopeDecomposition compiled) :
    Alignment left right := by
  cases left with
  | mk leftOuter leftAbove leftVisible leftDecomposition =>
      cases right with
      | mk rightOuter rightAbove rightVisible rightDecomposition =>
          have outerExact : leftOuter = rightOuter :=
            extend_injective (leftVisible.symm.trans rightVisible)
          cases outerExact
          refine ⟨rfl, ?_⟩
          have visibleProofExact :
              leftVisible = rightVisible :=
            Subsingleton.elim _ _
          cases visibleProofExact
          exact
            DiagramContext.StopsAboveBindMany.stopped_unique
              leftDecomposition rightDecomposition

theorem AboveScopeDecomposition.stopped_unique
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (left right : AboveScopeDecomposition compiled) :
    ∃ same : left.siteOuter = right.siteOuter,
      congrArg ConcreteElaboration.WireContext.sigs same ▸ left.above =
        right.above := by
  exact
    ⟨(left.alignment right).siteOuterExact,
      (left.alignment right).aboveExact⟩

private theorem compileSiblingFrame?_stopsAboveBindMany
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : ConcreteElaboration.WireContext diagram)
    (selected : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      (frame : RegionFrame definitions diagram outer),
      compileSiblingFrame? definitions diagram fuel outer selected nested
          leading children =
        some frame →
      ∀ {bound stoppedHole : List Sig}
        (stopped : DiagramContext definitions stoppedHole outer.sigs)
        (holeExact : nested.visible.sigs = bound ++ stoppedHole),
        DiagramContext.StopsAboveBindMany bound stopped
            (holeExact ▸ nested.context) →
          ∃ (frameStopped :
              DiagramContext definitions stoppedHole outer.sigs)
            (visibleExact : frame.visible = nested.visible),
            DiagramContext.StopsAboveBindMany bound frameStopped
              (((congrArg ConcreteElaboration.WireContext.sigs
                    visibleExact).trans holeExact) ▸
                frame.context) := by
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro frame compiled
      simp [compileSiblingFrame?] at compiled
  | cons child tail induction =>
      intro frame compiled bound stoppedHole stopped holeExact decomposition
      unfold compileSiblingFrame? at compiled
      by_cases same : child = selected
      · simp only [same, ↓reduceDIte] at compiled
        obtain ⟨suffix, _suffixCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp compiled
        have frameExact :
            ({ visible := nested.visible
               siteBody := nested.siteBody
               context :=
                 .surround leading (.cut nested.context) suffix } :
              RegionFrame definitions diagram outer) =
            frame :=
          Option.some.inj frameEquation
        subst frame
        refine
          ⟨.surround leading (.cut stopped) suffix, rfl, ?_⟩
        rw [cast_surround_cut_hole]
        exact .surround leading suffix (.cut decomposition)
      · simp only [same, ↓reduceDIte] at compiled
        obtain ⟨body, _bodyCompiled, recursive⟩ :=
          Option.bind_eq_some_iff.mp compiled
        exact
          induction
            (leading.append (.cons (.cut body) .nil))
            frame recursive stopped holeExact decomposition

private theorem compileRegionFrame?_aboveScopeDecomposition
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : ConcreteElaboration.WireContext diagram)
      (frame : RegionFrame definitions diagram outer),
      compileRegionFrame? definitions diagram site fuel region outer =
          some frame →
        ∃ (siteOuter : ConcreteElaboration.WireContext diagram)
          (above : DiagramContext definitions siteOuter.sigs outer.sigs)
          (visibleExact : frame.visible = siteOuter.extend site),
          DiagramContext.StopsAboveBindMany
            ((diagram.wiresAt site).map
              (fun wire => (diagram.wires wire).sig))
            above
            (((congrArg ConcreteElaboration.WireContext.sigs
                  visibleExact).trans
                (ConcreteElaboration.WireContext.sigs_extend
                  siteOuter site)) ▸
              frame.context) := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame compiled
      simp [compileRegionFrame?] at compiled
  | succ childFuel induction =>
      intro region outer frame compiled
      unfold compileRegionFrame? at compiled
      simp only [] at compiled
      split at compiled
      · rename_i atSite
        subst region
        cases bodyEquation :
            compileRegionBody? definitions diagram childFuel site outer with
        | none =>
            simp [bodyEquation] at compiled
        | some body =>
            have frameExact :
                ({ visible := outer.extend site
                   siteBody := body
                   context :=
                     bindContextFor diagram outer.ids
                       (diagram.wiresAt site) .hole } :
                  RegionFrame definitions diagram outer) =
                frame :=
              Option.some.inj (by
                simpa [bodyEquation] using compiled)
            subst frame
            refine ⟨outer, .hole, rfl, ?_⟩
            change
              DiagramContext.StopsAboveBindMany
                ((diagram.wiresAt site).map
                  (fun wire => (diagram.wires wire).sig))
                (.hole :
                  DiagramContext definitions outer.sigs outer.sigs)
                ((ConcreteElaboration.WireContext.sigs_extend
                    outer site) ▸
                  bindContextFor diagram outer.ids
                    (diagram.wiresAt site) .hole)
            exact
              bindContextFor_hole_stopsAboveBindMany
                (definitions := definitions) diagram outer site
      · cases nodesEquation :
          compileNodes? definitions diagram (outer.extend region)
            (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at compiled
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at compiled
            | some child =>
                cases nestedEquation :
                    compileRegionFrame? definitions diagram site childFuel
                      child (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation]
                      at compiled
                | some nested =>
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram childFuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at compiled
                    | some around =>
                        have frameExact :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            frame :=
                          Option.some.inj (by
                            simpa [nodesEquation, childEquation,
                              nestedEquation, aroundEquation] using compiled)
                        subst frame
                        obtain ⟨siteOuter, nestedAbove,
                            nestedVisibleExact, nestedDecomposition⟩ :=
                          induction child (outer.extend region) nested
                            nestedEquation
                        let nestedHoleExact :
                            nested.visible.sigs =
                              (diagram.wiresAt site).map
                                  (fun wire =>
                                    (diagram.wires wire).sig) ++
                                siteOuter.sigs :=
                          (congrArg
                              ConcreteElaboration.WireContext.sigs
                              nestedVisibleExact).trans
                            (ConcreteElaboration.WireContext.sigs_extend
                              siteOuter site)
                        obtain ⟨aroundAbove, aroundVisibleExact,
                            aroundDecomposition⟩ :=
                          compileSiblingFrame?_stopsAboveBindMany
                            definitions diagram childFuel
                            (outer.extend region) child nested nodes
                            (diagram.childrenOf region) around aroundEquation
                            nestedAbove nestedHoleExact
                            (by
                              unfold nestedHoleExact
                              exact nestedDecomposition)
                        refine
                          ⟨siteOuter,
                            bindContextFor diagram outer.ids
                              (diagram.wiresAt region) aroundAbove,
                            aroundVisibleExact.trans nestedVisibleExact,
                            ?_⟩
                        change
                          DiagramContext.StopsAboveBindMany
                            ((diagram.wiresAt site).map
                              (fun wire => (diagram.wires wire).sig))
                            (bindContextFor diagram outer.ids
                              (diagram.wiresAt region) aroundAbove)
                            ((((congrArg
                                  ConcreteElaboration.WireContext.sigs
                                  (aroundVisibleExact.trans
                                    nestedVisibleExact)).trans
                                (ConcreteElaboration.WireContext.sigs_extend
                                  siteOuter site))) ▸
                              bindContextFor diagram outer.ids
                                (diagram.wiresAt region) around.context)
                        rw [cast_bindContextFor_hole]
                        have holeProofExact :
                            ((congrArg
                                ConcreteElaboration.WireContext.sigs
                                (aroundVisibleExact.trans
                                  nestedVisibleExact)).trans
                              (ConcreteElaboration.WireContext.sigs_extend
                                siteOuter site)) =
                              ((congrArg
                                  ConcreteElaboration.WireContext.sigs
                                  aroundVisibleExact).trans
                                nestedHoleExact) :=
                          Subsingleton.elim _ _
                        rw [holeProofExact]
                        exact
                          aroundDecomposition.bindContextFor diagram
                            outer.ids (diagram.wiresAt region)

/--
Every retained site compilation carries a canonical structural stop outside
the selected site's ordered local binder block.
-/
theorem aboveScopeDecomposition
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    Nonempty (AboveScopeDecomposition compiled) := by
  obtain ⟨siteOuter, above, visibleExact, contextDecomposition⟩ :=
    compileRegionFrame?_aboveScopeDecomposition definitions base.val site
      (base.val.regionCount + 1) base.val.root
      (ConcreteElaboration.WireContext.empty base.val) compiled.frame
      compiled.frame_compiles
  exact
    ⟨{
      siteOuter := siteOuter
      above := above
      visibleExact := visibleExact
      contextDecomposition := contextDecomposition
    }⟩

end SiteCompilation

namespace FactorizationInternal

theorem siteCompilationCovers
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    CoversAt base.val site compiled.frame.visible := by
  obtain ⟨frame, generated, covers⟩ :=
    compileSiteFrame?_complete base site
  have same : frame = compiled.frame :=
    Option.some.inj (generated.symm.trans compiled.frame_compiles)
  simpa [same] using covers

end FactorizationInternal

namespace SiteCompilation

/--
A wire whose scope encloses the compiled site occurs in the retained visible
context. This projects only the membership fact, not the private coverage map.
-/
theorem visible_of_encloses
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (wire : base.val.WireId)
    (encloses :
      base.val.Encloses (base.val.wires wire).scope site) :
    wire ∈ compiled.frame.visible.ids :=
  FactorizationInternal.siteCompilationCovers compiled wire encloses

/-- The intrinsic root produced by the ordinary checked elaborator. -/
def checked
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    Region definitions [] :=
  elaborate base

/-- Exact executable equation for the retained site path. -/
theorem frame_generated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    compileRegionFrame? definitions base.val site
        (base.val.regionCount + 1) base.val.root
        (WireContext.empty base.val) =
      some compiled.frame :=
  compiled.frame_compiles

theorem factorAt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (scope : base.val.RegionId) (encloses : base.val.Encloses scope site) :
    ∃ scopeCompiled : SiteCompilation base scope,
      RegionFrame.GeneratedRelativeFrame site scope
        compiled.frame scopeCompiled.frame := by
  have rootScope : base.val.Encloses base.val.root scope :=
    of_decide_eq_true
      ((List.all_eq_true.mp base.property.all_regions_reach_root)
        scope (Data.Finite.mem_allFin scope))
  obtain ⟨scopeFrame, generated, decomposed⟩ :=
    compileRegionFrame?_generated_relative_at
      definitions base.val base.property
      site scope (base.val.regionCount + 1) base.val.root
      (WireContext.empty base.val) compiled.frame ⟨by
        simp [WireContext.empty], by simp [WireContext.empty]⟩
      rootScope encloses
      compiled.frame_generated
  exact ⟨SiteCompilation.mk scopeFrame generated, decomposed⟩

theorem factorAt_relative_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (scope : base.val.RegionId)
    (encloses : base.val.Encloses scope site) :
    ∃ (scopeCompiled : SiteCompilation base scope)
      (outer : WireContext base.val) (fuel : Nat)
      (relative : RegionFrame definitions base.val outer)
      (relativeVisible : relative.visible = compiled.frame.visible)
      (inner : DiagramContext definitions relative.visible.sigs
        (outer.extend scope).sigs)
      (scopeVisible : scopeCompiled.frame.visible = outer.extend scope)
      (rootInner : DiagramContext definitions compiled.frame.visible.sigs
        scopeCompiled.frame.visible.sigs),
      ContextAbove base.val outer scope ∧ compileRegionFrame? definitions base.val
        site fuel scope outer = some relative ∧
      congrArg WireContext.sigs relativeVisible ▸ relative.siteBody =
        compiled.frame.siteBody ∧
      relative.context = bindContextFor base.val outer.ids
        (base.val.wiresAt scope) inner ∧
      congrArg WireContext.sigs scopeVisible ▸ scopeCompiled.frame.siteBody =
        inner.fill relative.siteBody ∧
      scopeCompiled.frame.siteBody =
        rootInner.fill compiled.frame.siteBody ∧
      (∀ body : Region definitions compiled.frame.visible.sigs,
        compiled.frame.context.fill body =
          scopeCompiled.frame.context.fill (rootInner.fill body)) ∧
      compiled.frame.context.cutDepth =
        scopeCompiled.frame.context.cutDepth + rootInner.cutDepth := by
  obtain ⟨scopeCompiled, outer, fuel, relative, relativeVisible,
      above, generated, relativeBody, inner, relativeContext, scopeVisible,
      scopeBody, rootInner, rootBody, replacementBody, cutDepth⟩ :=
    compiled.factorAt scope encloses
  exact ⟨scopeCompiled, outer, fuel, relative, relativeVisible, inner, scopeVisible,
    rootInner, above, generated, relativeBody, relativeContext, scopeBody, rootBody,
    replacementBody, cutDepth⟩

theorem site_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    ∃ (outer : WireContext base.val) (fuel : Nat)
      (nodes children :
        ItemSeq definitions (outer.extend site).sigs)
      (visibleEquality : compiled.frame.visible = outer.extend site),
        compileNodes? definitions base.val (outer.extend site)
            (base.val.nodesAt site) =
          some nodes ∧
        compileChildrenWith? definitions base.val
            (compileRegion? definitions base.val fuel)
            (outer.extend site) (base.val.childrenOf site) =
          some children ∧
        congrArg WireContext.sigs visibleEquality ▸
            compiled.frame.siteBody =
          .mk (nodes.append children) :=
  compileRegionFrame?_site_origin definitions base.val site
    (base.val.regionCount + 1) base.val.root
    (WireContext.empty base.val) compiled.frame
    compiled.frame_generated

/-- The site-body decomposition transported back to the canonical visible
context of the retained compilation receipt. -/
theorem siteBody_decomposition
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    ∃ (fuel : Nat)
      (nodes children : ItemSeq definitions compiled.frame.visible.sigs),
      compileNodes? definitions base.val compiled.frame.visible
          (base.val.nodesAt site) = some nodes ∧
        compileChildrenWith? definitions base.val
            (compileRegion? definitions base.val fuel)
            compiled.frame.visible (base.val.childrenOf site) =
          some children ∧
        compiled.frame.siteBody = .mk (nodes.append children) := by
  rcases compiled with ⟨⟨visible, siteBody, context⟩, generated⟩
  obtain ⟨outer, fuel, nodes, children, visibleExact, nodesCompiled,
      childrenCompiled, bodyExact⟩ :=
    (SiteCompilation.mk ⟨visible, siteBody, context⟩ generated).site_origin
  cases visibleExact
  exact ⟨fuel, nodes, children, nodesCompiled, childrenCompiled, bodyExact⟩

/-- Exact executable equation for ordinary checked root elaboration. -/
theorem root_generated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    ConcreteElaboration.compileRoot? definitions base.val =
      some compiled.checked :=
  elaborateWith_compiles definitions base.val base.property

/-- Filling the generated frame with its site body reconstructs the root. -/
theorem frame_fills_checked
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    compiled.frame.context.fill compiled.frame.siteBody =
      compiled.checked := by
  have framed :
      compileRegion? definitions base.val (base.val.regionCount + 1)
          base.val.root (WireContext.empty base.val) =
        some
          (compiled.frame.context.fill compiled.frame.siteBody) :=
    compileRegionFrame?_sound definitions base.val site
      (base.val.regionCount + 1) base.val.root
      (WireContext.empty base.val) compiled.frame
      compiled.frame_generated
  have rooted := compiled.root_generated
  unfold ConcreteElaboration.compileRoot? at rooted
  exact Option.some.inj (framed.symm.trans rooted)

end SiteCompilation

end VisualProof
