import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof

namespace RemovalFactorization

open ConcreteElaboration


private def mappedIndex
    (map : α → β) (values : List α) :
    Fin values.length → Fin (values.map map).length :=
  fun index => ⟨index.val, by simpa using index.isLt⟩

private theorem indexOf?_map_injective
    [DecidableEq α] [DecidableEq β]
    (map : α → β) (injective : Function.Injective map)
    (values : List α) (value : α) :
    Data.Finite.indexOf? (values.map map) (map value) =
      (Data.Finite.indexOf? values value).map
        (mappedIndex map values) := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      by_cases same : value = head
      · subst value
        simp [Data.Finite.indexOf?, mappedIndex]
      · have mappedDifferent : map value ≠ map head :=
          fun mappedSame => same (injective mappedSame)
        simp only [List.map_cons, Data.Finite.indexOf?, same,
          mappedDifferent, ↓reduceIte, induction, Option.map_map]
        apply Option.map_congr
        intro index
        intro _
        apply Fin.ext
        rfl

private theorem denseIndex_map_injective
    [DecidableEq α] [DecidableEq β]
    (map : α → β) (injective : Function.Injective map)
    (values : List α) (value : α) (member : value ∈ values) :
    DenseList.index (values.map map) (map value)
        (List.mem_map.mpr ⟨value, member, rfl⟩) =
      mappedIndex map values (DenseList.index values value member) := by
  obtain ⟨sourceIndex, sourceEquation⟩ :=
    Data.Finite.indexOf?_complete member
  have mappedEquation :
      Data.Finite.indexOf? (values.map map) (map value) =
        some (mappedIndex map values sourceIndex) := by
    rw [indexOf?_map_injective map injective, sourceEquation]
    rfl
  unfold DenseList.index
  apply Fin.ext
  rw [Option.get_of_eq_some _ mappedEquation,
    Option.get_of_eq_some _ sourceEquation]

private theorem denseIndex_val_of_list_eq
    [DecidableEq α]
    {left right : List α} (same : left = right)
    (value : α) (leftMember : value ∈ left)
    (rightMember : value ∈ right) :
    (DenseList.index left value leftMember).val =
      (DenseList.index right value rightMember).val := by
  subst right
  rfl

/--
The context obtained while the concrete compiler follows one region path to a
removal site. `siteBody` is the actual compiler output at the hole, before the
enclosing frame is filled.
-/
structure RegionFrame
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (outer : WireContext diagram) where
  visible : WireContext diagram
  siteBody : Region definitions visible.sigs
  context : DiagramContext definitions visible.sigs outer.sigs

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
Compile ordered siblings around an already generated nested child frame.
The target child is data selected by the enclosure search, never caller input
to the public frame compiler.
-/
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
Follow the unique checked enclosure path to `site`, compiling every complete
sibling with the ordinary concrete compiler.
-/
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

/-- A root-specialized generated compiler frame. -/
abbrev RemovalFrame
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length) :=
  RegionFrame definitions diagram (WireContext.empty diagram)

/--
Generate a typed one-hole frame from only a checked complement and its concrete
site. No context or semantic conclusion is supplied by a caller.
-/
def compileRemovalFrame?
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (removed : RemovalResult occurrence) :
    Option (RemovalFrame definitions removed.complement.val) :=
  compileRegionFrame? definitions removed.complement.val removed.site
    (removed.complement.val.regionCount + 1)
    removed.complement.val.root
    (WireContext.empty removed.complement.val)

theorem compileRemovalFrame?_sound
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (removed : RemovalResult occurrence)
    (frame : RemovalFrame definitions removed.complement.val)
    (accepted : compileRemovalFrame? removed = some frame) :
    ConcreteElaboration.compileRoot? definitions removed.complement.val =
      some (frame.context.fill frame.siteBody) := by
  unfold compileRemovalFrame? at accepted
  unfold ConcreteElaboration.compileRoot?
  exact
    compileRegionFrame?_sound definitions removed.complement.val
      removed.site (removed.complement.val.regionCount + 1)
      removed.complement.val.root
      (WireContext.empty removed.complement.val) frame accepted

/--
Accepted structural output of the generated removal-frame compiler. The only
evidence fields are equations about executable compilers.
-/
structure RemovalCompilation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (removed : RemovalResult occurrence) where
  frame : RemovalFrame definitions removed.complement.val
  frame_compiles : compileRemovalFrame? removed = some frame

namespace RemovalCompilation

theorem root_compiles
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (compiled : RemovalCompilation removed) :
    ConcreteElaboration.compileRoot? definitions removed.complement.val =
      some (compiled.frame.context.fill compiled.frame.siteBody) :=
  compileRemovalFrame?_sound removed compiled.frame compiled.frame_compiles

/-- The concrete wire context visible exactly at the generated removal site. -/
def visible
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (compiled : RemovalCompilation removed) :
    WireContext removed.complement.val :=
  compiled.frame.visible

/-- The generated intrinsic one-hole frame. -/
def context
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (compiled : RemovalCompilation removed) :
    DiagramContext definitions compiled.visible.sigs [] :=
  compiled.frame.context

/-- The actual concrete compiler body occupying the generated hole. -/
def siteBody
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (compiled : RemovalCompilation removed) :
    Region definitions compiled.visible.sigs :=
  compiled.frame.siteBody

theorem elaborate_complement_eq_fill
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (compiled : RemovalCompilation removed) :
    elaborate removed.complement =
      compiled.context.fill compiled.siteBody := by
  have elaborated :=
    elaborateWith_compiles definitions removed.complement.val
      removed.complement.property
  exact Option.some.inj
    (elaborated.symm.trans (root_compiles compiled))

/--
The generated frame is the sole semantic owner of the removed complement:
any pointwise-equivalent replacement may fill its site at every cut polarity.
-/
theorem removal_frame_semantics
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (compiled : RemovalCompilation removed)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (replacement : Region definitions compiled.visible.sigs)
    (equivalent : ∀ env : Env pre compiled.visible.sigs,
      denoteRegion pre definitionEnv env compiled.siteBody ↔
        denoteRegion pre definitionEnv env replacement) :
    denoteChecked pre definitionEnv removed.complement ↔
      denoteRegion pre definitionEnv Env.empty
        (compiled.context.fill replacement) := by
  rw [elaborate_denotes_checked,
    compiled.elaborate_complement_eq_fill]
  exact context_equiv compiled.context pre definitionEnv
    compiled.siteBody replacement equivalent Env.empty

end RemovalCompilation

private def resolveVisibleWireIn?
    (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) → (wire : diagram.WireId) →
      Option (Var
        (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig)
  | [], _ => none
  | head :: tail, wire =>
      if equality : wire = head then
        equality ▸ some .here
      else
        (resolveVisibleWireIn? diagram tail wire).map .there

private theorem resolveVisibleWireIn?_complete
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId)
    (member : wire ∈ ids) :
    ∃ value, resolveVisibleWireIn? diagram ids wire = some value := by
  induction ids with
  | nil => simp at member
  | cons head tail induction =>
      by_cases same : wire = head
      · subst head
        exact ⟨.here, by simp [resolveVisibleWireIn?]⟩
      · have tailMember : wire ∈ tail := by simpa [same] using member
        obtain ⟨value, compiled⟩ := induction tailMember
        exact ⟨.there value, by
          simp [resolveVisibleWireIn?, same, compiled]⟩

/-- A typed variable records the exact concrete wire found in a visible list. -/
inductive ResolvedVisible
    (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) →
      (wire : diagram.WireId) →
      Var (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig →
      Prop
  | head (tail : List diagram.WireId) (wire : diagram.WireId) :
      ResolvedVisible diagram (wire :: tail) wire .here
  | tail
      (head : diagram.WireId)
      (resolved : ResolvedVisible diagram tail wire value) :
      ResolvedVisible diagram (head :: tail) wire (.there value)

private theorem resolveVisibleWireIn?_sound
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId)
    (value : Var
      (ids.map fun id => (diagram.wires id).sig)
      (diagram.wires wire).sig)
    (compiled :
      resolveVisibleWireIn? diagram ids wire = some value) :
    ResolvedVisible diagram ids wire value := by
  induction ids with
  | nil =>
      simp [resolveVisibleWireIn?] at compiled
  | cons head tail induction =>
      unfold resolveVisibleWireIn? at compiled
      split at compiled
      · rename_i equality
        subst head
        have valueEquality : (.here :
            Var ((wire :: tail).map fun id =>
              (diagram.wires id).sig)
              (diagram.wires wire).sig) = value :=
          Option.some.inj compiled
        subst value
        exact .head tail wire
      · cases recursive :
            resolveVisibleWireIn? diagram tail wire with
        | none =>
            simp [recursive] at compiled
        | some tailValue =>
            have valueEquality : Var.there tailValue = value :=
              Option.some.inj (by simpa [recursive] using compiled)
            subst value
            exact .tail head (induction tailValue recursive)

theorem ResolvedVisible.member
    (resolved : ResolvedVisible diagram ids wire value) :
    wire ∈ ids := by
  induction resolved with
  | head => simp
  | tail _ _ induction => exact List.mem_cons_of_mem _ induction

private abbrev visibleWireOfVar
    (diagram : ConcreteDiagram definitionCount) :
    {ids : List diagram.WireId} →
      Var (ids.map fun id => (diagram.wires id).sig) sig →
      diagram.WireId :=
  fun {ids} value =>
    ConcreteElaboration.WireContext.origin diagram ids value

theorem ResolvedVisible.origin
    (resolved : ResolvedVisible diagram ids wire value) :
    visibleWireOfVar diagram value = wire := by
  induction ids with
  | nil => nomatch resolved
  | cons head tail induction =>
      cases resolved with
      | head => rfl
      | tail _ tailResolved => exact induction tailResolved

private abbrev visibleWireOfPacked
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) :
    PackedVar (ids.map fun id => (diagram.wires id).sig) →
      diagram.WireId :=
  fun packed =>
    match packed with
    | ⟨_, value⟩ =>
        ConcreteElaboration.WireContext.origin diagram ids value

private def resolveVisiblePacked?
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId) :
    Option (PackedVar
      (ids.map fun id => (diagram.wires id).sig)) :=
  (resolveVisibleWireIn? diagram ids wire).map fun value =>
    ⟨_, value⟩

theorem ResolvedVisible.injective
    {left right : diagram.WireId}
    {leftValue : Var
      (ids.map fun id => (diagram.wires id).sig)
      (diagram.wires left).sig}
    {rightValue : Var
      (ids.map fun id => (diagram.wires id).sig)
      (diagram.wires right).sig}
    (leftResolved : ResolvedVisible diagram ids left leftValue)
    (rightResolved : ResolvedVisible diagram ids right rightValue)
    (same :
      (⟨_, leftValue⟩ :
          PackedVar (ids.map fun id => (diagram.wires id).sig)) =
        ⟨_, rightValue⟩) :
    left = right := by
  calc
    left = visibleWireOfVar diagram leftValue :=
      leftResolved.origin.symm
    _ = visibleWireOfVar diagram rightValue :=
      congrArg (visibleWireOfPacked diagram ids) same
    _ = right := rightResolved.origin

private def compileTargetPositionsFor?
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target) :
    (boundary : List source.WireId) →
      (targets : Fin boundary.length → target.WireId) →
      (signatures : ∀ position,
        (target.wires (targets position)).sig =
          (source.wires (boundary.get position)).sig) →
      Option (Vars visible.sigs
        (boundary.map fun wire => (source.wires wire).sig))
  | [], _, _ => some .nil
  | sourceWire :: tail, targets, signatures => do
      let headPosition : Fin (sourceWire :: tail).length :=
        ⟨0, by simp⟩
      let resolved ←
        resolveVisibleWireIn? target visible.ids (targets headPosition)
      let typed :
          Var visible.sigs (source.wires sourceWire).sig :=
        signatures headPosition ▸ resolved
      let rest ←
        compileTargetPositionsFor? source target visible tail
          (fun position => targets position.succ)
          (fun position => signatures position.succ)
      pure (.cons typed rest)

private theorem compileTargetPositionsFor?_complete
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target) :
    ∀ (boundary : List source.WireId)
      (targets : Fin boundary.length → target.WireId)
      (signatures : ∀ position,
        (target.wires (targets position)).sig =
          (source.wires (boundary.get position)).sig),
      (∀ position, targets position ∈ visible.ids) →
      ∃ positions,
        compileTargetPositionsFor? source target visible boundary
            targets signatures =
          some positions := by
  intro boundary
  induction boundary with
  | nil =>
      intro targets signatures _
      exact ⟨.nil, rfl⟩
  | cons sourceWire tail induction =>
      intro targets signatures members
      let head : Fin (sourceWire :: tail).length := ⟨0, by simp⟩
      obtain ⟨resolved, resolvedCompiled⟩ :=
        resolveVisibleWireIn?_complete target visible.ids
          (targets head) (members head)
      obtain ⟨rest, restCompiled⟩ :=
        induction (fun position => targets position.succ)
          (fun position => signatures position.succ)
          (fun position => members position.succ)
      simp only [compileTargetPositionsFor?]
      rw [resolvedCompiled, restCompiled]
      exact ⟨_, rfl⟩

private def targetWiresFor
    {source : ConcreteDiagram sourceDefinitions}
    {target : ConcreteDiagram targetDefinitions} :
    (boundary : List source.WireId) →
      (Fin boundary.length → target.WireId) →
      List target.WireId
  | [], _ => []
  | _ :: tail, targets =>
      targets ⟨0, by simp⟩ ::
        targetWiresFor tail (fun position => targets position.succ)

private def castVisibleVar
    (equality : sourceSig = targetSig)
    (value : Var ctx sourceSig) :
    Var ctx targetSig :=
  equality ▸ value

private theorem packed_castVisibleVar
    (value : Var ctx sourceSig)
    (equality : sourceSig = targetSig) :
    (⟨sourceSig, value⟩ : PackedVar ctx) =
      ⟨targetSig, castVisibleVar equality value⟩ := by
  cases equality
  rfl

private theorem visibleWireOfVar_cast
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId}
    (value : Var (ids.map fun id => (diagram.wires id).sig) sourceSig)
    (equality : sourceSig = targetSig) :
    visibleWireOfVar diagram (castVisibleVar equality value) =
      visibleWireOfVar diagram value := by
  cases equality
  rfl

private theorem compileTargetPositionsFor?_origins
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target) :
    ∀ boundary targets signatures positions,
      compileTargetPositionsFor? source target visible boundary
          targets signatures = some positions →
        positions.entries.map
            (visibleWireOfPacked target visible.ids) =
          targetWiresFor boundary targets := by
  intro boundary
  induction boundary with
  | nil =>
      intro targets signatures positions compiled
      simp [compileTargetPositionsFor?] at compiled
      subst positions
      rfl
  | cons sourceWire tail induction =>
      intro targets signatures positions compiled
      unfold compileTargetPositionsFor? at compiled
      let headPosition : Fin (sourceWire :: tail).length :=
        ⟨0, by simp⟩
      have headSignature :
          (target.wires (targets headPosition)).sig =
            (source.wires sourceWire).sig := by
        simpa [headPosition] using signatures headPosition
      change
        (resolveVisibleWireIn? target visible.ids
            (targets headPosition)).bind (fun resolved =>
          (compileTargetPositionsFor? source target visible tail
            (fun position => targets position.succ)
            (fun position => signatures position.succ)).bind
              (fun rest =>
                some (.cons
                  (castVisibleVar headSignature resolved) rest))) =
          some positions at compiled
      cases headEquation :
          resolveVisibleWireIn? target visible.ids
            (targets headPosition) with
      | none =>
          simp [headEquation] at compiled
      | some headValue =>
          cases tailEquation :
              compileTargetPositionsFor? source target visible tail
                (fun position => targets position.succ)
                (fun position => signatures position.succ) with
          | none =>
              simp [headEquation, tailEquation] at compiled
          | some rest =>
              let typed :
                  Var visible.sigs (source.wires sourceWire).sig :=
                castVisibleVar headSignature headValue
              have positionsEquality :
                  (.cons typed rest :
                    Vars visible.sigs
                      ((sourceWire :: tail).map fun wire =>
                        (source.wires wire).sig)) = positions :=
                Option.some.inj
                  (by simpa [headEquation, tailEquation, typed] using
                    compiled)
              subst positions
              simp only [Vars.entries, List.map_cons, targetWiresFor]
              change
                visibleWireOfVar target typed ::
                    rest.entries.map
                      (visibleWireOfPacked target visible.ids) =
                  targets headPosition ::
                    targetWiresFor tail
                      (fun position => targets position.succ)
              have headOrigin : visibleWireOfVar target typed =
                  targets headPosition := by
                change
                  visibleWireOfVar target
                      (castVisibleVar headSignature headValue) =
                    targets headPosition
                rw [visibleWireOfVar_cast]
                exact
                  (resolveVisibleWireIn?_sound target visible.ids
                    (targets headPosition) headValue headEquation).origin
              have tailOrigins :
                  rest.entries.map
                      (visibleWireOfPacked target visible.ids) =
                    targetWiresFor tail
                      (fun position => targets position.succ) :=
                induction
                  (fun position => targets position.succ)
                  (fun position => signatures position.succ)
                  rest tailEquation
              rw [headOrigin, tailOrigins]

private def targetPackedAt
    (source : ConcreteDiagram sourceDefinitions)
    (boundary : List source.WireId)
    (positions : Vars ctx
      (boundary.map fun wire => (source.wires wire).sig))
    (position : Fin boundary.length) :
    PackedVar ctx :=
  positions.entries.get
    ⟨position.val, by
      rw [ExtractedBoundaryCompiler.entries_length]
      simpa only [List.length_map] using position.isLt⟩

private theorem compileTargetPositionsFor?_resolved_at
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target) :
    ∀ boundary targets signatures positions,
      compileTargetPositionsFor? source target visible boundary
          targets signatures = some positions →
        ∀ position,
          resolveVisiblePacked? target visible.ids
              (targets position) =
            some (targetPackedAt source boundary positions position) := by
  intro boundary
  induction boundary with
  | nil =>
      intro targets signatures positions compiled position
      exact Fin.elim0 position
  | cons sourceWire tail induction =>
      intro targets signatures positions compiled
      unfold compileTargetPositionsFor? at compiled
      let headPosition : Fin (sourceWire :: tail).length :=
        ⟨0, by simp⟩
      have headSignature :
          (target.wires (targets headPosition)).sig =
            (source.wires sourceWire).sig := by
        simpa [headPosition] using signatures headPosition
      change
        (resolveVisibleWireIn? target visible.ids
            (targets headPosition)).bind (fun resolved =>
          (compileTargetPositionsFor? source target visible tail
            (fun position => targets position.succ)
            (fun position => signatures position.succ)).bind
              (fun rest =>
                some (.cons
                  (castVisibleVar headSignature resolved) rest))) =
          some positions at compiled
      cases headEquation :
          resolveVisibleWireIn? target visible.ids
            (targets headPosition) with
      | none =>
          simp [headEquation] at compiled
      | some headValue =>
          cases tailEquation :
              compileTargetPositionsFor? source target visible tail
                (fun position => targets position.succ)
                (fun position => signatures position.succ) with
          | none =>
              simp [headEquation, tailEquation] at compiled
          | some rest =>
              let typed :
                  Var visible.sigs (source.wires sourceWire).sig :=
                castVisibleVar headSignature headValue
              have positionsEquality :
                  (.cons typed rest :
                    Vars visible.sigs
                      ((sourceWire :: tail).map fun wire =>
                        (source.wires wire).sig)) = positions :=
                Option.some.inj
                  (by simpa [headEquation, tailEquation, typed] using
                    compiled)
              subst positions
              intro position
              refine Fin.cases ?_ (fun tailPosition => ?_) position
              · change
                  resolveVisiblePacked? target visible.ids
                      (targets headPosition) =
                    some
                      (targetPackedAt source (sourceWire :: tail)
                        (.cons typed rest) headPosition)
                unfold resolveVisiblePacked?
                rw [headEquation]
                simp only [Option.map_some]
                congr 1
                change
                  (⟨_, headValue⟩ : PackedVar visible.sigs) =
                    targetPackedAt source (sourceWire :: tail)
                      (.cons typed rest) ⟨0, by simp⟩
                simp only [targetPackedAt, Vars.entries,
                  List.get_eq_getElem, List.getElem_cons_zero]
                exact packed_castVisibleVar headValue headSignature
              · simpa only [targetPackedAt, Vars.entries,
                  List.get_eq_getElem, List.getElem_cons_succ] using
                  induction
                    (fun position => targets position.succ)
                    (fun position => signatures position.succ)
                    rest tailEquation tailPosition

private abbrev PairedTarget
    (sources : Vars source args)
    (targets : Vars target args)
    (fiber : Var source sig) :=
  { targetVar : Var target sig //
      Vars.Paired sources targets fiber targetVar }

private def firstPairedTarget? :
    {args : List Sig} →
      (sources : Vars source args) →
      (targets : Vars target args) →
      (fiber : Var source sig) →
      Option (PairedTarget sources targets fiber)
  | [], .nil, .nil, _ => none
  | _ :: _, .cons sourceHead sourceTail,
      .cons targetHead targetTail, fiber =>
      if equality :
          (⟨_, sourceHead⟩ : PackedVar source) =
            (⟨_, fiber⟩ : PackedVar source) then
        match equality with
        | rfl => some ⟨targetHead, .head⟩
      else
        match firstPairedTarget? sourceTail targetTail fiber with
        | none => none
        | some paired => some ⟨paired.val, .tail paired.property⟩

private theorem firstPairedTarget?_exists
    (sources : Vars source args)
    (targets : Vars target args)
    (fiber : Var source sig)
    (contains : sources.Contains fiber) :
    ∃ paired, firstPairedTarget? sources targets fiber = some paired := by
  induction sources with
  | nil =>
      simp [Vars.Contains, Vars.entries] at contains
  | cons sourceHead sourceTail induction =>
      cases targets with
      | cons targetHead targetTail =>
          simp only [Vars.Contains, Vars.entries, List.mem_cons] at contains
          by_cases equality :
              (⟨_, sourceHead⟩ : PackedVar source) =
                (⟨_, fiber⟩ : PackedVar source)
          · cases equality
            exact ⟨⟨targetHead, .head⟩, by
              simp [firstPairedTarget?]⟩
          · have tailContains : sourceTail.Contains fiber := by
              rcases contains with headEquality | tailMember
              · exact (equality headEquality.symm).elim
              · exact tailMember
            obtain ⟨paired, compiled⟩ :=
              induction targetTail tailContains
            exact
              ⟨⟨paired.val, .tail paired.property⟩, by
                simp [firstPairedTarget?, equality, compiled]⟩

private def firstPaired
    (sources : Vars source args)
    (targets : Vars target args)
    (fiber : Var source sig)
    (contains : sources.Contains fiber) :
    PairedTarget sources targets fiber :=
  (firstPairedTarget? sources targets fiber).get (by
    obtain ⟨paired, compiled⟩ :=
      firstPairedTarget?_exists sources targets fiber contains
    simp [compiled])

private def pairedFirstIndex
    (sources : Vars source args)
    (targets : Vars target args)
    (fiber : Var source sig)
    (contains : sources.Contains fiber) :
    Fin targets.entries.length :=
  let sourceIndex :=
    DenseList.index sources.entries
      (⟨sig, fiber⟩ : PackedVar source) contains
  ⟨sourceIndex.val, by
    simpa only [ExtractedBoundaryCompiler.entries_length] using
      sourceIndex.isLt⟩

private theorem firstPairedTarget?_at_first_index
    {args : List Sig}
    (sources : Vars source args)
    (targets : Vars target args)
    (fiber : Var source sig)
    (contains : sources.Contains fiber)
    (paired : PairedTarget sources targets fiber)
    (compiled :
      firstPairedTarget? sources targets fiber = some paired) :
    targets.entries.get
        (pairedFirstIndex sources targets fiber contains) =
      (⟨sig, paired.val⟩ : PackedVar target) := by
  induction sources with
  | nil =>
      simp [Vars.Contains, Vars.entries] at contains
  | cons sourceHead sourceTail induction =>
      cases targets with
      | cons targetHead targetTail =>
          by_cases equality :
              (⟨_, sourceHead⟩ : PackedVar source) =
                (⟨sig, fiber⟩ : PackedVar source)
          · cases equality
            have pairedEquality :
                (⟨targetHead, .head⟩ :
                  PairedTarget (.cons fiber sourceTail)
                    (.cons targetHead targetTail) fiber) = paired := by
              exact Option.some.inj (by
                simpa [firstPairedTarget?] using compiled)
            cases pairedEquality
            have indexEquality :
                pairedFirstIndex (.cons fiber sourceTail)
                    (.cons targetHead targetTail) fiber contains =
                  ⟨0, by simp [Vars.entries]⟩ := by
              apply Fin.ext
              unfold pairedFirstIndex DenseList.index
              simp [Vars.entries, Data.Finite.indexOf?]
            rw [indexEquality]
            rfl
          · have different :
                (⟨sig, fiber⟩ : PackedVar source) ≠
                  (⟨_, sourceHead⟩ : PackedVar source) :=
              fun same => equality same.symm
            have tailContains : sourceTail.Contains fiber := by
              simp only [Vars.Contains, Vars.entries, List.mem_cons] at contains
              rcases contains with head | tail
              · exact (different head).elim
              · exact tail
            cases tailResult :
                firstPairedTarget? sourceTail targetTail fiber with
            | none =>
                simp [firstPairedTarget?, equality, tailResult] at compiled
            | some tailPaired =>
                have pairedEquality :
                    (⟨tailPaired.val, .tail tailPaired.property⟩ :
                      PairedTarget (.cons sourceHead sourceTail)
                        (.cons targetHead targetTail) fiber) = paired := by
                  exact Option.some.inj (by
                    simpa [firstPairedTarget?, equality, tailResult] using
                      compiled)
                cases pairedEquality
                have tailAt :=
                  induction targetTail tailContains tailPaired tailResult
                have indexEquality :
                    pairedFirstIndex (.cons sourceHead sourceTail)
                        (.cons targetHead targetTail) fiber contains =
                      Fin.succ
                        (pairedFirstIndex sourceTail targetTail fiber
                          tailContains) := by
                  apply Fin.ext
                  unfold pairedFirstIndex DenseList.index
                  simp [Vars.entries, Data.Finite.indexOf?, different]
                rw [indexEquality]
                simpa [Vars.entries] using tailAt

private theorem firstPaired_at_first_index
    (sources : Vars source args)
    (targets : Vars target args)
    (fiber : Var source sig)
    (contains : sources.Contains fiber) :
    targets.entries.get
        (pairedFirstIndex sources targets fiber contains) =
      (⟨sig, (firstPaired sources targets fiber contains).val⟩ :
        PackedVar target) := by
  unfold firstPaired
  obtain ⟨paired, compiled⟩ :=
    firstPairedTarget?_exists sources targets fiber contains
  have available :
      (firstPairedTarget? sources targets fiber).isSome = true := by
    simp [compiled]
  rw [Option.get_of_eq_some available compiled]
  exact firstPairedTarget?_at_first_index sources targets fiber contains
    paired compiled

theorem complement_nodesAt_site_eq_nil
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    (Removal.diagram occurrence).nodesAt (Removal.site occurrence) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node member
  have atSite :
      ((Removal.diagram occurrence).nodes node).region =
        Removal.site occurrence :=
    eq_of_beq (List.mem_filter.mp member).2
  have retained :
      Removal.sourceNode occurrence node ∉
        occurrence.selection.nodes :=
    of_decide_eq_true
      (List.mem_filter.mp
        (List.get_mem (Removal.nodes occurrence) node)).2
  apply retained
  apply (occurrence.selection.nodes_exact _).mpr
  have renamed := congrArg CNode.region
    (Removal.diagramNode_rename occurrence node)
  have mappedRegion :
      (mapNode (Removal.sourceRegion occurrence)
          ((Removal.diagram occurrence).nodes node)).region =
        Removal.sourceRegion occurrence
          ((Removal.diagram occurrence).nodes node).region := by
    cases (Removal.diagram occurrence).nodes node <;> rfl
  have regionEquality :
      (host.val.nodes (Removal.sourceNode occurrence node)).region =
        occurrence.selection.root := by
    rw [mappedRegion, atSite] at renamed
    simpa [Removal.site,
      Removal.sourceRegion_regionIndex] using renamed
  rw [regionEquality]
  exact occurrence.selection.root_mem

theorem complement_wiresAt_site_eq_nil
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    (Removal.diagram occurrence).wiresAt (Removal.site occurrence) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro wire member
  have atSite :
      ((Removal.diagram occurrence).wires wire).scope =
        Removal.site occurrence :=
    eq_of_beq (List.mem_filter.mp member).2
  have external :
      (host.val.wires (Removal.sourceWire occurrence wire)).scope ∉
        occurrence.selection.regions :=
    of_decide_eq_true
      (List.mem_filter.mp
        (List.get_mem (Removal.wires occurrence) wire)).2
  apply external
  have renamed :=
    Removal.diagramWire_scope_rename occurrence wire
  have scopeEquality :
      (host.val.wires (Removal.sourceWire occurrence wire)).scope =
        occurrence.selection.root := by
    simpa [atSite, Removal.site,
      Removal.sourceRegion_regionIndex] using renamed
  rw [scopeEquality]
  exact occurrence.selection.root_mem

theorem complement_childrenOf_site_eq_nil
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    (Removal.diagram occurrence).childrenOf (Removal.site occurrence) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro child member
  have childData :=
    ConcreteElaboration.mem_childrenOf
      (Removal.diagram occurrence) (Removal.site occurrence) child member
  have renamed :=
    Removal.diagramRegion_rename occurrence child
  cases sourceData :
      host.val.regions (Removal.sourceRegion occurrence child) with
  | sheet =>
      simp [sourceData, childData, mapRegion] at renamed
  | cut parent =>
      have parentEquality :
          parent = occurrence.selection.root := by
        simpa [sourceData, childData, mapRegion, Removal.site,
          Removal.sourceRegion_regionIndex] using renamed
      have childMember :
          Removal.sourceRegion occurrence child ∈
            host.val.childrenOf occurrence.selection.root := by
        simp [ConcreteDiagram.childrenOf, ConcreteDiagram.regionsList,
          Data.Finite.mem_allFin, sourceData, parentEquality]
      have selected :=
        occurrence.selection.descendants_closed
          occurrence.selection.root occurrence.selection.root_mem
          (Removal.sourceRegion occurrence child) childMember
      have retainedCase :
          Removal.sourceRegion occurrence child ∉
              occurrence.selection.regions ∨
            Removal.sourceRegion occurrence child =
              occurrence.selection.root :=
        of_decide_eq_true
          (List.mem_filter.mp
            (List.get_mem (Removal.regions occurrence) child)).2
      rcases retainedCase with outside | root
      · exact outside selected
      · have parentExternal :=
          occurrence.selection.root_parent_external parent
            (by simpa [root] using sourceData)
        rw [parentEquality] at parentExternal
        exact parentExternal occurrence.selection.root_mem


private theorem compileSiblingFrame?_siteBody_eq_blank
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer)
    (nestedBlank : nested.siteBody = blank) :
    ∀ leading children frame,
      compileSiblingFrame? definitions diagram fuel outer target nested
          leading children = some frame →
        frame.siteBody = blank := by
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
                     DiagramContext.surround leading
                       (.cut nested.context) suffix } :
                  RegionFrame definitions diagram outer) = frame :=
              Option.some.inj
                (by simpa [suffixEquation] using accepted)
            subst frame
            exact nestedBlank
      · cases bodyEquation :
            compileRegion? definitions diagram fuel child outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            exact induction
              (leading.append (.cons (.cut body) .nil))
              frame (by simpa [bodyEquation] using accepted)

private theorem compileRegionFrame?_siteBody_eq_blank
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId)
    (nodesEmpty : diagram.nodesAt site = [])
    (childrenEmpty : diagram.childrenOf site = []) :
    ∀ fuel region outer frame,
      compileRegionFrame? definitions diagram site fuel region outer =
          some frame →
        frame.siteBody = blank := by
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
        have bodyCompiled :
            compileRegionBody? definitions diagram fuel site outer =
              some blank := by
          simp [compileRegionBody?, nodesEmpty, childrenEmpty,
            ConcreteElaboration.compileNodes?,
            ConcreteElaboration.compileChildrenWith?, blank]
        have frameEquality :
            ({ visible := outer.extend site
               siteBody := blank
               context :=
                 bindContextFor diagram outer.ids
                   (diagram.wiresAt site) .hole } :
              RegionFrame definitions diagram outer) = frame :=
          Option.some.inj
            (by simpa [bodyCompiled] using accepted)
        subst frame
        rfl
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
                          Option.some.inj
                            (by simpa [nodesEquation, childEquation,
                                nestedEquation, aroundEquation] using
                              accepted)
                        subst frame
                        have nestedBlank :=
                          induction child (outer.extend region) nested
                            nestedEquation
                        exact
                          compileSiblingFrame?_siteBody_eq_blank definitions
                            diagram fuel (outer.extend region) child nested
                            nestedBlank nodes (diagram.childrenOf region)
                            around aroundEquation

theorem RemovalCompilation.siteBody_eq_blank
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (compiled : RemovalCompilation removed) :
    compiled.siteBody = blank := by
  exact
    compileRegionFrame?_siteBody_eq_blank definitions
      removed.complement.val removed.site
      (complement_nodesAt_site_eq_nil occurrence)
      (complement_childrenOf_site_eq_nil occurrence)
      (removed.complement.val.regionCount + 1)
      removed.complement.val.root
      (WireContext.empty removed.complement.val)
      compiled.frame compiled.frame_compiles

/--
Follow an ancestor path exactly as the generated removal-frame compiler does,
but compile the whole target region as the replacement body. Consequently all
target-region local binders belong to the body, while only genuinely enclosing
wires remain visible at the hole.
-/
def compileWholeSiteFrame?
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    (fuel : Nat) →
      (region : diagram.RegionId) →
      (outer : WireContext diagram) →
      Option (RegionFrame definitions diagram outer)
  | 0, _, _ => none
  | fuel + 1, region, outer =>
      if atSite : region = site then do
        let siteBody ←
          compileRegion? definitions diagram (fuel + 1) region outer
        pure
          { visible := outer
            siteBody := siteBody
            context := .hole }
      else do
        let extended := outer.extend region
        let nodes ← compileNodes? definitions diagram extended
          (diagram.nodesAt region)
        let child ← (diagram.childrenOf region).find?
          (fun candidate => decide (diagram.Encloses candidate site))
        let nested ← compileWholeSiteFrame? definitions diagram site fuel
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

theorem compileWholeSiteFrame?_sound
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId)
    (fuel : Nat)
    (region : diagram.RegionId)
    (outer : WireContext diagram)
    (frame : RegionFrame definitions diagram outer)
    (accepted :
      compileWholeSiteFrame? definitions diagram site fuel region outer =
        some frame) :
    compileRegion? definitions diagram fuel region outer =
      some (frame.context.fill frame.siteBody) := by
  induction fuel generalizing region outer frame with
  | zero =>
      simp [compileWholeSiteFrame?] at accepted
  | succ fuel induction =>
      unfold compileWholeSiteFrame? at accepted
      split at accepted
      · rename_i atSite
        subst region
        cases bodyEquation :
            compileRegion? definitions diagram (fuel + 1) site outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have frameEquality :
                ({ visible := outer
                   siteBody := body
                   context := .hole } :
                  RegionFrame definitions diagram outer) = frame :=
              Option.some.inj (by simpa [bodyEquation] using accepted)
            subst frame
            simpa [DiagramContext.fill] using bodyEquation
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
                    compileWholeSiteFrame? definitions diagram site fuel child
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

private theorem compileSiblingFrame?_preserves_site_compilation
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : WireContext diagram)
    (target site : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer)
    (siteFuel : Nat)
    (nestedSite :
      compileRegion? definitions diagram siteFuel site nested.visible =
        some nested.siteBody) :
    ∀ leading children frame,
      compileSiblingFrame? definitions diagram fuel outer target nested
          leading children = some frame →
        compileRegion? definitions diagram siteFuel site frame.visible =
          some frame.siteBody := by
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
                     DiagramContext.surround leading
                       (.cut nested.context) suffix } :
                  RegionFrame definitions diagram outer) = frame :=
              Option.some.inj
                (by simpa [suffixEquation] using accepted)
            subst frame
            exact nestedSite
      · cases bodyEquation :
            compileRegion? definitions diagram fuel child outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            exact induction
              (leading.append (.cons (.cut body) .nil))
              frame (by simpa [bodyEquation] using accepted)

/--
An accepted whole-site frame exposes the ordinary compiler equation for its
actual concrete replacement body; no such equation is supplied by a caller.
-/
theorem compileWholeSiteFrame?_site_compiles
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ fuel region outer frame,
      compileWholeSiteFrame? definitions diagram site fuel region outer =
          some frame →
        ∃ siteFuel,
          compileRegion? definitions diagram siteFuel site frame.visible =
            some frame.siteBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame accepted
      simp [compileWholeSiteFrame?] at accepted
  | succ fuel induction =>
      intro region outer frame accepted
      unfold compileWholeSiteFrame? at accepted
      split at accepted
      · rename_i atSite
        subst region
        cases bodyEquation :
            compileRegion? definitions diagram (fuel + 1) site outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have frameEquality :
                ({ visible := outer
                   siteBody := body
                   context := .hole } :
                  RegionFrame definitions diagram outer) = frame :=
              Option.some.inj
                (by simpa [bodyEquation] using accepted)
            subst frame
            exact ⟨fuel + 1, bodyEquation⟩
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
                    compileWholeSiteFrame? definitions diagram site fuel child
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
                        obtain ⟨siteFuel, nestedSite⟩ :=
                          induction child (outer.extend region) nested
                            nestedEquation
                        exact
                          ⟨siteFuel,
                            compileSiblingFrame?_preserves_site_compilation
                              definitions diagram fuel
                              (outer.extend region) child site nested
                              siteFuel nestedSite nodes
                              (diagram.childrenOf region) around
                              aroundEquation⟩

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
              · exact
                  induction tailItems tailEquation tailMember

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

private def CoversStrictlyAbove
    (diagram : ConcreteDiagram definitionCount)
    (site : diagram.RegionId)
    (context : WireContext diagram) : Prop :=
  ∀ wire,
    diagram.Encloses (diagram.wires wire).scope site →
    (diagram.wires wire).scope ≠ site →
    wire ∈ context.ids

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

private theorem compileWholeSiteFrame?_complete_of_region
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
        compileWholeSiteFrame? definitions diagram site fuel region outer =
          some frame ∧
        CoversStrictlyAbove diagram site frame.visible := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer body _ _ compiled
      simp [compileRegion?] at compiled
  | succ fuel induction =>
      intro region outer body encloses covers compiled
      by_cases atSite : region = site
      · subst region
        let frame : RegionFrame definitions diagram outer :=
          { visible := outer
            siteBody := body
            context := .hole }
        refine ⟨frame, ?_, covers⟩
        change
          compileWholeSiteFrame? definitions diagram site (fuel + 1)
              site outer =
            some frame
        simp [compileWholeSiteFrame?, compiled, frame]
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
                            exact eq_of_beq (by simpa [data] using filtered)
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
                      induction child extended childBody childEncloses childCovers
                        childCompiled
                    have nestedRegionCompiled :=
                      compileWholeSiteFrame?_sound definitions diagram site
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
                            (diagram.wiresAt region) around.context }
                    unfold extended at nodesEquation nestedCompiled aroundCompiled
                    refine ⟨frame, by
                      simp [compileWholeSiteFrame?, atSite,
                        nodesEquation, childEquation, nestedCompiled,
                        aroundCompiled, frame], ?_⟩
                    simpa [frame, aroundVisible] using nestedCovers

/-- Root-specialized frame generated directly from the concrete splice candidate. -/
abbrev CandidateFrame
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :=
  RegionFrame definitions attachment.diagram
    (WireContext.empty attachment.diagram)

/--
Generate the actual candidate carrier frame at the identified host splice site.
-/
private def compileCandidateFrame?
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Option (CandidateFrame attachment) :=
  compileWholeSiteFrame? definitions attachment.diagram
    (attachment.hostRegion removed.site)
    (attachment.diagram.regionCount + 1)
    attachment.diagram.root
    (WireContext.empty attachment.diagram)

private theorem compileCandidateFrame?_sound
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (frame : CandidateFrame attachment)
    (accepted : compileCandidateFrame? attachment = some frame) :
    ConcreteElaboration.compileRoot? definitions attachment.diagram =
      some (frame.context.fill frame.siteBody) := by
  unfold compileCandidateFrame? at accepted
  unfold ConcreteElaboration.compileRoot?
  exact
    compileWholeSiteFrame?_sound definitions attachment.diagram
      (attachment.hostRegion removed.site)
      (attachment.diagram.regionCount + 1)
      attachment.diagram.root
      (WireContext.empty attachment.diagram) frame accepted

/-- Resolve ordered concrete targets in the ancestor-visible candidate context. -/
private def compileCandidateAttachmentPositions?
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (visible : WireContext attachment.diagram) :
    Option (Vars visible.sigs (checkedBoundarySigs fragment)) :=
  compileTargetPositionsFor? fragment.val.diagram attachment.diagram
    visible fragment.val.boundary
      (fun position =>
        attachment.hostWire (attachment.target position))
      (fun position => by
        simpa using attachment.signature position)

/-- All generated structural data needed to factor one concrete splice. -/
structure SpliceFactor
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) where
  frame : CandidateFrame attachment
  positions : Vars frame.visible.sigs (checkedBoundarySigs fragment)

/--
Execute candidate-frame generation and ordered target resolution as one
proof-independent compiler.
-/
private def compileSpliceFactor?
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) :
    Option (SpliceFactor attachment) := do
  let frame ← compileCandidateFrame? attachment
  let positions ←
    compileCandidateAttachmentPositions? attachment frame.visible
  pure ⟨frame, positions⟩

structure SpliceCompilation
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment) where
  private mk ::
  factor : SpliceFactor attachment
  private factor_compiles :
    compileSpliceFactor? attachment = some factor

private theorem hostRegion_climb
    (attachment : ConcreteSpliceAttachment removed fragment) :
    ∀ steps region,
      attachment.diagram.climb steps
          (attachment.hostRegion region) =
        (removed.complement.val.climb steps region).map
          attachment.hostRegion := by
  intro steps
  induction steps with
  | zero => intro region; rfl
  | succ steps induction =>
      intro region
      cases data : removed.complement.val.regions region with
      | sheet =>
          simp [ConcreteDiagram.climb,
            ConcreteSpliceAttachment.diagram_region_hostRegion,
            data, mapRegion]
          rfl
      | cut parent =>
          simp [ConcreteDiagram.climb,
            ConcreteSpliceAttachment.diagram_region_hostRegion,
            data, mapRegion, induction parent]

private theorem hostRegion_encloses
    (attachment : ConcreteSpliceAttachment removed fragment)
    {ancestor descendant : removed.complement.val.RegionId}
    (encloses :
      removed.complement.val.Encloses ancestor descendant) :
    attachment.diagram.Encloses
      (attachment.hostRegion ancestor)
      (attachment.hostRegion descendant) := by
  obtain ⟨⟨steps, bound⟩, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      removed.complement.val ancestor descendant).mp encloses
  apply
    (ConcreteElaboration.encloses_iff_exists
      attachment.diagram _ _).mpr
  refine ⟨⟨steps, by
    simp only [ConcreteSpliceAttachment.diagram,
      ConcreteSpliceAttachment.regionCount]
    omega⟩, ?_⟩
  rw [hostRegion_climb attachment, climbed]
  rfl

private theorem empty_covers_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    CoversStrictlyAbove diagram diagram.root
      (WireContext.empty diagram) := by
  intro wire encloses strict
  obtain ⟨⟨steps, bound⟩, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram
      (diagram.wires wire).scope diagram.root).mp encloses
  cases steps with
  | zero => exact (strict (by simpa using climbed.symm)).elim
  | succ steps =>
      rw [ConcreteDiagram.climb, wellFormed.root_is_sheet] at climbed
      simp at climbed

private theorem target_scope_ne_site
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment removed fragment)
    (position : Fin fragment.val.boundary.length) :
    (removed.complement.val.wires
        (attachment.target position)).scope ≠ removed.site := by
  intro same
  have member :
      attachment.target position ∈
        removed.complement.val.wiresAt removed.site := by
    simp [ConcreteDiagram.wiresAt, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, same]
  change
    attachment.target position ∈
      (Removal.diagram occurrence).wiresAt
        (Removal.site occurrence) at member
  rw [complement_wiresAt_site_eq_nil occurrence] at member
  cases member

/--
Every checked splice result makes executable factor compilation succeed;
callers never supply a frame or a target-membership proof.
-/
private theorem compileSpliceFactor?_complete
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (result : ConcreteSpliceResult attachment)
    (spliceAccepted : splice attachment = .ok result) :
    ∃ factor, compileSpliceFactor? attachment = some factor := by
  have wellFormed :=
    splice_success_wellFormed spliceAccepted
  have rootEncloses :
      attachment.diagram.Encloses attachment.diagram.root
        (attachment.hostRegion removed.site) := by
    have checked :=
      (List.all_eq_true.mp wellFormed.all_regions_reach_root)
        (attachment.hostRegion removed.site)
        (Data.Finite.mem_allFin _)
    exact of_decide_eq_true checked
  have rootCompiled :=
    elaborateWith_compiles definitions attachment.diagram
      wellFormed
  unfold ConcreteElaboration.compileRoot? at rootCompiled
  obtain ⟨frame, frameCompiled, covers⟩ :=
    compileWholeSiteFrame?_complete_of_region definitions
      attachment.diagram (attachment.hostRegion removed.site)
      (attachment.diagram.regionCount + 1) attachment.diagram.root
      (WireContext.empty attachment.diagram)
      (elaborateWith definitions attachment.diagram wellFormed)
      rootEncloses
      (empty_covers_root definitions attachment.diagram wellFormed)
      rootCompiled
  have targetMembers :
      ∀ position,
        attachment.hostWire (attachment.target position) ∈
          frame.visible.ids := by
    intro position
    apply covers
    · simpa using
        hostRegion_encloses attachment (attachment.scope position)
    · intro same
      apply target_scope_ne_site attachment position
      apply Fin.ext
      simpa [ConcreteSpliceAttachment.hostRegion] using
        congrArg Fin.val same
  obtain ⟨positions, positionsCompiled⟩ :=
    compileTargetPositionsFor?_complete fragment.val.diagram
      attachment.diagram frame.visible fragment.val.boundary
      (fun position =>
        attachment.hostWire (attachment.target position))
      (fun position => by simpa using attachment.signature position)
      targetMembers
  change compileCandidateFrame? attachment = some frame at frameCompiled
  change
    compileCandidateAttachmentPositions? attachment frame.visible =
      some positions at positionsCompiled
  let factor : SpliceFactor attachment := ⟨frame, positions⟩
  refine ⟨factor, ?_⟩
  unfold compileSpliceFactor?
  rw [frameCompiled]
  change
    (compileCandidateAttachmentPositions? attachment
      frame.visible).bind _ = some factor
  rw [positionsCompiled]
  rfl

/--
The proof-only factorization witness for a generated candidate exists only when
the exact public splice pipeline accepted that candidate.
-/
theorem spliceCompilation_complete
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (result : ConcreteSpliceResult attachment)
    (spliceAccepted : splice attachment = .ok result) :
    Nonempty (SpliceCompilation attachment) := by
  obtain ⟨factor, factorCompiled⟩ :=
    compileSpliceFactor?_complete result spliceAccepted
  exact ⟨SpliceCompilation.mk factor factorCompiled⟩

namespace SpliceCompilation

theorem frame_compiles
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment) :
    compileCandidateFrame? attachment = some compiled.factor.frame := by
  rcases compiled with ⟨factor, accepted⟩
  dsimp
  unfold compileSpliceFactor? at accepted
  cases frameEquation : compileCandidateFrame? attachment with
  | none =>
      simp [frameEquation] at accepted
  | some frame =>
      cases positionsEquation :
          compileCandidateAttachmentPositions? attachment
            frame.visible with
      | none =>
          simp [frameEquation, positionsEquation]
            at accepted
      | some positions =>
          have factorEquality :
              (⟨frame, positions⟩ : SpliceFactor attachment) = factor :=
            Option.some.inj
              (by simpa [frameEquation, positionsEquation] using
                accepted)
          cases factorEquality
          rfl

theorem positions_compiles
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment) :
    compileCandidateAttachmentPositions? attachment
        compiled.factor.frame.visible =
      some compiled.factor.positions := by
  rcases compiled with ⟨factor, accepted⟩
  dsimp
  unfold compileSpliceFactor? at accepted
  cases frameEquation : compileCandidateFrame? attachment with
  | none =>
      simp [frameEquation] at accepted
  | some frame =>
      cases positionsEquation :
          compileCandidateAttachmentPositions? attachment
            frame.visible with
      | none =>
          simp [frameEquation, positionsEquation]
            at accepted
      | some positions =>
          have factorEquality :
              (⟨frame, positions⟩ : SpliceFactor attachment) = factor :=
            Option.some.inj
              (by simpa [frameEquation, positionsEquation] using
                accepted)
          cases factorEquality
          exact positionsEquation

/-- The intrinsic candidate attachment occurrence at one generated position. -/
def positionPackedAt
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment)
    (position : Fin fragment.val.boundary.length) :
    PackedVar compiled.factor.frame.visible.sigs :=
  targetPackedAt fragment.val.diagram fragment.val.boundary
    compiled.factor.positions position

private theorem positionPackedAt_resolved
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment)
    (position : Fin fragment.val.boundary.length) :
    resolveVisiblePacked? attachment.diagram
        compiled.factor.frame.visible.ids
        (attachment.hostWire (attachment.target position)) =
      some (compiled.positionPackedAt position) := by
  unfold positionPackedAt
  apply compileTargetPositionsFor?_resolved_at
    fragment.val.diagram attachment.diagram
      compiled.factor.frame.visible
      fragment.val.boundary
      (fun position =>
        attachment.hostWire (attachment.target position))
      (fun position => by
        simpa using attachment.signature position)
      compiled.factor.positions
  exact compiled.positions_compiles

theorem positionPackedAt_origin
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment)
    (position : Fin fragment.val.boundary.length) :
    (match compiled.positionPackedAt position with
      | ⟨_, value⟩ =>
          ConcreteElaboration.WireContext.origin attachment.diagram
            compiled.factor.frame.visible.ids value) =
      attachment.hostWire (attachment.target position) := by
  have resolved := compiled.positionPackedAt_resolved position
  unfold resolveVisiblePacked? at resolved
  cases equation :
      resolveVisibleWireIn? attachment.diagram
        compiled.factor.frame.visible.ids
        (attachment.hostWire (attachment.target position)) with
  | none =>
      simp [equation] at resolved
  | some value =>
      have someEquality :
          some
              (⟨_, value⟩ :
                PackedVar compiled.factor.frame.visible.sigs) =
            some (compiled.positionPackedAt position) := by
        rw [equation] at resolved
        change
          some
              (⟨_, value⟩ :
                PackedVar compiled.factor.frame.visible.sigs) =
            some (compiled.positionPackedAt position) at resolved
        exact resolved
      have packedEquality :
          (⟨_, value⟩ :
            PackedVar compiled.factor.frame.visible.sigs) =
            compiled.positionPackedAt position :=
        Option.some.inj someEquality
      rw [← packedEquality]
      exact
        (resolveVisibleWireIn?_sound attachment.diagram
          compiled.factor.frame.visible.ids
          (attachment.hostWire (attachment.target position))
          value equation).origin

/--
The compiled candidate variables reflect exactly equality of the concrete
attachment targets, including the signature casts performed by the resolver.
-/
theorem positionPackedAt_eq_iff
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment)
    (left right : Fin fragment.val.boundary.length) :
    compiled.positionPackedAt left =
        compiled.positionPackedAt right ↔
      attachment.target left = attachment.target right := by
  constructor
  · intro same
    apply attachment.hostWire_injective
    have mapped := congrArg
      (fun packed =>
        match packed with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin attachment.diagram
              compiled.factor.frame.visible.ids value)
      same
    simpa [compiled.positionPackedAt_origin left,
      compiled.positionPackedAt_origin right] using mapped
  · intro same
    have leftResolved := compiled.positionPackedAt_resolved left
    have rightResolved := compiled.positionPackedAt_resolved right
    rw [same] at leftResolved
    exact Option.some.inj (leftResolved.symm.trans rightResolved)

theorem root_compiles
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment) :
    ConcreteElaboration.compileRoot? definitions attachment.diagram =
      some
        (compiled.factor.frame.context.fill
          compiled.factor.frame.siteBody) :=
  compileCandidateFrame?_sound attachment compiled.factor.frame
    compiled.frame_compiles

theorem site_compiles
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment removed fragment}
    (compiled : SpliceCompilation attachment) :
    ∃ siteFuel,
      compileRegion? definitions attachment.diagram siteFuel
          (attachment.hostRegion removed.site)
          compiled.factor.frame.visible =
        some compiled.factor.frame.siteBody :=
  compileWholeSiteFrame?_site_compiles definitions attachment.diagram
    (attachment.hostRegion removed.site)
    (attachment.diagram.regionCount + 1)
    attachment.diagram.root
    (WireContext.empty attachment.diagram)
    compiled.factor.frame compiled.frame_compiles

/-- Intrinsic attachment generated from this factor's exact ordered positions. -/
def intrinsicAttachment
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment : ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment) :
    SpliceAttachment extracted.openDiagram
      compiled.factor.frame.visible.sigs where
  positions := compiled.factor.positions
  classMap := fun fiber =>
    (firstPaired extracted.boundary compiled.factor.positions fiber
      (extracted.boundary_surjective _ fiber)).val
  representative_position := fun fiber =>
    (firstPaired extracted.boundary compiled.factor.positions fiber
      (extracted.boundary_surjective _ fiber)).property

theorem intrinsicClassWire_mem_boundary
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {sig : Sig}
    (fiber : Var extracted.openDiagram.classes sig) :
    ExtractedBoundaryCompiler.wireOfPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires extracted.checked.val)
        (⟨sig, fiber⟩ : PackedVar extracted.openDiagram.classes) ∈
      extracted.checked.val.boundary := by
  have contains := extracted.boundary_surjective sig fiber
  have mappedMember :
      ExtractedBoundaryCompiler.wireOfPacked
          extracted.checked.val.diagram
          (ConcreteElaboration.openBoundaryWires extracted.checked.val)
          (⟨sig, fiber⟩ : PackedVar extracted.openDiagram.classes) ∈
        extracted.boundary.entries.map
          (ExtractedBoundaryCompiler.wireOfPacked
            extracted.checked.val.diagram
            (ConcreteElaboration.openBoundaryWires
              extracted.checked.val)) :=
    List.mem_map.mpr ⟨⟨sig, fiber⟩, contains, rfl⟩
  have origins :=
    compileExtractedBoundary?_origins extracted.checked
      extracted.boundary extracted.boundary_compiles
  exact
    (congrArg (fun values =>
      ExtractedBoundaryCompiler.wireOfPacked
          extracted.checked.val.diagram
          (ConcreteElaboration.openBoundaryWires extracted.checked.val)
          (⟨sig, fiber⟩ : PackedVar extracted.openDiagram.classes) ∈ values)
      origins).mp mappedMember

/--
The intrinsic class representative is the target at the first concrete
occurrence of that extracted boundary class.
-/
theorem intrinsicAttachment_classMap_eq_positionPackedAt
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (extracted : ExtractionCompilation occurrence)
    {removed : RemovalResult occurrence}
    {attachment : ConcreteSpliceAttachment removed extracted.checked}
    (compiled : SpliceCompilation attachment)
    {sig : Sig}
    (fiber : Var extracted.openDiagram.classes sig) :
    let source :=
      ExtractedBoundaryCompiler.wireOfPacked
        extracted.checked.val.diagram
        (ConcreteElaboration.openBoundaryWires extracted.checked.val)
        (⟨sig, fiber⟩ : PackedVar extracted.openDiagram.classes)
    let member := intrinsicClassWire_mem_boundary extracted fiber
    (⟨sig, (compiled.intrinsicAttachment extracted).classMap fiber⟩ :
        PackedVar compiled.factor.frame.visible.sigs) =
      compiled.positionPackedAt
        (attachment.representativePosition source member) := by
  dsimp only
  let packedSource :=
    (⟨sig, fiber⟩ : PackedVar extracted.openDiagram.classes)
  let source :=
    ExtractedBoundaryCompiler.wireOfPacked
      extracted.checked.val.diagram
      (ConcreteElaboration.openBoundaryWires extracted.checked.val)
      packedSource
  have contains := extracted.boundary_surjective sig fiber
  have sourceMember := intrinsicClassWire_mem_boundary extracted fiber
  let representative :=
    attachment.representativePosition source sourceMember
  have origins :=
    compileExtractedBoundary?_origins extracted.checked
      extracted.boundary extracted.boundary_compiles
  let origin :=
    ExtractedBoundaryCompiler.wireOfPacked
      extracted.checked.val.diagram
      (ConcreteElaboration.openBoundaryWires extracted.checked.val)
  have originInjective :
      Function.Injective origin :=
    ExtractedBoundaryCompiler.wireOfPacked_injective
      extracted.checked.val.diagram
      (ConcreteElaboration.openBoundaryWires extracted.checked.val)
      (Data.Finite.eraseDups_nodup _)
  have mappedMember :
      origin packedSource ∈ extracted.boundary.entries.map origin :=
    List.mem_map.mpr ⟨packedSource, contains, rfl⟩
  have mappedIndexEquality :=
    denseIndex_map_injective origin originInjective
      extracted.boundary.entries packedSource contains
  have representativeValue :
      representative.val =
        (pairedFirstIndex extracted.boundary
          compiled.factor.positions fiber contains).val := by
    change
      (DenseList.index extracted.checked.val.boundary source
          sourceMember).val =
        (DenseList.index extracted.boundary.entries packedSource
          contains).val
    calc
      _ = (DenseList.index
            (extracted.boundary.entries.map origin)
            (origin packedSource) mappedMember).val :=
        (denseIndex_val_of_list_eq origins
          (origin packedSource) mappedMember sourceMember).symm
      _ = (mappedIndex origin extracted.boundary.entries
            (DenseList.index extracted.boundary.entries packedSource
              contains)).val :=
        congrArg Fin.val mappedIndexEquality
      _ = _ := rfl
  have positionEquality :
      representative =
        ⟨(pairedFirstIndex extracted.boundary
          compiled.factor.positions fiber contains).val, by
            simpa only [ExtractedBoundaryCompiler.entries_length,
              checkedBoundarySigs, List.length_map] using
              (pairedFirstIndex extracted.boundary
                compiled.factor.positions fiber contains).isLt⟩ :=
    Fin.ext representativeValue
  have firstTarget :=
    firstPaired_at_first_index extracted.boundary
      compiled.factor.positions fiber contains
  change
    (⟨sig, (compiled.intrinsicAttachment extracted).classMap fiber⟩ :
        PackedVar compiled.factor.frame.visible.sigs) =
      compiled.positionPackedAt representative
  rw [positionEquality]
  unfold SpliceCompilation.intrinsicAttachment
  dsimp only
  rw [← firstTarget]
  unfold positionPackedAt targetPackedAt
  congr 1

end SpliceCompilation

end RemovalFactorization

end VisualProof
