import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame

namespace VisualProof
open ConcreteElaboration
open FactorizationInternal

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

/-- A successful visible-variable lookup retains its exact concrete origin. -/
private theorem resolveVisibleWireIn?_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId)
    (value : Var
      (ids.map fun id => (diagram.wires id).sig)
      (diagram.wires wire).sig)
    (accepted :
      resolveVisibleWireIn? diagram ids wire = some value) :
    ConcreteElaboration.WireContext.origin diagram ids value = wire := by
  induction ids with
  | nil =>
      simp [resolveVisibleWireIn?] at accepted
  | cons head tail induction =>
      unfold resolveVisibleWireIn? at accepted
      split at accepted
      · rename_i equality
        subst head
        have same : (.here :
            Var ((wire :: tail).map fun id =>
              (diagram.wires id).sig)
              (diagram.wires wire).sig) = value :=
          Option.some.inj accepted
        subst value
        rfl
      · cases recursive :
            resolveVisibleWireIn? diagram tail wire with
        | none =>
            simp [recursive] at accepted
        | some tailValue =>
            have same : Var.there tailValue = value :=
              Option.some.inj (by simpa [recursive] using accepted)
            subst value
            exact induction tailValue recursive

private theorem resolveVisibleWireIn?_complete
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId)
    (member : wire ∈ ids) :
    ∃ value, resolveVisibleWireIn? diagram ids wire = some value := by
  induction ids with
  | nil => simp at member
  | cons head tail induction =>
      by_cases equality : wire = head
      · subst head
        exact ⟨.here, by simp [resolveVisibleWireIn?]⟩
      · have tailMember : wire ∈ tail := by
          simpa [equality] using member
        obtain ⟨value, generated⟩ := induction tailMember
        exact ⟨.there value, by
          simp [resolveVisibleWireIn?, equality, generated]⟩

private def resolveVisiblePacked?
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId) :
    Option (PackedVar
      (ids.map fun id => (diagram.wires id).sig)) :=
  (resolveVisibleWireIn? diagram ids wire).map fun value =>
    ⟨_, value⟩

/-- The intrinsic target occurrence at one ordered concrete boundary position. -/
def targetPackedAt
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

/--
Ordered intrinsic target variables together with their exact concrete origins.
The origin proof is structural output of lookup, never a caller premise.
-/
structure TargetCompilation
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target)
    (boundary : List source.WireId)
    (targets : Fin boundary.length → target.WireId) where
  private mk ::
  positions : Vars visible.sigs
    (boundary.map fun wire => (source.wires wire).sig)
  private origin :
    ∀ position,
      (match targetPackedAt source boundary positions position with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin target
              visible.ids value) =
        targets position
  private resolved :
    ∀ position,
      resolveVisiblePacked? target visible.ids (targets position) =
        some (targetPackedAt source boundary positions position)

/-- Build an explicit ordered target tuple from its exact visibility evidence. -/
private def targetCompilation
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target) :
    (boundary : List source.WireId) →
      (targets : Fin boundary.length → target.WireId) →
      (signatures : ∀ position,
        (target.wires (targets position)).sig =
          (source.wires (boundary.get position)).sig) →
      (∀ position, targets position ∈ visible.ids) →
      TargetCompilation source target visible boundary targets
  | [], targets, _ =>
      fun _ =>
      { positions := .nil
        origin := fun position => Fin.elim0 position
        resolved := fun position => Fin.elim0 position }
  | sourceWire :: tail, targets, signatures =>
      fun visibleTargets =>
      let headPosition : Fin (sourceWire :: tail).length :=
        ⟨0, by simp⟩
      let available :
          (resolveVisibleWireIn? target visible.ids
            (targets headPosition)).isSome = true :=
        Option.isSome_iff_exists.mpr
          (resolveVisibleWireIn?_complete target visible.ids
            (targets headPosition) (visibleTargets headPosition))
      let resolved :=
        (resolveVisibleWireIn? target visible.ids
          (targets headPosition)).get available
      let accepted :
          resolveVisibleWireIn? target visible.ids
              (targets headPosition) =
            some resolved :=
        (Option.some_get available).symm
      let headSignature :
          (target.wires (targets headPosition)).sig =
            (source.wires sourceWire).sig := by
        simpa [headPosition] using signatures headPosition
      let typed :
          Var visible.sigs (source.wires sourceWire).sig :=
        castVisibleVar headSignature resolved
      let rest :=
        targetCompilation source target visible tail
          (fun position => targets position.succ)
          (fun position => signatures position.succ)
          (fun position => visibleTargets position.succ)
      { positions := .cons typed rest.positions
        origin := fun position => by
          refine Fin.cases ?_ (fun tailPosition => ?_) position
          · change
              ConcreteElaboration.WireContext.origin target visible.ids
                  (castVisibleVar headSignature resolved) =
                targets headPosition
            rw [visibleOrigin_cast]
            exact
              resolveVisibleWireIn?_origin target visible.ids
                (targets headPosition) resolved accepted
          · simpa only [targetPackedAt, Vars.entries,
              List.get_eq_getElem, List.getElem_cons_succ] using
              rest.origin tailPosition
        resolved := fun position => by
          refine Fin.cases ?_ (fun tailPosition => ?_) position
          · change
              resolveVisiblePacked? target visible.ids
                  (targets headPosition) =
                some
                  (VisualProof.targetPackedAt source
                    (sourceWire :: tail)
                    (.cons typed rest.positions) headPosition)
            unfold resolveVisiblePacked?
            rw [accepted]
            simp only [Option.map_some]
            congr 1
            simpa only [targetPackedAt, Vars.entries,
              List.get_eq_getElem, List.getElem_cons_zero] using
              packed_castVisibleVar resolved headSignature
          · simpa only [targetPackedAt, Vars.entries,
              List.get_eq_getElem, List.getElem_cons_succ] using
              rest.resolved tailPosition }

/-- Resolve an explicit ordered target tuple in one compiler-visible context. -/
private def compileTargetPositions?
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target)
    (boundary : List source.WireId)
    (targets : Fin boundary.length → target.WireId)
    (signatures : ∀ position,
      (target.wires (targets position)).sig =
        (source.wires (boundary.get position)).sig) :
    Option (TargetCompilation source target visible boundary targets) :=
  if visibleTargets : ∀ position, targets position ∈ visible.ids then
    some
      (targetCompilation source target visible boundary targets
        signatures visibleTargets)
  else
    none

private theorem compileTargetPositions?_complete
    (source : ConcreteDiagram sourceDefinitions)
    (target : ConcreteDiagram targetDefinitions)
    (visible : WireContext target) :
    ∀ (boundary : List source.WireId)
      (targets : Fin boundary.length → target.WireId)
      (signatures : ∀ position,
        (target.wires (targets position)).sig =
          (source.wires (boundary.get position)).sig),
      (∀ position, targets position ∈ visible.ids) →
      ∃ compiled,
        compileTargetPositions? source target visible boundary targets
          signatures =
        some compiled := by
  intro boundary targets signatures visibleTargets
  refine
    ⟨targetCompilation source target visible boundary targets
        signatures visibleTargets, ?_⟩
  simp [compileTargetPositions?, visibleTargets]

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

/--
Build the intrinsic attachment from the authoritative compiled open boundary
and the exact ordered target tuple.
-/
def intrinsicAttachmentFromPositions
    {definitions : List (List Sig)}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    {target : List Sig}
    (positions : Vars target (checkedBoundarySigs fragment)) :
    SpliceAttachment fragmentCompiled.openDiagram target where
  positions := positions
  classMap := fun fiber =>
    (firstPaired fragmentCompiled.boundary positions fiber
      (fragmentCompiled.openDiagram.boundary_surjective _ fiber)).val
  representative_position := fun fiber =>
    (firstPaired fragmentCompiled.boundary positions fiber
      (fragmentCompiled.openDiagram.boundary_surjective _ fiber)).property

/--
Executable structural receipt for non-replacing insertion of one compiled open
fragment into one checked base site.
-/
structure InsertionCompilation
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment) where
  private mk ::
  site : SiteCompilation base site
  targets : TargetCompilation fragment.val.diagram base.val
    site.frame.visible fragment.val.boundary attachment.target
  private targets_compile :
    compileTargetPositions? fragment.val.diagram base.val
        site.frame.visible fragment.val.boundary attachment.target
        attachment.signature =
      some targets
  candidate : ConcreteSpliceResult attachment
  private candidate_accepts :
    splice attachment = .ok candidate

/--
Resolve ordered targets and check a concrete splice at an already-compiled
canonical site. No site traversal is performed.
-/
def compileInsertionAt?
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (siteCompiled : SiteCompilation base site)
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Option (InsertionCompilation fragmentCompiled attachment) :=
  match targetsAccepted :
      compileTargetPositions? fragment.val.diagram base.val
        siteCompiled.frame.visible fragment.val.boundary
        attachment.target attachment.signature with
  | none => none
  | some targets =>
      match candidateAccepted : splice attachment with
      | .error _ => none
      | .ok candidate =>
          some
            (InsertionCompilation.mk siteCompiled targets
              targetsAccepted candidate candidateAccepted)

/--
Run the site compiler before ordered target resolution and splice checking.
This legacy entry point remains for callers that do not already own a site.
-/
def compileInsertion?
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Option (InsertionCompilation fragmentCompiled attachment) :=
  match compileSite? base site with
  | none => none
  | some siteCompiled =>
      compileInsertionAt? siteCompiled fragmentCompiled attachment

namespace InsertionCompilation

/--
An accepted splice at an existing canonical site has a complete ordered
insertion receipt. Target completeness uses only that site's retained coverage.
-/
theorem ofSite
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (siteCompiled : SiteCompilation base site)
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment)
    (result : ConcreteSpliceResult attachment)
    (accepted : splice attachment = .ok result) :
    ∃ compiled,
      compileInsertionAt? siteCompiled fragmentCompiled attachment =
        some compiled := by
  have visibleTargets :
    ∀ position,
        attachment.target position ∈ siteCompiled.frame.visible.ids :=
    fun position =>
      FactorizationInternal.siteCompilationCovers siteCompiled
        (attachment.target position)
        (attachment.scope position)
  obtain ⟨targets, targetsGenerated⟩ :=
    compileTargetPositions?_complete fragment.val.diagram base.val
      siteCompiled.frame.visible fragment.val.boundary attachment.target
      attachment.signature visibleTargets
  let compiled : InsertionCompilation fragmentCompiled attachment :=
    InsertionCompilation.mk (fragmentCompiled := fragmentCompiled)
      siteCompiled targets targetsGenerated result accepted
  refine ⟨compiled, ?_⟩
  unfold compileInsertionAt?
  split
  · rename_i rejected
    rw [targetsGenerated] at rejected
    contradiction
  · rename_i generatedTargets generatedTargetsEquation
    have sameTargets : generatedTargets = targets :=
      Option.some.inj
        (generatedTargetsEquation.symm.trans targetsGenerated)
    subst generatedTargets
    split
    · rename_i error rejected
      rw [accepted] at rejected
      contradiction
    · rename_i generatedResult generatedResultEquation
      have sameResult : generatedResult = result :=
        Except.ok.inj (generatedResultEquation.symm.trans accepted)
      subst generatedResult
      congr

end InsertionCompilation

/--
Every accepted concrete splice internally supplies the complete structural
insertion receipt. Callers provide only the executable splice equation.
-/
theorem compileInsertion_complete_of_splice
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    (attachment : ConcreteSpliceAttachment base site fragment)
    (result : ConcreteSpliceResult attachment)
    (accepted : splice attachment = .ok result) :
    ∃ compiled,
      compileInsertion? fragmentCompiled attachment = some compiled := by
  obtain ⟨siteCompiled, siteGenerated⟩ :=
    compileSite_complete base site
  obtain ⟨compiled, compiledGenerated⟩ :=
    InsertionCompilation.ofSite siteCompiled fragmentCompiled attachment
      result accepted
  refine ⟨compiled, ?_⟩
  unfold compileInsertion?
  rw [siteGenerated]
  exact compiledGenerated

namespace InsertionCompilation

/-- Exact executable equation for ordered attachment-target compilation. -/
theorem targets_generated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    compileTargetPositions? fragment.val.diagram base.val
        compiled.site.frame.visible fragment.val.boundary attachment.target
        attachment.signature =
      some compiled.targets :=
  compiled.targets_compile

/-- The intrinsic target occurrence at one ordered attachment position. -/
def targetPackedAt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (position : Fin fragment.val.boundary.length) :
    PackedVar compiled.site.frame.visible.sigs :=
  VisualProof.targetPackedAt fragment.val.diagram fragment.val.boundary
    compiled.targets.positions position

/-- Every intrinsic target position recovers the exact supplied base wire. -/
theorem targetPackedAt_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (position : Fin fragment.val.boundary.length) :
    (match compiled.targetPackedAt position with
      | ⟨_, value⟩ =>
          ConcreteElaboration.WireContext.origin base.val
            compiled.site.frame.visible.ids value) =
      attachment.target position :=
  compiled.targets.origin position

/--
Compiled intrinsic target equality is exactly supplied concrete target
equality; the reverse direction follows from deterministic private lookup.
-/
theorem targetPackedAt_eq_iff
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (left right : Fin fragment.val.boundary.length) :
    compiled.targetPackedAt left = compiled.targetPackedAt right ↔
      attachment.target left = attachment.target right := by
  constructor
  · intro same
    have mapped := congrArg
      (fun packed =>
        match packed with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin base.val
              compiled.site.frame.visible.ids value)
      same
    simpa [compiled.targetPackedAt_origin left,
      compiled.targetPackedAt_origin right] using mapped
  · intro same
    have leftResolved := compiled.targets.resolved left
    have rightResolved := compiled.targets.resolved right
    rw [same] at leftResolved
    exact Option.some.inj (leftResolved.symm.trans rightResolved)

/-- The intrinsic ordered attachment compiled from the exact concrete tuple. -/
def intrinsicAttachment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    SpliceAttachment fragmentCompiled.openDiagram
      compiled.site.frame.visible.sigs :=
  intrinsicAttachmentFromPositions fragmentCompiled
    compiled.targets.positions

/--
Transport the compiler-owned ordered targets to the unique receipt for the
same base and site. This exposes no alternate construction path.
-/
def positionsAt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (common : SiteCompilation base site) :
    Vars common.frame.visible.sigs (checkedBoundarySigs fragment) :=
  congrArg
      (fun receipt : SiteCompilation base site =>
        receipt.frame.visible.sigs)
      (SiteCompilation.unique compiled.site common) ▸
    compiled.targets.positions

def targetPackedAtAt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (common : SiteCompilation base site)
    (position : Fin fragment.val.boundary.length) :
    PackedVar common.frame.visible.sigs :=
  VisualProof.targetPackedAt fragment.val.diagram fragment.val.boundary
    (compiled.positionsAt common) position

theorem targetPackedAtAt_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (common : SiteCompilation base site)
    (position : Fin fragment.val.boundary.length) :
    (match compiled.targetPackedAtAt common position with
      | ⟨_, value⟩ =>
          ConcreteElaboration.WireContext.origin base.val
            common.frame.visible.ids value) =
      attachment.target position := by
  have same := SiteCompilation.unique compiled.site common
  cases same
  simpa [targetPackedAtAt, positionsAt,
    InsertionCompilation.targetPackedAt] using
      compiled.targetPackedAt_origin position

def intrinsicAttachmentAt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (common : SiteCompilation base site) :
    SpliceAttachment fragmentCompiled.openDiagram
      common.frame.visible.sigs :=
  intrinsicAttachmentFromPositions fragmentCompiled
    (compiled.positionsAt common)

def insertedAt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (common : SiteCompilation base site) :
    Region definitions [] :=
  by
    simpa using
      common.frame.context.fill
        (Region.conjoin common.frame.siteBody
          (intrinsicSplice fragmentCompiled.openDiagram
            (compiled.intrinsicAttachmentAt common)))

/-- Every intrinsic open-boundary class names an actual concrete boundary wire. -/
theorem intrinsicClassWire_mem_boundary
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (_compiled : InsertionCompilation fragmentCompiled attachment)
    {sig : Sig}
    (fiber : Var fragmentCompiled.openDiagram.classes sig) :
    ExtractedBoundaryCompiler.wireOfPacked
        fragment.val.diagram
        (ConcreteElaboration.openBoundaryWires fragment.val)
        (⟨sig, fiber⟩ :
          PackedVar fragmentCompiled.openDiagram.classes) ∈
      fragment.val.boundary := by
  have contains :=
    fragmentCompiled.openDiagram.boundary_surjective sig fiber
  have mappedMember :
      ExtractedBoundaryCompiler.wireOfPacked
          fragment.val.diagram
          (ConcreteElaboration.openBoundaryWires fragment.val)
          (⟨sig, fiber⟩ :
            PackedVar fragmentCompiled.openDiagram.classes) ∈
        fragmentCompiled.boundary.entries.map
          (ExtractedBoundaryCompiler.wireOfPacked
            fragment.val.diagram
            (ConcreteElaboration.openBoundaryWires fragment.val)) :=
    List.mem_map.mpr ⟨⟨sig, fiber⟩, contains, rfl⟩
  have origins :=
    compileExtractedBoundary?_origins fragment fragmentCompiled.boundary
      fragmentCompiled.boundary_generated
  exact
    (congrArg (fun values =>
      ExtractedBoundaryCompiler.wireOfPacked
          fragment.val.diagram
          (ConcreteElaboration.openBoundaryWires fragment.val)
          (⟨sig, fiber⟩ :
            PackedVar fragmentCompiled.openDiagram.classes) ∈ values)
      origins).mp mappedMember

/--
The intrinsic class map is exactly the compiled target at the concrete
source class's canonical first boundary position.
-/
theorem intrinsicAttachment_classMap_eq_representative
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    {sig : Sig}
    (fiber : Var fragmentCompiled.openDiagram.classes sig) :
    let source :=
      ExtractedBoundaryCompiler.wireOfPacked
        fragment.val.diagram
        (ConcreteElaboration.openBoundaryWires fragment.val)
        (⟨sig, fiber⟩ :
          PackedVar fragmentCompiled.openDiagram.classes)
    let member := compiled.intrinsicClassWire_mem_boundary fiber
    (⟨sig, compiled.intrinsicAttachment.classMap fiber⟩ :
        PackedVar compiled.site.frame.visible.sigs) =
      compiled.targetPackedAt
        (attachment.representativePosition source member) := by
  dsimp only
  let packedSource :=
    (⟨sig, fiber⟩ :
      PackedVar fragmentCompiled.openDiagram.classes)
  let source :=
    ExtractedBoundaryCompiler.wireOfPacked
      fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val)
      packedSource
  have contains :=
    fragmentCompiled.openDiagram.boundary_surjective sig fiber
  have sourceMember := compiled.intrinsicClassWire_mem_boundary fiber
  let representative :=
    attachment.representativePosition source sourceMember
  have origins :=
    compileExtractedBoundary?_origins fragment fragmentCompiled.boundary
      fragmentCompiled.boundary_generated
  let origin :=
    ExtractedBoundaryCompiler.wireOfPacked
      fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val)
  have originInjective :
      Function.Injective origin :=
    ExtractedBoundaryCompiler.wireOfPacked_injective
      fragment.val.diagram
      (ConcreteElaboration.openBoundaryWires fragment.val)
      (Data.Finite.eraseDups_nodup _)
  have mappedMember :
      origin packedSource ∈ fragmentCompiled.boundary.entries.map origin :=
    List.mem_map.mpr ⟨packedSource, contains, rfl⟩
  have mappedIndexEquality :=
    denseIndex_map_injective origin originInjective
      fragmentCompiled.boundary.entries packedSource contains
  have representativeValue :
      representative.val =
        (pairedFirstIndex fragmentCompiled.boundary
          compiled.targets.positions fiber contains).val := by
    change
      (DenseList.index fragment.val.boundary source sourceMember).val =
        (DenseList.index fragmentCompiled.boundary.entries packedSource
          contains).val
    calc
      _ = (DenseList.index
            (fragmentCompiled.boundary.entries.map origin)
            (origin packedSource) mappedMember).val :=
        (denseIndex_val_of_list_eq origins
          (origin packedSource) mappedMember sourceMember).symm
      _ = (mappedIndex origin fragmentCompiled.boundary.entries
            (DenseList.index fragmentCompiled.boundary.entries packedSource
              contains)).val :=
        congrArg Fin.val mappedIndexEquality
      _ = _ := rfl
  have positionEquality :
      representative =
        ⟨(pairedFirstIndex fragmentCompiled.boundary
          compiled.targets.positions fiber contains).val, by
            simpa only [ExtractedBoundaryCompiler.entries_length,
              checkedBoundarySigs, List.length_map] using
              (pairedFirstIndex fragmentCompiled.boundary
                compiled.targets.positions fiber contains).isLt⟩ :=
    Fin.ext representativeValue
  have firstTarget :=
    firstPaired_at_first_index fragmentCompiled.boundary
      compiled.targets.positions fiber contains
  change
    (⟨sig, compiled.intrinsicAttachment.classMap fiber⟩ :
        PackedVar compiled.site.frame.visible.sigs) =
      compiled.targetPackedAt representative
  rw [positionEquality]
  unfold InsertionCompilation.intrinsicAttachment
    intrinsicAttachmentFromPositions
  rw [← firstTarget]
  unfold InsertionCompilation.targetPackedAt VisualProof.targetPackedAt
  congr 1

/-- Non-replacing intrinsic insertion at the retained site frame. -/
def inserted
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    Region definitions [] :=
  by
    simpa using
      compiled.site.frame.context.fill
        (Region.conjoin compiled.site.frame.siteBody
          (intrinsicSplice fragmentCompiled.openDiagram
            compiled.intrinsicAttachment))

theorem inserted_eq_insertedAt
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (common : SiteCompilation base site) :
    compiled.inserted = compiled.insertedAt common := by
  have same := SiteCompilation.unique compiled.site common
  cases same
  rfl

/-- Exact executable acceptance equation for the concrete splice candidate. -/
theorem candidate_accepted
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    splice attachment = .ok compiled.candidate :=
  compiled.candidate_accepts

/-- The ordinary intrinsic compilation of the accepted checked candidate. -/
def candidateBody
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    Region definitions [] :=
  elaborate compiled.candidate.checked

/-- Exact ordinary compiler equation for the accepted splice candidate. -/
theorem candidate_generated
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ConcreteElaboration.compileRoot? definitions
        compiled.candidate.checked.val =
      some compiled.candidateBody :=
  elaborateWith_compiles definitions compiled.candidate.checked.val
    compiled.candidate.checked.property

end InsertionCompilation

end VisualProof
