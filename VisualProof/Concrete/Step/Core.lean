import VisualProof.Concrete.Subgraph.Splice

namespace VisualProof.Concrete

open VisualProof.Diagram

def concreteCutDepthAux (diagram : Concrete.Diagram) :
    Nat → Fin diagram.regionCount → Nat
  | 0, _ => 0
  | fuel + 1, region =>
      match diagram.regions region with
      | .sheet => 0
      | .cut parent => concreteCutDepthAux diagram fuel parent + 1
      | .bubble parent _ => concreteCutDepthAux diagram fuel parent

def concreteCutDepth (diagram : Concrete.Diagram)
    (region : Fin diagram.regionCount) : Nat :=
  concreteCutDepthAux diagram diagram.regionCount region

private theorem concreteCutDepthAux_route
    (route : Concrete.Splice.RegionRoute diagram start target path)
    (hdepth : route.HasCutDepth depth) (fuel : Nat) :
    concreteCutDepthAux diagram (path.length + fuel) target =
      concreteCutDepthAux diagram fuel start + depth := by
  induction hdepth generalizing fuel with
  | here => simp
  | @cut start child target rest depth hparent position hposition tail
      child_is_cut tail_depth ih =>
      rw [show (position.val :: rest).length + fuel =
          rest.length + (fuel + 1) by simp; omega]
      rw [ih (fuel + 1)]
      simp [concreteCutDepthAux, child_is_cut]
      omega
  | @bubble start child target rest depth arity hparent position hposition tail
      child_is_bubble tail_depth ih =>
      rw [show (position.val :: rest).length + fuel =
          rest.length + (fuel + 1) by simp; omega]
      rw [ih (fuel + 1)]
      simp [concreteCutDepthAux, child_is_bubble]

private theorem concreteCutDepthAux_root_eq_zero
    (diagram : Concrete.Diagram) (rootSheet : diagram.RootIsSheet)
    (fuel : Nat) : concreteCutDepthAux diagram fuel diagram.root = 0 := by
  unfold Concrete.Diagram.RootIsSheet at rootSheet
  cases fuel with
  | zero => rfl
  | succ fuel => simp [concreteCutDepthAux, rootSheet]

/-- The sheet root is at positive depth zero. -/
theorem concreteCutDepth_root_eq_zero
    (checked : Concrete.Checked ) :
    concreteCutDepth checked.val checked.val.root = 0 := by
  unfold concreteCutDepth
  exact concreteCutDepthAux_root_eq_zero checked.val
    checked.property.root_is_sheet checked.val.regionCount

private theorem concreteCutDepthAux_coalesceFrameRaw
    (input : Concrete.Splice.Input ) (fuel : Nat)
    (region : Fin input.frame.val.regionCount) :
    concreteCutDepthAux input.coalesceFrameRaw fuel region =
      concreteCutDepthAux input.frame.val fuel region := by
  induction fuel generalizing region with
  | zero => rfl
  | succ fuel ih =>
      cases hregion : input.frame.val.regions region with
      | sheet => simp [concreteCutDepthAux, hregion]
      | cut parent => simp [concreteCutDepthAux, hregion, ih]
      | bubble parent arity => simp [concreteCutDepthAux, hregion, ih]

/-- Coalescing wire classes changes no region kind or parent edge, hence no
cut depth. -/
theorem concreteCutDepth_coalesceFrameRaw
    (input : Concrete.Splice.Input )
    (region : Fin input.frame.val.regionCount) :
    concreteCutDepth input.coalesceFrameRaw region =
      concreteCutDepth input.frame.val region := by
  unfold concreteCutDepth
  exact concreteCutDepthAux_coalesceFrameRaw input input.frame.val.regionCount
    region

private theorem concreteCutDepthAux_removeRaw
    (host : Concrete.Checked )
    (selection : Concrete.CheckedSelection host.val)
    (domains : Concrete.FrameDomains host.val selection)
    (fuel : Nat) (region : Fin host.val.regionCount)
    (hsurvives : domains.regions.survives region = true) :
    concreteCutDepthAux (host.val.removeRaw selection domains) fuel
        (domains.regions.index region hsurvives) =
      concreteCutDepthAux host.val fuel region := by
  induction fuel generalizing region with
  | zero => rfl
  | succ fuel ih =>
      cases hkind : host.val.regions region with
      | sheet =>
          have hreindexed := Concrete.Diagram.removeRaw_region_reindexed
            host selection domains (domains.regions.index region hsurvives)
          rw [domains.regions.origin_index region hsurvives, hkind] at hreindexed
          have hframe :
              (host.val.removeRaw selection domains).regions
                  (domains.regions.index region hsurvives) = .sheet := by
            simpa [Concrete.SurvivorDomain.reindexRegion?] using
              Option.some.inj hreindexed |>.symm
          simp [concreteCutDepthAux, hkind, hframe]
      | cut parent =>
          have hparent : (host.val.regions region).parent? = some parent := by
            exact (congrArg Concrete.CRegion.parent? hkind).trans rfl
          have hparentSurvives := domains.parent_survives host selection
            hsurvives hparent
          have hreindexed := Concrete.Diagram.removeRaw_region_reindexed
            host selection domains (domains.regions.index region hsurvives)
          rw [domains.regions.origin_index region hsurvives, hkind] at hreindexed
          have hframe :
              (host.val.removeRaw selection domains).regions
                  (domains.regions.index region hsurvives) =
                .cut (domains.regions.index parent hparentSurvives) := by
            simp only [Concrete.SurvivorDomain.reindexRegion?,
              domains.regions.index?_index parent hparentSurvives,
              Option.map_some] at hreindexed
            exact (Option.some.inj hreindexed).symm
          simp only [concreteCutDepthAux, hkind, hframe]
          exact congrArg (· + 1) (ih parent hparentSurvives)
      | bubble parent arity =>
          have hparent : (host.val.regions region).parent? = some parent := by
            exact (congrArg Concrete.CRegion.parent? hkind).trans rfl
          have hparentSurvives := domains.parent_survives host selection
            hsurvives hparent
          have hframe := Concrete.Diagram.removeRaw_bubble host selection
            domains hsurvives hkind
          simp only [concreteCutDepthAux, hkind, hframe]
          exact ih parent hparentSurvives

theorem siteView_concreteCutDepth_eq
    (view : Concrete.Splice.SiteView checked site) :
    concreteCutDepth checked.val site = view.focus.context.cutDepth := by
  have pathBound : view.path.length ≤ checked.val.regionCount :=
    VisualProof.Concrete.Elaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
      checked view.route.climb_length
  have routeDepth := concreteCutDepthAux_route view.route view.cutDepth
    (checked.val.regionCount - view.path.length)
  rw [Nat.add_sub_of_le pathBound] at routeDepth
  have rootDepth : concreteCutDepthAux checked.val
      (checked.val.regionCount - view.path.length) checked.val.root = 0 := by
    have rootSheet := checked.property.root_is_sheet
    unfold Concrete.Diagram.RootIsSheet at rootSheet
    cases checked.val.regionCount - view.path.length with
    | zero => rfl
    | succ fuel =>
        simp [concreteCutDepthAux, rootSheet]
  simpa [concreteCutDepth, rootDepth] using routeDepth

/-- Removing a checked selection preserves the cut depth of every retained
region.  The compact identifier may change, but every retained parent edge and
its cut/bubble kind is unchanged. -/
theorem concreteCutDepth_removeRaw_index
    (host : Concrete.Checked )
    (selection : Concrete.CheckedSelection host.val)
    (domains : Concrete.FrameDomains host.val selection)
    (region : Fin host.val.regionCount)
    (hsurvives : domains.regions.survives region = true) :
    concreteCutDepth (host.val.removeRaw selection domains)
        (domains.regions.index region hsurvives) =
      concreteCutDepth host.val region := by
  let view := Classical.choice (Concrete.Splice.siteView_complete host region)
  have pathBound : view.path.length ≤ domains.regions.count := by
    have hlt := Concrete.Diagram.removeRaw_climb_to_root_steps_lt_regionCount
      host selection domains hsurvives view.route.climb_length
    omega
  have routeDepth := concreteCutDepthAux_route view.route view.cutDepth
    (domains.regions.count - view.path.length)
  rw [Nat.add_sub_of_le pathBound] at routeDepth
  have rootDepth : concreteCutDepthAux host.val
      (domains.regions.count - view.path.length) host.val.root = 0 :=
    concreteCutDepthAux_root_eq_zero host.val host.property.root_is_sheet _
  have hhostAtFrameFuel : concreteCutDepthAux host.val domains.regions.count
      region = view.focus.context.cutDepth := by
    rw [rootDepth, Nat.zero_add] at routeDepth
    exact routeDepth
  rw [siteView_concreteCutDepth_eq view]
  unfold concreteCutDepth
  change concreteCutDepthAux (host.val.removeRaw selection domains)
      domains.regions.count (domains.regions.index region hsurvives) = _
  rw [concreteCutDepthAux_removeRaw host selection domains
    domains.regions.count region hsurvives]
  exact hhostAtFrameFuel

/-- The canonical retained splice site of a decomposition has exactly the cut
depth of the original selection anchor. -/
theorem Concrete.Splice.Decomposition.originalSite_concreteCutDepth_eq
    (decomposition : Concrete.Decomposition  host selection) :
    concreteCutDepth
        (host.val.removeRaw selection decomposition.frameDomains)
        (Concrete.Splice.Decomposition.originalSite decomposition) =
      concreteCutDepth host.val selection.val.anchor := by
  unfold Concrete.Splice.Decomposition.originalSite
  apply concreteCutDepth_removeRaw_index

theorem openSiteView_concreteCutDepth_eq
    (view : Concrete.Splice.OpenSiteView checked site) :
    concreteCutDepth checked.val.diagram site =
      view.focus.context.cutDepth := by
  let closed : Concrete.Checked :=
    ⟨checked.val.diagram, checked.property.diagram_well_formed⟩
  have pathBound : view.path.length ≤ checked.val.diagram.regionCount :=
    VisualProof.Concrete.Elaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
      closed view.route.climb_length
  have routeDepth := concreteCutDepthAux_route view.route view.cutDepth
    (checked.val.diagram.regionCount - view.path.length)
  rw [Nat.add_sub_of_le pathBound] at routeDepth
  have rootDepth : concreteCutDepthAux checked.val.diagram
      (checked.val.diagram.regionCount - view.path.length)
      checked.val.diagram.root = 0 := by
    have rootSheet := checked.property.diagram_well_formed.root_is_sheet
    unfold Concrete.Diagram.RootIsSheet at rootSheet
    cases checked.val.diagram.regionCount - view.path.length with
    | zero => rfl
    | succ fuel => simp [concreteCutDepthAux, rootSheet]
  simpa [concreteCutDepth, rootDepth] using routeDepth

private theorem binderProxy_concreteCutDepthAux_eq_zero
    (pattern : Concrete.CheckedOpen )
    (spine : Concrete.BinderSpine pattern.val.diagram)
    (index : Fin spine.proxyCount) (fuel : Nat) :
    concreteCutDepthAux pattern.val.diagram fuel (spine.proxy index) = 0 := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
      simp only [concreteCutDepthAux]
      rw [spine.proxy_region]
      by_cases hzero : index.val = 0
      · have rootSheet := pattern.property.diagram_well_formed.root_is_sheet
        simp [hzero, concreteCutDepthAux_root_eq_zero _ rootSheet]
      · simpa [hzero] using
          ih ⟨index.val - 1, by omega⟩

theorem binderSpine_body_concreteCutDepth_eq_zero
    (pattern : Concrete.CheckedOpen )
    (spine : Concrete.BinderSpine pattern.val.diagram) :
    concreteCutDepth pattern.val.diagram spine.bodyContainer = 0 := by
  by_cases hzero : spine.proxyCount = 0
  · rw [spine.body_eq_root_of_empty hzero]
    unfold concreteCutDepth
    exact concreteCutDepthAux_root_eq_zero pattern.val.diagram
      pattern.property.diagram_well_formed.root_is_sheet _
  · rw [spine.body_eq_terminal_of_nonempty hzero]
    exact binderProxy_concreteCutDepthAux_eq_zero pattern spine
      ⟨spine.proxyCount - 1, by omega⟩ pattern.val.diagram.regionCount

theorem patternBodyView_cutDepth_eq_zero
    (input : Concrete.Splice.Input )
    (view : Concrete.Splice.OpenSiteView input.pattern
      input.binderSpine.bodyContainer) :
    view.focus.context.cutDepth = 0 := by
  rw [← openSiteView_concreteCutDepth_eq view]
  exact binderSpine_body_concreteCutDepth_eq_zero input.pattern input.binderSpine

inductive Orientation
  | forward
  | backward
  deriving DecidableEq, Repr

/-- Canonical logical rule inventory, in serialized `ProofStep` order. -/
inductive StepTag
  | boundRelationSpawn
  | wireJoin
  | erasure
  | wireSever
  | iteration
  | deiteration
  | doubleCutIntro
  | doubleCutElim
  | comprehensionInstantiate
  | comprehensionAbstract
  | vacuousIntro
  | vacuousElim
  deriving DecidableEq, Repr

def StepTag.all : List StepTag :=
  [.boundRelationSpawn, .wireJoin,
    .erasure, .wireSever, .iteration, .deiteration,
    .doubleCutIntro, .doubleCutElim,
    .comprehensionInstantiate, .comprehensionAbstract,
    .vacuousIntro, .vacuousElim]

theorem StepTag.all_length : StepTag.all.length = 12 := by
  native_decide

theorem StepTag.all_nodup : StepTag.all.Nodup := by
  native_decide

theorem StepTag.mem_all (tag : StepTag) : tag ∈ StepTag.all := by
  cases tag <;> native_decide

inductive Error
  | invalidRegion
  | invalidNode
  | invalidWire
  | invalidSelection
  | wrongPolarity
  | incomparableScopes
  | binderEscape
  | arityMismatch
  | occurrenceMismatch
  | boundaryMismatch
  | nonVacuousBinder
  | binderKindOrArityMismatch
  | binderDoesNotEnclose
  | selfWire
  | invalidOpenDiagram (error : Concrete.WFError)
  | invalidBoundaryPosition (position : Nat)
  | resultNotWellFormed (error : Concrete.WFError)
  | operationRejected
  deriving DecidableEq

/-- Errors that establish that a fully specified request is malformed or
illegal. Target-validation and non-classifying operational failures are
intentionally absent. -/
inductive Error.DomainInvalid : Error → Prop
  | invalidRegion : DomainInvalid .invalidRegion
  | invalidNode : DomainInvalid .invalidNode
  | invalidWire : DomainInvalid .invalidWire
  | invalidSelection : DomainInvalid .invalidSelection
  | wrongPolarity : DomainInvalid .wrongPolarity
  | incomparableScopes : DomainInvalid .incomparableScopes
  | binderEscape : DomainInvalid .binderEscape
  | arityMismatch : DomainInvalid .arityMismatch
  | occurrenceMismatch : DomainInvalid .occurrenceMismatch
  | boundaryMismatch : DomainInvalid .boundaryMismatch
  | nonVacuousBinder : DomainInvalid .nonVacuousBinder
  | binderKindOrArityMismatch : DomainInvalid .binderKindOrArityMismatch
  | binderDoesNotEnclose : DomainInvalid .binderDoesNotEnclose
  | selfWire : DomainInvalid .selfWire
  | invalidOpenDiagram (error) : DomainInvalid (.invalidOpenDiagram error)
  | invalidBoundaryPosition (position) :
      DomainInvalid (.invalidBoundaryPosition position)

/-- Provenance of source wire identities through one concrete transformation.
`none` means that the source identity was deleted. -/
structure WireProvenance (source target : Concrete.Diagram) where
  image? : Fin source.wireCount → Option (Fin target.wireCount)
  image_injective : ∀ {left right mapped},
    image? left = some mapped → image? right = some mapped → left = right
  root_scoped : ∀ {wire mapped}, image? wire = some mapped →
    (source.wires wire).scope = source.root →
      (target.wires mapped).scope = target.root

namespace WireProvenance

def identity (diagram : Concrete.Diagram) :
    WireProvenance diagram diagram where
  image? wire := some wire
  image_injective := by
    intro left right mapped hleft hright
    simpa only [Option.some.injEq] using hleft.trans hright.symm
  root_scoped := by
    intro wire mapped himage hroot
    simp only [Option.some.injEq] at himage
    subst mapped
    exact hroot

def compose (first : WireProvenance source middle)
    (second : WireProvenance middle target) :
    WireProvenance source target where
  image? wire := first.image? wire >>= second.image?
  image_injective := by
    intro left right mapped hleft hright
    cases hleftFirst : first.image? left with
    | none => simp [hleftFirst] at hleft
    | some leftMiddle =>
        cases hleftSecond : second.image? leftMiddle with
        | none => simp [hleftFirst, hleftSecond] at hleft
        | some leftMapped =>
            cases hrightFirst : first.image? right with
            | none => simp [hrightFirst] at hright
            | some rightMiddle =>
                cases hrightSecond : second.image? rightMiddle with
                | none => simp [hrightFirst, hrightSecond] at hright
                | some rightMapped =>
                    simp [hleftFirst, hleftSecond] at hleft
                    simp [hrightFirst, hrightSecond] at hright
                    subst leftMapped
                    subst rightMapped
                    have middleEq := second.image_injective
                      hleftSecond hrightSecond
                    subst rightMiddle
                    exact first.image_injective hleftFirst hrightFirst
  root_scoped := by
    intro wire mapped himage hroot
    cases hfirst : first.image? wire with
    | none => simp [hfirst] at himage
    | some middleWire =>
        cases hsecond : second.image? middleWire with
        | none => simp [hfirst, hsecond] at himage
        | some targetWire =>
            simp [hfirst, hsecond] at himage
            subst targetWire
            exact second.root_scoped hsecond
              (first.root_scoped hfirst hroot)

/-- Turn an operation's partial injective origin map into boundary provenance.
Candidates whose result scope is not the result root are reported as deleted,
so boundary transport cannot silently move an open parameter under a binder. -/
def rootFiltered (source target : Concrete.Diagram)
    (candidate : Fin source.wireCount → Option (Fin target.wireCount))
    (candidate_injective : ∀ {left right mapped},
      candidate left = some mapped → candidate right = some mapped →
        left = right) : WireProvenance source target where
  image? wire := do
    let mapped ← candidate wire
    if (target.wires mapped).scope = target.root then some mapped else none
  image_injective := by
    intro left right mapped hleft hright
    cases hleftCandidate : candidate left with
    | none => simp [hleftCandidate] at hleft
    | some leftMapped =>
        cases hrightCandidate : candidate right with
        | none => simp [hrightCandidate] at hright
        | some rightMapped =>
            simp [hleftCandidate] at hleft
            simp [hrightCandidate] at hright
            obtain ⟨_, hleftEq⟩ := hleft
            obtain ⟨_, hrightEq⟩ := hright
            subst leftMapped
            subst rightMapped
            exact candidate_injective hleftCandidate hrightCandidate
  root_scoped := by
    intro wire mapped himage _
    cases hcandidate : candidate wire with
    | none => simp [hcandidate] at himage
    | some candidateMapped =>
        simp [hcandidate] at himage
        obtain ⟨hroot, heq⟩ := himage
        subst mapped
        exact hroot

/-- Reindex provenance across a proved equality of concrete results. -/
def castTarget (provenance : WireProvenance source target)
    (targetEq : target = replacement) :
    WireProvenance source replacement := by
  subst replacement
  exact provenance

/-- Reindex provenance across a proved equality of concrete sources. -/
def castSource (provenance : WireProvenance source target)
    (sourceEq : source = replacement) :
    WireProvenance replacement target := by
  subst replacement
  exact provenance

/-- Preserve every dense wire position when an operation changes no wire
identities. Root filtering still rejects a wire that the operation moved under
a binder, so this constructor cannot manufacture open-boundary survival. -/
def byWireCount (source target : Concrete.Diagram)
    (wireCountEq : source.wireCount = target.wireCount) :
    WireProvenance source target :=
  rootFiltered source target (fun wire => some (Fin.cast wireCountEq wire)) (by
    intro left right mapped hleft hright
    have mappedEq : Fin.cast wireCountEq left = Fin.cast wireCountEq right :=
      Option.some.inj (hleft.trans hright.symm)
    apply Fin.ext
    simpa using congrArg Fin.val mappedEq)

/-- Preserve the old wire prefix when an operation only appends fresh wire
identities. -/
def append (source target : Concrete.Diagram) (added : Nat)
    (wireCountEq : target.wireCount = source.wireCount + added) :
    WireProvenance source target :=
  rootFiltered source target
    (fun wire => some (Fin.cast wireCountEq.symm (Fin.castAdd added wire))) (by
      intro left right mapped hleft hright
      have mappedEq :
          Fin.cast wireCountEq.symm (Fin.castAdd added left) =
            Fin.cast wireCountEq.symm (Fin.castAdd added right) :=
        Option.some.inj (hleft.trans hright.symm)
      apply Fin.ext
      simpa using congrArg Fin.val mappedEq)

/-- Preserve precisely the identities selected by a survivor domain. -/
def survivors (source target : Concrete.Diagram)
    (domain : Concrete.SurvivorDomain source.wireCount)
    (wireCountEq : target.wireCount = domain.count) :
    WireProvenance source target :=
  rootFiltered source target
    (fun wire => (domain.index? wire).map (Fin.cast wireCountEq.symm)) (by
      intro left right mapped hleft hright
      rw [Option.map_eq_some_iff] at hleft hright
      obtain ⟨leftIndex, hleftIndex, hleftMapped⟩ := hleft
      obtain ⟨rightIndex, hrightIndex, hrightMapped⟩ := hright
      have mappedEq : Fin.cast wireCountEq.symm leftIndex =
          Fin.cast wireCountEq.symm rightIndex :=
        hleftMapped.trans hrightMapped.symm
      have indexEq : leftIndex = rightIndex := by
        apply Fin.ext
        simpa using congrArg Fin.val mappedEq
      subst rightIndex
      have leftOrigin := (domain.index?_eq_some_iff left leftIndex).mp hleftIndex
      have rightOrigin :=
        (domain.index?_eq_some_iff right leftIndex).mp hrightIndex
      exact leftOrigin.symm.trans rightOrigin)

end WireProvenance

/-- Logical transport of source wire identities through one proof step.
Unlike graph provenance, distinct source identities may intentionally coalesce
to one target identity. `none` means that the source identity has no designated
open-interface image. -/
structure WireTransport (source target : Concrete.Diagram) where
  image? : Fin source.wireCount → Option (Fin target.wireCount)
  root_scoped : ∀ {wire mapped}, image? wire = some mapped →
    (source.wires wire).scope = source.root →
      (target.wires mapped).scope = target.root

namespace WireTransport

def identity (diagram : Concrete.Diagram) :
    WireTransport diagram diagram where
  image? wire := some wire
  root_scoped := by
    intro wire mapped himage hroot
    simp only [Option.some.injEq] at himage
    subst mapped
    exact hroot

def compose (first : WireTransport source middle)
    (second : WireTransport middle target) :
    WireTransport source target where
  image? wire := first.image? wire >>= second.image?
  root_scoped := by
    intro wire mapped himage hroot
    cases hfirst : first.image? wire with
    | none => simp [hfirst] at himage
    | some middleWire =>
        cases hsecond : second.image? middleWire with
        | none => simp [hfirst, hsecond] at himage
        | some targetWire =>
            simp [hfirst, hsecond] at himage
            subst targetWire
            exact second.root_scoped hsecond
              (first.root_scoped hfirst hroot)

/-- Restrict an operation's proposed logical wire map to root-scoped targets.
No injectivity hypothesis is required: coalescence is part of the interface
semantics rather than an error. -/
def rootFiltered (source target : Concrete.Diagram)
    (candidate : Fin source.wireCount → Option (Fin target.wireCount)) :
    WireTransport source target where
  image? wire := do
    let mapped ← candidate wire
    if (target.wires mapped).scope = target.root then some mapped else none
  root_scoped := by
    intro wire mapped himage _
    cases hcandidate : candidate wire with
    | none => simp [hcandidate] at himage
    | some candidateMapped =>
        simp [hcandidate] at himage
        obtain ⟨hroot, heq⟩ := himage
        subst mapped
        exact hroot

/-- Reindex an interface transport across a proved equality of concrete
results. -/
def castTarget (transport : WireTransport source target)
    (targetEq : target = replacement) :
    WireTransport source replacement := by
  subst replacement
  exact transport

/-- Use graph provenance as a logical transport when no additional
coalescence is intended. -/
def ofProvenance (provenance : WireProvenance source target) :
    WireTransport source target where
  image? := provenance.image?
  root_scoped := provenance.root_scoped

/-- Preserve every dense wire position when an operation changes no wire
identities, while refusing any source wire whose target is not root-scoped. -/
def byWireCount (source target : Concrete.Diagram)
    (wireCountEq : source.wireCount = target.wireCount) :
    WireTransport source target :=
  rootFiltered source target (fun wire => some (Fin.cast wireCountEq wire))

/-- Preserve the old wire prefix when an operation only appends fresh wire
identities. -/
def append (source target : Concrete.Diagram) (added : Nat)
    (wireCountEq : target.wireCount = source.wireCount + added) :
    WireTransport source target :=
  rootFiltered source target
    (fun wire => some (Fin.cast wireCountEq.symm (Fin.castAdd added wire)))

/-- Preserve precisely the identities selected by a survivor domain. -/
def survivors (source target : Concrete.Diagram)
    (domain : Concrete.SurvivorDomain source.wireCount)
    (wireCountEq : target.wireCount = domain.count) :
    WireTransport source target :=
  rootFiltered source target
    (fun wire => (domain.index? wire).map (Fin.cast wireCountEq.symm))

/-- Transport an ordered boundary, failing exactly when one position has no
designated image. Repeated positions remain repeated, and distinct positions
may become aliases when their source wires coalesce. -/
def transportBoundary (transport : WireTransport source target) :
    List (Fin source.wireCount) → Option (List (Fin target.wireCount))
  | [] => some []
  | wire :: rest => do
      let mapped ← transport.image? wire
      let mappedRest ← transport.transportBoundary rest
      pure (mapped :: mappedRest)

theorem transportBoundary_compose
    (first : WireTransport source middle)
    (second : WireTransport middle target)
    (boundary : List (Fin source.wireCount)) :
    (first.compose second).transportBoundary boundary =
      first.transportBoundary boundary >>= second.transportBoundary := by
  induction boundary with
  | nil => rfl
  | cons wire rest ih =>
      simp only [transportBoundary]
      change
        (do
          let mapped ← first.image? wire >>= second.image?
          let mappedRest ← (first.compose second).transportBoundary rest
          pure (mapped :: mappedRest)) =
        ((do
          let mapped ← first.image? wire
          let mappedRest ← first.transportBoundary rest
          pure (mapped :: mappedRest)) >>= second.transportBoundary)
      rw [ih]
      cases hfirst : first.image? wire with
      | none => simp
      | some middleWire =>
          cases hrest : first.transportBoundary rest with
          | none => simp
          | some intermediate =>
              cases hsecond : second.image? middleWire <;>
                simp [hsecond, transportBoundary]

theorem transportBoundary_compose_iff
    (first : WireTransport source middle)
    (second : WireTransport middle target)
    (boundary : List (Fin source.wireCount))
    (mapped : List (Fin target.wireCount)) :
    (first.compose second).transportBoundary boundary = some mapped ↔
      ∃ intermediate,
        first.transportBoundary boundary = some intermediate ∧
          second.transportBoundary intermediate = some mapped := by
  rw [transportBoundary_compose]
  constructor
  · intro htransport
    cases hfirst : first.transportBoundary boundary with
    | none => simp [hfirst] at htransport
    | some intermediate =>
        refine ⟨intermediate, rfl, ?_⟩
        simpa [hfirst] using htransport
  · rintro ⟨intermediate, hfirst, hsecond⟩
    simp [hfirst, hsecond]

theorem transportBoundary_length
    (transport : WireTransport source target)
    (htransport : transport.transportBoundary boundary = some mapped) :
    mapped.length = boundary.length := by
  induction boundary generalizing mapped with
  | nil => simp [transportBoundary] at htransport; subst mapped; rfl
  | cons wire rest ih =>
      cases hwire : transport.image? wire with
      | none => simp [transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : transport.transportBoundary rest with
          | none => simp [transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [transportBoundary, hwire, hrest] at htransport
              subst mapped
              simp [ih hrest]

theorem transportBoundary_root_scoped
    (transport : WireTransport source target)
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (source.wires wire).scope = source.root)
    (htransport : transport.transportBoundary boundary = some mapped) :
    ∀ wire, wire ∈ mapped → (target.wires wire).scope = target.root := by
  induction boundary generalizing mapped with
  | nil => simp [transportBoundary] at htransport; subst mapped; simp
  | cons sourceWire rest ih =>
      cases hwire : transport.image? sourceWire with
      | none => simp [transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : transport.transportBoundary rest with
          | none => simp [transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [transportBoundary, hwire, hrest] at htransport
              subst mapped
              intro wire hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hrestMem
              · exact transport.root_scoped hwire
                  (sourceRoot sourceWire (by simp))
              · exact ih (fun candidate hcandidate =>
                  sourceRoot candidate (by simp [hcandidate])) hrest wire hrestMem

/-- If every boundary wire has a specified image, ordered transport is
exactly `List.map`; order and repeated positions are retained. -/
theorem transportBoundary_eq_map
    (transport : WireTransport source target)
    (image : Fin source.wireCount → Fin target.wireCount)
    (himage : ∀ wire, wire ∈ boundary →
      transport.image? wire = some (image wire)) :
    transport.transportBoundary boundary = some (boundary.map image) := by
  induction boundary with
  | nil => rfl
  | cons wire rest ih =>
      rw [transportBoundary, himage wire (by simp), ih (fun candidate hmem =>
        himage candidate (by simp [hmem]))]
      rfl

/-- Pointwise form of successful ordered-boundary transport. -/
theorem transportBoundary_get
    (transport : WireTransport source target)
    (htransport : transport.transportBoundary boundary = some mapped)
    (index : Fin boundary.length) :
    transport.image? (boundary.get index) =
      some (mapped.get (Fin.cast
        (transport.transportBoundary_length htransport).symm index)) := by
  induction boundary generalizing mapped with
  | nil => exact Fin.elim0 index
  | cons wire rest ih =>
      cases hwire : transport.image? wire with
      | none => simp [transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : transport.transportBoundary rest with
          | none => simp [transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [transportBoundary, hwire, hrest] at htransport
              subst mapped
              refine Fin.cases ?_ (fun tail => ?_) index
              · simpa using hwire
              · simpa using ih hrest tail

/-- A source alias remains an alias after successful transport. The converse
is intentionally absent: distinct source wires may legitimately coalesce. -/
theorem transportBoundary_get_eq
    (transport : WireTransport source target)
    (htransport : transport.transportBoundary boundary = some mapped)
    {left right : Fin boundary.length}
    (heq : boundary.get left = boundary.get right) :
    mapped.get (Fin.cast
        (transport.transportBoundary_length htransport).symm left) =
      mapped.get (Fin.cast
        (transport.transportBoundary_length htransport).symm right) := by
  have hleft := transport.transportBoundary_get htransport left
  have hright := transport.transportBoundary_get htransport right
  rw [heq] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

end WireTransport

theorem castTarget_provenance_image_realizes
    (expected : WireProvenance source raw)
    (resultEq : result = raw) (wire : Fin source.wireCount) :
    Option.map (Fin.cast (congrArg Diagram.wireCount resultEq))
        ((expected.castTarget resultEq.symm).image? wire) =
      expected.image? wire := by
  subst raw
  simp [WireProvenance.castTarget]

theorem castTarget_interface_image_realizes
    (expected : WireTransport source raw)
    (resultEq : result = raw) (wire : Fin source.wireCount) :
    Option.map (Fin.cast (congrArg Diagram.wireCount resultEq))
        ((expected.castTarget resultEq.symm).image? wire) =
      expected.image? wire := by
  subst raw
  simp [WireTransport.castTarget]

/-- Raw open-state evidence used internally by the existing proof towers. -/
structure OperationState where
  diagram : Concrete.Checked
  boundary : List (Fin diagram.val.wireCount)
  boundary_root_scoped : ∀ wire, wire ∈ boundary →
    (diagram.val.wires wire).scope = diagram.val.root

def OperationState.closed (diagram : Concrete.Checked ) :
    OperationState  where
  diagram := diagram
  boundary := []
  boundary_root_scoped := by simp

def OperationState.asCheckedOpen (state : OperationState ) :
    Concrete.CheckedOpen  := ⟨{
  diagram := state.diagram.val
  boundary := state.boundary
}, {
  diagram_well_formed := state.diagram.property
  boundary_is_root_scoped := state.boundary_root_scoped
}⟩

/-- Raw successful-operation evidence used by the existing proof towers.
Graph provenance is injective; the raw wire transport may record intentional
coalescence. Public execution returns `Concrete.Receipt`. -/
structure OperationReceipt (input : Concrete.Checked ) where
  result : Concrete.Checked
  provenance : WireProvenance input.val result.val
  interface : WireTransport input.val result.val

def OperationReceipt.ofChecked
    (input : Concrete.Checked ) (raw : Concrete.Diagram)
    (provenance : WireProvenance input.val raw)
    (interface : WireTransport input.val raw)
    (result : Concrete.Checked )
    (hcheck : Concrete.checkWellFormed  raw = .ok result) :
    OperationReceipt input where
  result := result
  provenance := provenance.castTarget
    (Concrete.checkWellFormed_preserves_input hcheck).symm
  interface := interface.castTarget
    (Concrete.checkWellFormed_preserves_input hcheck).symm

/-- A receipt realizes one exact raw transformation and both of its wire
authorities. Each map is compared pointwise after casting the checked result's
target indices to the exact raw result. -/
structure OperationReceipt.Realizes
    (receipt : OperationReceipt input) (raw : Concrete.Diagram)
    (expectedProvenance : WireProvenance input.val raw)
    (expectedInterface : WireTransport input.val raw) : Prop where
  result_eq : receipt.result.val = raw
  provenance_image_eq : ∀ wire,
    Option.map (Fin.cast (congrArg Concrete.Diagram.wireCount result_eq))
        (receipt.provenance.image? wire) =
      expectedProvenance.image? wire
  interface_image_eq : ∀ wire,
    Option.map (Fin.cast (congrArg Concrete.Diagram.wireCount result_eq))
        (receipt.interface.image? wire) =
      expectedInterface.image? wire

theorem OperationReceipt.ofChecked_realizes
    (input : Concrete.Checked ) (raw : Concrete.Diagram)
    (expectedProvenance : WireProvenance input.val raw)
    (expectedInterface : WireTransport input.val raw)
    (result : Concrete.Checked )
    (hcheck : Concrete.checkWellFormed  raw = .ok result) :
    (OperationReceipt.ofChecked input raw expectedProvenance expectedInterface result
      hcheck).Realizes raw expectedProvenance expectedInterface := by
  have hresult := Concrete.checkWellFormed_preserves_input hcheck
  cases hresult
  refine ⟨rfl, ?_, ?_⟩
  · intro wire
    simp [OperationReceipt.ofChecked, WireProvenance.castTarget]
  · intro wire
    simp [OperationReceipt.ofChecked, WireTransport.castTarget]

namespace OperationReceipt.Realizes

def targetWire
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface) :
    Fin receipt.result.val.wireCount → Fin raw.wireCount :=
  Fin.cast (congrArg Concrete.Diagram.wireCount realizes.result_eq)

def targetBoundary
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    List (Fin raw.wireCount) :=
  mapped.map realizes.targetWire

theorem expected_provenance_image_eq_some
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {wire : Fin input.val.wireCount}
    {mapped : Fin receipt.result.val.wireCount}
    (himage : receipt.provenance.image? wire = some mapped) :
    expectedProvenance.image? wire = some (realizes.targetWire mapped) := by
  rw [← realizes.provenance_image_eq wire, himage]
  rfl

theorem expected_interface_image_eq_some
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {wire : Fin input.val.wireCount}
    {mapped : Fin receipt.result.val.wireCount}
    (himage : receipt.interface.image? wire = some mapped) :
    expectedInterface.image? wire = some (realizes.targetWire mapped) := by
  rw [← realizes.interface_image_eq wire, himage]
  rfl

/-- Translate successful receipt-boundary transport to the exact raw
operation witnessed by `Realizes`.  This is positional: no list quotient or
deduplication occurs. -/
theorem transportBoundary_expected
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {mapped : List (Fin receipt.result.val.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    expectedInterface.transportBoundary boundary =
      some (realizes.targetBoundary mapped) := by
  induction boundary generalizing mapped with
  | nil =>
      simp [WireTransport.transportBoundary] at htransport
      subst mapped
      rfl
  | cons wire rest ih =>
      cases hwire : receipt.interface.image? wire with
      | none =>
          simp [WireTransport.transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : receipt.interface.transportBoundary rest with
          | none =>
              simp [WireTransport.transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [WireTransport.transportBoundary, hwire, hrest] at htransport
              subst mapped
              rw [WireTransport.transportBoundary,
                realizes.expected_interface_image_eq_some hwire, ih hrest]
              rfl

/-- Completeness of receipt-side ordered transport for a realized operation.
If the exact operation transports every requested position, the checked
receipt does too.  This is the inverse existence direction to
`transportBoundary_expected`; it preserves order and repeated positions. -/
theorem transportBoundary_receipt_complete
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {rawMapped : List (Fin raw.wireCount)}
    (hexpected : expectedInterface.transportBoundary boundary = some rawMapped) :
    ∃ mapped, receipt.interface.transportBoundary boundary = some mapped := by
  induction boundary generalizing rawMapped with
  | nil =>
      simp [WireTransport.transportBoundary] at hexpected
      exact ⟨[], rfl⟩
  | cons wire rest ih =>
      cases hexactWire : expectedInterface.image? wire with
      | none =>
          simp [WireTransport.transportBoundary, hexactWire] at hexpected
      | some exactWire =>
          cases hexactRest : expectedInterface.transportBoundary rest with
          | none =>
              simp [WireTransport.transportBoundary, hexactWire,
                hexactRest] at hexpected
          | some exactRest =>
              simp [WireTransport.transportBoundary, hexactWire,
                hexactRest] at hexpected
              obtain ⟨mappedRest, hmappedRest⟩ := ih hexactRest
              cases hreceiptWire : receipt.interface.image? wire with
              | none =>
                  have halign := realizes.interface_image_eq wire
                  simp [hreceiptWire, hexactWire] at halign
              | some mappedWire =>
                  exact ⟨mappedWire :: mappedRest, by
                    simp [WireTransport.transportBoundary, hreceiptWire,
                      hmappedRest]⟩

/-- The canonical ordered open view of the exact raw result witnessed by a
receipt.  Boundary positions are cast positionwise through `result_eq`; in
particular, repeated aliases remain repeated. -/
def rawResultOpen
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    Concrete.OpenDiagram where
  diagram := raw
  boundary := realizes.targetBoundary mapped

@[simp] theorem rawResultOpen_boundary_length
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    (realizes.rawResultOpen mapped).boundary.length = mapped.length := by
  simp [rawResultOpen, targetBoundary]

def rawResultOpen_wellFormed
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {mapped : List (Fin receipt.result.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    (realizes.rawResultOpen mapped).WellFormed  where
  diagram_well_formed := by
    change raw.WellFormed
    exact realizes.result_eq ▸ receipt.result.property
  boundary_is_root_scoped :=
    expectedInterface.transportBoundary_root_scoped sourceRoot
      (realizes.transportBoundary_expected htransport)

/-- The canonical raw open view and the receipt result are the same ordered
open graph up to the finite casts forced by `result_eq`. -/
def rawResultOpenIso
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    Concrete.OpenIso (realizes.rawResultOpen mapped) {
      diagram := receipt.result.val
      boundary := mapped
    } := by
  rcases realizes with ⟨hresult, hprovenance, hinterface⟩
  subst raw
  refine {
    diagram := Concrete.Iso.refl receipt.result.val
    boundary := ?_
  }
  simp only [rawResultOpen, targetBoundary, targetWire]
  induction mapped with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      exact congrArg (List.cons head) ih

/-- Uniqueness of successful positional transport aligns any operation-facing
raw boundary with the receipt's canonical raw boundary. -/
theorem expectedMapped_eq_targetBoundary
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {mapped : List (Fin receipt.result.val.wireCount)}
    {rawMapped : List (Fin raw.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped)
    (hexpected : expectedInterface.transportBoundary boundary = some rawMapped) :
    rawMapped = realizes.targetBoundary mapped := by
  exact Option.some.inj (hexpected.symm.trans
    (realizes.transportBoundary_expected htransport))

/-- The operation-facing ordered raw boundary is canonically the receipt's
raw boundary.  This packages exact positional boundary transport as an open
isomorphism; repeated positions are preserved because the proof uses list
equality, not membership. -/
def operationalIso_to_rawResultOpen
    {input : Concrete.Checked }
    {receipt : OperationReceipt input} {raw : Concrete.Diagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : WireTransport input.val raw}
    (realizes : OperationReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {mapped : List (Fin receipt.result.val.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped)
    (rawMapped : List (Fin raw.wireCount))
    (hexpected : expectedInterface.transportBoundary boundary = some rawMapped) :
    Concrete.OpenIso { diagram := raw, boundary := rawMapped }
      (realizes.rawResultOpen mapped) := by
  refine {
    diagram := Concrete.Iso.refl raw
    boundary := ?_
  }
  have hmapped : rawMapped = realizes.targetBoundary mapped :=
    realizes.expectedMapped_eq_targetBoundary htransport hexpected
  change rawMapped.map (Concrete.Iso.refl raw).wires =
    realizes.targetBoundary mapped
  rw [hmapped]
  simp [Concrete.Iso.refl, FiniteEquiv.refl]

end OperationReceipt.Realizes

def OperationReceipt.transportOpen {input : Concrete.Checked }
    (receipt : OperationReceipt input)
    (boundary : List (Fin input.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    Option (OperationState ) :=
  match htransport : receipt.interface.transportBoundary boundary with
  | none => none
  | some mapped => some {
      diagram := receipt.result
      boundary := mapped
      boundary_root_scoped := receipt.interface.transportBoundary_root_scoped
        rootScoped htransport
    }

/-- Successful open-state transport exposes the exact ordered boundary
transport and the open state constructed from it. -/
theorem OperationReceipt.transportOpen_result {input : Concrete.Checked }
    (receipt : OperationReceipt input)
    (boundary : List (Fin input.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (result : OperationState )
    (hopen : receipt.transportOpen boundary rootScoped = some result) :
    ∃ (mapped : List (Fin receipt.result.val.wireCount))
      (htransport :
        receipt.interface.transportBoundary boundary = some mapped),
      result = {
        diagram := receipt.result
        boundary := mapped
        boundary_root_scoped :=
          receipt.interface.transportBoundary_root_scoped
            rootScoped htransport
      } := by
  unfold OperationReceipt.transportOpen at hopen
  split at hopen
  · contradiction
  · rename_i mapped htransport
    cases hopen
    exact ⟨mapped, htransport, rfl⟩

structure OperationAbstractionOccurrence (input : Concrete.Checked ) where
  selection : Concrete.CheckedSelection input.val
  args : List (Fin input.val.wireCount)

def selectedLayout (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) :
    Concrete.FragmentLayout input.val selection := {}

def selectedFragment (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) :
    Concrete.OpenDiagram :=
  input.val.extractOpenRaw selection (selectedLayout input selection)

theorem selectedFragment_wellFormed
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) :
    (selectedFragment input selection).WellFormed  :=
  Concrete.Diagram.extractOpenRaw_wellFormed input selection
    (selectedLayout input selection)

def pinnedSelectedFragment (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) (arity : Nat)
    (position : Fin arity →
      Fin selection.touchingWires.length) : Concrete.OpenDiagram where
  diagram := (selectedFragment input selection).diagram
  boundary := List.ofFn fun index =>
    (selectedLayout input selection).boundaryWire (position index)

/-- The pinned selected fragment is independent of the private choice of
fragment-layout witness: a checked selection determines that layout uniquely. -/
theorem pinnedSelectedFragment_eq_extractOpenRaw
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) (arity : Nat)
    (position : Fin arity → Fin selection.touchingWires.length)
    (layout : Concrete.FragmentLayout input.val selection) :
    pinnedSelectedFragment input selection arity position = {
      diagram := (input.val.extractOpenRaw selection layout).diagram
      boundary := List.ofFn fun index => layout.boundaryWire (position index)
    } := by
  unfold pinnedSelectedFragment selectedFragment
  rw [Concrete.FragmentLayout.unique (selectedLayout input selection) layout]

theorem pinnedSelectedFragment_wellFormed
    (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) (arity : Nat)
    (position : Fin arity → Fin selection.touchingWires.length) :
    (pinnedSelectedFragment input selection arity position).WellFormed  where
  diagram_well_formed :=
    Concrete.Diagram.extractDiagramRaw_wellFormed input selection
      (selectedLayout input selection)
  boundary_is_root_scoped := by
    intro wire hwire
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hwire
    apply input.val.extractBoundaryRaw_root_scoped selection
      (selectedLayout input selection)
    simp [Concrete.Diagram.extractBoundaryRaw]

def selectedProxy (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val)
    (index : Fin (selectedLayout input selection).proxyCount) :
    Fin (selectedFragment input selection).diagram.regionCount :=
  (selectedLayout input selection).proxy index

/-- A supplied certificate that another disjoint occurrence justifies
deiteration. Boundary order, repeated aliases, and external binder identities
are pinned explicitly. -/
structure OperationDeiterationWitness (input : Concrete.Checked )
    (selection : Concrete.CheckedSelection input.val) where
  justifier : Concrete.CheckedSelection input.val
  ancestor : input.val.Encloses justifier.val.anchor selection.val.anchor
  sameAttachments : justifier.touchingWires = selection.touchingWires
  sameExternalBinders :
    (selectedLayout input justifier).externalBinders =
      (selectedLayout input selection).externalBinders
  occurrence : Concrete.OpenOccurrenceEquiv
    (selectedFragment input justifier) (selectedFragment input selection)
  proxy_alignment : ∀ index,
    occurrence.diagram.regions (selectedProxy input justifier index) =
      selectedProxy input selection
        (Fin.cast (congrArg List.length sameExternalBinders) index)
  regions_disjoint : ∀ region,
    region ∈ justifier.selectedRegions → region ∉ selection.selectedRegions
  nodes_disjoint : ∀ node,
    node ∈ justifier.selectedNodes → node ∉ selection.selectedNodes
  internalWires_disjoint : ∀ wire,
    wire ∈ justifier.internalWires → wire ∉ selection.internalWires

/--
One abstraction occurrence together with a concrete diagonalized relation and
an intrinsic proof that it is exactly capture-avoiding boundary substitution
of the supplied comprehension.
-/
structure OperationAbstractionWitness (input : Concrete.Checked )
    (comprehension : Concrete.CheckedOpen )
    (occurrenceData : OperationAbstractionOccurrence input) where
  args_length : occurrenceData.args.length = comprehension.val.boundary.length
  assignment : Diagram.BoundaryAssignment comprehension.elaborate
    (Fin occurrenceData.selection.touchingWires.length)
  argument_alignment : ∀ index,
    occurrenceData.selection.touchingWires.get (assignment.args index) =
      occurrenceData.args.get (Fin.cast args_length.symm index)
  all_touching_used : Function.Surjective assignment.args
  diagonal : Concrete.CheckedOpen
  diagonal_boundary_length : diagonal.val.boundary.length =
    occurrenceData.selection.touchingWires.length
  diagonal_externalClasses : diagonal.elaborate.externalClasses =
    occurrenceData.selection.touchingWires.length
  diagonal_boundary_identity : ∀ index,
    Fin.cast diagonal_externalClasses
        (diagonal.elaborate.boundary
          (Fin.cast diagonal_boundary_length.symm index)) = index
  diagonal_body_eq :
    diagonal.elaborate.body.castWiresEq diagonal_externalClasses =
      comprehension.elaborate.substituteBoundary assignment
  externalBinders_empty : occurrenceData.selection.externalBinders = []
  exactOccurrence : Concrete.OpenIso
    (selectedFragment input occurrenceData.selection) diagonal.val

structure OperationComprehensionAbstractPayload
    (input : Concrete.Checked )
    (wrap : Concrete.CheckedSelection input.val)
    (comprehension : Concrete.CheckedOpen )
    (occurrences : List (OperationAbstractionOccurrence input)) where
  witnesses : ∀ index : Fin occurrences.length,
    OperationAbstractionWitness input comprehension (occurrences.get index)
  anchors_inside : ∀ index : Fin occurrences.length,
    let occurrence := occurrences.get index
    occurrence.selection.val.anchor = wrap.val.anchor ∨
      occurrence.selection.val.anchor ∈ wrap.selectedRegions
  nodes_inside : ∀ index : Fin occurrences.length, ∀ node,
    node ∈ (occurrences.get index).selection.selectedNodes →
      node ∈ wrap.selectedNodes
  regions_inside : ∀ index : Fin occurrences.length, ∀ region,
    region ∈ (occurrences.get index).selection.selectedRegions →
      region ∈ wrap.selectedRegions
  nodes_disjoint : ∀ left right : Fin occurrences.length, left ≠ right →
    ∀ node, node ∈ (occurrences.get left).selection.selectedNodes →
      node ∉ (occurrences.get right).selection.selectedNodes
  regions_disjoint : ∀ left right : Fin occurrences.length, left ≠ right →
    ∀ region, region ∈ (occurrences.get left).selection.selectedRegions →
      region ∉ (occurrences.get right).selection.selectedRegions
  wires_disjoint : ∀ left right : Fin occurrences.length, left ≠ right →
    ∀ wire, wire ∈ (occurrences.get left).selection.internalWires →
      wire ∉ (occurrences.get right).selection.internalWires
  anchors_not_nested : ∀ left right : Fin occurrences.length, left ≠ right →
    (occurrences.get left).selection.val.anchor ∉
      (occurrences.get right).selection.selectedRegions

structure OperationComprehensionInstantiatePayload
    (input : Concrete.Checked )
    (bubble : Fin input.val.regionCount)
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount ×
        Fin input.val.regionCount)) where
  parent : Fin input.val.regionCount
  arity : Nat
  bubble_eq : input.val.regions bubble = .bubble parent arity
  boundarySplit : comprehension.val.boundary.length = arity + attachments.length
  parameterScopesProper : ∀ index : Fin attachments.length,
    input.val.Encloses (input.val.wires (attachments.get index)).scope bubble ∧
      (input.val.wires (attachments.get index)).scope ≠ bubble
  binderSpine : Concrete.BinderSpine comprehension.val.diagram
  terminalBody : binderSpine.TerminalBodyContract comprehension.val
  binderTargets : Fin binderSpine.proxyCount → Fin input.val.regionCount
  binderPairsExact : binders = List.ofFn fun index =>
    (binderSpine.proxy index, binderTargets index)
  binderTargetsProper : ∀ index,
    input.val.Encloses (binderTargets index) bubble ∧
      binderTargets index ≠ bubble

end VisualProof.Concrete
