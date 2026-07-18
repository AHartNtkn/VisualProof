import VisualProof.Theory.Semantics
import VisualProof.Diagram.Concrete.Subgraph.Splice
import VisualProof.Lambda.Certificate
import VisualProof.Rule.NamedReference

namespace VisualProof.Rule

private def concreteCutDepthAux (diagram : Diagram.ConcreteDiagram) :
    Nat → Fin diagram.regionCount → Nat
  | 0, _ => 0
  | fuel + 1, region =>
      match diagram.regions region with
      | .sheet => 0
      | .cut parent => concreteCutDepthAux diagram fuel parent + 1
      | .bubble parent _ => concreteCutDepthAux diagram fuel parent

def concreteCutDepth (diagram : Diagram.ConcreteDiagram)
    (region : Fin diagram.regionCount) : Nat :=
  concreteCutDepthAux diagram diagram.regionCount region

private theorem concreteCutDepthAux_route
    (route : Diagram.Splice.RegionRoute diagram start target path)
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
    (diagram : Diagram.ConcreteDiagram) (rootSheet : diagram.RootIsSheet)
    (fuel : Nat) : concreteCutDepthAux diagram fuel diagram.root = 0 := by
  unfold Diagram.ConcreteDiagram.RootIsSheet at rootSheet
  cases fuel with
  | zero => rfl
  | succ fuel => simp [concreteCutDepthAux, rootSheet]

/-- The sheet root is at positive depth zero. -/
theorem concreteCutDepth_root_eq_zero
    (checked : Diagram.CheckedDiagram signature) :
    concreteCutDepth checked.val checked.val.root = 0 := by
  unfold concreteCutDepth
  exact concreteCutDepthAux_root_eq_zero checked.val
    checked.property.root_is_sheet checked.val.regionCount

private theorem concreteCutDepthAux_coalesceFrameRaw
    (input : Diagram.Splice.Input signature) (fuel : Nat)
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
    (input : Diagram.Splice.Input signature)
    (region : Fin input.frame.val.regionCount) :
    concreteCutDepth input.coalesceFrameRaw region =
      concreteCutDepth input.frame.val region := by
  unfold concreteCutDepth
  exact concreteCutDepthAux_coalesceFrameRaw input input.frame.val.regionCount
    region

private theorem concreteCutDepthAux_removeRaw
    (host : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection host.val)
    (domains : Diagram.FrameDomains host.val selection)
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
          have hreindexed := Diagram.ConcreteDiagram.removeRaw_region_reindexed
            host selection domains (domains.regions.index region hsurvives)
          rw [domains.regions.origin_index region hsurvives, hkind] at hreindexed
          have hframe :
              (host.val.removeRaw selection domains).regions
                  (domains.regions.index region hsurvives) = .sheet := by
            simpa [Diagram.SurvivorDomain.reindexRegion?] using
              Option.some.inj hreindexed |>.symm
          simp [concreteCutDepthAux, hkind, hframe]
      | cut parent =>
          have hparent : (host.val.regions region).parent? = some parent := by
            exact (congrArg Diagram.CRegion.parent? hkind).trans rfl
          have hparentSurvives := domains.parent_survives host selection
            hsurvives hparent
          have hreindexed := Diagram.ConcreteDiagram.removeRaw_region_reindexed
            host selection domains (domains.regions.index region hsurvives)
          rw [domains.regions.origin_index region hsurvives, hkind] at hreindexed
          have hframe :
              (host.val.removeRaw selection domains).regions
                  (domains.regions.index region hsurvives) =
                .cut (domains.regions.index parent hparentSurvives) := by
            simp only [Diagram.SurvivorDomain.reindexRegion?,
              domains.regions.index?_index parent hparentSurvives,
              Option.map_some] at hreindexed
            exact (Option.some.inj hreindexed).symm
          simp only [concreteCutDepthAux, hkind, hframe]
          exact congrArg (· + 1) (ih parent hparentSurvives)
      | bubble parent arity =>
          have hparent : (host.val.regions region).parent? = some parent := by
            exact (congrArg Diagram.CRegion.parent? hkind).trans rfl
          have hparentSurvives := domains.parent_survives host selection
            hsurvives hparent
          have hframe := Diagram.ConcreteDiagram.removeRaw_bubble host selection
            domains hsurvives hkind
          simp only [concreteCutDepthAux, hkind, hframe]
          exact ih parent hparentSurvives

theorem siteView_concreteCutDepth_eq
    (view : Diagram.Splice.SiteView checked site) :
    concreteCutDepth checked.val site = view.focus.context.cutDepth := by
  have pathBound : view.path.length ≤ checked.val.regionCount :=
    VisualProof.Diagram.ConcreteElaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
      checked view.route.climb_length
  have routeDepth := concreteCutDepthAux_route view.route view.cutDepth
    (checked.val.regionCount - view.path.length)
  rw [Nat.add_sub_of_le pathBound] at routeDepth
  have rootDepth : concreteCutDepthAux checked.val
      (checked.val.regionCount - view.path.length) checked.val.root = 0 := by
    have rootSheet := checked.property.root_is_sheet
    unfold Diagram.ConcreteDiagram.RootIsSheet at rootSheet
    cases checked.val.regionCount - view.path.length with
    | zero => rfl
    | succ fuel =>
        simp [concreteCutDepthAux, rootSheet]
  simpa [concreteCutDepth, rootDepth] using routeDepth

/-- Removing a checked selection preserves the cut depth of every retained
region.  The compact identifier may change, but every retained parent edge and
its cut/bubble kind is unchanged. -/
theorem concreteCutDepth_removeRaw_index
    (host : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection host.val)
    (domains : Diagram.FrameDomains host.val selection)
    (region : Fin host.val.regionCount)
    (hsurvives : domains.regions.survives region = true) :
    concreteCutDepth (host.val.removeRaw selection domains)
        (domains.regions.index region hsurvives) =
      concreteCutDepth host.val region := by
  let view := Classical.choice (Diagram.Splice.siteView_complete host region)
  have pathBound : view.path.length ≤ domains.regions.count := by
    have hlt := Diagram.ConcreteDiagram.removeRaw_climb_to_root_steps_lt_regionCount
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
theorem Diagram.Splice.Decomposition.originalSite_concreteCutDepth_eq
    (decomposition : Diagram.Decomposition signature host selection) :
    concreteCutDepth
        (host.val.removeRaw selection decomposition.frameDomains)
        (Diagram.Splice.Decomposition.originalSite decomposition) =
      concreteCutDepth host.val selection.val.anchor := by
  unfold Diagram.Splice.Decomposition.originalSite
  apply concreteCutDepth_removeRaw_index

theorem openSiteView_concreteCutDepth_eq
    (view : Diagram.Splice.OpenSiteView checked site) :
    concreteCutDepth checked.val.diagram site =
      view.focus.context.cutDepth := by
  let closed : Diagram.CheckedDiagram _ :=
    ⟨checked.val.diagram, checked.property.diagram_well_formed⟩
  have pathBound : view.path.length ≤ checked.val.diagram.regionCount :=
    VisualProof.Diagram.ConcreteElaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
      closed view.route.climb_length
  have routeDepth := concreteCutDepthAux_route view.route view.cutDepth
    (checked.val.diagram.regionCount - view.path.length)
  rw [Nat.add_sub_of_le pathBound] at routeDepth
  have rootDepth : concreteCutDepthAux checked.val.diagram
      (checked.val.diagram.regionCount - view.path.length)
      checked.val.diagram.root = 0 := by
    have rootSheet := checked.property.diagram_well_formed.root_is_sheet
    unfold Diagram.ConcreteDiagram.RootIsSheet at rootSheet
    cases checked.val.diagram.regionCount - view.path.length with
    | zero => rfl
    | succ fuel => simp [concreteCutDepthAux, rootSheet]
  simpa [concreteCutDepth, rootDepth] using routeDepth

private theorem binderProxy_concreteCutDepthAux_eq_zero
    (pattern : Diagram.CheckedOpenDiagram signature)
    (spine : Diagram.BinderSpine pattern.val.diagram)
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
    (pattern : Diagram.CheckedOpenDiagram signature)
    (spine : Diagram.BinderSpine pattern.val.diagram) :
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
    (input : Diagram.Splice.Input signature)
    (view : Diagram.Splice.OpenSiteView input.pattern
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
  | openTermSpawn
  | relationSpawn
  | boundRelationSpawn
  | wireJoin
  | erasure
  | wireSever
  | iteration
  | deiteration
  | doubleCutIntro
  | doubleCutElim
  | conversion
  | congruenceJoin
  | anchoredWireSplit
  | anchoredWireContract
  | headStrip
  | closedTermIntro
  | fusion
  | fission
  | comprehensionInstantiate
  | comprehensionAbstract
  | theorem
  | vacuousIntro
  | vacuousElim
  | relUnfold
  | relFold
  deriving DecidableEq, Repr

def StepTag.all : List StepTag :=
  [.openTermSpawn, .relationSpawn, .boundRelationSpawn, .wireJoin,
    .erasure, .wireSever, .iteration, .deiteration,
    .doubleCutIntro, .doubleCutElim, .conversion, .congruenceJoin,
    .anchoredWireSplit, .anchoredWireContract, .headStrip, .closedTermIntro,
    .fusion, .fission, .comprehensionInstantiate, .comprehensionAbstract,
    .theorem, .vacuousIntro, .vacuousElim, .relUnfold, .relFold]

theorem StepTag.all_length : StepTag.all.length = 25 := by
  native_decide

theorem StepTag.all_nodup : StepTag.all.Nodup := by
  native_decide

theorem StepTag.mem_all (tag : StepTag) : tag ∈ StepTag.all := by
  cases tag <;> native_decide

inductive SemanticMode
  | directed
  | equivalent
  deriving DecidableEq, Repr

/-- Whether a rule is genuinely one-way or a polarity-blind equivalence. -/
def StepTag.semanticMode : StepTag → SemanticMode
  | .openTermSpawn | .relationSpawn | .boundRelationSpawn | .wireJoin
  | .erasure | .wireSever | .comprehensionInstantiate
  | .comprehensionAbstract | .headStrip | .theorem => .directed
  | .iteration | .deiteration | .doubleCutIntro | .doubleCutElim
  | .conversion | .congruenceJoin | .anchoredWireSplit
  | .anchoredWireContract | .closedTermIntro
  | .fusion | .fission | .vacuousIntro | .vacuousElim
  | .relUnfold | .relFold => .equivalent

def DirectedImplication (orientation : Orientation)
    (before after : Prop) : Prop :=
  match orientation with
  | .forward => before → after
  | .backward => after → before

def DirectedEntailment (tag : StepTag) (orientation : Orientation)
    (before after : Prop) : Prop :=
  match tag.semanticMode with
  | .directed => DirectedImplication orientation before after
  | .equivalent => before ↔ after

inductive StepError
  | invalidRegion
  | invalidNode
  | invalidWire
  | invalidSelection
  | wrongPolarity
  | incomparableScopes
  | binderEscape
  | arityMismatch
  | invalidCertificate
  | occurrenceMismatch
  | boundaryMismatch
  | nonVacuousBinder
  | openTermRequired
  | unknownDefinition
  | unknownTheorem
  | binderKindOrArityMismatch
  | binderDoesNotEnclose
  | selfWire
  | resultNotWellFormed (error : Diagram.WFError)
  | operationRejected
  deriving DecidableEq

/-- Provenance of source wire identities through one concrete transformation.
`none` means that the source identity was deleted. -/
structure WireProvenance (source target : Diagram.ConcreteDiagram) where
  image? : Fin source.wireCount → Option (Fin target.wireCount)
  image_injective : ∀ {left right mapped},
    image? left = some mapped → image? right = some mapped → left = right
  root_scoped : ∀ {wire mapped}, image? wire = some mapped →
    (source.wires wire).scope = source.root →
      (target.wires mapped).scope = target.root

namespace WireProvenance

def identity (diagram : Diagram.ConcreteDiagram) :
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
def rootFiltered (source target : Diagram.ConcreteDiagram)
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

/-- Preserve every dense wire position when an operation changes no wire
identities. Root filtering still rejects a wire that the operation moved under
a binder, so this constructor cannot manufacture open-boundary survival. -/
def byWireCount (source target : Diagram.ConcreteDiagram)
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
def append (source target : Diagram.ConcreteDiagram) (added : Nat)
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
def survivors (source target : Diagram.ConcreteDiagram)
    (domain : Diagram.SurvivorDomain source.wireCount)
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
structure InterfaceTransport (source target : Diagram.ConcreteDiagram) where
  image? : Fin source.wireCount → Option (Fin target.wireCount)
  root_scoped : ∀ {wire mapped}, image? wire = some mapped →
    (source.wires wire).scope = source.root →
      (target.wires mapped).scope = target.root

namespace InterfaceTransport

def identity (diagram : Diagram.ConcreteDiagram) :
    InterfaceTransport diagram diagram where
  image? wire := some wire
  root_scoped := by
    intro wire mapped himage hroot
    simp only [Option.some.injEq] at himage
    subst mapped
    exact hroot

def compose (first : InterfaceTransport source middle)
    (second : InterfaceTransport middle target) :
    InterfaceTransport source target where
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
def rootFiltered (source target : Diagram.ConcreteDiagram)
    (candidate : Fin source.wireCount → Option (Fin target.wireCount)) :
    InterfaceTransport source target where
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
def castTarget (transport : InterfaceTransport source target)
    (targetEq : target = replacement) :
    InterfaceTransport source replacement := by
  subst replacement
  exact transport

/-- Use graph provenance as a logical transport when no additional
coalescence is intended. -/
def ofProvenance (provenance : WireProvenance source target) :
    InterfaceTransport source target where
  image? := provenance.image?
  root_scoped := provenance.root_scoped

/-- Preserve every dense wire position when an operation changes no wire
identities, while refusing any source wire whose target is not root-scoped. -/
def byWireCount (source target : Diagram.ConcreteDiagram)
    (wireCountEq : source.wireCount = target.wireCount) :
    InterfaceTransport source target :=
  rootFiltered source target (fun wire => some (Fin.cast wireCountEq wire))

/-- Preserve the old wire prefix when an operation only appends fresh wire
identities. -/
def append (source target : Diagram.ConcreteDiagram) (added : Nat)
    (wireCountEq : target.wireCount = source.wireCount + added) :
    InterfaceTransport source target :=
  rootFiltered source target
    (fun wire => some (Fin.cast wireCountEq.symm (Fin.castAdd added wire)))

/-- Preserve precisely the identities selected by a survivor domain. -/
def survivors (source target : Diagram.ConcreteDiagram)
    (domain : Diagram.SurvivorDomain source.wireCount)
    (wireCountEq : target.wireCount = domain.count) :
    InterfaceTransport source target :=
  rootFiltered source target
    (fun wire => (domain.index? wire).map (Fin.cast wireCountEq.symm))

/-- Transport an ordered boundary, failing exactly when one position has no
designated image. Repeated positions remain repeated, and distinct positions
may become aliases when their source wires coalesce. -/
def transportBoundary (transport : InterfaceTransport source target) :
    List (Fin source.wireCount) → Option (List (Fin target.wireCount))
  | [] => some []
  | wire :: rest => do
      let mapped ← transport.image? wire
      let mappedRest ← transport.transportBoundary rest
      pure (mapped :: mappedRest)

theorem transportBoundary_compose
    (first : InterfaceTransport source middle)
    (second : InterfaceTransport middle target)
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
      | none => simp [hfirst]
      | some middleWire =>
          cases hrest : first.transportBoundary rest with
          | none => simp [hfirst, hrest]
          | some intermediate =>
              cases hsecond : second.image? middleWire <;>
                simp [hfirst, hrest, hsecond, transportBoundary]

theorem transportBoundary_compose_iff
    (first : InterfaceTransport source middle)
    (second : InterfaceTransport middle target)
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
    (transport : InterfaceTransport source target)
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
    (transport : InterfaceTransport source target)
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
    (transport : InterfaceTransport source target)
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
    (transport : InterfaceTransport source target)
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
    (transport : InterfaceTransport source target)
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

end InterfaceTransport

/-- A checked proof state with an ordered, possibly aliased open boundary. -/
structure OpenProofState (signature : List Nat) where
  diagram : Diagram.CheckedDiagram signature
  boundary : List (Fin diagram.val.wireCount)
  boundary_root_scoped : ∀ wire, wire ∈ boundary →
    (diagram.val.wires wire).scope = diagram.val.root

def OpenProofState.closed (diagram : Diagram.CheckedDiagram signature) :
    OpenProofState signature where
  diagram := diagram
  boundary := []
  boundary_root_scoped := by simp

def OpenProofState.asCheckedOpen (state : OpenProofState signature) :
    Diagram.CheckedOpenDiagram signature := ⟨{
  diagram := state.diagram.val
  boundary := state.boundary
}, {
  diagram_well_formed := state.diagram.property
  boundary_is_root_scoped := state.boundary_root_scoped
}⟩

def OpenProofState.denote (state : OpenProofState signature)
    (model : Lambda.LambdaModel)
    (named : Diagram.NamedEnv model.Carrier signature)
    (args : Fin state.boundary.length → model.Carrier) : Prop :=
  state.asCheckedOpen.denote model named args

/-- Canonical successful-step receipt. Graph identity provenance and logical
open-interface transport are separate authorities: the former is injective,
while the latter may record semantically intentional coalescence. -/
structure StepReceipt (input : Diagram.CheckedDiagram signature) where
  result : Diagram.CheckedDiagram signature
  provenance : WireProvenance input.val result.val
  interface : InterfaceTransport input.val result.val

def StepReceipt.ofChecked
    (input : Diagram.CheckedDiagram signature) (raw : Diagram.ConcreteDiagram)
    (provenance : WireProvenance input.val raw)
    (interface : InterfaceTransport input.val raw)
    (result : Diagram.CheckedDiagram signature)
    (hcheck : Diagram.checkWellFormed signature raw = .ok result) :
    StepReceipt input where
  result := result
  provenance := provenance.castTarget
    (Diagram.checkWellFormed_preserves_input hcheck).symm
  interface := interface.castTarget
    (Diagram.checkWellFormed_preserves_input hcheck).symm

/-- A receipt realizes one exact raw transformation and both of its wire
authorities. Each map is compared pointwise after casting the checked result's
target indices to the exact raw result. -/
structure StepReceipt.Realizes
    (receipt : StepReceipt input) (raw : Diagram.ConcreteDiagram)
    (expectedProvenance : WireProvenance input.val raw)
    (expectedInterface : InterfaceTransport input.val raw) : Prop where
  result_eq : receipt.result.val = raw
  provenance_image_eq : ∀ wire,
    Option.map (Fin.cast (congrArg Diagram.ConcreteDiagram.wireCount result_eq))
        (receipt.provenance.image? wire) =
      expectedProvenance.image? wire
  interface_image_eq : ∀ wire,
    Option.map (Fin.cast (congrArg Diagram.ConcreteDiagram.wireCount result_eq))
        (receipt.interface.image? wire) =
      expectedInterface.image? wire

theorem StepReceipt.ofChecked_realizes
    (input : Diagram.CheckedDiagram signature) (raw : Diagram.ConcreteDiagram)
    (expectedProvenance : WireProvenance input.val raw)
    (expectedInterface : InterfaceTransport input.val raw)
    (result : Diagram.CheckedDiagram signature)
    (hcheck : Diagram.checkWellFormed signature raw = .ok result) :
    (StepReceipt.ofChecked input raw expectedProvenance expectedInterface result
      hcheck).Realizes raw expectedProvenance expectedInterface := by
  have hresult := Diagram.checkWellFormed_preserves_input hcheck
  cases hresult
  refine ⟨rfl, ?_, ?_⟩
  · intro wire
    simp [StepReceipt.ofChecked, WireProvenance.castTarget]
  · intro wire
    simp [StepReceipt.ofChecked, InterfaceTransport.castTarget]

namespace StepReceipt.Realizes

def targetWire
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface) :
    Fin receipt.result.val.wireCount → Fin raw.wireCount :=
  Fin.cast (congrArg Diagram.ConcreteDiagram.wireCount realizes.result_eq)

def targetBoundary
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    List (Fin raw.wireCount) :=
  mapped.map realizes.targetWire

theorem expected_provenance_image_eq_some
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {wire : Fin input.val.wireCount}
    {mapped : Fin receipt.result.val.wireCount}
    (himage : receipt.provenance.image? wire = some mapped) :
    expectedProvenance.image? wire = some (realizes.targetWire mapped) := by
  rw [← realizes.provenance_image_eq wire, himage]
  rfl

theorem expected_interface_image_eq_some
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
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
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {mapped : List (Fin receipt.result.val.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    expectedInterface.transportBoundary boundary =
      some (realizes.targetBoundary mapped) := by
  induction boundary generalizing mapped with
  | nil =>
      simp [InterfaceTransport.transportBoundary] at htransport
      subst mapped
      rfl
  | cons wire rest ih =>
      cases hwire : receipt.interface.image? wire with
      | none =>
          simp [InterfaceTransport.transportBoundary, hwire] at htransport
      | some mappedWire =>
          cases hrest : receipt.interface.transportBoundary rest with
          | none =>
              simp [InterfaceTransport.transportBoundary, hwire, hrest] at htransport
          | some mappedRest =>
              simp [InterfaceTransport.transportBoundary, hwire, hrest] at htransport
              subst mapped
              rw [InterfaceTransport.transportBoundary,
                realizes.expected_interface_image_eq_some hwire, ih hrest]
              rfl

/-- Completeness of receipt-side ordered transport for a realized operation.
If the exact operation transports every requested position, the checked
receipt does too.  This is the inverse existence direction to
`transportBoundary_expected`; it preserves order and repeated positions. -/
theorem transportBoundary_receipt_complete
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {rawMapped : List (Fin raw.wireCount)}
    (hexpected : expectedInterface.transportBoundary boundary = some rawMapped) :
    ∃ mapped, receipt.interface.transportBoundary boundary = some mapped := by
  induction boundary generalizing rawMapped with
  | nil =>
      simp [InterfaceTransport.transportBoundary] at hexpected
      exact ⟨[], rfl⟩
  | cons wire rest ih =>
      cases hexactWire : expectedInterface.image? wire with
      | none =>
          simp [InterfaceTransport.transportBoundary, hexactWire] at hexpected
      | some exactWire =>
          cases hexactRest : expectedInterface.transportBoundary rest with
          | none =>
              simp [InterfaceTransport.transportBoundary, hexactWire,
                hexactRest] at hexpected
          | some exactRest =>
              simp [InterfaceTransport.transportBoundary, hexactWire,
                hexactRest] at hexpected
              obtain ⟨mappedRest, hmappedRest⟩ := ih hexactRest
              cases hreceiptWire : receipt.interface.image? wire with
              | none =>
                  have halign := realizes.interface_image_eq wire
                  simp [hreceiptWire, hexactWire] at halign
              | some mappedWire =>
                  exact ⟨mappedWire :: mappedRest, by
                    simp [InterfaceTransport.transportBoundary, hreceiptWire,
                      hmappedRest]⟩

/-- The canonical ordered open view of the exact raw result witnessed by a
receipt.  Boundary positions are cast positionwise through `result_eq`; in
particular, repeated aliases remain repeated. -/
def rawResultOpen
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    Diagram.OpenConcreteDiagram where
  diagram := raw
  boundary := realizes.targetBoundary mapped

@[simp] theorem rawResultOpen_boundary_length
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    (realizes.rawResultOpen mapped).boundary.length = mapped.length := by
  simp [rawResultOpen, targetBoundary]

def rawResultOpen_wellFormed
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {mapped : List (Fin receipt.result.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (htransport : receipt.interface.transportBoundary boundary = some mapped) :
    (realizes.rawResultOpen mapped).WellFormed signature where
  diagram_well_formed := by
    change raw.WellFormed signature
    exact realizes.result_eq ▸ receipt.result.property
  boundary_is_root_scoped :=
    expectedInterface.transportBoundary_root_scoped sourceRoot
      (realizes.transportBoundary_expected htransport)

/-- The canonical raw open view and the receipt result are the same ordered
open graph up to the finite casts forced by `result_eq`. -/
def rawResultOpenIso
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    (mapped : List (Fin receipt.result.val.wireCount)) :
    Diagram.OpenConcreteIso (realizes.rawResultOpen mapped) {
      diagram := receipt.result.val
      boundary := mapped
    } := by
  rcases realizes with ⟨hresult, hprovenance, hinterface⟩
  subst raw
  refine {
    diagram := Diagram.ConcreteIso.refl receipt.result.val
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
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
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
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    {mapped : List (Fin receipt.result.val.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped)
    (rawMapped : List (Fin raw.wireCount))
    (hexpected : expectedInterface.transportBoundary boundary = some rawMapped) :
    Diagram.OpenConcreteIso { diagram := raw, boundary := rawMapped }
      (realizes.rawResultOpen mapped) := by
  refine {
    diagram := Diagram.ConcreteIso.refl raw
    boundary := ?_
  }
  have hmapped : rawMapped = realizes.targetBoundary mapped :=
    realizes.expectedMapped_eq_targetBoundary htransport hexpected
  change rawMapped.map (Diagram.ConcreteIso.refl raw).wires =
    realizes.targetBoundary mapped
  rw [hmapped]
  simp [Diagram.ConcreteIso.refl, Diagram.FiniteEquiv.refl]

/-- Normalize any checked operational open view of a realized raw result to
the exact ordered target used by boundary-parametric receipt soundness.  The
operational isomorphism must preserve the boundary list, so order and repeated
aliases survive unchanged. -/
theorem operationalOpen_denote_iff_result
    {signature : List Nat} {input : Diagram.CheckedDiagram signature}
    {receipt : StepReceipt input} {raw : Diagram.ConcreteDiagram}
    {expectedProvenance : WireProvenance input.val raw}
    {expectedInterface : InterfaceTransport input.val raw}
    (realizes : StepReceipt.Realizes receipt raw expectedProvenance
      expectedInterface)
    {boundary : List (Fin input.val.wireCount)}
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    {mapped : List (Fin receipt.result.val.wireCount)}
    (htransport : receipt.interface.transportBoundary boundary = some mapped)
    (operational : Diagram.CheckedOpenDiagram signature)
    (operationalIso : Diagram.OpenConcreteIso operational.val
      (realizes.rawResultOpen mapped))
    (model : Lambda.LambdaModel)
    (named : Diagram.NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    let target : OpenProofState signature := {
      diagram := receipt.result
      boundary := mapped
      boundary_root_scoped :=
        receipt.interface.transportBoundary_root_scoped sourceRoot htransport
    }
    let totalIso := operationalIso.trans (realizes.rawResultOpenIso mapped)
    operational.denote model named
        (args ∘ Fin.cast (totalIso.boundary_length_eq.trans
          (receipt.interface.transportBoundary_length htransport))) ↔
      target.denote model named
        (args ∘ Fin.cast
          (receipt.interface.transportBoundary_length htransport)) := by
  dsimp only
  let target : OpenProofState signature := {
    diagram := receipt.result
    boundary := mapped
    boundary_root_scoped :=
      receipt.interface.transportBoundary_root_scoped sourceRoot htransport
  }
  let totalIso := operationalIso.trans (realizes.rawResultOpenIso mapped)
  let sourceArgs := args ∘ Fin.cast (totalIso.boundary_length_eq.trans
    (receipt.interface.transportBoundary_length htransport))
  let targetArgs := args ∘ Fin.cast
    (receipt.interface.transportBoundary_length htransport)
  have hargs : sourceArgs ∘ Fin.cast totalIso.boundary_length_eq.symm =
      targetArgs := by
    funext index
    apply congrArg args
    rfl
  have hdenote := totalIso.denote_iff operational.property
    target.asCheckedOpen.property model named sourceArgs
  change operational.denote model named sourceArgs ↔
    target.asCheckedOpen.denote model named targetArgs
  rw [← hargs]
  exact hdenote

end StepReceipt.Realizes

def StepReceipt.transportOpen {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    (receipt : StepReceipt input)
    (boundary : List (Fin input.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    Option (OpenProofState signature) :=
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
theorem StepReceipt.transportOpen_result {signature : List Nat}
    {input : Diagram.CheckedDiagram signature}
    (receipt : StepReceipt input)
    (boundary : List (Fin input.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (result : OpenProofState signature)
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
  unfold StepReceipt.transportOpen at hopen
  split at hopen
  · contradiction
  · rename_i mapped htransport
    cases hopen
    exact ⟨mapped, htransport, rfl⟩

inductive Direction
  | forward
  | reverse
  deriving DecidableEq, Repr

structure TheoremSchema (signature : List Nat) where
  left : Diagram.CheckedOpenDiagram signature
  right : Diagram.CheckedOpenDiagram signature
  sameBoundaryArity : left.val.boundary.length = right.val.boundary.length

structure ProofContext (signature : List Nat) where
  definitions : Theory.VerifiedDefinitions signature
  theorems : List (TheoremSchema signature)

def ProofContext.definitionEntry (context : ProofContext signature)
    (index : Fin signature.length) : Theory.DefinitionEntry signature index :=
  context.definitions.entry index

def ProofContext.definition? (context : ProofContext signature) (index : Nat) :
    Option (Diagram.CheckedOpenDiagram signature) :=
  if h : index < signature.length then
    some (context.definitionEntry ⟨index, h⟩).body
  else none

theorem ProofContext.definition?_eq_some
    (context : ProofContext signature) (index : Fin signature.length) :
    context.definition? index.val = some (context.definitionEntry index).body := by
  simp [ProofContext.definition?, index.isLt]

structure AbstractionOccurrence (input : Diagram.CheckedDiagram signature) where
  selection : Diagram.CheckedSelection input.val
  args : List (Fin input.val.wireCount)

private def selectedLayout (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val) :
    Diagram.FragmentLayout input.val selection := {}

def selectedFragment (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val) :
    Diagram.OpenConcreteDiagram :=
  input.val.extractOpenRaw selection (selectedLayout input selection)

theorem selectedFragment_wellFormed
    (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val) :
    (selectedFragment input selection).WellFormed signature :=
  Diagram.ConcreteDiagram.extractOpenRaw_wellFormed input selection
    (selectedLayout input selection)

def pinnedSelectedFragment (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val) (arity : Nat)
    (position : Fin arity →
      Fin selection.touchingWires.length) : Diagram.OpenConcreteDiagram where
  diagram := (selectedFragment input selection).diagram
  boundary := List.ofFn fun index =>
    (selectedLayout input selection).boundaryWire (position index)

/-- The pinned selected fragment is independent of the private choice of
fragment-layout witness: a checked selection determines that layout uniquely. -/
theorem pinnedSelectedFragment_eq_extractOpenRaw
    (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val) (arity : Nat)
    (position : Fin arity → Fin selection.touchingWires.length)
    (layout : Diagram.FragmentLayout input.val selection) :
    pinnedSelectedFragment input selection arity position = {
      diagram := (input.val.extractOpenRaw selection layout).diagram
      boundary := List.ofFn fun index => layout.boundaryWire (position index)
    } := by
  unfold pinnedSelectedFragment selectedFragment
  rw [Diagram.FragmentLayout.unique (selectedLayout input selection) layout]

theorem pinnedSelectedFragment_wellFormed
    (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val) (arity : Nat)
    (position : Fin arity → Fin selection.touchingWires.length) :
    (pinnedSelectedFragment input selection arity position).WellFormed signature where
  diagram_well_formed :=
    Diagram.ConcreteDiagram.extractDiagramRaw_wellFormed input selection
      (selectedLayout input selection)
  boundary_is_root_scoped := by
    intro wire hwire
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hwire
    apply input.val.extractBoundaryRaw_root_scoped selection
      (selectedLayout input selection)
    simp [Diagram.ConcreteDiagram.extractBoundaryRaw]

/-- The canonical declaration that an ordinary open diagram has no proxy prefix. -/
def emptyBinderSpine (pattern : Diagram.CheckedOpenDiagram signature) :
    Diagram.BinderSpine pattern.val.diagram where
  proxyCount := 0
  proxy := nofun
  arity := nofun
  bodyContainer := pattern.val.diagram.root
  proxy_injective := fun index => Fin.elim0 index
  proxy_ne_root := fun index => Fin.elim0 index
  body_eq_root_of_empty := fun _ => rfl
  body_eq_terminal_of_nonempty := fun h => False.elim (h rfl)
  proxy_region := fun index => Fin.elim0 index

def emptyTerminalBody (pattern : Diagram.CheckedOpenDiagram signature) :
    (emptyBinderSpine pattern).TerminalBodyContract pattern.val where
  root_direct_child := fun h => False.elim (h rfl)
  nonterminal_direct_child := fun index => Fin.elim0 index
  root_has_no_nodes := fun h => False.elim (h rfl)
  nonterminal_has_no_nodes := fun index => Fin.elim0 index
  root_has_no_nonboundary_wires := fun h => False.elim (h rfl)
  nonterminal_has_no_nonboundary_wires := fun index => Fin.elim0 index
  boundary_is_root_scoped := pattern.property.boundary_is_root_scoped

private def selectedProxy (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (index : Fin (selectedLayout input selection).proxyCount) :
    Fin (selectedFragment input selection).diagram.regionCount :=
  (selectedLayout input selection).proxy index

/--
A matcher-independent certificate that another, disjoint certified occurrence
justifies deiteration. The matcher constructs this value; the rule layer
does not contain a competing search procedure. Boundary order, repeated
aliases, and external binder identities are pinned explicitly.
-/
structure DeiterationWitness (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val) where
  justifier : Diagram.CheckedSelection input.val
  ancestor : input.val.Encloses justifier.val.anchor selection.val.anchor
  sameAttachments : justifier.touchingWires = selection.touchingWires
  sameExternalBinders :
    (selectedLayout input justifier).externalBinders =
      (selectedLayout input selection).externalBinders
  occurrence : Diagram.OpenOccurrenceEquiv
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
An exact occurrence whose boundary positions are pinned to a caller-supplied
host argument list. `position` may repeat, so intrinsic boundary aliases are
represented without inventing new host wires; surjectivity prevents silently
discarding a crossing wire.
-/
structure PinnedOccurrence (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (pattern : Diagram.CheckedOpenDiagram signature)
    (args : List (Fin input.val.wireCount)) where
  args_length : args.length = pattern.val.boundary.length
  position : Fin pattern.val.boundary.length →
    Fin selection.touchingWires.length
  argument_alignment : ∀ index,
    selection.touchingWires.get (position index) =
      args.get (Fin.cast args_length.symm index)
  all_touching_used : Function.Surjective position
  externalBinders_empty : selection.externalBinders = []
  occurrence : Diagram.OpenConcreteIso
    (pinnedSelectedFragment input selection pattern.val.boundary.length position)
    pattern.val

/--
One abstraction occurrence together with a concrete diagonalized relation and
an intrinsic proof that it is exactly capture-avoiding boundary substitution
of the supplied comprehension.
-/
structure AbstractionWitness (input : Diagram.CheckedDiagram signature)
    (comprehension : Diagram.CheckedOpenDiagram signature)
    (occurrenceData : AbstractionOccurrence input) where
  args_length : occurrenceData.args.length = comprehension.val.boundary.length
  assignment : Diagram.BoundaryAssignment comprehension.elaborate
    (Fin occurrenceData.selection.touchingWires.length)
  argument_alignment : ∀ index,
    occurrenceData.selection.touchingWires.get (assignment.args index) =
      occurrenceData.args.get (Fin.cast args_length.symm index)
  all_touching_used : Function.Surjective assignment.args
  diagonal : Diagram.CheckedOpenDiagram signature
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
  exactOccurrence : Diagram.OpenConcreteIso
    (selectedFragment input occurrenceData.selection) diagonal.val

structure ComprehensionAbstractPayload
    (input : Diagram.CheckedDiagram signature)
    (wrap : Diagram.CheckedSelection input.val)
    (comprehension : Diagram.CheckedOpenDiagram signature)
    (occurrences : List (AbstractionOccurrence input)) where
  witnesses : ∀ index : Fin occurrences.length,
    AbstractionWitness input comprehension (occurrences.get index)
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

structure ComprehensionInstantiatePayload
    (input : Diagram.CheckedDiagram signature)
    (bubble : Fin input.val.regionCount)
    (comprehension : Diagram.CheckedOpenDiagram signature)
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
  binderSpine : Diagram.BinderSpine comprehension.val.diagram
  terminalBody : binderSpine.TerminalBodyContract comprehension.val
  binderTargets : Fin binderSpine.proxyCount → Fin input.val.regionCount
  binderPairsExact : binders = List.ofFn fun index =>
    (binderSpine.proxy index, binderTargets index)
  binderTargetsProper : ∀ index,
    input.val.Encloses (binderTargets index) bubble ∧
      binderTargets index ≠ bubble

structure ConversionPayload (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount) where
  region : Fin input.val.regionCount
  oldFreePorts : Nat
  oldTerm : Lambda.Term 0 (Fin oldFreePorts)
  node_eq : input.val.nodes node = .term region oldFreePorts oldTerm
  newFreePorts : Nat
  newTerm : Lambda.Term 0 (Fin newFreePorts)
  commonPorts : Nat
  oldPort : Fin oldFreePorts → Fin commonPorts
  newPort : Fin newFreePorts → Fin commonPorts
  oldPort_injective : Function.Injective oldPort
  newPort_injective : Function.Injective newPort
  commonPorts_covered : ∀ common,
    (∃ old, oldPort old = common) ∨ (∃ new, newPort new = common)
  certificate : Lambda.Certificate
  certificate_valid : Lambda.checkCertificate
    (oldTerm.mapFree oldPort) (newTerm.mapFree newPort) certificate = true
  attachments : List (Fin newFreePorts × Fin input.val.wireCount)
  attachments_functional : ∀ port first second,
    (port, first) ∈ attachments → (port, second) ∈ attachments → first = second
  attachments_new_only : ∀ port wire,
    (port, wire) ∈ attachments →
      ¬ ∃ old, oldPort old = newPort port
  attachments_visible : ∀ port wire, (port, wire) ∈ attachments →
    input.val.Encloses (input.val.wires wire).scope region

/-- Proof-bearing refinement of the sound head-strip gate. A free head is not
rigid under arbitrary lambda-model assignments, so both aligned heads must be
the same bound de Bruijn variable. -/
structure HeadStripPayload (input : Diagram.CheckedDiagram signature)
    (first second : Fin input.val.nodeCount) where
  distinct : first ≠ second
  region : Fin input.val.regionCount
  firstFreePorts : Nat
  firstTerm : Lambda.Term 0 (Fin firstFreePorts)
  firstNode : input.val.nodes first = .term region firstFreePorts firstTerm
  secondFreePorts : Nat
  secondTerm : Lambda.Term 0 (Fin secondFreePorts)
  secondNode : input.val.nodes second = .term region secondFreePorts secondTerm
  commonPorts : Nat
  firstPort : Fin firstFreePorts → Fin commonPorts
  secondPort : Fin secondFreePorts → Fin commonPorts
  firstPort_injective : Function.Injective firstPort
  secondPort_injective : Function.Injective secondPort
  commonPorts_covered : ∀ common,
    (∃ first, firstPort first = common) ∨
      (∃ second, secondPort second = common)
  shared_port_alignment : ∀ left right leftWire rightWire,
    firstPort left = secondPort right →
      input.val.EndpointOccurs leftWire { node := first, port := .free left } →
      input.val.EndpointOccurs rightWire { node := second, port := .free right } →
      leftWire = rightWire
  firstOriginalSpine : Lambda.HeadSpine 0 (Fin firstFreePorts)
  secondOriginalSpine : Lambda.HeadSpine 0 (Fin secondFreePorts)
  firstOriginalSpine_eq : Lambda.headSpine firstTerm = some firstOriginalSpine
  secondOriginalSpine_eq : Lambda.headSpine secondTerm = some secondOriginalSpine
  sameBinders : firstOriginalSpine.binders = secondOriginalSpine.binders
  headIndex : Fin firstOriginalSpine.binders
  firstHead : firstOriginalSpine.head = .bound headIndex
  secondHead : secondOriginalSpine.head =
    .bound (Fin.cast sameBinders headIndex)
  sameArgumentCount : firstOriginalSpine.args.length =
    secondOriginalSpine.args.length
  outputWire : Fin input.val.wireCount
  firstOutput : input.val.EndpointOccurs outputWire
    { node := first, port := .output }
  secondOutput : input.val.EndpointOccurs outputWire
    { node := second, port := .output }

def HeadStripPayload.firstSpine
    (payload : HeadStripPayload input first second) :
    Lambda.HeadSpine 0 (Fin payload.commonPorts) :=
  payload.firstOriginalSpine.mapFree payload.firstPort

def HeadStripPayload.secondSpine
    (payload : HeadStripPayload input first second) :
    Lambda.HeadSpine 0 (Fin payload.commonPorts) :=
  payload.secondOriginalSpine.mapFree payload.secondPort

theorem HeadStripPayload.firstSpine_eq
    (payload : HeadStripPayload input first second) :
    Lambda.headSpine (payload.firstTerm.mapFree payload.firstPort) =
      some payload.firstSpine :=
  Lambda.headSpine_mapFree payload.firstOriginalSpine_eq payload.firstPort

theorem HeadStripPayload.secondSpine_eq
    (payload : HeadStripPayload input first second) :
    Lambda.headSpine (payload.secondTerm.mapFree payload.secondPort) =
      some payload.secondSpine :=
  Lambda.headSpine_mapFree payload.secondOriginalSpine_eq payload.secondPort

theorem HeadStripPayload.mappedSameBinders
    (payload : HeadStripPayload input first second) :
    payload.firstSpine.binders = payload.secondSpine.binders :=
  payload.sameBinders

theorem HeadStripPayload.mappedFirstHead
    (payload : HeadStripPayload input first second) :
    payload.firstSpine.head = .bound payload.headIndex := by
  unfold HeadStripPayload.firstSpine
  dsimp only [Lambda.HeadSpine.mapFree]
  rw [payload.firstHead]
  rfl

theorem HeadStripPayload.mappedSecondHead
    (payload : HeadStripPayload input first second) :
    payload.secondSpine.head =
      .bound (Fin.cast payload.mappedSameBinders payload.headIndex) := by
  unfold HeadStripPayload.secondSpine
  dsimp only [Lambda.HeadSpine.mapFree]
  rw [payload.secondHead]
  rfl

theorem HeadStripPayload.mappedSameArgumentCount
    (payload : HeadStripPayload input first second) :
    payload.firstSpine.args.length = payload.secondSpine.args.length := by
  simpa [HeadStripPayload.firstSpine, HeadStripPayload.secondSpine,
    Lambda.HeadSpine.mapFree] using payload.sameArgumentCount

theorem HeadStripPayload.headCorresponds
    (payload : HeadStripPayload input first second) :
    payload.firstSpine.head.Corresponds payload.secondSpine.head := by
  unfold HeadStripPayload.firstSpine HeadStripPayload.secondSpine
  dsimp only [Lambda.HeadSpine.mapFree]
  rw [payload.firstHead, payload.secondHead]
  simp only [Lambda.Head.mapFree]
  exact .bound payload.headIndex.val payload.headIndex.isLt
    (by simpa only [payload.sameBinders] using payload.headIndex.isLt)

structure CongruencePayload (input : Diagram.CheckedDiagram signature)
    (first second : Fin input.val.nodeCount) where
  distinct : first ≠ second
  region : Fin input.val.regionCount
  firstFreePorts : Nat
  firstTerm : Lambda.Term 0 (Fin firstFreePorts)
  firstNode : input.val.nodes first = .term region firstFreePorts firstTerm
  secondFreePorts : Nat
  secondTerm : Lambda.Term 0 (Fin secondFreePorts)
  secondNode : input.val.nodes second = .term region secondFreePorts secondTerm
  commonPorts : Nat
  firstPort : Fin firstFreePorts → Fin commonPorts
  secondPort : Fin secondFreePorts → Fin commonPorts
  firstPort_injective : Function.Injective firstPort
  secondPort_injective : Function.Injective secondPort
  commonPorts_covered : ∀ common,
    (∃ first, firstPort first = common) ∨
      (∃ second, secondPort second = common)
  certificate : Lambda.Certificate
  certificate_valid : Lambda.checkCertificate
    (firstTerm.mapFree firstPort) (secondTerm.mapFree secondPort)
      certificate = true
  shared_port_alignment : ∀ left right leftWire rightWire,
    firstPort left = secondPort right →
      input.val.EndpointOccurs leftWire { node := first, port := .free left } →
      input.val.EndpointOccurs rightWire { node := second, port := .free right } →
      leftWire = rightWire
  firstOutput : Fin input.val.wireCount
  secondOutput : Fin input.val.wireCount
  firstOutput_occurs : input.val.EndpointOccurs firstOutput
    { node := first, port := .output }
  secondOutput_occurs : input.val.EndpointOccurs secondOutput
    { node := second, port := .output }
  outputsDistinct : firstOutput ≠ secondOutput
  firstScopeDepth :
    concreteCutDepth input.val (input.val.wires firstOutput).scope =
      concreteCutDepth input.val region
  secondScopeDepth :
    concreteCutDepth input.val (input.val.wires secondOutput).scope =
      concreteCutDepth input.val region

/-- An exact pinned occurrence of one named-reference node together with the
checked definition body that will replace it. -/
structure RelUnfoldPayload (input : Diagram.CheckedDiagram signature)
    (node : Fin input.val.nodeCount)
    (definition : Fin signature.length) where
  selection : Diagram.CheckedSelection input.val
  args : List (Fin input.val.wireCount)
  occurrence : PinnedOccurrence input selection
    (namedReferencePattern signature definition) args
  selected_node : selection.selectedNodes = [node]
  body : Diagram.CheckedOpenDiagram signature

/-- Exact pinned occurrence of a named relation body, ready to contract. -/
structure RelFoldPayload (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (definition : Nat) (args : List (Fin input.val.wireCount)) where
  body : Diagram.CheckedOpenDiagram signature
  occurrence : PinnedOccurrence input selection body args

/-- Proof-bearing refinement of a cited theorem side at one exact occurrence. -/
structure TheoremPayload (input : Diagram.CheckedDiagram signature)
    (selection : Diagram.CheckedSelection input.val)
    (args : List (Fin input.val.wireCount)) where
  source : Diagram.CheckedOpenDiagram signature
  target : Diagram.CheckedOpenDiagram signature
  sameBoundaryArity : source.val.boundary.length = target.val.boundary.length
  occurrence : PinnedOccurrence input selection source args

def theoremSidesMatch (schema : TheoremSchema signature) (direction : Direction)
    (payload : TheoremPayload input selection args) : Prop :=
  match direction with
  | .forward =>
      payload.source.val = schema.left.val ∧
        payload.target.val = schema.right.val
  | .reverse =>
      payload.source.val = schema.right.val ∧
        payload.target.val = schema.left.val

/--
Proof-bearing refinement of one serialized step against its current input.
Finite references cannot be stale, and selection closure is already validated.
-/
inductive Step (context : ProofContext signature)
    (input : Diagram.CheckedDiagram signature)
  | openTermSpawn (region : Fin input.val.regionCount) (freePorts : Nat)
      (term : Lambda.Term 0 (Fin freePorts))
  | relationSpawn (region : Fin input.val.regionCount)
      (definition arity : Nat)
  | boundRelationSpawn (region binder : Fin input.val.regionCount)
      (arity : Nat)
  | wireJoin (first second : Fin input.val.wireCount)
  | erasure (selection : Diagram.CheckedSelection input.val)
  | wireSever (wire : Fin input.val.wireCount)
      (keep : List (Diagram.CEndpoint input.val.nodeCount))
  | iteration (selection : Diagram.CheckedSelection input.val)
      (target : Fin input.val.regionCount)
  | deiteration (selection : Diagram.CheckedSelection input.val)
      (witness : DeiterationWitness input selection)
  | doubleCutIntro (selection : Diagram.CheckedSelection input.val)
  | doubleCutElim (region : Fin input.val.regionCount)
  | conversion (node : Fin input.val.nodeCount)
      (payload : ConversionPayload input node)
  | congruenceJoin (first second : Fin input.val.nodeCount)
      (payload : CongruencePayload input first second)
  | anchoredWireSplit (wire : Fin input.val.wireCount)
      (witness : Fin input.val.nodeCount)
      (endpoints : List (Diagram.CEndpoint input.val.nodeCount))
      (target : Fin input.val.regionCount)
  | anchoredWireContract (redundant survivor : Fin input.val.nodeCount)
      (certificate : Lambda.Certificate)
  | headStrip (first second : Fin input.val.nodeCount)
      (payload : HeadStripPayload input first second)
  | closedTermIntro (region : Fin input.val.regionCount)
      (term : Lambda.Term 0 (Fin 0))
  | fusion (wire : Fin input.val.wireCount)
  | fission (node : Fin input.val.nodeCount)
      (path : List Lambda.PathSegment)
  | comprehensionInstantiate (bubble : Fin input.val.regionCount)
      (comprehension : Diagram.CheckedOpenDiagram signature)
      (attachments : List (Fin input.val.wireCount))
      (binders : List
        (Fin comprehension.val.diagram.regionCount ×
          Fin input.val.regionCount))
      (payload : ComprehensionInstantiatePayload input bubble comprehension
        attachments binders)
  | comprehensionAbstract (wrap : Diagram.CheckedSelection input.val)
      (comprehension : Diagram.CheckedOpenDiagram signature)
      (occurrences : List (AbstractionOccurrence input))
      (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
  | theorem (theoremIndex : Fin context.theorems.length)
      (selection : Diagram.CheckedSelection input.val)
      (args : List (Fin input.val.wireCount)) (direction : Direction)
      (payload : TheoremPayload input selection args)
      (registered : theoremSidesMatch (context.theorems.get theoremIndex)
        direction payload)
  | vacuousIntro (selection : Diagram.CheckedSelection input.val)
      (arity : Nat)
  | vacuousElim (region : Fin input.val.regionCount)
  | relUnfold (node : Fin input.val.nodeCount)
      (definition : Fin signature.length)
      (payload : RelUnfoldPayload input node definition)
      (body_eq : payload.body.val = (context.definitionEntry definition).body.val)
  | relFold (selection : Diagram.CheckedSelection input.val)
      (definition : Fin signature.length)
      (args : List (Fin input.val.wireCount))
      (payload : RelFoldPayload input selection definition.val args)
      (body_eq : payload.body.val = (context.definitionEntry definition).body.val)

def Step.tag : Step context input → StepTag
  | .openTermSpawn .. => .openTermSpawn
  | .relationSpawn .. => .relationSpawn
  | .boundRelationSpawn .. => .boundRelationSpawn
  | .wireJoin .. => .wireJoin
  | .erasure .. => .erasure
  | .wireSever .. => .wireSever
  | .iteration .. => .iteration
  | .deiteration .. => .deiteration
  | .doubleCutIntro .. => .doubleCutIntro
  | .doubleCutElim .. => .doubleCutElim
  | .conversion .. => .conversion
  | .congruenceJoin .. => .congruenceJoin
  | .anchoredWireSplit .. => .anchoredWireSplit
  | .anchoredWireContract .. => .anchoredWireContract
  | .headStrip .. => .headStrip
  | .closedTermIntro .. => .closedTermIntro
  | .fusion .. => .fusion
  | .fission .. => .fission
  | .comprehensionInstantiate .. => .comprehensionInstantiate
  | .comprehensionAbstract .. => .comprehensionAbstract
  | .theorem .. => .theorem
  | .vacuousIntro .. => .vacuousIntro
  | .vacuousElim .. => .vacuousElim
  | .relUnfold .. => .relUnfold
  | .relFold .. => .relFold

theorem Step.tag_mem_all (step : Step context input) :
    step.tag ∈ StepTag.all := StepTag.mem_all step.tag

end VisualProof.Rule
