import VisualProof.Concrete.Elaboration.Splice

/-! Source-derived context maps for compositional splice elaboration.

The maps in this file mention only the checked splice inputs and successful
source compiler certificates.  In particular, they do not inspect a plug
target or select any target occurrence. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace BinderSpine

private theorem proxy_climb_to_root_aux
    (spine : BinderSpine diagram) (value : Nat) :
    ∀ index : Fin spine.proxyCount, index.val = value →
      diagram.climb (value + 1) (spine.proxy index) = some diagram.root := by
  induction value with
  | zero =>
      intro index valueEq
      simp only [Diagram.climb]
      rw [spine.proxy_region index]
      simp [CRegion.parent?, valueEq]
  | succ value inductionHypothesis =>
      intro index valueEq
      let previous : Fin spine.proxyCount :=
        ⟨index.val - 1, by omega⟩
      have indexPositive : index.val ≠ 0 := by omega
      have parentEq :
          (diagram.regions (spine.proxy index)).parent? =
            some (spine.proxy previous) := by
        rw [spine.proxy_region index]
        simp only [CRegion.parent?]
        simp [indexPositive, previous]
      have previousValue : previous.val = value := by
        simp [previous]
        omega
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
        Diagram.climb, parentEq] using
          inductionHypothesis previous previousValue

/-- Every proxy has the depth prescribed by its position in the spine. -/
theorem proxy_climb_to_root (spine : BinderSpine diagram)
    (index : Fin spine.proxyCount) :
    diagram.climb (index.val + 1) (spine.proxy index) =
      some diagram.root := by
  exact proxy_climb_to_root_aux spine index.val index rfl

private theorem proxy_climb_between_aux
    (spine : BinderSpine diagram) (value : Nat) :
    ∀ source target : Fin spine.proxyCount, source.val = value →
      target.val ≤ source.val →
      diagram.climb (source.val - target.val) (spine.proxy source) =
        some (spine.proxy target) := by
  induction value with
  | zero =>
      intro source target sourceValue targetLe
      have indexEq : source = target := by
        apply Fin.ext
        omega
      subst target
      simp
  | succ value inductionHypothesis =>
      intro source target sourceValue targetLe
      by_cases sameValue : target.val = source.val
      · have indexEq : target = source := Fin.ext sameValue
        subst target
        simp
      · let previous : Fin spine.proxyCount :=
          ⟨source.val - 1, by omega⟩
        have sourcePositive : source.val ≠ 0 := by omega
        have previousValue : previous.val = value := by
          simp [previous]
          omega
        have targetPrevious : target.val ≤ previous.val := by
          simp [previous]
          omega
        have parentEq :
            (diagram.regions (spine.proxy source)).parent? =
              some (spine.proxy previous) := by
          rw [spine.proxy_region source]
          simp only [CRegion.parent?]
          simp [sourcePositive, previous]
        have stepsEq : source.val - target.val =
            (previous.val - target.val) + 1 := by
          simp [previous]
          omega
        rw [stepsEq]
        simp only [Diagram.climb, parentEq]
        exact inductionHypothesis previous target previousValue targetPrevious

/-- Climbing between two ordered proxies subtracts their spine positions. -/
theorem proxy_climb_between (spine : BinderSpine diagram)
    (source target : Fin spine.proxyCount) (targetLe : target.val ≤ source.val) :
    diagram.climb (source.val - target.val) (spine.proxy source) =
      some (spine.proxy target) := by
  exact proxy_climb_between_aux spine source.val source target rfl targetLe

/-- Every bubble enclosing the designated terminal body is one of the
designated proxies, with the proxy's declared arity. -/
theorem enclosing_body_bubble
    (spine : BinderSpine diagram) (wellFormed : diagram.WellFormed)
    {binder parent : Fin diagram.regionCount} {arity : Nat}
    (bubble : diagram.regions binder = .bubble parent arity)
    (encloses : diagram.Encloses binder spine.bodyContainer) :
    ∃ proxy : Fin spine.proxyCount,
      binder = spine.proxy proxy ∧ arity = spine.arity proxy := by
  by_cases empty : spine.proxyCount = 0
  · have bodyEq : spine.bodyContainer = diagram.root :=
      spine.body_eq_root_of_empty empty
    have binderEq : binder = diagram.root :=
      encloses_sheet_eq wellFormed.root_is_sheet (by simpa [bodyEq] using encloses)
    subst binder
    rw [wellFormed.root_is_sheet] at bubble
    contradiction
  · let terminal : Fin spine.proxyCount :=
      ⟨spine.proxyCount - 1, by omega⟩
    have bodyEq : spine.bodyContainer = spine.proxy terminal :=
      spine.body_eq_terminal_of_nonempty empty
    obtain ⟨steps, climbToBinder⟩ := encloses
    have climbFromTerminal :
        diagram.climb steps.val (spine.proxy terminal) = some binder := by
      simpa [bodyEq] using climbToBinder
    obtain ⟨rootSteps, binderToRoot⟩ :=
      wellFormed.all_regions_reach_root binder
    have composedRoot :
        diagram.climb (steps.val + rootSteps.val) (spine.proxy terminal) =
          some diagram.root :=
      climb_add climbFromTerminal binderToRoot
    have terminalRoot := spine.proxy_climb_to_root terminal
    have totalDepth : steps.val + rootSteps.val = terminal.val + 1 :=
      ParentTraversal.climb_to_root_steps_unique diagram
        wellFormed.root_is_sheet composedRoot terminalRoot
    have binderNeRoot : binder ≠ diagram.root := by
      intro binderEq
      subst binder
      rw [wellFormed.root_is_sheet] at bubble
      contradiction
    have rootStepsPositive : 0 < rootSteps.val := by
      apply Nat.pos_of_ne_zero
      intro rootStepsZero
      have : binder = diagram.root := by
        simpa [rootStepsZero, Diagram.climb] using binderToRoot
      exact binderNeRoot this
    have stepsLeTerminal : steps.val ≤ terminal.val := by omega
    let proxy : Fin spine.proxyCount :=
      ⟨terminal.val - steps.val, by
        have terminalBound := terminal.isLt
        omega⟩
    have climbToProxy := spine.proxy_climb_between terminal proxy (by
      simp [proxy])
    have stepCount : terminal.val - proxy.val = steps.val := by
      simp [proxy]
      omega
    rw [stepCount] at climbToProxy
    have binderEq : binder = spine.proxy proxy :=
      Option.some.inj (climbFromTerminal.symm.trans climbToProxy)
    refine ⟨proxy, binderEq, ?_⟩
    have bubbleEq := (spine.proxy_region proxy).symm.trans (by
      simpa [binderEq] using bubble)
    exact (CRegion.bubble.inj bubbleEq).2.symm

end BinderSpine

namespace Splice.Input

namespace PlugLayout

/-- The canonical boundary position chosen for an exposed class names that
class's concrete pattern wire. -/
theorem boundary_get_exposedPosition (layout : PlugLayout input)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.pattern.val.boundary.get (layout.exposedPosition external) =
      input.pattern.val.exposedWires.get external := by
  unfold exposedPosition
  have present :
      (indexOf? input.pattern.val.boundary
        (input.pattern.val.exposedWires.get external)).isSome := by
    rw [indexOf?_isSome_iff]
    exact (OpenDiagram.mem_exposedWires _ _).1 (List.get_mem _ _)
  obtain ⟨position, foundEq⟩ := Option.isSome_iff_exists.mp present
  change input.pattern.val.boundary.get
      ((indexOf? input.pattern.val.boundary
        (input.pattern.val.exposedWires.get external)).get present) = _
  have getEq :
      (indexOf? input.pattern.val.boundary
        (input.pattern.val.exposedWires.get external)).get present = position :=
    Option.get_of_eq_some present foundEq
  rw [getEq]
  exact indexOf?_sound foundEq

private theorem attached_wire_mem
    (layout : PlugLayout input) (admissible : input.Admissible)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (external : Fin input.pattern.val.exposedWires.length) :
    input.attachment (layout.exposedPosition external) ∈ hostContext := by
  exact (hostExact.mem_iff _).2
    (admissible.attachments_visible (layout.exposedPosition external))

/-- The lexical position of one attached exposed pattern class in an exact
complete host-site wire context. -/
noncomputable def attachedWireIndex
    (layout : PlugLayout input) (admissible : input.Admissible)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (external : Fin input.pattern.val.exposedWires.length) :
    Fin hostContext.length :=
  Classical.choose (WireContext.lookup?_complete
    (layout.attached_wire_mem admissible hostContext hostExact external))

theorem attachedWireIndex_lookup
    (layout : PlugLayout input) (admissible : input.Admissible)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (external : Fin input.pattern.val.exposedWires.length) :
    hostContext.lookup?
        (input.attachment (layout.exposedPosition external)) =
      some (layout.attachedWireIndex admissible hostContext hostExact external) :=
  Classical.choose_spec (WireContext.lookup?_complete
    (layout.attached_wire_mem admissible hostContext hostExact external))

theorem attachedWireIndex_get
    (layout : PlugLayout input) (admissible : input.Admissible)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (external : Fin input.pattern.val.exposedWires.length) :
    hostContext[layout.attachedWireIndex admissible hostContext hostExact
        external] =
      input.attachment (layout.exposedPosition external) :=
  WireContext.lookup?_sound
    (layout.attachedWireIndex_lookup admissible hostContext hostExact external)

end PlugLayout

end Splice.Input

namespace Splice.Input.CompiledMaterial

/-- The exposed pattern class corresponding to one inherited terminal-body
wire position. -/
def spliceWireExternalIndex
    (input : Splice.Input) (compiled : CompiledMaterial input)
    (wire : Fin compiled.siteContext.length) :
    Fin input.pattern.val.exposedWires.length :=
  Fin.cast (congrArg List.length
    compiled.siteContext_eq) wire

/-- Map each inherited wire position of the compiled terminal material body
to the exact complete host-site context position selected by its attachment. -/
noncomputable def spliceWireMap
    (input : Splice.Input) (layout : Splice.Input.PlugLayout input)
    (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site) :
    Fin compiled.siteContext.length → Fin hostContext.length :=
  fun wire => layout.attachedWireIndex admissible hostContext hostExact
    (compiled.spliceWireExternalIndex input wire)

theorem spliceWireMap_lookup
    (input : Splice.Input) (layout : Splice.Input.PlugLayout input)
    (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (wire : Fin compiled.siteContext.length) :
    hostContext.lookup? (input.attachment (layout.exposedPosition
        (compiled.spliceWireExternalIndex input wire))) =
      some (compiled.spliceWireMap input layout admissible hostContext
        hostExact wire) :=
  layout.attachedWireIndex_lookup admissible hostContext hostExact _

theorem spliceWireMap_get
    (input : Splice.Input) (layout : Splice.Input.PlugLayout input)
    (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (wire : Fin compiled.siteContext.length) :
    hostContext[compiled.spliceWireMap input layout admissible hostContext
        hostExact wire] =
      input.attachment (layout.exposedPosition
        (compiled.spliceWireExternalIndex input wire)) :=
  layout.attachedWireIndex_get admissible hostContext hostExact _

theorem spliceWireMap_source_get
    (input : Splice.Input) (layout : Splice.Input.PlugLayout input)
    (compiled : CompiledMaterial input)
    (wire : Fin compiled.siteContext.length) :
    input.pattern.val.boundary.get (layout.exposedPosition
        (compiled.spliceWireExternalIndex input wire)) =
      compiled.siteContext.get wire := by
  rw [layout.boundary_get_exposedPosition]
  exact (List.get_of_eq
    compiled.siteContext_eq wire).symm

private theorem relation_proxy
    (input : Splice.Input)
    (compiled : CompiledMaterial input)
    {arity : Nat} (relation : RelVar compiled.siteRels arity) :
    ∃ proxy : Fin input.binderSpine.proxyCount,
      compiled.siteBinders (input.binderSpine.proxy proxy) =
          some ⟨arity, relation⟩ ∧
        arity = input.binderSpine.arity proxy := by
  rcases relation with ⟨index, hasArity⟩
  subst arity
  obtain ⟨parent, bubble⟩ := compiled.binder_enumeration.bubble index
  have encloses := compiled.binder_enumeration.encloses index
  obtain ⟨proxy, binderEq, arityEq⟩ :=
    input.binderSpine.enclosing_body_bubble
      input.pattern.property.diagram_well_formed bubble encloses
  refine ⟨proxy, ?_, ?_⟩
  · have lookup := compiled.binder_enumeration.lookup index
    rw [binderEq] at lookup
    simpa using lookup
  · exact arityEq

private theorem hostRelation_exists
    (input : Splice.Input) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    {arity : Nat} (relation : RelVar compiled.siteRels arity) :
    ∃ target : RelVar hostRels arity,
      ∃ proxy : Fin input.binderSpine.proxyCount,
        compiled.siteBinders (input.binderSpine.proxy proxy) =
            some ⟨arity, relation⟩ ∧
          hostBinders (input.binderTarget proxy) =
            some ⟨arity, target⟩ := by
  obtain ⟨proxy, patternLookup, arityEq⟩ :=
    relation_proxy input compiled relation
  obtain ⟨parent, hostBubble⟩ :=
    admissible.binder_targets_match proxy
  have hostEncloses := admissible.binder_targets_enclose proxy
  subst arity
  obtain ⟨target, hostLookup⟩ := hostCovers
    (input.binderTarget proxy) parent (input.binderSpine.arity proxy)
    hostBubble hostEncloses
  exact ⟨target, proxy, patternLookup, hostLookup⟩

/-- Map the compiled terminal material body's inherited relation variables to
the relations owned by the corresponding source host binders. -/
noncomputable def spliceRelationMap
    (input : Splice.Input) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site) :
    RelationRenaming compiled.siteRels hostRels :=
  fun relation => Classical.choose
    (hostRelation_exists input admissible compiled hostBinders hostCovers relation)

/-- Every mapped pattern relation is witnessed by one source proxy and its
admissible host binder target. -/
theorem spliceRelationMap_lookup
    (input : Splice.Input) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    {arity : Nat} (relation : RelVar compiled.siteRels arity) :
    ∃ proxy : Fin input.binderSpine.proxyCount,
      compiled.siteBinders (input.binderSpine.proxy proxy) =
          some ⟨arity, relation⟩ ∧
        hostBinders (input.binderTarget proxy) =
          some ⟨arity,
            compiled.spliceRelationMap input admissible hostBinders hostCovers
              relation⟩ :=
  Classical.choose_spec
    (hostRelation_exists input admissible compiled hostBinders hostCovers relation)

/-- A successful lookup in the pattern's terminal binder context transports
to the host lookup selected by `spliceRelationMap`. -/
theorem spliceRelationMap_of_lookup
    (input : Splice.Input) (admissible : input.Admissible)
    (compiled : CompiledMaterial input)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    {binder : Fin input.pattern.val.diagram.regionCount} {arity : Nat}
    {relation : RelVar compiled.siteRels arity}
    (lookup : compiled.siteBinders binder = some ⟨arity, relation⟩) :
    ∃ proxy : Fin input.binderSpine.proxyCount,
      binder = input.binderSpine.proxy proxy ∧
        hostBinders (input.binderTarget proxy) =
          some ⟨arity,
            compiled.spliceRelationMap input admissible hostBinders hostCovers
              relation⟩ := by
  obtain ⟨proxy, patternLookup, hostLookup⟩ :=
    compiled.spliceRelationMap_lookup input admissible hostBinders hostCovers
      relation
  have ownerEq := compiled.binder_enumeration.lookup_owner relation lookup
  have proxyOwner := compiled.binder_enumeration.lookup_owner relation
    patternLookup
  exact ⟨proxy, ownerEq.symm.trans proxyOwner, hostLookup⟩

end Splice.Input.CompiledMaterial

end VisualProof.Concrete
