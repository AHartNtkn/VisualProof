import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSiteBackward

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- The target local valuation for a nonzero-spine splice is the exact local
wire equivalence applied to the source host locals followed by the terminal
comprehension locals supplied by the relation witness. -/
noncomputable def siteTargetLocalOfNonempty
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D) :
    Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).length → D :=
  Fin.addCases sourceLocal patternLocal ∘
    (layout.siteLocalWireEquivOfNonempty hnonempty).symm

theorem siteTargetLocalOfNonempty_host
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length) :
    siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal
        (layout.siteLocalWireEquivOfNonempty hnonempty
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
              input.binderSpine.bodyContainer).length index)) =
      sourceLocal index := by
  unfold siteTargetLocalOfNonempty
  change Fin.addCases sourceLocal patternLocal
      ((layout.siteLocalWireEquivOfNonempty hnonempty).symm
        ((layout.siteLocalWireEquivOfNonempty hnonempty)
          (Fin.castAdd _ index))) = sourceLocal index
  rw [FiniteEquiv.symm_apply_apply]
  exact Fin.addCases_left index

theorem siteTargetLocalOfNonempty_pattern
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length) :
    siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal
        (layout.siteLocalWireEquivOfNonempty hnonempty
          (Fin.natAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length index)) =
      patternLocal index := by
  unfold siteTargetLocalOfNonempty
  change Fin.addCases sourceLocal patternLocal
      ((layout.siteLocalWireEquivOfNonempty hnonempty).symm
        ((layout.siteLocalWireEquivOfNonempty hnonempty)
          (Fin.natAdd _ index))) = patternLocal index
  rw [FiniteEquiv.symm_apply_apply]
  exact Fin.addCases_right index

/-- The source host context embeds into the combined nonzero-spine target
context using the caller's inherited-wire map and the splice's certified host
local block. -/
noncomputable def siteForwardHostWireMapOfNonempty
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length) :
    Fin (sourceOuter.extend input.site).length →
      Fin (targetOuter.extend (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend targetOuter
        (layout.frameRegion input.site)).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length (outerMap outer))
        (fun localIndex => Fin.natAdd targetOuter.length
          (layout.siteLocalWireEquivOfNonempty hnonempty
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
                input.binderSpine.bodyContainer).length localIndex)))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceOuter input.site)
          index))

theorem siteForwardHostWireMapOfNonempty_spec
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (index : Fin (sourceOuter.extend input.site).length) :
    (targetOuter.extend (layout.frameRegion input.site)).get
        (siteForwardHostWireMapOfNonempty layout hnonempty sourceOuter
          targetOuter outerMap index) =
      layout.frameWire ((sourceOuter.extend input.site).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have mapEq : siteForwardHostWireMapOfNonempty layout hnonempty
        sourceOuter targetOuter outerMap
          (Fin.cast (ConcreteElaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.castAdd _ outer)) =
        Fin.cast (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.castAdd _ (outerMap outer)) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfNonempty]
    rw [mapEq,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_outer,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_outer]
    exact outerSpec outer
  · have mapEq : siteForwardHostWireMapOfNonempty layout hnonempty
        sourceOuter targetOuter outerMap
          (Fin.cast (ConcreteElaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.natAdd sourceOuter.length localIndex)) =
        Fin.cast (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.natAdd targetOuter.length
            (layout.siteLocalWireEquivOfNonempty hnonempty
              (Fin.castAdd _ localIndex))) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfNonempty]
    rw [mapEq,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_local,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_local]
    exact layout.siteLocalWireEquivOfNonempty_host_spec hnonempty localIndex

theorem siteForwardHostEnvironmentsAgreeOfNonempty
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (sourceOuterEnv : Fin sourceOuter.length → D)
    (targetOuterEnv : Fin targetOuter.length → D)
    (outerEq : sourceOuterEnv = targetOuterEnv ∘ outerMap)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D) :
    ConcreteElaboration.extendedEnvironment sourceOuter input.site
        sourceOuterEnv sourceLocal =
      ConcreteElaboration.extendedEnvironment targetOuter
          (layout.frameRegion input.site) targetOuterEnv
          (siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal) ∘
        siteForwardHostWireMapOfNonempty layout hnonempty sourceOuter
          targetOuter outerMap := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simpa [ConcreteElaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfNonempty, split, outerEq]
  · simp only [ConcreteElaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfNonempty, Function.comp_apply]
    simp
    exact (siteTargetLocalOfNonempty_host layout hnonempty sourceLocal
      patternLocal localIndex).symm

/-- Zero-spine analogue: the material-local block consists of the checked
open comprehension's hidden root wires. -/
noncomputable def siteTargetLocalOfEmpty
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D) :
    Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).length → D :=
  Fin.addCases sourceLocal patternHidden ∘
    (layout.siteLocalWireEquivOfEmpty hzero).symm

theorem siteTargetLocalOfEmpty_host
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length) :
    siteTargetLocalOfEmpty layout hzero sourceLocal patternHidden
        (layout.siteLocalWireEquivOfEmpty hzero
          (Fin.castAdd input.pattern.val.hiddenWires.length index)) =
      sourceLocal index := by
  unfold siteTargetLocalOfEmpty
  change Fin.addCases sourceLocal patternHidden
      ((layout.siteLocalWireEquivOfEmpty hzero).symm
        ((layout.siteLocalWireEquivOfEmpty hzero)
          (Fin.castAdd _ index))) = sourceLocal index
  rw [FiniteEquiv.symm_apply_apply]
  exact Fin.addCases_left index

theorem siteTargetLocalOfEmpty_pattern
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D)
    (index : Fin input.pattern.val.hiddenWires.length) :
    siteTargetLocalOfEmpty layout hzero sourceLocal patternHidden
        (layout.siteLocalWireEquivOfEmpty hzero
          (Fin.natAdd
            (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length index)) =
      patternHidden index := by
  unfold siteTargetLocalOfEmpty
  change Fin.addCases sourceLocal patternHidden
      ((layout.siteLocalWireEquivOfEmpty hzero).symm
        ((layout.siteLocalWireEquivOfEmpty hzero)
          (Fin.natAdd _ index))) = patternHidden index
  rw [FiniteEquiv.symm_apply_apply]
  exact Fin.addCases_right index

noncomputable def siteForwardHostWireMapOfEmpty
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length) :
    Fin (sourceOuter.extend input.site).length →
      Fin (targetOuter.extend (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend targetOuter
        (layout.frameRegion input.site)).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length (outerMap outer))
        (fun localIndex => Fin.natAdd targetOuter.length
          (layout.siteLocalWireEquivOfEmpty hzero
            (Fin.castAdd input.pattern.val.hiddenWires.length localIndex)))
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceOuter input.site)
          index))

theorem siteForwardHostWireMapOfEmpty_spec
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (index : Fin (sourceOuter.extend input.site).length) :
    (targetOuter.extend (layout.frameRegion input.site)).get
        (siteForwardHostWireMapOfEmpty layout hzero sourceOuter targetOuter
          outerMap index) =
      layout.frameWire ((sourceOuter.extend input.site).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have mapEq : siteForwardHostWireMapOfEmpty layout hzero sourceOuter
        targetOuter outerMap
          (Fin.cast (ConcreteElaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.castAdd _ outer)) =
        Fin.cast (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.castAdd _ (outerMap outer)) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfEmpty]
    rw [mapEq,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_outer,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_outer]
    exact outerSpec outer
  · have mapEq : siteForwardHostWireMapOfEmpty layout hzero sourceOuter
        targetOuter outerMap
          (Fin.cast (ConcreteElaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.natAdd sourceOuter.length localIndex)) =
        Fin.cast (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.natAdd targetOuter.length
            (layout.siteLocalWireEquivOfEmpty hzero
              (Fin.castAdd input.pattern.val.hiddenWires.length localIndex))) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfEmpty]
    rw [mapEq,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_local,
      Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_local]
    exact layout.siteLocalWireEquivOfEmpty_host_spec hzero localIndex

theorem siteForwardHostEnvironmentsAgreeOfEmpty
    {signature : List Nat}
    {input : Splice.Input signature}
    (layout : Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (sourceOuterEnv : Fin sourceOuter.length → D)
    (targetOuterEnv : Fin targetOuter.length → D)
    (outerEq : sourceOuterEnv = targetOuterEnv ∘ outerMap)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D) :
    ConcreteElaboration.extendedEnvironment sourceOuter input.site
        sourceOuterEnv sourceLocal =
      ConcreteElaboration.extendedEnvironment targetOuter
          (layout.frameRegion input.site) targetOuterEnv
          (siteTargetLocalOfEmpty layout hzero sourceLocal patternHidden) ∘
        siteForwardHostWireMapOfEmpty layout hzero sourceOuter targetOuter
          outerMap := by
  funext index
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simpa [ConcreteElaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfEmpty, split, outerEq]
  · simp only [ConcreteElaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfEmpty, Function.comp_apply]
    simp
    exact (siteTargetLocalOfEmpty_host layout hzero sourceLocal patternHidden
      localIndex).symm

end InstantiationSemantic

end VisualProof.Rule
