import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSiteBackward

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Any exact target-site valuation that agrees with a frame embedding induces
the original source valuation through the splice quotient.  This is the
pointwise bridge used to identify the relation witness's ordered arguments and
parameters with the source atom's arguments and parameters. -/
theorem siteQuotientEnvironment_of_frameMap
    (input : Concrete.Splice.Input )
    (sourceContext : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetContext : Concrete.Elaboration.WireContext input.plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact input.site)
    (targetExact : targetContext.Exact
      (input.plugLayout.frameRegion input.site))
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      input.plugLayout.frameWire (sourceContext.get index))
    (sourceEnv : Fin sourceContext.length → D)
    (targetEnv : Fin targetContext.length → D)
    (environmentEq : sourceEnv = targetEnv ∘ wireMap)
    (fallback : D)
    (index : Fin sourceContext.length) :
    Concrete.Splice.Input.siteQuotientEnvironment input targetContext targetExact
        targetEnv fallback (sourceContext.get index) =
      sourceEnv index := by
  have visible : input.plugLayout.plugRaw.Encloses
      (input.plugLayout.plugRaw.wires
        (input.plugLayout.frameWire (sourceContext.get index))).scope
      (input.plugLayout.frameRegion input.site) :=
    (input.plugLayout.frameWire_visible_at_region_iff input.site
      (sourceContext.get index)).2
      ((sourceExact.mem_iff (sourceContext.get index)).1
        (List.get_mem sourceContext index))
  have quotientEq := Concrete.Splice.Input.siteQuotientEnvironment_eq input
    targetContext targetExact targetEnv fallback (sourceContext.get index)
    visible (wireMap index) (wireSpec index)
  have sourceEq := congrFun environmentEq index
  exact quotientEq.trans sourceEq.symm

/-- The target local valuation for a nonzero-spine splice is the exact local
wire equivalence applied to the source host locals followed by the terminal
comprehension locals supplied by the relation witness. -/
noncomputable def siteTargetLocalOfNonempty
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D) :
    Fin (Concrete.Elaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).length → D :=
  Fin.addCases sourceLocal patternLocal ∘
    (layout.siteLocalWireEquivOfNonempty hnonempty).symm

theorem siteTargetLocalOfNonempty_host
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D)
    (index : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length) :
    siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal
        (layout.siteLocalWireEquivOfNonempty hnonempty
          (Fin.castAdd
            (Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
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
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D)
    (index : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length) :
    siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal
        (layout.siteLocalWireEquivOfNonempty hnonempty
          (Fin.natAdd
            (Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length index)) =
      patternLocal index := by
  unfold siteTargetLocalOfNonempty
  change Fin.addCases sourceLocal patternLocal
      ((layout.siteLocalWireEquivOfNonempty hnonempty).symm
        ((layout.siteLocalWireEquivOfNonempty hnonempty)
          (Fin.natAdd _ index))) = patternLocal index
  rw [FiniteEquiv.symm_apply_apply]
  exact Fin.addCases_right index

/-- The complete target compiler environment built from
`siteTargetLocalOfNonempty` reads the supplied terminal local valuation at the
authoritative pattern seam index. -/
theorem siteTargetEnvironment_patternLocalOfNonempty
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hadmissible : input.Admissible)
    (host : Concrete.Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region  patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      input.pattern.val.diagram input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (outerEnv : Fin outputLeaf.inheritedWires.length → D)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D)
    (index : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length) :
    Concrete.Elaboration.extendedEnvironment outputLeaf.inheritedWires
        (layout.frameRegion input.site) outerEnv
        (siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal)
        (layout.patternSeamWireMapOfNonempty hadmissible host patternWitness
          patternLeaf outputWitness outputLeaf hnonempty
          (Fin.cast
            (Concrete.Elaboration.WireContext.length_extend
              patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
            (Fin.natAdd patternLeaf.inheritedWires.length index))) =
      patternLocal index := by
  let targetIndex := layout.patternSeamWireMapOfNonempty hadmissible host
    patternWitness patternLeaf outputWitness outputLeaf hnonempty
    (Fin.cast
      (Concrete.Elaboration.WireContext.length_extend patternLeaf.inheritedWires
        input.binderSpine.bodyContainer).symm
      (Fin.natAdd patternLeaf.inheritedWires.length index))
  let localIndex := layout.siteLocalWireEquivOfNonempty hnonempty
    (Fin.natAdd
      (Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
        input.site).length index)
  let expectedIndex : Fin (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend outputLeaf.inheritedWires
        (layout.frameRegion input.site)).symm
      (Fin.natAdd outputLeaf.inheritedWires.length localIndex)
  have targetWire : (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).get targetIndex =
      layout.patternPlugWire
        ((patternLeaf.inheritedWires.extend
          input.binderSpine.bodyContainer).get
          (Fin.cast
            (Concrete.Elaboration.WireContext.length_extend
              patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
            (Fin.natAdd patternLeaf.inheritedWires.length index))) :=
    layout.patternSeamWireMapOfNonempty_spec hadmissible host patternWitness
      patternLeaf outputWitness outputLeaf hnonempty _
  have targetWire' : (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).get targetIndex =
      layout.patternPlugWire
        ((Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).get index) := by
    simpa only [
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_local]
      using
      targetWire
  have expectedWire : (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).get expectedIndex =
      layout.patternPlugWire
        ((Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).get index) := by
    rw [Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_local]
    rw [layout.siteLocalWireEquivOfNonempty_pattern_spec hnonempty]
    exact (layout.patternPlugWire_terminal_local hnonempty index).symm
  have indexEq : targetIndex = expectedIndex := by
    apply Fin.ext
    apply (List.getElem_inj outputLeaf.wiresExact.nodup).mp
    simpa only [List.get_eq_getElem] using targetWire'.trans expectedWire.symm
  change Concrete.Elaboration.extendedEnvironment outputLeaf.inheritedWires
      (layout.frameRegion input.site) outerEnv
      (siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal)
      targetIndex = patternLocal index
  rw [indexEq]
  simp only [Concrete.Elaboration.extendedEnvironment, Function.comp_apply]
  have castEq : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend outputLeaf.inheritedWires
        (layout.frameRegion input.site)) expectedIndex =
      Fin.natAdd outputLeaf.inheritedWires.length localIndex := by
    apply Fin.ext
    rfl
  rw [castEq]
  simp only [extendWireEnv, Fin.addCases_right]
  exact siteTargetLocalOfNonempty_pattern layout hnonempty sourceLocal
    patternLocal index

/-- The source host context embeds into the combined nonzero-spine target
context using the caller's inherited-wire map and the splice's certified host
local block. -/
noncomputable def siteForwardHostWireMapOfNonempty
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length) :
    Fin (sourceOuter.extend input.site).length →
      Fin (targetOuter.extend (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend targetOuter
        (layout.frameRegion input.site)).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length (outerMap outer))
        (fun localIndex => Fin.natAdd targetOuter.length
          (layout.siteLocalWireEquivOfNonempty hnonempty
            (Fin.castAdd
              (Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
                input.binderSpine.bodyContainer).length localIndex)))
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site)
          index))

theorem siteForwardHostWireMapOfNonempty_spec
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (index : Fin (sourceOuter.extend input.site).length) :
    (targetOuter.extend (layout.frameRegion input.site)).get
        (siteForwardHostWireMapOfNonempty layout hnonempty sourceOuter
          targetOuter outerMap index) =
      layout.frameWire ((sourceOuter.extend input.site).get index) := by
  let split := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have mapEq : siteForwardHostWireMapOfNonempty layout hnonempty
        sourceOuter targetOuter outerMap
          (Fin.cast (Concrete.Elaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.castAdd _ outer)) =
        Fin.cast (Concrete.Elaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.castAdd _ (outerMap outer)) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfNonempty]
    rw [mapEq,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_outer,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_outer]
    exact outerSpec outer
  · have mapEq : siteForwardHostWireMapOfNonempty layout hnonempty
        sourceOuter targetOuter outerMap
          (Fin.cast (Concrete.Elaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.natAdd sourceOuter.length localIndex)) =
        Fin.cast (Concrete.Elaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.natAdd targetOuter.length
            (layout.siteLocalWireEquivOfNonempty hnonempty
              (Fin.castAdd _ localIndex))) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfNonempty]
    rw [mapEq,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_local,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_local]
    exact layout.siteLocalWireEquivOfNonempty_host_spec hnonempty localIndex

theorem siteForwardHostEnvironmentsAgreeOfNonempty
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (sourceOuterEnv : Fin sourceOuter.length → D)
    (targetOuterEnv : Fin targetOuter.length → D)
    (outerEq : sourceOuterEnv = targetOuterEnv ∘ outerMap)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length → D) :
    Concrete.Elaboration.extendedEnvironment sourceOuter input.site
        sourceOuterEnv sourceLocal =
      Concrete.Elaboration.extendedEnvironment targetOuter
          (layout.frameRegion input.site) targetOuterEnv
          (siteTargetLocalOfNonempty layout hnonempty sourceLocal patternLocal) ∘
        siteForwardHostWireMapOfNonempty layout hnonempty sourceOuter
          targetOuter outerMap := by
  funext index
  let split := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simpa [Concrete.Elaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfNonempty, split, outerEq]
  · simp only [Concrete.Elaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfNonempty, Function.comp_apply]
    simp
    exact (siteTargetLocalOfNonempty_host layout hnonempty sourceLocal
      patternLocal localIndex).symm

/-- Zero-spine analogue: the material-local block consists of the checked
open comprehension's hidden root wires. -/
noncomputable def siteTargetLocalOfEmpty
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D) :
    Fin (Concrete.Elaboration.exactScopeWires layout.plugRaw
      (layout.frameRegion input.site)).length → D :=
  Fin.addCases sourceLocal patternHidden ∘
    (layout.siteLocalWireEquivOfEmpty hzero).symm

theorem siteTargetLocalOfEmpty_host
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D)
    (index : Fin (Concrete.Elaboration.exactScopeWires
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
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D)
    (index : Fin input.pattern.val.hiddenWires.length) :
    siteTargetLocalOfEmpty layout hzero sourceLocal patternHidden
        (layout.siteLocalWireEquivOfEmpty hzero
          (Fin.natAdd
            (Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length index)) =
      patternHidden index := by
  unfold siteTargetLocalOfEmpty
  change Fin.addCases sourceLocal patternHidden
      ((layout.siteLocalWireEquivOfEmpty hzero).symm
        ((layout.siteLocalWireEquivOfEmpty hzero)
          (Fin.natAdd _ index))) = patternHidden index
  rw [FiniteEquiv.symm_apply_apply]
  exact Fin.addCases_right index

/-- The generic focused zero-spine valuation is the concrete target-local
valuation used here once its quotient valuation agrees with the supplied host
locals. -/
theorem focusedLocalEnvironmentOfEmpty_eq_siteTargetLocal
    {input : Concrete.Splice.Input }
    (hzero : input.binderSpine.proxyCount = 0)
    (values : input.wireQuotient.Carrier → D)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D)
    (hostValues : ∀ index, values
      ((Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
        input.site).get index) = sourceLocal index) :
    Concrete.Splice.Input.focusedLocalEnvironmentOfEmpty input hzero values
        patternHidden =
      siteTargetLocalOfEmpty input.plugLayout hzero sourceLocal
        patternHidden := by
  funext targetIndex
  let semantic :=
    (input.plugLayout.siteLocalWireEquivOfEmpty hzero).symm targetIndex
  have recover : input.plugLayout.siteLocalWireEquivOfEmpty hzero semantic =
      targetIndex :=
    (input.plugLayout.siteLocalWireEquivOfEmpty hzero).apply_symm_apply _
  rw [← recover]
  refine Fin.addCases (fun hostIndex => ?_) (fun hiddenIndex => ?_) semantic
  · rw [Concrete.Splice.Input.focusedLocalEnvironmentOfEmpty_frame,
      siteTargetLocalOfEmpty_host]
    exact hostValues hostIndex
  · rw [Concrete.Splice.Input.focusedLocalEnvironmentOfEmpty_hidden,
      siteTargetLocalOfEmpty_pattern]

noncomputable def siteForwardHostWireMapOfEmpty
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length) :
    Fin (sourceOuter.extend input.site).length →
      Fin (targetOuter.extend (layout.frameRegion input.site)).length :=
  fun index =>
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend targetOuter
        (layout.frameRegion input.site)).symm
      (Fin.addCases
        (fun outer => Fin.castAdd
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length (outerMap outer))
        (fun localIndex => Fin.natAdd targetOuter.length
          (layout.siteLocalWireEquivOfEmpty hzero
            (Fin.castAdd input.pattern.val.hiddenWires.length localIndex)))
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site)
          index))

theorem siteForwardHostWireMapOfEmpty_spec
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (index : Fin (sourceOuter.extend input.site).length) :
    (targetOuter.extend (layout.frameRegion input.site)).get
        (siteForwardHostWireMapOfEmpty layout hzero sourceOuter targetOuter
          outerMap index) =
      layout.frameWire ((sourceOuter.extend input.site).get index) := by
  let split := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have mapEq : siteForwardHostWireMapOfEmpty layout hzero sourceOuter
        targetOuter outerMap
          (Fin.cast (Concrete.Elaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.castAdd _ outer)) =
        Fin.cast (Concrete.Elaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.castAdd _ (outerMap outer)) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfEmpty]
    rw [mapEq,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_outer,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_outer]
    exact outerSpec outer
  · have mapEq : siteForwardHostWireMapOfEmpty layout hzero sourceOuter
        targetOuter outerMap
          (Fin.cast (Concrete.Elaboration.WireContext.length_extend sourceOuter
            input.site).symm (Fin.natAdd sourceOuter.length localIndex)) =
        Fin.cast (Concrete.Elaboration.WireContext.length_extend targetOuter
          (layout.frameRegion input.site)).symm
          (Fin.natAdd targetOuter.length
            (layout.siteLocalWireEquivOfEmpty hzero
              (Fin.castAdd input.pattern.val.hiddenWires.length localIndex))) := by
      apply Fin.ext
      simp [siteForwardHostWireMapOfEmpty]
    rw [mapEq,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_local,
      Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_local]
    exact layout.siteLocalWireEquivOfEmpty_host_spec hzero localIndex

theorem siteForwardHostEnvironmentsAgreeOfEmpty
    {input : Concrete.Splice.Input }
    (layout : Concrete.Splice.Input.PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (sourceOuter : Concrete.Elaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (sourceOuterEnv : Fin sourceOuter.length → D)
    (targetOuterEnv : Fin targetOuter.length → D)
    (outerEq : sourceOuterEnv = targetOuterEnv ∘ outerMap)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      input.coalesceFrameRaw input.site).length → D)
    (patternHidden : Fin input.pattern.val.hiddenWires.length → D) :
    Concrete.Elaboration.extendedEnvironment sourceOuter input.site
        sourceOuterEnv sourceLocal =
      Concrete.Elaboration.extendedEnvironment targetOuter
          (layout.frameRegion input.site) targetOuterEnv
          (siteTargetLocalOfEmpty layout hzero sourceLocal patternHidden) ∘
        siteForwardHostWireMapOfEmpty layout hzero sourceOuter targetOuter
          outerMap := by
  funext index
  let split := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site) index
  have recover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceOuter input.site).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · simpa [Concrete.Elaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfEmpty, split, outerEq]
  · simp only [Concrete.Elaboration.extendedEnvironment, extendWireEnv,
      siteForwardHostWireMapOfEmpty, Function.comp_apply]
    simp
    exact (siteTargetLocalOfEmpty_host layout hzero sourceLocal patternHidden
      localIndex).symm

/-- One native terminal-pattern conjunct transports into the executor's actual
next-state survivor compiler.  This is the forward half of the authoritative
seam item isomorphism; it deliberately targets the survivor compiler rather
than an intrinsic reconstruction of the splice output. -/
theorem advance_pattern_item_denotes_nonempty_forward
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (host : Concrete.Splice.SiteView
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrame hadmissible) site)
    {patternBody : Region  patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      comprehension.val.diagram payload.binderSpine.bodyContainer
      patternWitness)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      comprehension.val.diagram.regionCount comprehension.val.diagram.nodeCount)
    (occurrenceMember : occurrence ∈ Concrete.Elaboration.localOccurrences
      comprehension.val.diagram payload.binderSpine.bodyContainer)
    (sourceItem : Item
      (patternLeaf.inheritedWires.extend
        payload.binderSpine.bodyContainer).length
      patternWitness.toFocus.holeRels)
    (targetItem : Item
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length
      outputWitness.toFocus.holeRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      comprehension.val.diagram
      (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
        patternLeaf.fuel)
      (patternLeaf.inheritedWires.extend payload.binderSpine.bodyContainer)
      patternLeaf.binders occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) outputLeaf.binders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.mapPatternOccurrence occurrence) =
        some targetItem)
    (sourceDenotes :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let layout := spliceInput.plugLayout
      let targetEq := Concrete.Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion site)
      let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
        outputWitness outputLeaf hnonempty
      let targetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (Concrete.Elaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion site)).length) → model.Carrier :=
        env ∘ Fin.cast targetEq.symm
      let sourceEnv := targetEnv ∘ combined
      let seam := layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty
      let relationMap : RelationRenaming patternWitness.toFocus.holeRels
          outputWitness.toFocus.holeRels := fun relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty relation)
      denoteItem model  (sourceEnv ∘ seam)
        (RelEnv.pullback relationMap relEnv) sourceItem) :
    denoteItem model  env relEnv targetItem := by
  dsimp only at sourceDenotes
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  have compilerEq := advance_compilePatternOccurrence_eq comprehension
    attachments binders payload state atom tail site arguments hadmissible
    outputLeaf.fuel
    (outputLeaf.inheritedWires.extend (layout.frameRegion site))
    outputLeaf.binders occurrence occurrenceMember
  have targetCompiledAuthoritative :
      Concrete.Elaboration.compileOccurrenceWith?  layout.plugRaw
        (Concrete.Elaboration.compileRegion?  layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion site))
        outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
          some targetItem := by
    have targetInNext := compilerEq ▸ targetCompiled
    simpa [next, layout, spliceInput] using targetInNext
  have itemIso := layout.compilePatternOccurrence_at_seam_iso
    spliceInput hadmissible host patternWitness patternLeaf outputWitness
    outputLeaf hnonempty occurrence occurrenceMember sourceItem targetItem
    sourceCompiled targetCompiledAuthoritative
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let seam := layout.patternSeamPreparedWireOfNonempty hadmissible host
    patternWitness patternLeaf hnonempty
  let sourceEnv := targetEnv ∘ combined
  let relationMap : RelationRenaming patternWitness.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf
      (layout.coalescedTerminalRelationRenaming hadmissible
        host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
        hnonempty relation)
  have wirePrepared : denoteItem model  sourceEnv
      (RelEnv.pullback relationMap relEnv) (sourceItem.renameWires seam) :=
    (denoteItem_renameWires model  seam sourceEnv
      (RelEnv.pullback relationMap relEnv) sourceItem).mpr sourceDenotes
  have prepared : denoteItem model  sourceEnv relEnv
      ((sourceItem.renameWires seam).renameRelations relationMap) :=
    (denoteItem_renameRelations model  relationMap
      (RelEnv.pullback relationMap relEnv) relEnv
      (RelEnv.pullback_agrees relationMap relEnv) sourceEnv
      (sourceItem.renameWires seam)).mpr wirePrepared
  have targetCastDenotes : denoteItem model  targetEnv relEnv
      (targetItem.castWiresEq targetEq) :=
    (itemIso.denotation model  sourceEnv targetEnv relEnv
      (fun _ => rfl)).mp prepared
  rw [Item.castWiresEq_eq_renameWires, denoteItem_renameWires]
    at targetCastDenotes
  simpa [targetEnv, targetEq, Function.comp_def] using targetCastDenotes

/-- Zero-spine counterpart of
`advance_pattern_item_denotes_nonempty_forward`, using the checked-open root
compiler and its repeated-alias seam map. -/
theorem advance_pattern_root_item_denotes_empty_forward
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (host : Concrete.Splice.SiteView
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrame hadmissible) site)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hzero : payload.binderSpine.proxyCount = 0)
    (model : Model)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      comprehension.val.diagram.regionCount comprehension.val.diagram.nodeCount)
    (occurrenceMember : occurrence ∈ Concrete.Elaboration.localOccurrences
      comprehension.val.diagram comprehension.val.diagram.root)
    (sourceItem : Item
      (comprehension.val.exposedWires ++ comprehension.val.hiddenWires).length [])
    (targetItem : Item
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length
      outputWitness.toFocus.holeRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      comprehension.val.diagram
      (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
        comprehension.val.diagram.regionCount)
      (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
      Concrete.Elaboration.BinderContext.empty occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) outputLeaf.binders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.mapPatternOccurrence occurrence) =
        some targetItem)
    (sourceDenotes :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let layout := spliceInput.plugLayout
      let targetEq := Concrete.Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion site)
      let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
        outputWitness outputLeaf hzero
      let targetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (Concrete.Elaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion site)).length) → model.Carrier :=
        env ∘ Fin.cast targetEq.symm
      let sourceEnv := targetEnv ∘ combined
      let seam := layout.patternRootSeamPreparedWireOfEmpty hadmissible host
      denoteItem (relCtx := []) model  (sourceEnv ∘ seam) PUnit.unit
        sourceItem) :
    denoteItem model  env relEnv targetItem := by
  dsimp only at sourceDenotes
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  have bodyRoot : payload.binderSpine.bodyContainer =
      comprehension.val.diagram.root :=
    payload.binderSpine.body_eq_root_of_empty hzero
  have bodyMember : occurrence ∈ Concrete.Elaboration.localOccurrences
      comprehension.val.diagram payload.binderSpine.bodyContainer := by
    simpa [bodyRoot] using occurrenceMember
  have compilerEq := advance_compilePatternOccurrence_eq comprehension
    attachments binders payload state atom tail site arguments hadmissible
    outputLeaf.fuel
    (outputLeaf.inheritedWires.extend (layout.frameRegion site))
    outputLeaf.binders occurrence bodyMember
  have targetCompiledAuthoritative :
      Concrete.Elaboration.compileOccurrenceWith?  layout.plugRaw
        (Concrete.Elaboration.compileRegion?  layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion site))
        outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
          some targetItem := by
    have targetInNext := compilerEq ▸ targetCompiled
    simpa [next, layout, spliceInput] using targetInNext
  have itemIso := layout.compilePatternRootOccurrence_at_seam_iso
    spliceInput hadmissible host outputWitness outputLeaf hzero occurrence
    occurrenceMember sourceItem targetItem sourceCompiled
    targetCompiledAuthoritative
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let seam := layout.patternRootSeamPreparedWireOfEmpty hadmissible host
  let sourceEnv := targetEnv ∘ combined
  let relationMap : RelationRenaming [] outputWitness.toFocus.holeRels :=
    Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
      outputWitness.toFocus.holeRels
  have wirePrepared : denoteItem (relCtx := []) model  sourceEnv PUnit.unit
      (sourceItem.renameWires seam) :=
    (denoteItem_renameWires (relCtx := []) model  seam sourceEnv PUnit.unit
      sourceItem).mpr sourceDenotes
  have prepared : denoteItem model  sourceEnv relEnv
      ((sourceItem.renameWires seam).renameRelations relationMap) :=
    (denoteItem_renameRelations model  relationMap PUnit.unit relEnv
      (RelEnv.pullback_agrees relationMap relEnv) sourceEnv
      (sourceItem.renameWires seam)).mpr wirePrepared
  have targetCastDenotes : denoteItem model  targetEnv relEnv
      (targetItem.castWiresEq targetEq) :=
    (itemIso.denotation model  sourceEnv targetEnv relEnv
      (fun _ => rfl)).mp prepared
  rw [Item.castWiresEq_eq_renameWires, denoteItem_renameWires]
    at targetCastDenotes
  simpa [targetEnv, targetEq, Function.comp_def] using targetCastDenotes

end InstantiationSemantic

end VisualProof.Rule
