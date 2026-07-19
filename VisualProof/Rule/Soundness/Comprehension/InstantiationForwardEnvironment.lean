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

end InstantiationSemantic

end VisualProof.Rule
