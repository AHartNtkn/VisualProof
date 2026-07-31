import VisualProof.Diagram.Concrete.WirePartition
import VisualProof.Diagram.Concrete.WireQuantifierFrameNaturality

namespace VisualProof

namespace ConcreteWireQuantifier

namespace WireJoinResult

/--
A checked equal-signature comparable-scope join is sound in the polarity
determined by the checker-generated site frame.
-/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : WireJoinResult source outer inner)
    (comparable :
      source.val.Encloses (source.val.wires outer).scope
        (source.val.wires inner).scope)
    (site : SiteCompilation source (source.val.wires inner).scope)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    (site.frame.context.cutDepth % 2 = 0 →
      denoteChecked pre definitionEnv result.checked →
        denoteChecked pre definitionEnv source) ∧
    (site.frame.context.cutDepth % 2 = 1 →
      denoteChecked pre definitionEnv source →
        denoteChecked pre definitionEnv result.checked) := by
  have direction :=
    WireJoinSemantics.root_direction result comparable site pre definitionEnv
  rw [site.frame_fills_checked] at direction
  simpa only [elaborate_denotes_checked] using direction

end WireJoinResult

namespace WireSeverResult

/--
A checked signature-indexed sever is sound in the polarity of its chosen
fresh scope. The target site receipt, comparable inverse join, and parity
transport are derived from the checker-owned sever receipt.
-/
theorem denotes
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    {scope : source.val.RegionId}
    (result : WireSeverResult source wire keep scope)
    (sourceSite : SiteCompilation source scope)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    (sourceSite.frame.context.cutDepth % 2 = 0 →
      denoteChecked pre definitionEnv source →
        denoteChecked pre definitionEnv result.checked) ∧
    (sourceSite.frame.context.cutDepth % 2 = 1 →
      denoteChecked pre definitionEnv result.checked →
        denoteChecked pre definitionEnv source) := by
  obtain ⟨targetSite, _⟩ :=
    compileSite_complete result.checked
      (result.checked.val.wires result.freshWire).scope
  have comparable :
      result.checked.val.Encloses
        (result.checked.val.wires (result.wireImage wire)).scope
        (result.checked.val.wires result.freshWire).scope := by
    simpa using
      result.encloses_regionImage result.sourceScope_encloses_scope
  have joined :=
    WireJoinResult.denotes result.inverseJoin comparable targetSite
      pre definitionEnv
  have sameDepth :=
    WireJoinSemantics.sever_site_cutDepth result sourceSite targetSite
  have rejoined :=
    iso_denotation result.inverseIso pre definitionEnv
  constructor
  · intro sourceEven sourceHolds
    have targetEven :
        targetSite.frame.context.cutDepth % 2 = 0 := by
      rw [sameDepth]
      exact sourceEven
    exact joined.1 targetEven (rejoined.mp sourceHolds)
  · intro sourceOdd targetHolds
    have targetOdd :
        targetSite.frame.context.cutDepth % 2 = 1 := by
      rw [sameDepth]
      exact sourceOdd
    exact rejoined.mpr (joined.2 targetOdd targetHolds)

end WireSeverResult

end ConcreteWireQuantifier

end VisualProof
