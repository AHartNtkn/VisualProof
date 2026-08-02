import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRaw
import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalProvenance

namespace VisualProof

namespace ConcreteWireQuantifier

namespace SingletonRemovalSemantics

/-!
Relation-join projections into the generic singleton-erasure owner.

Keeping this bridge separate is what lets primitive uniform-site
factorization reuse singleton erasure and insertion without importing the
monolithic relation-content checker.
-/

/-- The relation-join step already owns the canonical checked erasure. -/
def RelationJoinStep.checkedErasure
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    CheckedErasure step.prior step.priorApplication where
  target := step.base
  generated := step.base_generated

namespace RelationJoinStep

/-- The raw erased region is exactly the step's checked base-region image. -/
theorem rawTargetRegion_eq_baseRegionImage
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (region : source.val.RegionId) :
    Fin.cast
        (congrArg ConcreteDiagram.regionCount step.base_generated).symm
        (targetRegion step.prior step.priorApplication
          (step.priorRegionImage region)) =
      step.baseRegionImage region := by
  rw [step.baseRegionImageExact]
  rfl

/-- The raw erased wire is exactly the step's checked base-wire image. -/
theorem rawTargetWire_eq_baseWireImage
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId) :
    Fin.cast
        (congrArg ConcreteDiagram.wireCount step.base_generated).symm
        (targetWire step.prior step.priorApplication
          (step.priorWireImage wire)) =
      step.baseWireImage wire := by
  rw [step.baseWireImageExact]
  rfl

/-- Project a context-above fact through the step-owned raw erasure. -/
theorem rawTargetContext_above
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (region : step.prior.val.RegionId)
    (above :
      ConcreteElaboration.ContextAbove step.prior.val context region) :
    ConcreteElaboration.ContextAbove
      (ConcreteDiagram.DenseErasure.eraseNodeCandidate
        step.prior step.priorApplication)
      (targetContext step.prior step.priorApplication context)
      (targetRegion step.prior step.priorApplication region) :=
  targetContext_above step.prior step.priorApplication context region above

@[simp] theorem rawTargetSite_eq_site
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    Fin.cast
        (congrArg ConcreteDiagram.regionCount step.base_generated).symm
        (targetRegion step.prior step.priorApplication
          (step.priorRegionImage step.sourceRegion)) =
      step.site := by
  rw [rawTargetRegion_eq_baseRegionImage step, step.siteExact]

private theorem argumentOrigins_eq
    (prior : CheckedDiagram definitions)
    (node : prior.val.NodeId)
    (context : ConcreteElaboration.WireContext prior.val) :
    ∀ (args : List Sig) (position : Nat)
      (arguments : Vars context.sigs args)
      (wires : List prior.val.WireId),
      ConcreteElaboration.ArgumentOrigins prior.val context node position
          arguments →
        relationArgumentWires? prior node args position = some wires →
        ConcreteElaboration.variableOrigins prior.val context arguments =
          wires
  | [], _position, .nil, wires, _origins, accepted => by
      simp [relationArgumentWires?] at accepted
      exact accepted.symm
  | sig :: rest, position, .cons head tail, wires, origins, accepted => by
      rcases origins with ⟨headOwner, tailOrigins⟩
      simp only [relationArgumentWires?, headOwner] at accepted
      by_cases signature :
          (prior.val.wires
            (ConcreteElaboration.WireContext.origin prior.val context.ids
              head)).sig = sig
      · cases tailAccepted :
            relationArgumentWires? prior node rest (position + 1) with
        | none => simp [tailAccepted] at accepted
        | some tailWires =>
            have wiresExact :
                ConcreteElaboration.WireContext.origin prior.val context.ids
                    head ::
                  tailWires =
                wires := by
                  simpa [signature, tailAccepted] using accepted
            rw [← wiresExact]
            simp only [ConcreteElaboration.variableOrigins, List.cons.injEq,
              true_and]
            exact
              argumentOrigins_eq prior node context rest (position + 1) tail
                tailWires tailOrigins tailAccepted
      · simp [signature] at accepted

/-- Project the accepted site compilation to its application singleton. -/
theorem compiledApplication
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    ∃ (outer : ConcreteElaboration.WireContext step.prior.val)
      (visibleExact :
        step.priorSite.frame.visible =
          outer.extend (step.priorRegionImage step.sourceRegion))
      (head :
        Var (outer.extend
          (step.priorRegionImage step.sourceRegion)).sigs
          (.rel step.relationArgs))
      (arguments :
        Vars (outer.extend
          (step.priorRegionImage step.sourceRegion)).sigs
          step.relationArgs),
      ConcreteElaboration.compileNodes? definitions step.prior.val
          (outer.extend (step.priorRegionImage step.sourceRegion))
          [step.priorApplication] =
        some (.cons (.atom head arguments) .nil) ∧
      ConcreteElaboration.WireContext.origin step.prior.val
          (outer.extend
            (step.priorRegionImage step.sourceRegion)).ids head =
        step.priorWireImage dying ∧
      ConcreteElaboration.variableOrigins step.prior.val
          (outer.extend
            (step.priorRegionImage step.sourceRegion)) arguments =
        step.priorArguments := by
  obtain ⟨outer, _fuel, nodes, _children, visibleExact,
      nodesCompiled, _childrenCompiled, _bodyExact⟩ :=
    step.priorSite.site_origin
  have member :
      step.priorApplication ∈
        step.prior.val.nodesAt (step.priorRegionImage step.sourceRegion) := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.mem_filter.mpr
    constructor
    · exact Data.Finite.mem_allFin step.priorApplication
    · rw [step.priorNodeExact]
      exact beq_iff_eq.mpr rfl
  obtain ⟨item, singletonCompiled⟩ :=
    compileNodes_singleton_of_member definitions step.prior.val
      (outer.extend (step.priorRegionImage step.sourceRegion))
      (step.prior.val.nodesAt
        (step.priorRegionImage step.sourceRegion))
      nodes nodesCompiled step.priorApplication member
  obtain ⟨head, arguments, itemExact, headOrigin, argumentOrigins⟩ :=
    ConcreteElaboration.compileNodes?_atom_shape step.prior.val
      (outer.extend (step.priorRegionImage step.sourceRegion))
      step.priorApplication step.priorNodeExact singletonCompiled
  have itemSame : item = .atom head arguments :=
    ItemSeq.cons.inj itemExact |>.1
  subst item
  have exactHead :
      ConcreteElaboration.WireContext.origin step.prior.val
          (outer.extend
            (step.priorRegionImage step.sourceRegion)).ids head =
        step.priorWireImage dying :=
    Option.some.inj (headOrigin.symm.trans step.priorDyingOwner)
  have exactArguments :
      ConcreteElaboration.variableOrigins step.prior.val
          (outer.extend
            (step.priorRegionImage step.sourceRegion)) arguments =
        step.priorArguments :=
    argumentOrigins_eq step.prior step.priorApplication
      (outer.extend (step.priorRegionImage step.sourceRegion))
      step.relationArgs 0 arguments step.priorArguments argumentOrigins
      step.priorArgumentsAccepted
  exact
    ⟨outer, visibleExact, head, arguments, singletonCompiled, exactHead,
      exactArguments⟩

end RelationJoinStep

/-- Project a relation-join step into the canonical paired erasure frame. -/
theorem RelationJoinStep.pairedGeneratedFrame
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (site region : step.prior.val.RegionId)
    (fuel : Nat)
    (sourceOuter :
      ConcreteElaboration.WireContext step.prior.val)
    (sourceFrame :
      RegionFrame definitions step.prior.val sourceOuter)
    (sourceAbove :
      ConcreteElaboration.ContextAbove step.prior.val sourceOuter region)
    (sourceGenerated :
      compileRegionFrame? definitions step.prior.val site fuel region
          sourceOuter =
        some sourceFrame) :
    PairedGeneratedFrame step.prior step.priorApplication site region fuel
      sourceOuter sourceFrame :=
  SingletonRemovalSemantics.pairedGeneratedFrame
    step.prior step.priorApplication
    (RelationJoinStep.checkedErasure step)
      site region fuel sourceOuter sourceFrame
      sourceAbove sourceGenerated

end SingletonRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
