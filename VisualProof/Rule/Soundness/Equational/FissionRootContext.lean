import VisualProof.Rule.Soundness.Equational.FissionRootFocused

namespace VisualProof.Rule

open VisualProof
open Diagram
open Theory

namespace FissionSoundness

noncomputable def rootContext
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (portWire : Fin freePorts → Fin input.val.wireCount)
    (depth : Nat) (selectedTerm : Lambda.Term depth
      (Fin input.val.wireCount))
    (path : List Lambda.PathSegment)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (nodeShape : input.val.nodes selected = .term site freePorts term)
    (resolved : resolveNodeFreeWires? input selected freePorts = some portWire)
    (selectedResult : subtermAt? (term.mapFree portWire) path =
      some ⟨depth, selectedTerm⟩)
    (residualResult : replaceAtPort?
      ((term.mapFree portWire).mapFree some) path none = some residual)
    (producerResult : lowerToZero depth selectedTerm = some producer)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature)
    (named : NamedEnv Lambda.Individual signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    let simulation := semanticSimulation input selected site freePorts term
      portWire depth selectedTerm path producer residual nodeShape resolved
      selectedResult residualResult producerResult targetWellFormed
      Lambda.canonicalModel named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction
      (sourceOpen input boundary).exposedWires
      (sourceOpen input boundary).hiddenWires
      (targetOpen input selected site producer residual boundary).exposedWires
      (targetOpen input selected site producer residual boundary).hiddenWires := by
  let simulation := semanticSimulation input selected site freePorts term
    portWire depth selectedTerm path producer residual nodeShape resolved
    selectedResult residualResult producerResult targetWellFormed
    Lambda.canonicalModel named
  let embedding := rootEmbedding input selected site producer residual boundary
    sourceRoot targetWellFormed
  refine {
    outer := ConcreteElaboration.ContextIndexRelation.forwardMap
      (exposedIndex (input := input) (selected := selected) (site := site)
        (producer := producer) (residual := residual) (boundary := boundary))
    context := ?_
    atRoot := True.intro
    atRootChild := by
      intro regular child parent
      trivial
    atFocusedRootChild := by
      intro focused child sourceParent targetParent
      trivial
    transport := ?_
    focusedRootKernel := ?_
  }
  · simpa only [OpenConcreteDiagram.rootWires] using embedding
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    refine ConcreteElaboration.directionalRootTransport_of_agreement direction
      (sourceOpen input boundary).exposedWires
      (sourceOpen input boundary).hiddenWires
      (targetOpen input selected site producer residual boundary).exposedWires
      (targetOpen input selected site producer residual boundary).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedIndex (input := input) (selected := selected) (site := site)
          (producer := producer) (residual := residual) (boundary := boundary)))
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      Lambda.canonicalModel named
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty)) targetItems ?_
      itemSemantics
    intro sourceOuter targetOuter outerAgrees
    rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
      at outerAgrees
    have rootNe : input.val.root ≠ site := regular
    have rootFreshEmpty : rootFresh input site = [] := by
      simp [rootFresh, rootNe]
    cases direction with
    | forward =>
        intro sourceLocal
        let fresh : Fin (rootFresh input site).length → Lambda.Individual :=
          fun index => nomatch (rootFreshEmpty ▸ index)
        let targetLocal := rootForwardLocal
          (input := input) (selected := selected) (site := site)
          (producer := producer) (residual := residual) (boundary := boundary)
          sourceLocal fresh
        refine ⟨targetLocal, ?_⟩
        apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          embedding.index _ _).mpr
        have indexEq : embedding.index =
            rootIndex input selected site producer residual boundary := rfl
        rw [indexEq]
        exact rootEnvironment_forward input selected site producer residual
          boundary sourceOuter targetOuter sourceLocal fresh outerAgrees
    | backward =>
        intro targetLocal
        let sourceLocal := rootBackwardLocal
          (input := input) (selected := selected) (site := site)
          (producer := producer) (residual := residual) (boundary := boundary)
          targetLocal
        refine ⟨sourceLocal, ?_⟩
        apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          embedding.index _ _).mpr
        have indexEq : embedding.index =
            rootIndex input selected site producer residual boundary := rfl
        rw [indexEq]
        exact rootEnvironment_backward input selected site producer residual
          boundary sourceOuter targetOuter targetLocal outerAgrees
  · intro atRoot distinguished allowed recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    have rootSite : input.val.root = site := distinguished
    have sourceCompiled' : ConcreteElaboration.compileOccurrencesWith? signature
        input.val (ConcreteElaboration.compileRegion? signature input.val
          input.val.regionCount) (sourceOpen input boundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input.val input.val.root) =
          some sourceItems := by
      simpa only [OpenConcreteDiagram.rootWires] using sourceCompiled
    have targetCompiled' : ConcreteElaboration.compileOccurrencesWith? signature
        (fissionRaw input selected site producer residual)
        (ConcreteElaboration.compileRegion? signature
          (fissionRaw input selected site producer residual)
          (fissionRaw input selected site producer residual).regionCount)
        (targetOpen input selected site producer residual boundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences
          (fissionRaw input selected site producer residual)
          (fissionRaw input selected site producer residual).root) =
          some targetItems := by
      simpa only [OpenConcreteDiagram.rootWires] using targetCompiled
    have sourceCover :
        (ConcreteElaboration.BinderContext.empty :
          ConcreteElaboration.BinderContext input.val []).Covers site := by
      rw [← rootSite]
      exact ConcreteElaboration.BinderContext.empty_covers_root input.property
    have targetCover :
        (ConcreteElaboration.BinderContext.empty :
          ConcreteElaboration.BinderContext
            (fissionRaw input selected site producer residual) []).Covers
              site := by
      have atRoot :=
        ConcreteElaboration.BinderContext.empty_covers_root targetWellFormed
      have targetRootSite :
          (fissionRaw input selected site producer residual).root = site := by
        simpa [fissionRaw] using rootSite
      exact Eq.mp (congrArg
        (fun region =>
          (ConcreteElaboration.BinderContext.empty :
            ConcreteElaboration.BinderContext
              (fissionRaw input selected site producer residual) []).Covers
                region) targetRootSite) atRoot
    have sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
        input.val ConcreteElaboration.BinderContext.empty site := by
      rw [← rootSite]
      exact ConcreteElaboration.BinderContext.Enumeration.empty input.val
    have targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
        (fissionRaw input selected site producer residual)
        ConcreteElaboration.BinderContext.empty site := by
      have atRoot := ConcreteElaboration.BinderContext.Enumeration.empty
        (fissionRaw input selected site producer residual)
      have targetRootSite :
          (fissionRaw input selected site producer residual).root = site := by
        simpa [fissionRaw] using rootSite
      exact Eq.mp (congrArg
        (fun region => ConcreteElaboration.BinderContext.Enumeration
          (fissionRaw input selected site producer residual)
          ConcreteElaboration.BinderContext.empty region) targetRootSite) atRoot
    have relationMapEq :
        (fun {arity} => simulation.relationMap simulation.binders_empty :
          RelationRenaming [] []) = fun {arity} relation => relation := by
      rfl
    rw [relationMapEq, Region.renameRelations_id]
    apply ConcreteElaboration.finishRoot_denote direction
      (sourceOpen input boundary).exposedWires
      (sourceOpen input boundary).hiddenWires
      (targetOpen input selected site producer residual boundary).exposedWires
      (targetOpen input selected site producer residual boundary).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedIndex (input := input) (selected := selected) (site := site)
          (producer := producer) (residual := residual) (boundary := boundary)))
      Lambda.canonicalModel named sourceItems targetItems
    exact focusedRootTransport input selected site freePorts term portWire depth
      selectedTerm path producer residual nodeShape resolved selectedResult
      residualResult producerResult targetWellFormed boundary sourceRoot rootSite
      Lambda.canonicalModel named direction input.val.regionCount
      (fissionRaw input selected site producer residual).regionCount
      (fun child sourceItem targetItem parent sourceOccurrence targetOccurrence =>
        focusedChild_itemSimulation input selected site producer residual
          targetWellFormed Lambda.canonicalModel named direction
          input.val.regionCount
          (fissionRaw input selected site producer residual).regionCount
          (sourceOpen input boundary).rootWires
          (targetOpen input selected site producer residual boundary).rootWires
          embedding ConcreteElaboration.BinderContext.empty
          ConcreteElaboration.BinderContext.empty HEq.rfl sourceCover targetCover
          sourceEnumeration targetEnumeration
          (fun {childDirection child childSourceRels childTargetRels
              childSourceBinders childTargetBinders sourceBody targetBody}
              sourceParent targetParent childAllowed childBinderWitness
              childSourceCover childTargetCover childSourceEnumeration
              childTargetEnumeration sourceBodyCompiled targetBodyCompiled => by
            have transported := recurse
              (childDirection := childDirection) (child := child)
              (childSourceBinders := childSourceBinders)
              (childTargetBinders := childTargetBinders)
              (sourceBody := sourceBody) (targetBody := targetBody)
              (by simpa [rootSite] using sourceParent)
              (by simpa [simulation, fissionRaw, rootSite] using targetParent)
              childAllowed childBinderWitness childSourceCover childTargetCover
              childSourceEnumeration childTargetEnumeration
              (by simpa only [OpenConcreteDiagram.rootWires] using
                sourceBodyCompiled)
              (by simpa only [OpenConcreteDiagram.rootWires] using
                targetBodyCompiled)
            simpa [simulation] using transported)
          child parent sourceItem
          targetItem sourceOccurrence targetOccurrence)
      sourceItems targetItems sourceCompiled' targetCompiled'

end FissionSoundness

end VisualProof.Rule
