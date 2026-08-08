import VisualProof.Concrete.Step
import VisualProof.Refinement.Represents
import VisualProof.Refinement.Implementation.WireSeverNested
import VisualProof.Refinement.Implementation.WireSeverCanonical
import VisualProof.Refinement.Implementation.WireSeverResult
import VisualProof.Refinement.Implementation.WireSeverRootOpen
import VisualProof.Refinement.Implementation.WireJoinNested
import VisualProof.Refinement.Implementation.WireJoinResult
import VisualProof.Refinement.Implementation.WireJoinRootContext
import VisualProof.Refinement.Implementation.WireJoinRootOpen
import VisualProof.Rule.WireSever

namespace VisualProof.Refinement.WireSever

open VisualProof.Diagram

private def castOpenIso
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem castArity_castArity
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

private theorem atPolarity_castArity
    (equality : sourceArity = targetArity)
    {polarity : Polarity}
    {source target : OpenDiagram sourceArity}
    (step : Rule.atPolarity polarity Rule.WireSever source target) :
    Rule.atPolarity polarity Rule.WireSever
      (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using step

private theorem checkedElaborate_cast_eq
    {source target : Concrete.CheckedOpen}
    (equality : source = target)
    {arity : Nat}
    (sourceLength : source.val.boundary.length = arity)
    (targetLength : target.val.boundary.length = arity) :
    source.elaborate.castArity sourceLength =
      target.elaborate.castArity targetLength := by
  subst target
  have proofEq : sourceLength = targetLength := Subsingleton.elim _ _
  subst targetLength
  rfl

theorem wireSever
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    {receipt : Concrete.Receipt source}
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source
      (.wireSever wire keep boundary) = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
      | .forward => Rule.WireSever sourceDiagram targetDiagram
       | .backward => Rule.WireSever targetDiagram sourceDiagram) ∧
      StateRepresents receipt.target targetDiagram := by
  obtain ⟨result, operationSuccess, targetEq, realizes,
      operationPolarity⟩ :=
    Concrete.execute_wireSever_success wire keep boundary success
  let targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed :=
    (Concrete.applyWireSever_preserves_raw operationSuccess).symm ▸
      result.result.property
  let separated :=
    Implementation.WireSever.separatedOpen source wire keep boundary
      targetWellFormed
  let separatedLength : separated.val.boundary.length = arity := by
    simp [separated, Implementation.WireSever.separatedOpen]
  let sourceCanonical :=
    source.checked.elaborate.castArity source.boundary_length
  let separatedDiagram := separated.elaborate.castArity separatedLength
  have separatedStep :
      match orientation with
      | .forward => Rule.WireSever sourceCanonical separatedDiagram
      | .backward => Rule.WireSever separatedDiagram sourceCanonical := by
    by_cases scopeRoot :
        (source.checked.val.diagram.wires wire).scope =
          source.checked.val.diagram.root
    · have zeroDepth : Concrete.concreteCutDepth
          source.checked.val.diagram
          (source.checked.val.diagram.wires wire).scope = 0 := by
        rw [scopeRoot]
        exact Concrete.concreteCutDepth_root_eq_zero source.diagram
      cases orientation with
      | forward =>
          obtain reflects | split :=
            Implementation.WireSever.separatedBoundaryDichotomyRaw source wire
              keep boundary targetWellFormed
          · have concreteReflects := reflects
            simpa [sourceCanonical, separatedDiagram, separated,
              separatedLength] using
              Implementation.WireSever.root source wire keep boundary
                targetWellFormed scopeRoot concreteReflects
          · exact Or.inr (Implementation.WireSever.rootOpen source wire keep
              boundary targetWellFormed scopeRoot split)
      | backward =>
          simp [Concrete.erasurePolarity, zeroDepth] at operationPolarity
    · let canonical := Implementation.WireSever.canonicalOpen source.checked
          wire keep targetWellFormed
      have separatedEq :=
        Implementation.WireSever.separatedOpen_eq_canonical_of_nested source
          wire keep boundary targetWellFormed
            (fun equality => scopeRoot equality.symm)
      let targetView := Concrete.Splice.openSiteView_complete canonical
        (source.checked.val.diagram.wires wire).scope
      let sourceView := Concrete.Splice.openSiteView_complete source.checked
        (source.checked.val.diagram.wires wire).scope
      have nestedStep := Implementation.WireSeverNested.nested source.checked
        wire keep targetWellFormed (fun equality => scopeRoot equality.symm)
          targetView sourceView
      have castStep := atPolarity_castArity source.boundary_length nestedStep
      have targetDiagramEq :
          ((canonical.elaborate.castArity
              (VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq source.checked.val wire keep)).castArity
                source.boundary_length) = separatedDiagram := by
        rw [castArity_castArity]
        exact checkedElaborate_cast_eq separatedEq.symm
          ((VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq source.checked.val wire keep).trans
            source.boundary_length)
          separatedLength
      have normalizedStep : Rule.atPolarity sourceView.focus.context.polarity
          Rule.WireSever sourceCanonical separatedDiagram := by
        rw [← targetDiagramEq]
        simpa [sourceCanonical, canonical] using castStep
      have depthEq : Concrete.concreteCutDepth source.checked.val.diagram
          (source.checked.val.diagram.wires wire).scope =
          sourceView.focus.context.cutDepth :=
        Concrete.openSiteView_concreteCutDepth_eq sourceView
      cases orientation with
      | forward =>
          have even : sourceView.focus.context.cutDepth % 2 = 0 := by
            rw [← depthEq]
            exact operationPolarity
          have polarityEq : sourceView.focus.context.polarity =
              Polarity.positive := by
            unfold DiagramContext.polarity
            rw [if_pos even]
          rw [polarityEq] at normalizedStep
          simpa [Rule.atPolarity] using normalizedStep
      | backward =>
          have odd : sourceView.focus.context.cutDepth % 2 = 1 := by
            rw [← depthEq]
            exact operationPolarity
          have notEven : sourceView.focus.context.cutDepth % 2 ≠ 0 := by
            rw [odd]
            decide
          have polarityEq : sourceView.focus.context.polarity =
              Polarity.negative := by
            unfold DiagramContext.polarity
            rw [if_neg notEven]
          rw [polarityEq] at normalizedStep
          simpa [Rule.atPolarity, Rule.converse] using normalizedStep
  let targetState := Concrete.wireSeverResultState orientation source wire keep
    boundary result operationSuccess
  let targetCanonical :=
    targetState.checked.elaborate.castArity targetState.boundary_length
  let resultConcreteIso :=
    Implementation.WireSever.separatedOpen_resultOpen_iso source wire keep
      boundary result operationSuccess
  have resultElabIso := resultConcreteIso.elaborate_isomorphic
    separated.property targetState.checked.property
  have targetIso : OpenDiagramIso separatedDiagram targetCanonical := by
    have castIso := castOpenIso separatedLength resultElabIso
    rw [castArity_castArity] at castIso
    simpa [separatedDiagram, targetCanonical, targetState,
      resultConcreteIso] using castIso
  have sourceCanonicalRep : StateRepresents source sourceCanonical :=
    StateRepresents.checked source
  obtain ⟨sourceIso⟩ :=
    StateRepresents.unique sourceRep sourceCanonicalRep
  have targetCanonicalRep : StateRepresents targetState targetCanonical :=
    StateRepresents.checked targetState
  refine ⟨targetCanonical, ?_, ?_⟩
  · cases orientation with
    | forward =>
        exact Rule.WireSever.iso sourceIso.symm separatedStep targetIso
    | backward =>
        exact Rule.WireSever.iso targetIso separatedStep sourceIso.symm
  · rw [targetEq]
    exact targetCanonicalRep

end VisualProof.Refinement.WireSever

namespace VisualProof.Refinement.WireJoin

open VisualProof.Diagram

private def castOpenIso
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem castArity_castArity
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

private theorem atPolarity_castArity
    (equality : sourceArity = targetArity)
    {polarity : Polarity}
    {source target : OpenDiagram sourceArity}
    (step : Rule.atPolarity polarity Rule.WireSever source target) :
    Rule.atPolarity polarity Rule.WireSever
      (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using step

private theorem wireSever_castArity
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (step : Rule.WireSever source target) :
    Rule.WireSever
      (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using step

private theorem contextualStep
    {orientation : Concrete.Orientation}
    (source : Concrete.CheckedOpen)
    (site : Fin source.val.diagram.regionCount)
    (sourceView : Concrete.Splice.OpenSiteView source site)
    (operationPolarity : Concrete.spawnPolarity orientation
      (Concrete.concreteCutDepth source.val.diagram site))
    (target : Concrete.CheckedOpen)
    (boundaryLength : target.val.boundary.length =
      source.val.boundary.length)
    (sourceLength : source.val.boundary.length = arity)
    (targetLength : target.val.boundary.length = arity)
    (step : Rule.atPolarity sourceView.focus.context.polarity
      Rule.WireSever target.elaborate
        (source.elaborate.castArity boundaryLength.symm)) :
    match orientation with
    | .forward => Rule.WireSever
        (source.elaborate.castArity sourceLength)
        (target.elaborate.castArity targetLength)
    | .backward => Rule.WireSever
        (target.elaborate.castArity targetLength)
        (source.elaborate.castArity sourceLength) := by
  have castStep := atPolarity_castArity targetLength step
  have sourceEq :
      ((source.elaborate.castArity boundaryLength.symm).castArity
        targetLength) = source.elaborate.castArity sourceLength := by
    rw [castArity_castArity]
  rw [sourceEq] at castStep
  have depthEq : Concrete.concreteCutDepth source.val.diagram site =
      sourceView.focus.context.cutDepth :=
    Concrete.openSiteView_concreteCutDepth_eq sourceView
  cases orientation with
  | forward =>
      have odd : sourceView.focus.context.cutDepth % 2 = 1 := by
        rw [← depthEq]
        exact operationPolarity
      have notEven : sourceView.focus.context.cutDepth % 2 ≠ 0 := by
        rw [odd]
        decide
      have polarityEq : sourceView.focus.context.polarity =
          Polarity.negative := by
        unfold DiagramContext.polarity
        rw [if_neg notEven]
      rw [polarityEq] at castStep
      simpa [Rule.atPolarity, Rule.converse] using castStep
  | backward =>
      have even : sourceView.focus.context.cutDepth % 2 = 0 := by
        rw [← depthEq]
        exact operationPolarity
      have polarityEq : sourceView.focus.context.polarity =
          Polarity.positive := by
        unfold DiagramContext.polarity
        rw [if_pos even]
      rw [polarityEq] at castStep
      simpa [Rule.atPolarity] using castStep

private theorem contextualStepIso
    {orientation : Concrete.Orientation}
    (source : Concrete.CheckedOpen)
    (site : Fin source.val.diagram.regionCount)
    (sourceView : Concrete.Splice.OpenSiteView source site)
    (operationPolarity : Concrete.spawnPolarity orientation
      (Concrete.concreteCutDepth source.val.diagram site))
    (target normalized : Concrete.CheckedOpen)
    (targetIso : Concrete.OpenIso target.val normalized.val)
    (normalizedBoundary : normalized.val.boundary.length =
      source.val.boundary.length)
    (sourceLength : source.val.boundary.length = arity)
    (targetLength : target.val.boundary.length = arity)
    (normalizedLength : normalized.val.boundary.length = arity)
    (step : Rule.atPolarity sourceView.focus.context.polarity
      Rule.WireSever normalized.elaborate
        (source.elaborate.castArity normalizedBoundary.symm)) :
    match orientation with
    | .forward => Rule.WireSever
        (source.elaborate.castArity sourceLength)
        (target.elaborate.castArity targetLength)
    | .backward => Rule.WireSever
        (target.elaborate.castArity targetLength)
        (source.elaborate.castArity sourceLength) := by
  have normalizedStep := contextualStep source site sourceView
    operationPolarity normalized normalizedBoundary sourceLength
      normalizedLength step
  have elaboratedIso := targetIso.elaborate_isomorphic
    target.property normalized.property
  have castIso := castOpenIso targetLength elaboratedIso
  rw [castArity_castArity] at castIso
  have proofEq : targetIso.boundary_length_eq.symm.trans targetLength =
      normalizedLength := Subsingleton.elim _ _
  rw [proofEq] at castIso
  cases orientation with
  | forward =>
      exact Rule.WireSever.iso (OpenDiagramIso.refl _)
        normalizedStep castIso.symm
  | backward =>
      exact Rule.WireSever.iso castIso.symm normalizedStep
        (OpenDiagramIso.refl _)

private theorem rootOpenStep
    {orientation : Concrete.Orientation}
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner).WellFormed)
    (scopeRoot : (source.val.diagram.wires inner).scope =
      source.val.diagram.root)
    (outerExposed : outer ∈ source.val.exposedWires)
    (innerExposed : inner ∈ source.val.exposedWires)
    (operationPolarity : Concrete.spawnPolarity orientation
      (Concrete.concreteCutDepth source.val.diagram
        (source.val.diagram.wires inner).scope))
    (sourceLength : source.val.boundary.length = arity)
    (targetLength :
      (VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct ordered
        targetWellFormed).val.boundary.length = arity) :
    let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
      ordered targetWellFormed
    match orientation with
    | .forward => Rule.WireSever
        (source.elaborate.castArity sourceLength)
        (target.elaborate.castArity targetLength)
    | .backward => Rule.WireSever
        (target.elaborate.castArity targetLength)
        (source.elaborate.castArity sourceLength) := by
  dsimp only
  let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
    ordered targetWellFormed
  let boundaryLength : target.val.boundary.length =
      source.val.boundary.length :=
    VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq source.val outer inner distinct
  have zeroDepth : Concrete.concreteCutDepth source.val.diagram
      (source.val.diagram.wires inner).scope = 0 := by
    rw [scopeRoot]
    exact Concrete.concreteCutDepth_root_eq_zero
      ⟨source.val.diagram, source.property.diagram_well_formed⟩
  cases orientation with
  | forward =>
      simp [Concrete.spawnPolarity, zeroDepth] at operationPolarity
  | backward =>
      have rootStep : Rule.WireSever
          (target.elaborate.castArity boundaryLength) source.elaborate :=
        Or.inr (Implementation.WireJoin.rootOpen source outer inner distinct
          ordered targetWellFormed scopeRoot outerExposed innerExposed)
      have castStep := wireSever_castArity sourceLength rootStep
      rw [castArity_castArity] at castStep
      simpa [target, boundaryLength] using castStep

theorem wireJoin
    {arity : Nat}
    {source : Concrete.State arity}
    {sourceDiagram : OpenDiagram arity}
    {orientation : Concrete.Orientation}
    (first second : Fin source.checked.val.diagram.wireCount)
    {receipt : Concrete.Receipt source}
    (sourceRep : StateRepresents source sourceDiagram)
    (success : Concrete.execute orientation source
      (.wireJoin first second) = .ok receipt) :
    ∃ targetDiagram : OpenDiagram arity,
      (match orientation with
      | .forward => Rule.WireSever sourceDiagram targetDiagram
      | .backward => Rule.WireSever targetDiagram sourceDiagram) ∧
      StateRepresents receipt.target targetDiagram := by
  obtain ⟨result, _operationSuccess, packed, distinct, execution⟩ :=
    Concrete.execute_wireJoin_success first second success
  have orderedRefinement : ∀
      (outer inner : Fin source.checked.val.diagram.wireCount)
      (orderedDistinct : outer ≠ inner)
      (ordered : source.checked.val.diagram.Encloses
        (source.checked.val.diagram.wires outer).scope
        (source.checked.val.diagram.wires inner).scope)
      (operationPolarity : Concrete.spawnPolarity orientation
        (Concrete.concreteCutDepth source.checked.val.diagram
          (source.checked.val.diagram.wires inner).scope))
      (realizes : result.Realizes
        (Concrete.joinWireRaw source.checked.val.diagram outer inner)
        (Concrete.joinWireProvenance source.checked.val.diagram outer inner)
        (Concrete.joinWireWireTransport source.checked.val.diagram outer inner)),
      ∃ targetDiagram : OpenDiagram arity,
        (match orientation with
        | .forward => Rule.WireSever sourceDiagram targetDiagram
        | .backward => Rule.WireSever targetDiagram sourceDiagram) ∧
        StateRepresents receipt.target targetDiagram := by
    intro outer inner orderedDistinct ordered operationPolarity realizes
    let targetWellFormed :
        (Concrete.joinWireRaw source.checked.val.diagram outer inner).WellFormed :=
      realizes.result_eq ▸ result.result.property
    let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source.checked outer inner
      orderedDistinct ordered targetWellFormed
    let targetLength : target.val.boundary.length = arity :=
      (VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq source.checked.val outer inner
        orderedDistinct).trans source.boundary_length
    let sourceCanonical :=
      source.checked.elaborate.castArity source.boundary_length
    let targetJoined := target.elaborate.castArity targetLength
    have canonicalStep :
        match orientation with
        | .forward => Rule.WireSever sourceCanonical targetJoined
        | .backward => Rule.WireSever targetJoined sourceCanonical := by
      by_cases scopeRoot :
          (source.checked.val.diagram.wires inner).scope =
            source.checked.val.diagram.root
      · by_cases bothExposed :
            outer ∈ source.checked.val.exposedWires ∧
              inner ∈ source.checked.val.exposedWires
        · cases orientation with
          | forward =>
              simpa [sourceCanonical, targetJoined, target] using
                rootOpenStep source.checked outer inner orderedDistinct ordered
                  targetWellFormed scopeRoot bothExposed.1 bothExposed.2
                    operationPolarity source.boundary_length targetLength
          | backward =>
              simpa [sourceCanonical, targetJoined, target] using
                rootOpenStep source.checked outer inner orderedDistinct ordered
                  targetWellFormed scopeRoot bothExposed.1 bothExposed.2
                    operationPolarity source.boundary_length targetLength
        · cases orientation with
          | forward =>
              have zeroDepth : Concrete.concreteCutDepth
                  source.checked.val.diagram
                  (source.checked.val.diagram.wires inner).scope = 0 := by
                rw [scopeRoot]
                exact Concrete.concreteCutDepth_root_eq_zero source.diagram
              simp [Concrete.spawnPolarity, zeroDepth] at operationPolarity
          | backward =>
              have rootStep := Implementation.WireJoin.rootContext
                source.checked outer inner orderedDistinct ordered
                  targetWellFormed scopeRoot bothExposed
              dsimp only at rootStep
              have castStep := wireSever_castArity source.boundary_length
                rootStep
              have targetCastEq :
                  ((target.elaborate.castArity
                    (Implementation.WireJoin.boundaryLengthEq
                      source.checked.val outer inner orderedDistinct)).castArity
                        source.boundary_length) = targetJoined := by
                rw [castArity_castArity]
              rw [targetCastEq] at castStep
              simpa [sourceCanonical, targetJoined, target] using castStep
      · have nested : source.checked.val.diagram.root ≠
            (source.checked.val.diagram.wires inner).scope :=
          fun equality => scopeRoot equality.symm
        let sourceView := Concrete.Splice.openSiteView_complete
          source.checked (source.checked.val.diagram.wires inner).scope
        let targetView := Concrete.Splice.openSiteView_complete
          target (source.checked.val.diagram.wires inner).scope
        have nestedStep := Implementation.WireJoinNested.nested source.checked
          outer inner orderedDistinct ordered targetWellFormed nested
            sourceView targetView
        cases orientation with
        | forward =>
            simpa [sourceCanonical, targetJoined, target] using
              contextualStep source.checked
                (source.checked.val.diagram.wires inner).scope sourceView
                  operationPolarity target
                    (Implementation.WireJoin.boundaryLengthEq source.checked.val
                      outer inner orderedDistinct)
                    source.boundary_length targetLength nestedStep
        | backward =>
            simpa [sourceCanonical, targetJoined, target] using
              contextualStep source.checked
                (source.checked.val.diagram.wires inner).scope sourceView
                  operationPolarity target
                    (Implementation.WireJoin.boundaryLengthEq source.checked.val
                      outer inner orderedDistinct)
                    source.boundary_length targetLength nestedStep
    let targetCanonical := receipt.target.checked.elaborate.castArity
      receipt.target.boundary_length
    let resultConcreteIso :=
      Implementation.WireJoin.targetOpen_result_iso source outer inner
        orderedDistinct ordered realizes packed
    have resultElabIso := resultConcreteIso.elaborate_isomorphic
      target.property receipt.target.checked.property
    have targetIso : OpenDiagramIso targetJoined targetCanonical := by
      have castIso := castOpenIso targetLength resultElabIso
      rw [castArity_castArity] at castIso
      have proofEq : resultConcreteIso.boundary_length_eq.symm.trans
          targetLength = receipt.target.boundary_length :=
        Subsingleton.elim _ _
      rw [proofEq] at castIso
      simpa [targetJoined, targetCanonical] using castIso
    have sourceCanonicalRep : StateRepresents source sourceCanonical :=
      StateRepresents.checked source
    obtain ⟨sourceIso⟩ :=
      StateRepresents.unique sourceRep sourceCanonicalRep
    have targetCanonicalRep :
        StateRepresents receipt.target targetCanonical :=
      StateRepresents.checked receipt.target
    refine ⟨targetCanonical, ?_, targetCanonicalRep⟩
    cases orientation with
    | forward =>
        exact Rule.WireSever.iso sourceIso.symm canonicalStep targetIso
    | backward =>
        exact Rule.WireSever.iso targetIso canonicalStep sourceIso.symm
  rcases execution with forwardOrder | reverseOrder
  · obtain ⟨targetDiagram, step, represents⟩ :=
      orderedRefinement first second distinct forwardOrder.1
        forwardOrder.2.1 forwardOrder.2.2
    refine ⟨targetDiagram, ?_, represents⟩
    cases orientation <;> exact step
  · obtain ⟨targetDiagram, step, represents⟩ :=
      orderedRefinement second first distinct.symm reverseOrder.1
        reverseOrder.2.1 reverseOrder.2.2
    refine ⟨targetDiagram, ?_, represents⟩
    cases orientation <;> exact step

end VisualProof.Refinement.WireJoin
