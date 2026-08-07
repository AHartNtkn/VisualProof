import VisualProof.Refinement.Implementation.WireJoinSwap
import VisualProof.Refinement.Implementation.WireSever

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof
open VisualProof.Diagram

private noncomputable def restoreJoinWireEquiv
    (input : Concrete.Diagram)
    (inner : Fin input.wireCount) :
    FiniteEquiv
      (Fin ((Concrete.joinWireDomain input inner).count + 1))
      (Fin input.wireCount) where
  toFun := Fin.lastCases inner (Concrete.joinWireDomain input inner).origin
  invFun := fun wire =>
    if equality : wire = inner then
      Fin.last (Concrete.joinWireDomain input inner).count
    else
      Fin.castSucc ((Concrete.joinWireDomain input inner).index wire (by
        simp [Concrete.joinWireDomain, equality]))
  left_inv := by
    intro wire
    refine Fin.lastCases ?_ (fun survivor => ?_) wire
    · simp
    · have survives := (Concrete.joinWireDomain input inner).origin_survives
          survivor
      have distinct : (Concrete.joinWireDomain input inner).origin survivor ≠
          inner := by
        simpa [Concrete.joinWireDomain] using survives
      simp only [Fin.lastCases_castSucc]
      change (if equality :
          (Concrete.joinWireDomain input inner).origin survivor = inner then
            Fin.last (Concrete.joinWireDomain input inner).count
          else
            Fin.castSucc ((Concrete.joinWireDomain input inner).index
              ((Concrete.joinWireDomain input inner).origin survivor) _)) =
        survivor.castSucc
      rw [dif_neg distinct]
      exact congrArg Fin.castSucc
        ((Concrete.joinWireDomain input inner).index_origin survivor)
  right_inv := by
    intro wire
    by_cases equality : wire = inner
    · subst wire
      simp
    · rw [dif_neg equality]
      rw [Fin.lastCases_castSucc]
      change (Concrete.joinWireDomain input inner).origin
          ((Concrete.joinWireDomain input inner).index wire _) = wire
      exact (Concrete.joinWireDomain input inner).origin_index wire (by
        simp [Concrete.joinWireDomain, equality])

@[simp] private theorem restoreJoinWireEquiv_last
    (input : Concrete.Diagram) (inner : Fin input.wireCount) :
    restoreJoinWireEquiv input inner
        (Fin.last (Concrete.joinWireDomain input inner).count) = inner := by
  simp [restoreJoinWireEquiv]

@[simp] private theorem restoreJoinWireEquiv_castSucc
    (input : Concrete.Diagram) (inner : Fin input.wireCount)
    (survivor : Fin (Concrete.joinWireDomain input inner).count) :
    restoreJoinWireEquiv input inner survivor.castSucc =
      (Concrete.joinWireDomain input inner).origin survivor := by
  simp [restoreJoinWireEquiv]

private noncomputable def severJoinDiagramIso
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (sameScope : (input.wires outer).scope =
      (input.wires inner).scope) :
    Concrete.Iso
      (Concrete.severWireRaw
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
        (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct outer)
        (input.wires outer).endpoints)
      input := by
  classical
  let domain := Concrete.joinWireDomain input inner
  let joined := VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct outer
  let outerEndpoints := (input.wires outer).endpoints
  let innerEndpoints := (input.wires inner).endpoints
  have disjoint : ∀ endpoint, endpoint ∈ outerEndpoints →
      endpoint ∉ innerEndpoints := by
    intro endpoint outerMember innerMember
    have absent := inputWellFormed.wire_endpoints_are_disjoint outer inner
      (bne_iff_ne.mpr distinct) endpoint outerMember
    by_cases occurs : input.EndpointOccurs inner endpoint
    · simp [occurs] at absent
    · exact occurs innerMember
  have keepFilter : List.filter
      (fun endpoint => decide (endpoint ∈ outerEndpoints))
      (outerEndpoints ++ innerEndpoints) = outerEndpoints := by
    rw [List.filter_append]
    have outerFilter : List.filter
        (fun endpoint => decide (endpoint ∈ outerEndpoints))
        outerEndpoints = outerEndpoints := by
      apply List.filter_eq_self.2
      intro endpoint member
      exact decide_eq_true member
    have innerFilter : List.filter
        (fun endpoint => decide (endpoint ∈ outerEndpoints))
        innerEndpoints = [] := by
      apply List.filter_eq_nil_iff.2
      intro endpoint innerMember accepted
      exact disjoint endpoint (of_decide_eq_true accepted) innerMember
    rw [outerFilter, innerFilter, List.append_nil]
  have removeFilter : List.filter
      (fun endpoint => decide (endpoint ∉ outerEndpoints))
      (outerEndpoints ++ innerEndpoints) = innerEndpoints := by
    rw [List.filter_append]
    have outerFilter : List.filter
        (fun endpoint => decide (endpoint ∉ outerEndpoints))
        outerEndpoints = [] := by
      apply List.filter_eq_nil_iff.2
      intro endpoint member accepted
      exact (of_decide_eq_true accepted) member
    have innerFilter : List.filter
        (fun endpoint => decide (endpoint ∉ outerEndpoints))
        innerEndpoints = innerEndpoints := by
      apply List.filter_eq_self.2
      intro endpoint member
      exact decide_eq_true (disjoint endpoint · member)
    rw [outerFilter, innerFilter, List.nil_append]
  let wireEquiv := restoreJoinWireEquiv input inner
  have renameRefl (values : List (Concrete.CEndpoint input.nodeCount)) :
      values.map (Concrete.CEndpoint.rename (FiniteEquiv.refl _)) = values := by
    induction values with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.map_cons, Concrete.CEndpoint.rename_refl, ih]
  have joinedOrigin : domain.origin joined = outer := by
    simpa [domain, joined, distinct] using
      (VisualProof.Refinement.Implementation.WireJoin.origin_wireMap
        input outer inner outer distinct)
  refine {
    regionCount_eq := rfl
    nodeCount_eq := rfl
    wireCount_eq := by
      apply Nat.le_antisymm
      · exact VisualProof.Data.Finite.fin_card_le_of_injective wireEquiv
          wireEquiv.injective
      · exact VisualProof.Data.Finite.fin_card_le_of_injective wireEquiv.symm
          wireEquiv.symm.injective
    regions := FiniteEquiv.refl _
    nodes := FiniteEquiv.refl _
    wires := wireEquiv
    root_eq := rfl
    regions_eq := by intro region; exact Concrete.CRegion.rename_refl _
    nodes_eq := by intro node; exact Concrete.CNode.rename_refl _
    wire_scope_eq := ?_
    wire_endpoints_perm := ?_
  }
  · intro wire
    refine Fin.lastCases ?_ (fun survivor => ?_) wire
    · have wireImage : wireEquiv
          (Fin.last (VisualProof.Refinement.Implementation.WireJoin.Target
            input outer inner).wireCount) = inner := by
        change restoreJoinWireEquiv input inner
          (Fin.last (Concrete.joinWireDomain input inner).count) = inner
        exact restoreJoinWireEquiv_last input inner
      rw [wireImage]
      have joinedScope :=
          VisualProof.Refinement.Implementation.WireJoin.target_wire_scope
            input outer inner outer distinct
      simpa [Concrete.severWireRaw, wireEquiv, joined, distinct,
        sameScope] using joinedScope
    · let original := domain.origin survivor
      have wireImage : wireEquiv survivor.castSucc = original := by
        change restoreJoinWireEquiv input inner survivor.castSucc =
          (Concrete.joinWireDomain input inner).origin survivor
        exact restoreJoinWireEquiv_castSucc input inner survivor
      rw [wireImage]
      have originalNeInner : original ≠ inner := by
        have survives := domain.origin_survives survivor
        have : ¬ domain.origin survivor = inner := by
          simpa [domain, Concrete.joinWireDomain] using survives
        simpa [original] using this
      have survivorMap :
          VisualProof.Refinement.Implementation.WireJoin.wireMap
              input outer inner distinct original = survivor := by
        rw [VisualProof.Refinement.Implementation.WireJoin.wireMap_of_ne
          input outer inner original distinct originalNeInner]
        exact domain.index_origin survivor
      have targetScope :=
        VisualProof.Refinement.Implementation.WireJoin.target_wire_scope
          input outer inner original distinct
      rw [survivorMap] at targetScope
      simp only [if_neg originalNeInner] at targetScope
      by_cases originalOuter : original = outer
      · have survivorJoined : survivor = joined := by
          apply domain.origin_injective
          exact originalOuter.trans joinedOrigin.symm
        simpa [Concrete.severWireRaw, wireEquiv, joined,
          survivorJoined] using targetScope
      · have survivorNeJoined : survivor ≠ joined := by
          intro equality
          apply originalOuter
          have mapped := congrArg domain.origin equality
          exact mapped.trans joinedOrigin
        simpa [Concrete.severWireRaw, wireEquiv, joined,
          survivorNeJoined] using targetScope
  · intro wire
    refine Fin.lastCases ?_ (fun survivor => ?_) wire
    · have wireImage : wireEquiv
          (Fin.last (VisualProof.Refinement.Implementation.WireJoin.Target
            input outer inner).wireCount) = inner := by
        change restoreJoinWireEquiv input inner
          (Fin.last (Concrete.joinWireDomain input inner).count) = inner
        exact restoreJoinWireEquiv_last input inner
      rw [wireImage]
      have joinedEndpoints :=
          VisualProof.Refinement.Implementation.WireJoin.target_wire_endpoints
            input outer inner outer distinct
      have removed : List.filter
          (fun endpoint => decide
            (endpoint ∉ (input.wires outer).endpoints))
          ((VisualProof.Refinement.Implementation.WireJoin.Target
            input outer inner).wires joined).endpoints =
          (input.wires inner).endpoints := by
        rw [joinedEndpoints]
        simpa [outerEndpoints, innerEndpoints] using removeFilter
      simp only [Concrete.severWireRaw, Fin.lastCases_last]
      change (List.filter
          (fun endpoint => decide
            (endpoint ∉ (input.wires outer).endpoints))
          ((VisualProof.Refinement.Implementation.WireJoin.Target
            input outer inner).wires joined).endpoints |>.map
              (Concrete.CEndpoint.rename (FiniteEquiv.refl _))).Perm
        (input.wires inner).endpoints
      rw [removed, renameRefl]
    · let original := domain.origin survivor
      have wireImage : wireEquiv survivor.castSucc = original := by
        change restoreJoinWireEquiv input inner survivor.castSucc =
          (Concrete.joinWireDomain input inner).origin survivor
        exact restoreJoinWireEquiv_castSucc input inner survivor
      rw [wireImage]
      have originalNeInner : original ≠ inner := by
        have survives := domain.origin_survives survivor
        have : ¬ domain.origin survivor = inner := by
          simpa [domain, Concrete.joinWireDomain] using survives
        simpa [original] using this
      have survivorMap :
          VisualProof.Refinement.Implementation.WireJoin.wireMap
              input outer inner distinct original = survivor := by
        rw [VisualProof.Refinement.Implementation.WireJoin.wireMap_of_ne
          input outer inner original distinct originalNeInner]
        exact domain.index_origin survivor
      have targetEndpoints :=
        VisualProof.Refinement.Implementation.WireJoin.target_wire_endpoints
          input outer inner original distinct
      rw [survivorMap] at targetEndpoints
      by_cases originalOuter : original = outer
      · have survivorJoined : survivor = joined := by
          apply domain.origin_injective
          exact originalOuter.trans joinedOrigin.symm
        have kept : List.filter
            (fun endpoint => decide
              (endpoint ∈ (input.wires outer).endpoints))
            ((VisualProof.Refinement.Implementation.WireJoin.Target
              input outer inner).wires survivor).endpoints =
            (input.wires outer).endpoints := by
          rw [targetEndpoints]
          simp only [originalOuter]
          simpa [outerEndpoints, innerEndpoints] using keepFilter
        simp only [Concrete.severWireRaw, Fin.lastCases_castSucc]
        rw [if_pos survivorJoined]
        rw [originalOuter]
        have keptJoined : List.filter
            (fun endpoint => decide
              (endpoint ∈ (input.wires outer).endpoints))
            ((VisualProof.Refinement.Implementation.WireJoin.Target
              input outer inner).wires joined).endpoints =
            (input.wires outer).endpoints := by
          simpa only [survivorJoined] using kept
        change (List.filter
            (fun endpoint => decide
              (endpoint ∈ (input.wires outer).endpoints))
            ((VisualProof.Refinement.Implementation.WireJoin.Target
              input outer inner).wires joined).endpoints |>.map
                (Concrete.CEndpoint.rename (FiniteEquiv.refl _))).Perm
          (input.wires outer).endpoints
        rw [keptJoined, renameRefl]
      · have survivorNeJoined : survivor ≠ joined := by
          intro equality
          apply originalOuter
          have mapped := congrArg domain.origin equality
          exact mapped.trans joinedOrigin
        simp only [if_neg originalNeInner, if_neg originalOuter] at targetEndpoints
        simp only [Concrete.severWireRaw, Fin.lastCases_castSucc]
        rw [if_neg survivorNeJoined, targetEndpoints]
        change ((input.wires original).endpoints.map
            (Concrete.CEndpoint.rename (FiniteEquiv.refl _))).Perm
          (input.wires original).endpoints
        rw [renameRefl]

private noncomputable def severJoinOpenIso
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (sameScope : (source.val.diagram.wires outer).scope =
      (source.val.diagram.wires inner).scope)
    (innerHidden : inner ∉ source.val.exposedWires) :
    Concrete.OpenIso
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw
          source.val outer inner distinct)
        (VisualProof.Refinement.Implementation.WireJoin.wireMap
          source.val.diagram outer inner distinct outer)
        (source.val.diagram.wires outer).endpoints)
      source.val := by
  let diagramIso := severJoinDiagramIso source.val.diagram
    source.property.diagram_well_formed outer inner distinct sameScope
  refine {
    diagram := diagramIso
    boundary := ?_
  }
  simp only [VisualProof.Refinement.Implementation.WireSever.severWireRawOpen,
    VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw]
  rw [List.map_map, List.map_map]
  calc
    _ = source.val.boundary.map id := by
      apply List.map_congr_left
      intro wire member
      have wireNe : wire ≠ inner := by
        intro equality
        subst wire
        exact innerHidden
          ((Concrete.OpenDiagram.mem_exposedWires source.val inner).2 member)
      change diagramIso.wires
          (Fin.castSucc
            (VisualProof.Refinement.Implementation.WireJoin.wireMap
              source.val.diagram outer inner distinct wire)) = wire
      have castImage : diagramIso.wires
          (Fin.castSucc
            (VisualProof.Refinement.Implementation.WireJoin.wireMap
              source.val.diagram outer inner distinct wire)) =
          (Concrete.joinWireDomain source.val.diagram inner).origin
            (VisualProof.Refinement.Implementation.WireJoin.wireMap
              source.val.diagram outer inner distinct wire) := by
        change restoreJoinWireEquiv source.val.diagram inner
            (Fin.castSucc
              (VisualProof.Refinement.Implementation.WireJoin.wireMap
                source.val.diagram outer inner distinct wire)) = _
        exact restoreJoinWireEquiv_castSucc source.val.diagram inner _
      rw [castImage]
      change (Concrete.joinWireDomain source.val.diagram inner).origin
          (VisualProof.Refinement.Implementation.WireJoin.wireMap
            source.val.diagram outer inner distinct wire) = wire
      rw [VisualProof.Refinement.Implementation.WireJoin.origin_wireMap]
      simp [wireNe]
    _ = source.val.boundary := List.map_id _

private def castOpenIso
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality)
      (target.castArity equality) := by
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

private theorem wireSever_castArity
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (step : Rule.WireSever source target) :
    Rule.WireSever (source.castArity equality)
      (target.castArity equality) := by
  subst targetArity
  simpa using step

private theorem wireSever_castTargetTrans
    {firstArity middleArity finalArity : Nat}
    (first : firstArity = middleArity)
    (second : middleArity = finalArity)
    {source : OpenDiagram middleArity}
    {target : OpenDiagram firstArity}
    (step : Rule.WireSever source (target.castArity first)) :
    Rule.WireSever (source.castArity second)
      (target.castArity (first.trans second)) := by
  subst middleArity
  subst finalArity
  simpa using step

private def castOpenIsoCancel
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source : OpenDiagram sourceArity}
    {target : OpenDiagram targetArity}
    (iso : OpenDiagramIso source
      (target.castArity equality.symm)) :
    OpenDiagramIso (source.castArity equality) target := by
  subst targetArity
  simpa using iso

private def castOpenIsoTargetTrans
    {firstArity middleArity finalArity : Nat}
    (first : firstArity = middleArity)
    (second : middleArity = finalArity)
    {source : OpenDiagram middleArity}
    {target : OpenDiagram firstArity}
    (iso : OpenDiagramIso source (target.castArity first)) :
    OpenDiagramIso (source.castArity second)
      (target.castArity (first.trans second)) := by
  subst middleArity
  subst finalArity
  simpa using iso

private theorem rootContextHiddenInner
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
    (innerHidden : inner ∉ source.val.exposedWires) :
    let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
      ordered targetWellFormed
    let boundaryLength := VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq
      source.val outer inner distinct
    Rule.WireSever (target.elaborate.castArity boundaryLength)
      source.elaborate := by
  dsimp only
  let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
    ordered targetWellFormed
  let joined := VisualProof.Refinement.Implementation.WireJoin.wireMap
    source.val.diagram outer inner distinct outer
  let keep := (source.val.diagram.wires outer).endpoints
  have outerScopeRoot : (source.val.diagram.wires outer).scope =
      source.val.diagram.root := by
    have outerEnclosesRoot : source.val.diagram.Encloses
        (source.val.diagram.wires outer).scope source.val.diagram.root := by
      simpa only [scopeRoot] using ordered
    exact Concrete.Elaboration.encloses_sheet_eq
      source.property.diagram_well_formed.root_is_sheet outerEnclosesRoot
  have sameScope : (source.val.diagram.wires outer).scope =
      (source.val.diagram.wires inner).scope :=
    outerScopeRoot.trans scopeRoot.symm
  let rawIso := severJoinOpenIso source outer inner distinct sameScope
    innerHidden
  let severWellFormed :
      (VisualProof.Refinement.Implementation.WireSever.severWireRawOpen
        target.val joined keep).WellFormed :=
    rawIso.symm.wellFormed_transport source.property
  let canonical := VisualProof.Refinement.Implementation.WireSever.canonicalOpen
    target joined keep severWellFormed.diagram_well_formed
  have joinedScope : (target.val.diagram.wires joined).scope =
      target.val.diagram.root := by
    have mapped := VisualProof.Refinement.Implementation.WireJoin.target_wire_scope
      source.val.diagram outer inner outer distinct
    simpa [target, joined, VisualProof.Refinement.Implementation.WireJoin.targetOpen,
      outerScopeRoot] using mapped
  let severLength :=
    VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq
      target.val joined keep
  have base : Rule.WireSever target.elaborate
      (canonical.elaborate.castArity
        (VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq
          target.val joined keep)) :=
    VisualProof.Refinement.Implementation.WireSever.canonicalRoot
      target joined keep severWellFormed.diagram_well_formed joinedScope
  have normalizedBase : Rule.WireSever target.elaborate
      (canonical.elaborate.castArity severLength) := by
    simpa [severLength] using base
  let boundaryLength := VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq
    source.val outer inner distinct
  have castBase := wireSever_castTargetTrans severLength boundaryLength
    normalizedBase
  let rawElaborated := rawIso.elaborate_isomorphic severWellFormed
    source.property
  let combined :=
    severLength.trans boundaryLength
  have combinedEq : combined = rawIso.boundary_length_eq :=
    Subsingleton.elim _ _
  have normalizedCastBase : Rule.WireSever
      (target.elaborate.castArity boundaryLength)
      (canonical.elaborate.castArity rawIso.boundary_length_eq) := by
    simpa only [combinedEq] using castBase
  let transported := castOpenIsoCancel rawIso.boundary_length_eq
    rawElaborated
  exact Rule.WireSever.iso (OpenDiagramIso.refl _)
    normalizedCastBase transported

theorem rootContext
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
    (notBoth : ¬ (outer ∈ source.val.exposedWires ∧
      inner ∈ source.val.exposedWires)) :
    let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
      ordered targetWellFormed
    let boundaryLength := VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq
      source.val outer inner distinct
    Rule.WireSever (target.elaborate.castArity boundaryLength)
      source.elaborate := by
  dsimp only
  by_cases innerExposed : inner ∈ source.val.exposedWires
  · have outerHidden : outer ∉ source.val.exposedWires := by
      intro outerExposed
      exact notBoth ⟨outerExposed, innerExposed⟩
    have outerScopeRoot : (source.val.diagram.wires outer).scope =
        source.val.diagram.root := by
      have outerEnclosesRoot : source.val.diagram.Encloses
          (source.val.diagram.wires outer).scope source.val.diagram.root := by
        simpa only [scopeRoot] using ordered
      exact Concrete.Elaboration.encloses_sheet_eq
        source.property.diagram_well_formed.root_is_sheet outerEnclosesRoot
    have sameScope : (source.val.diagram.wires outer).scope =
        (source.val.diagram.wires inner).scope :=
      outerScopeRoot.trans scopeRoot.symm
    have swappedOrdered : source.val.diagram.Encloses
        (source.val.diagram.wires inner).scope
        (source.val.diagram.wires outer).scope := by
      rw [sameScope]
      exact VisualProof.Concrete.Diagram.Encloses.refl source.val.diagram _
    let swapDiagramIso :=
      joinWireSwapIso source.val.diagram outer inner distinct sameScope
    let swappedWellFormed :
        (VisualProof.Refinement.Implementation.WireJoin.Target
          source.val.diagram inner outer).WellFormed :=
      swapDiagramIso.wellFormed_transport targetWellFormed
    have swappedStep := rootContextHiddenInner source inner outer
      distinct.symm swappedOrdered swappedWellFormed outerScopeRoot outerHidden
    let originalTarget :=
      VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
        ordered targetWellFormed
    let swappedTarget :=
      VisualProof.Refinement.Implementation.WireJoin.targetOpen source inner outer distinct.symm
        swappedOrdered swappedWellFormed
    obtain ⟨swapOpenIso⟩ := joinWireSwapOpenIso source.val outer inner
      distinct sameScope
    let elaboratedSwap := swapOpenIso.elaborate_isomorphic
      originalTarget.property swappedTarget.property
    let originalLength :=
      VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq
        source.val outer inner distinct
    let swappedLength :=
      VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq
        source.val inner outer distinct.symm
    let castSwap := castOpenIsoTargetTrans
      swapOpenIso.boundary_length_eq.symm originalLength elaboratedSwap
    have castProof : swapOpenIso.boundary_length_eq.symm.trans
        originalLength = swappedLength := Subsingleton.elim _ _
    have normalizedSwap : OpenDiagramIso
        (originalTarget.elaborate.castArity originalLength)
        (swappedTarget.elaborate.castArity swappedLength) := by
      simpa only [castProof] using castSwap
    exact Rule.WireSever.iso normalizedSwap.symm swappedStep
      (OpenDiagramIso.refl _)
  · exact rootContextHiddenInner source outer inner distinct ordered
      targetWellFormed scopeRoot innerExposed

end VisualProof.Refinement.Implementation.WireJoin
