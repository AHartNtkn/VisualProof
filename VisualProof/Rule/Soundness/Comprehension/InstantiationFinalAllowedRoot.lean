import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalInterface

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

namespace InstantiationTrace

/-- Map an original route ending at the quantified bubble's parent through
the complete instantiation trace.  The mapped route has exactly the same cut
count; inserted comprehension material is not part of this frame route. -/
theorem mapRouteToFinalFocus
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    {start target : Fin input.val.regionCount}
    {path : List Nat}
    (route : Splice.RegionRoute input.val start target path)
    (targetEq : target = payload.parent)
    (startAdmissible : start = payload.parent ∨ FrameRegular payload start) :
    ∃ finalPath,
      ∃ finalRoute : Splice.RegionRoute elimTrace.sourceDiagram
          (copyTrace.finalRegionMap elimTrace finalWellFormed start)
          (elimTrace.targetIndex finalWellFormed) finalPath,
        ∀ {depth}, route.HasCutDepth depth → finalRoute.HasCutDepth depth := by
  induction route with
  | @here region =>
      subst region
      have focusEq := copyTrace.finalRegionMap_parent elimTrace finalWellFormed
      let finalWitness :
          { candidate : Splice.RegionRoute elimTrace.sourceDiagram
              (copyTrace.finalRegionMap elimTrace finalWellFormed payload.parent)
              (elimTrace.targetIndex finalWellFormed) [] //
            candidate.HasCutDepth 0 } := by
        rw [focusEq]
        exact ⟨.here _, Splice.RegionRoute.HasCutDepth.here
          (d := elimTrace.sourceDiagram) _⟩
      refine ⟨[], finalWitness.val, ?_⟩
      intro depth routeDepth
      cases routeDepth
      exact finalWitness.property
  | @step start child target rest hparent position hposition tail ih =>
      subst target
      have startRegular : FrameRegular payload start := by
        rcases startAdmissible with startEq | regular
        · subst start
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property hparent
                (VisualProof.Diagram.Splice.Input.RegionRoute.encloses
                  tail input.property))
        · exact regular
      have childAdmissible : child = payload.parent ∨
          FrameRegular payload child := by
        by_cases childEq : child = payload.parent
        · exact Or.inl childEq
        · right
          refine ⟨?_, childEq⟩
          intro bubbleEnclosesChild
          have childEnclosesParent :=
            VisualProof.Diagram.Splice.Input.RegionRoute.encloses
              tail input.property
          have bubbleEnclosesParent :=
            ConcreteElaboration.checked_encloses_trans input.property
              bubbleEnclosesChild childEnclosesParent
          exact payload_bubble_not_encloses_parent payload
            bubbleEnclosesParent
      obtain ⟨finalRest, finalTail, tailDepth⟩ := ih rfl childAdmissible
      have finalParent := copyTrace.final_region_parent_of_regular elimTrace
        finalWellFormed start child startRegular hparent
      obtain ⟨finalPosition, finalPositionLookup⟩ := indexOf?_complete
        ((ConcreteElaboration.mem_localOccurrences_child
          elimTrace.sourceDiagram
          (copyTrace.finalRegionMap elimTrace finalWellFormed start)
          (copyTrace.finalRegionMap elimTrace finalWellFormed child)).2
            finalParent)
      let finalRoute := Splice.RegionRoute.step finalParent finalPosition
        finalPositionLookup finalTail
      refine ⟨finalPosition.val :: finalRest, finalRoute, ?_⟩
      intro depth routeDepth
      obtain ⟨tailNatural, tailOriginalDepth⟩ :=
        tail.hasCutDepth_exists input.property
      have tailFinalDepth := tailDepth tailOriginalDepth
      cases childKind : input.val.regions child with
      | sheet =>
          simp [childKind, CRegion.parent?] at hparent
      | cut parent =>
          have parentEq : parent = start := by
            simpa [childKind, CRegion.parent?] using hparent
          subst parent
          have sourceDepth :
              (Splice.RegionRoute.step hparent position hposition tail).HasCutDepth
                (tailNatural + 1) :=
            Splice.RegionRoute.HasCutDepth.cut
              (hparent := hparent) (hposition := hposition)
              childKind tailOriginalDepth
          have depthEq := regionRoute_cutDepth_unique routeDepth sourceDepth
          have finalShape := copyTrace.final_region_shape_of_regular elimTrace
            finalWellFormed start startRegular child hparent
          rw [childKind] at finalShape
          have finalDepth : finalRoute.HasCutDepth (tailNatural + 1) :=
            Splice.RegionRoute.HasCutDepth.cut
              (hparent := finalParent) (hposition := finalPositionLookup)
              (by simpa using finalShape) tailFinalDepth
          rwa [depthEq]
      | bubble parent arity =>
          have parentEq : parent = start := by
            simpa [childKind, CRegion.parent?] using hparent
          subst parent
          have sourceDepth :
              (Splice.RegionRoute.step hparent position hposition tail).HasCutDepth
                tailNatural :=
            Splice.RegionRoute.HasCutDepth.bubble
              (hparent := hparent) (hposition := hposition)
              childKind tailOriginalDepth
          have depthEq := regionRoute_cutDepth_unique routeDepth sourceDepth
          have finalShape := copyTrace.final_region_shape_of_regular elimTrace
            finalWellFormed start startRegular child hparent
          rw [childKind] at finalShape
          have finalDepth : finalRoute.HasCutDepth tailNatural :=
            Splice.RegionRoute.HasCutDepth.bubble
              (hparent := finalParent) (hposition := finalPositionLookup)
              (by simpa using finalShape) tailFinalDepth
          rwa [depthEq]

/-- The quantified bubble and its immediate parent have the same concrete cut
depth because the connecting boundary is a bubble, not a cut. -/
theorem bubble_parent_concreteCutDepth
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    concreteCutDepth input.val bubble =
      concreteCutDepth input.val payload.parent := by
  let parentView := Classical.choice
    (Splice.siteView_complete input payload.parent)
  let bubbleView := Classical.choice
    (Splice.siteView_complete input bubble)
  have bubbleParent : (input.val.regions bubble).parent? =
      some payload.parent := by
    rw [payload.bubble_eq]
    rfl
  obtain ⟨position, positionLookup⟩ := indexOf?_complete
    ((ConcreteElaboration.mem_localOccurrences_child input.val
      payload.parent bubble).2 bubbleParent)
  let lastRoute : Splice.RegionRoute input.val payload.parent bubble
      [position.val] :=
    Splice.RegionRoute.step bubbleParent position positionLookup (.here bubble)
  have lastDepth : lastRoute.HasCutDepth 0 := by
    exact Splice.RegionRoute.HasCutDepth.bubble
      (hparent := bubbleParent) (hposition := positionLookup)
      payload.bubble_eq (Splice.RegionRoute.HasCutDepth.here bubble)
  let extended := parentView.route.trans lastRoute
  have extendedDepth : extended.HasCutDepth parentView.focus.context.cutDepth := by
    simpa [extended] using parentView.cutDepth.trans lastDepth
  have pathEq := VisualProof.Diagram.Splice.Input.RegionRoute.path_unique
    input.property extended bubbleView.route
  let castExtended := extended.castPath pathEq
  have castDepth : castExtended.HasCutDepth
      parentView.focus.context.cutDepth :=
    extendedDepth.castPath pathEq
  have routeEq : castExtended = bubbleView.route := Subsingleton.elim _ _
  rw [routeEq] at castDepth
  have depthEq := regionRoute_cutDepth_unique castDepth bubbleView.cutDepth
  rw [siteView_concreteCutDepth_eq parentView,
    siteView_concreteCutDepth_eq bubbleView]
  exact depthEq.symm

/-- Executor polarity at the original quantified bubble is exactly the
`FinalAllowed` condition at the root of the promoted operational diagram. -/
theorem finalAllowed_root
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (allowedDepth : FinalDepthAllowed direction
      (concreteCutDepth input.val bubble)) :
    FinalAllowed elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction
      elimTrace.sourceDiagram.root := by
  intro path depth route routeDepth
  have parentDepth := bubble_parent_concreteCutDepth payload
  by_cases rootFocus : input.val.root = payload.parent
  · have finalRootFocus : elimTrace.sourceDiagram.root =
        elimTrace.targetIndex finalWellFormed := by
      rw [← copyTrace.finalRegionMap_root elimTrace finalWellFormed, rootFocus]
      exact copyTrace.finalRegionMap_parent elimTrace finalWellFormed
    have sourceDepthZero : concreteCutDepth input.val bubble = 0 := by
      rw [parentDepth, ← rootFocus]
      exact concreteCutDepth_root_eq_zero input
    have allowedZero : FinalDepthAllowed direction 0 := by
      simpa [sourceDepthZero] using allowedDepth
    let original :
        { candidate : Splice.RegionRoute elimTrace.sourceDiagram
            elimTrace.sourceDiagram.root
            (elimTrace.targetIndex finalWellFormed) path //
          candidate.HasCutDepth depth } := ⟨route, routeDepth⟩
    let normalized :
        { candidate : Splice.RegionRoute elimTrace.sourceDiagram
            (elimTrace.targetIndex finalWellFormed)
            (elimTrace.targetIndex finalWellFormed) path //
          candidate.HasCutDepth depth } := finalRootFocus ▸ original
    let normalizedRoute := normalized.val
    have normalizedDepth : normalizedRoute.HasCutDepth depth :=
      normalized.property
    let here : Splice.RegionRoute elimTrace.sourceDiagram
        (elimTrace.targetIndex finalWellFormed)
        (elimTrace.targetIndex finalWellFormed) [] := .here _
    have pathEq :=
      VisualProof.Diagram.Splice.Input.RegionRoute.path_unique
        sourceWellFormed normalizedRoute here
    let hereCast := here.castPath pathEq.symm
    have hereCastDepth : hereCast.HasCutDepth 0 :=
      by
        simpa [hereCast] using
          (Splice.RegionRoute.HasCutDepth.here
            (d := elimTrace.sourceDiagram)
            (elimTrace.targetIndex finalWellFormed)).castPath pathEq.symm
    have routeEq : normalizedRoute = hereCast := Subsingleton.elim _ _
    rw [routeEq] at normalizedDepth
    have depthEq := regionRoute_cutDepth_unique normalizedDepth hereCastDepth
    subst depth
    exact allowedZero
  · let originalView := Classical.choice
        (Splice.siteView_complete input payload.parent)
    have rootRegular : FrameRegular payload input.val.root := by
      constructor
      · intro enclosed
        have bubbleRoot := ConcreteElaboration.encloses_sheet_eq
          input.property.root_is_sheet enclosed
        have sameShape := congrArg input.val.regions bubbleRoot
        have impossible := payload.bubble_eq.symm.trans
          (sameShape.trans input.property.root_is_sheet)
        cases impossible
      · exact rootFocus
    obtain ⟨finalPath, finalRoute, finalRouteDepth⟩ :=
      copyTrace.mapRouteToFinalFocus elimTrace finalWellFormed
        originalView.route rfl (Or.inr rootRegular)
    have mappedDepth := finalRouteDepth originalView.cutDepth
    have originalParentDepth := siteView_concreteCutDepth_eq originalView
    have allowedFinalDepth :
        FinalDepthAllowed direction originalView.focus.context.cutDepth := by
      rw [← originalParentDepth, ← parentDepth]
      exact allowedDepth
    have finalStart := copyTrace.finalRegionMap_root elimTrace finalWellFormed
    let normalized :
        { candidate : Splice.RegionRoute elimTrace.sourceDiagram
            elimTrace.sourceDiagram.root (elimTrace.targetIndex finalWellFormed)
            finalPath //
          candidate.HasCutDepth originalView.focus.context.cutDepth } := by
      rw [← finalStart]
      exact ⟨finalRoute, mappedDepth⟩
    let normalizedRoute := normalized.val
    have normalizedDepth : normalizedRoute.HasCutDepth
        originalView.focus.context.cutDepth := normalized.property
    have pathEq :=
      VisualProof.Diagram.Splice.Input.RegionRoute.path_unique
        sourceWellFormed route normalizedRoute
    subst path
    have routeEq : route = normalizedRoute := Subsingleton.elim _ _
    subst route
    have depthEq := regionRoute_cutDepth_unique routeDepth normalizedDepth
    subst depth
    exact allowedFinalDepth

end InstantiationTrace

end VisualProof.Rule
