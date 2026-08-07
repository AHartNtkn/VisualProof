import VisualProof.Refinement.Implementation.WireSever

namespace VisualProof.Refinement.Implementation.WireSever

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Data.Finite

private theorem castBoundaryEqIff
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (left right : Fin targetArity) :
    (diagram.castArity equality).boundary left =
        (diagram.castArity equality).boundary right ↔
      diagram.boundary (Fin.cast equality.symm left) =
        diagram.boundary (Fin.cast equality.symm right) := by
  subst targetArity
  rfl

private theorem castBoundaryVal
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (position : Fin targetArity) :
    ((diagram.castArity equality).boundary position).val =
      (diagram.boundary (Fin.cast equality.symm position)).val := by
  subst targetArity
  rfl

private theorem castBody
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (externalEq : (diagram.castArity equality).externalClasses =
      diagram.externalClasses) :
    (diagram.castArity equality).body =
      diagram.body.renameWires (Fin.cast externalEq.symm) := by
  subst targetArity
  have proofEq : externalEq = rfl := Subsingleton.elim _ _
  rw [proofEq]
  simpa using (Region.renameWires_id diagram.body).symm

theorem rootOpen
    (source : Concrete.State arity)
    (wire : Fin source.checked.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.checked.val.diagram.nodeCount))
    (boundary : Concrete.WireSeverBoundary source wire)
    (targetWellFormed :
      (Concrete.severWireRaw source.checked.val.diagram wire keep).WellFormed)
    (scopeRoot :
      (source.checked.val.diagram.wires wire).scope =
        source.checked.val.diagram.root)
    (externalPlus : Nonempty (FiniteEquiv
      (Fin (((separatedOpen source wire keep boundary targetWellFormed).elaborate.castArity
        (by simp [separatedOpen] :
          (separatedOpen source wire keep boundary targetWellFormed).val.boundary.length =
            arity)).externalClasses))
      (Fin ((source.checked.elaborate.castArity source.boundary_length).externalClasses + 1)))) :
    Nonempty (Rule.WireSever.Open
      (source.checked.elaborate.castArity source.boundary_length)
      ((separatedOpen source wire keep boundary targetWellFormed).elaborate.castArity
        (by simp [separatedOpen] :
          (separatedOpen source wire keep boundary targetWellFormed).val.boundary.length =
            arity))) := by
  classical
  let target := separatedOpen source wire keep boundary targetWellFormed
  let targetLength : target.val.boundary.length = arity := by
    simp [target, separatedOpen]
  let sourceDiagram :=
    source.checked.elaborate.castArity source.boundary_length
  let targetDiagram := target.elaborate.castArity targetLength
  change Nonempty (FiniteEquiv (Fin targetDiagram.externalClasses)
      (Fin (sourceDiagram.externalClasses + 1))) at externalPlus
  change Nonempty (Rule.WireSever.Open sourceDiagram targetDiagram)
  rcases externalPlus with ⟨externalPlus⟩
  have oneMore : targetDiagram.externalClasses =
      sourceDiagram.externalClasses + 1 := by
    apply Nat.le_antisymm
    · exact fin_card_le_of_injective externalPlus externalPlus.injective
    · exact fin_card_le_of_injective externalPlus.symm
        externalPlus.symm.injective
  have refines : ∀ left right,
      targetDiagram.boundary left = targetDiagram.boundary right →
        sourceDiagram.boundary left = sourceDiagram.boundary right := by
    intro left right targetAlias
    have targetAlias' := (castBoundaryEqIff target.elaborate targetLength
      left right).1 targetAlias
    have targetAlias'' : target.val.boundaryClass
        (Fin.cast targetLength.symm left) =
      target.val.boundaryClass (Fin.cast targetLength.symm right) := by
      simpa only [Concrete.CheckedOpen.elaborate_boundary] using targetAlias'
    apply (castBoundaryEqIff source.checked.elaborate source.boundary_length
      left right).2
    have targetRaw :=
      (Concrete.OpenDiagram.boundaryClass_eq_iff _ _ _).1 targetAlias''
    have targetRaw' : Concrete.severBoundaryImage source wire boundary left =
        Concrete.severBoundaryImage source wire boundary right := by
      simpa [target, separatedOpen, targetLength] using targetRaw
    have sourceRaw := (severBoundaryImage_eq_iff source wire boundary
      left right).1 targetRaw' |>.1
    apply (Concrete.OpenDiagram.boundaryClass_eq_iff _ _ _).2
    simpa only [Concrete.CheckedOpen.elaborate_boundary] using sourceRaw
  let collapse : Fin targetDiagram.externalClasses →
      Fin sourceDiagram.externalClasses :=
    fun external => sourceDiagram.boundary
      (Diagram.boundaryRepresentative targetDiagram external)
  have collapseBoundary (position : Fin arity) :
      collapse (targetDiagram.boundary position) =
        sourceDiagram.boundary position := by
    apply refines
    exact Diagram.boundaryRepresentative_mapsTo targetDiagram _
  have collapseSurjective : Function.Surjective collapse := by
    intro external
    obtain ⟨position, rfl⟩ := sourceDiagram.boundary_surjective external
    exact ⟨targetDiagram.boundary position, collapseBoundary position⟩
  have notReflects : ¬ ∀ left right,
      sourceDiagram.boundary left = sourceDiagram.boundary right →
        targetDiagram.boundary left = targetDiagram.boundary right := by
    intro reflects
    have collapseInjective : Function.Injective collapse := by
      intro left right equality
      let leftPosition := Diagram.boundaryRepresentative targetDiagram left
      let rightPosition := Diagram.boundaryRepresentative targetDiagram right
      have sourceAlias : sourceDiagram.boundary leftPosition =
          sourceDiagram.boundary rightPosition := equality
      have targetAlias := reflects leftPosition rightPosition sourceAlias
      exact (Diagram.boundaryRepresentative_mapsTo targetDiagram left).symm.trans
        (targetAlias.trans
          (Diagram.boundaryRepresentative_mapsTo targetDiagram right))
    have impossible := fin_card_le_of_injective collapse collapseInjective
    omega
  have witness : ∃ left right,
      sourceDiagram.boundary left = sourceDiagram.boundary right ∧
        targetDiagram.boundary left ≠ targetDiagram.boundary right := by
    exact Classical.byContradiction fun absent => notReflects (by
      intro left right sourceAlias
      exact Classical.byContradiction fun targetDistinct =>
        absent ⟨left, right, sourceAlias, targetDistinct⟩)
  obtain ⟨left, right, sourceAlias, targetDistinct⟩ := witness
  have sourceWireAlias :
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) =
        source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) := by
    have sourceAlias' := (castBoundaryEqIff source.checked.elaborate
      source.boundary_length left right).1 sourceAlias
    exact (Concrete.OpenDiagram.boundaryClass_eq_iff _ _ _).1 sourceAlias'
  have targetWireDistinct :
      Concrete.severBoundaryImage source wire boundary left ≠
        Concrete.severBoundaryImage source wire boundary right := by
    intro equality
    apply targetDistinct
    apply (castBoundaryEqIff target.elaborate targetLength left right).2
    apply (Concrete.OpenDiagram.boundaryClass_eq_iff _ _ _).2
    simpa [target, separatedOpen] using equality
  have sideDistinct : boundary.side left ≠ boundary.side right := by
    intro sideEq
    apply targetWireDistinct
    exact (severBoundaryImage_eq_iff source wire boundary left right).2
      ⟨sourceWireAlias, sideEq⟩
  have sourceWire :
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm left) = wire := by
    exact Classical.byContradiction fun distinct => by
      have leftFalse := boundary.other left distinct
      have rightDistinct : source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) ≠ wire := by
        intro rightEq
        exact distinct (sourceWireAlias.trans rightEq)
      have rightFalse := boundary.other right rightDistinct
      exact sideDistinct (leftFalse.trans rightFalse.symm)
  have rightWire :
      source.checked.val.boundary.get
          (Fin.cast source.boundary_length.symm right) = wire :=
    sourceWireAlias.symm.trans sourceWire
  obtain ⟨falsePosition, truePosition, falseSide, trueSide,
      falseWire, trueWire⟩ : ∃ falsePosition truePosition : Fin arity,
        boundary.side falsePosition = false ∧
        boundary.side truePosition = true ∧
        source.checked.val.boundary.get
            (Fin.cast source.boundary_length.symm falsePosition) = wire ∧
        source.checked.val.boundary.get
            (Fin.cast source.boundary_length.symm truePosition) = wire := by
    cases leftSide : boundary.side left <;>
      cases rightSide : boundary.side right
    · exact False.elim (sideDistinct (leftSide.trans rightSide.symm))
    · exact ⟨left, right, leftSide, rightSide, sourceWire, rightWire⟩
    · exact ⟨right, left, rightSide, leftSide, rightWire, sourceWire⟩
    · exact False.elim (sideDistinct (leftSide.trans rightSide.symm))
  let fresh := Fin.last source.checked.val.diagram.wireCount
  let old := wire.castSucc
  have falseImage : Concrete.severBoundaryImage source wire boundary
      falsePosition = old := by
    unfold Concrete.severBoundaryImage
    rw [falseWire, falseSide]
    simp [old]
  have trueImage : Concrete.severBoundaryImage source wire boundary
      truePosition = fresh := by
    unfold Concrete.severBoundaryImage
    rw [trueWire, trueSide]
    simp [fresh]
  have oldExposed : old ∈ target.val.exposedWires := by
    apply (Concrete.OpenDiagram.mem_exposedWires target.val old).2
    exact List.mem_ofFn.mpr ⟨falsePosition, by
      simpa [target, separatedOpen] using falseImage⟩
  have freshExposed : fresh ∈ target.val.exposedWires := by
    apply (Concrete.OpenDiagram.mem_exposedWires target.val fresh).2
    exact List.mem_ofFn.mpr ⟨truePosition, by
      simpa [target, separatedOpen] using trueImage⟩
  have oldExposedIff (candidate : Fin source.checked.val.diagram.wireCount) :
      candidate.castSucc ∈ target.val.exposedWires ↔
        candidate ∈ source.checked.val.exposedWires := by
    constructor
    · intro targetMember
      have targetBoundary :=
        (Concrete.OpenDiagram.mem_exposedWires target.val candidate.castSucc).1
          targetMember
      obtain ⟨position, imageEq⟩ := List.mem_ofFn.mp targetBoundary
      apply (Concrete.OpenDiagram.mem_exposedWires source.checked.val candidate).2
      apply List.mem_iff_get.mpr
      refine ⟨Fin.cast source.boundary_length.symm position, ?_⟩
      have collapsed := congrArg
        (VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep)
        imageEq
      simpa [target, separatedOpen] using
        (severBoundaryImage_collapse source wire keep boundary position).symm.trans
          collapsed
    · intro sourceMember
      by_cases candidateWire : candidate = wire
      · subst candidate
        exact oldExposed
      · have sourceBoundary :=
          (Concrete.OpenDiagram.mem_exposedWires source.checked.val candidate).1
            sourceMember
        obtain ⟨rawPosition, sourceImage⟩ := List.mem_iff_get.mp sourceBoundary
        let position : Fin arity := Fin.cast source.boundary_length rawPosition
        have sourceImage' : source.checked.val.boundary.get
            (Fin.cast source.boundary_length.symm position) = candidate := by
          simpa [position] using sourceImage
        apply (Concrete.OpenDiagram.mem_exposedWires target.val
          candidate.castSucc).2
        apply List.mem_ofFn.mpr
        refine ⟨position, ?_⟩
        have sideFalse := boundary.other position (by
          intro equality
          exact candidateWire (sourceImage'.symm.trans equality))
        simpa [target, separatedOpen, Concrete.severBoundaryImage,
          candidateWire, sideFalse] using congrArg Fin.castSucc sourceImage'
  have targetHiddenEq : target.val.hiddenWires =
      source.checked.val.hiddenWires.map Fin.castSucc := by
    unfold Concrete.OpenDiagram.hiddenWires
    change List.filter
        (fun candidate => decide (candidate ∉ target.val.exposedWires))
        (Concrete.Elaboration.exactScopeWires
          (Concrete.severWireRaw source.checked.val.diagram wire keep)
          source.checked.val.diagram.root) = _
    rw [VisualProof.Refinement.Implementation.WireSever.severWireRaw_exactScopeWires]
    rw [if_pos scopeRoot.symm]
    have filterSplit := List.filter_append
      (p := fun candidate => decide (candidate ∉ target.val.exposedWires))
      ((Concrete.Elaboration.exactScopeWires source.checked.val.diagram
        source.checked.val.diagram.root).map Fin.castSucc)
      [Fin.last source.checked.val.diagram.wireCount]
    have mapped :
        List.filter
            (fun candidate => decide (candidate ∉ target.val.exposedWires))
            ((Concrete.Elaboration.exactScopeWires
              source.checked.val.diagram source.checked.val.diagram.root).map
                Fin.castSucc) =
          (List.filter
            (fun candidate => decide
              (candidate ∉ source.checked.val.exposedWires))
            (Concrete.Elaboration.exactScopeWires source.checked.val.diagram
              source.checked.val.diagram.root)).map Fin.castSucc := by
      rw [List.filter_map]
      apply congrArg (List.map Fin.castSucc)
      apply congrArg (fun predicate => List.filter predicate
        (Concrete.Elaboration.exactScopeWires source.checked.val.diagram
          source.checked.val.diagram.root))
      funext candidate
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact not_congr (oldExposedIff candidate)
    have freshFilter : List.filter
        (fun candidate => decide (candidate ∉ target.val.exposedWires))
        [fresh] = [] := by
      simp only [List.filter_cons, List.filter_nil]
      have conditionFalse :
          ¬ (decide (fresh ∉ target.val.exposedWires) = true) := by
        intro accepted
        exact of_decide_eq_true accepted freshExposed
      exact if_neg conditionFalse
    calc
      _ = List.filter
            (fun candidate => decide (candidate ∉ target.val.exposedWires))
            ((Concrete.Elaboration.exactScopeWires
              source.checked.val.diagram source.checked.val.diagram.root).map
                Fin.castSucc) ++
          List.filter
            (fun candidate => decide (candidate ∉ target.val.exposedWires))
            [fresh] := filterSplit
      _ = _ := by
        rw [mapped, freshFilter]
        exact List.append_nil _
  have targetLocalEq : target.val.hiddenWires.length =
      source.checked.val.hiddenWires.length := by
    exact (congrArg List.length targetHiddenEq).trans (List.length_map _)
  let localEquiv : FiniteEquiv (Fin target.val.hiddenWires.length)
      (Fin source.checked.val.hiddenWires.length) :=
    FiniteEquiv.finCast targetLocalEq
  let rawCollapse := targetRootCollapse source wire keep boundary targetWellFormed
  obtain ⟨sourceItems, sourceItemsCompiled⟩ :=
    Concrete.Splice.checkedOpenRootItems_complete source.checked
  obtain ⟨targetItems, targetItemsCompiled⟩ :=
    Concrete.Splice.checkedOpenRootItems_complete target
  have sequence := severCompileSiteItems_of_nodes_children
    source.checked.val.diagram wire keep target.val.rootWires
    source.checked.val.rootWires rawCollapse
    Concrete.Elaboration.BinderContext.empty
    source.checked.val.diagram.root source.checked.val.diagram.regionCount
    source.checked.val.rootWires_nodup
    source.checked.property.diagram_well_formed.wire_endpoints_are_disjoint (by
      intro childRels child childBinders member
      have parent :=
        (Concrete.Elaboration.mem_localOccurrences_child
          source.checked.val.diagram source.checked.val.diagram.root child).mp
          member
      have childNotRoot : ¬ source.checked.val.diagram.Encloses child
          source.checked.val.diagram.root :=
        Concrete.Elaboration.checked_direct_child_not_encloses_parent
          source.checked.property.diagram_well_formed parent
      have targetRootExact :=
        Concrete.Elaboration.openRootWires_exact target.property
      have sourceRootExact :=
        Concrete.Elaboration.openRootWires_exact source.checked.property
      exact compileRegion_collapse_of_not_encloses
        source.checked.val.diagram wire keep
        source.checked.property.diagram_well_formed targetWellFormed
        source.checked.val.diagram.regionCount child target.val.rootWires
        source.checked.val.rootWires rawCollapse childBinders (by
          simpa only [scopeRoot] using childNotRoot)
        (targetRootExact.extend_child targetWellFormed parent)
        (sourceRootExact.extend_child
          source.checked.property.diagram_well_formed parent))
  have targetItemsCompiled' :
      Concrete.Elaboration.compileOccurrencesWith?
          (Concrete.severWireRaw source.checked.val.diagram wire keep)
          (Concrete.Elaboration.compileRegion?
            (Concrete.severWireRaw source.checked.val.diagram wire keep)
            source.checked.val.diagram.regionCount)
          target.val.rootWires Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences
            (Concrete.severWireRaw source.checked.val.diagram wire keep)
            source.checked.val.diagram.root) = some targetItems := by
    simpa [target, separatedOpen] using targetItemsCompiled
  have mappedTarget := congrArg
    (Option.map (ItemSeq.renameWires rawCollapse.indexMap))
    targetItemsCompiled'
  have sourceSome : some sourceItems =
      some (targetItems.renameWires rawCollapse.indexMap) :=
    sourceItemsCompiled.symm.trans
      (sequence.trans (mappedTarget.trans (by rfl)))
  have itemsEq : sourceItems =
      targetItems.renameWires rawCollapse.indexMap :=
    Option.some.inj sourceSome
  obtain ⟨sourceBody, sourceRootCompiled, sourceElaborates⟩ :=
    Concrete.CheckedOpen.elaborate_body_computation source.checked
  have sourceItemsCompiled' :
      Concrete.Elaboration.compileOccurrencesWith?
          source.checked.val.diagram
          (Concrete.Elaboration.compileRegion? source.checked.val.diagram
            source.checked.val.diagram.regionCount)
          (source.checked.val.exposedWires ++ source.checked.val.hiddenWires)
          Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences source.checked.val.diagram
            source.checked.val.diagram.root) = some sourceItems := by
    simpa only [Concrete.OpenDiagram.rootWires] using sourceItemsCompiled
  have sourceBodyEq : source.checked.elaborate.body =
      Concrete.Elaboration.finishRoot source.checked.val.exposedWires
        source.checked.val.hiddenWires sourceItems := by
    rw [sourceElaborates]
    simp only [Concrete.Elaboration.compileRoot?] at sourceRootCompiled
    rw [sourceItemsCompiled'] at sourceRootCompiled
    exact Option.some.inj sourceRootCompiled.symm
  obtain ⟨targetBody, targetRootCompiled, targetElaborates⟩ :=
    Concrete.CheckedOpen.elaborate_body_computation target
  have targetItemsCompiled'' :
      Concrete.Elaboration.compileOccurrencesWith? target.val.diagram
          (Concrete.Elaboration.compileRegion? target.val.diagram
            target.val.diagram.regionCount)
          (target.val.exposedWires ++ target.val.hiddenWires)
          Concrete.Elaboration.BinderContext.empty
          (Concrete.Elaboration.localOccurrences target.val.diagram
            target.val.diagram.root) = some targetItems := by
    simpa only [Concrete.OpenDiagram.rootWires] using targetItemsCompiled
  have targetBodyEq : target.elaborate.body =
      Concrete.Elaboration.finishRoot target.val.exposedWires
        target.val.hiddenWires targetItems := by
    rw [targetElaborates]
    simp only [Concrete.Elaboration.compileRoot?] at targetRootCompiled
    rw [targetItemsCompiled''] at targetRootCompiled
    exact Option.some.inj targetRootCompiled.symm
  let targetExternalEq : targetDiagram.externalClasses =
      target.val.exposedWires.length := by
    simp [targetDiagram]
  let sourceExternalEq : sourceDiagram.externalClasses =
      source.checked.val.exposedWires.length := by
    simp [sourceDiagram]
  let concreteCollapse : Fin target.val.exposedWires.length →
      Fin source.checked.val.exposedWires.length := fun index =>
    Fin.cast sourceExternalEq
      (collapse (Fin.cast targetExternalEq.symm index))
  have externalGet (index : Fin target.val.exposedWires.length) :
      source.checked.val.exposedWires.get (concreteCollapse index) =
        VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
          (target.val.exposedWires.get index) := by
    let abstractIndex := Fin.cast targetExternalEq.symm index
    let position := Diagram.boundaryRepresentative targetDiagram abstractIndex
    have targetClass : targetDiagram.boundary position = abstractIndex :=
      Diagram.boundaryRepresentative_mapsTo targetDiagram abstractIndex
    let targetPosition : Fin target.val.boundary.length :=
      Fin.cast targetLength.symm position
    let sourcePosition : Fin source.checked.val.boundary.length :=
      Fin.cast source.boundary_length.symm position
    have targetRaw : target.val.exposedWires.get index =
        Concrete.severBoundaryImage source wire boundary position := by
      calc
        target.val.exposedWires.get index =
            target.val.exposedWires.get
              (target.val.boundaryClass targetPosition) := by
          apply congrArg target.val.exposedWires.get
          have targetClass' : target.val.boundaryClass targetPosition = index := by
            apply Fin.ext
            have values := congrArg Fin.val targetClass
            calc
              (target.val.boundaryClass targetPosition).val =
                  (targetDiagram.boundary position).val := by
                simpa only [targetDiagram, targetPosition,
                  Concrete.CheckedOpen.elaborate_boundary] using
                    (castBoundaryVal target.elaborate targetLength position).symm
              _ = abstractIndex.val := values
              _ = index.val := by rfl
          exact targetClass'.symm
        _ = target.val.boundary.get targetPosition :=
          Concrete.OpenDiagram.boundaryClass_sound target.val targetPosition
        _ = Concrete.severBoundaryImage source wire boundary position := by
          simp [target, separatedOpen, targetPosition]
    have sourceRaw : source.checked.val.exposedWires.get (concreteCollapse index) =
        source.checked.val.boundary.get sourcePosition := by
      have collapseEq : concreteCollapse index =
          source.checked.val.boundaryClass sourcePosition := by
        apply Fin.ext
        dsimp [concreteCollapse, collapse]
        change (sourceDiagram.boundary position).val =
          (source.checked.val.boundaryClass sourcePosition).val
        exact (castBoundaryVal source.checked.elaborate source.boundary_length
          position).trans rfl
      rw [collapseEq]
      exact Concrete.OpenDiagram.boundaryClass_sound _ _
    rw [sourceRaw, targetRaw]
    simpa [sourcePosition] using
      (severBoundaryImage_collapse source wire keep boundary position).symm
  have localGet (index : Fin target.val.hiddenWires.length) :
      source.checked.val.hiddenWires.get (localEquiv index) =
        VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
          (target.val.hiddenWires.get index) := by
    have targetGet := VisualProof.Refinement.Implementation.WireSever.listGet_cast_of_eq targetHiddenEq index
    let sourceIndex := Fin.cast targetLocalEq index
    have indexEq : Fin.cast (List.length_map
        (as := source.checked.val.hiddenWires) Fin.castSucc).symm sourceIndex =
        Fin.cast (congrArg List.length targetHiddenEq) index := by
      apply Fin.ext
      rfl
    rw [← indexEq] at targetGet
    have mappedGet := VisualProof.Refinement.Implementation.WireSever.listGet_map_cast_soundness
      source.checked.val.hiddenWires Fin.castSucc sourceIndex
    change source.checked.val.hiddenWires.get sourceIndex = _
    calc
      source.checked.val.hiddenWires.get sourceIndex =
          VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
            (source.checked.val.hiddenWires.get sourceIndex).castSucc := by
        simp [VisualProof.Refinement.Implementation.WireSever.severWireCollapse]
      _ = VisualProof.Refinement.Implementation.WireSever.severWireCollapse source.checked.val.diagram wire keep
          ((source.checked.val.hiddenWires.map Fin.castSucc).get
            (Fin.cast
              (List.length_map
                (as := source.checked.val.hiddenWires) Fin.castSucc).symm
              sourceIndex)) := congrArg _ mappedGet.symm
      _ = _ := congrArg _ targetGet.symm
  let targetRootEq : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let sourceRootEq : source.checked.val.rootWires.length =
      source.checked.val.exposedWires.length +
        source.checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let factor : Fin (target.val.exposedWires.length +
      target.val.hiddenWires.length) →
      Fin (source.checked.val.exposedWires.length +
        source.checked.val.hiddenWires.length) :=
    fun index => extendWireEquiv
      (FiniteEquiv.refl (Fin source.checked.val.exposedWires.length))
      localEquiv
      (extendWireRenaming concreteCollapse target.val.hiddenWires.length index)
  have coordinateFactor (index : Fin target.val.rootWires.length) :
      Fin.cast sourceRootEq (rawCollapse.indexMap index) =
        factor (Fin.cast targetRootEq index) := by
    let split := Fin.cast targetRootEq index
    generalize splitEq : split = position
    revert splitEq
    refine Fin.addCases (fun externalIndex splitEq => ?_)
      (fun localIndex splitEq => ?_) position
    · have indexEq : index = Fin.cast targetRootEq.symm
          (Fin.castAdd target.val.hiddenWires.length externalIndex) := by
        apply Fin.ext
        have values := congrArg Fin.val splitEq
        simpa [split] using values
      let desired := Fin.cast sourceRootEq.symm
        (Fin.castAdd source.checked.val.hiddenWires.length
          (concreteCollapse externalIndex))
      have mapped : rawCollapse.indexMap index = desired := by
        apply Fin.ext
        apply (List.getElem_inj source.checked.val.rootWires_nodup).mp
        simpa only [List.get_eq_getElem] using
          (show source.checked.val.rootWires.get
              (rawCollapse.indexMap index) =
            source.checked.val.rootWires.get desired by
            calc
              _ = VisualProof.Refinement.Implementation.WireSever.severWireCollapse
                    source.checked.val.diagram wire keep
                    (target.val.rootWires.get index) := rawCollapse.get index
              _ = VisualProof.Refinement.Implementation.WireSever.severWireCollapse
                    source.checked.val.diagram wire keep
                    (target.val.exposedWires.get externalIndex) := by
                rw [indexEq]
                simp [Concrete.OpenDiagram.rootWires]
              _ = source.checked.val.exposedWires.get
                    (concreteCollapse externalIndex) :=
                (externalGet externalIndex).symm
              _ = source.checked.val.rootWires.get desired := by
                simp [desired, Concrete.OpenDiagram.rootWires])
      rw [mapped]
      apply Fin.ext
      simp [factor, split, splitEq, desired, extendWireRenaming,
        extendWireEquiv]
    · have indexEq : index = Fin.cast targetRootEq.symm
          (Fin.natAdd target.val.exposedWires.length localIndex) := by
        apply Fin.ext
        have values := congrArg Fin.val splitEq
        simpa [split] using values
      let desired := Fin.cast sourceRootEq.symm
        (Fin.natAdd source.checked.val.exposedWires.length
          (localEquiv localIndex))
      have mapped : rawCollapse.indexMap index = desired := by
        apply Fin.ext
        apply (List.getElem_inj source.checked.val.rootWires_nodup).mp
        simpa only [List.get_eq_getElem] using
          (show source.checked.val.rootWires.get
              (rawCollapse.indexMap index) =
            source.checked.val.rootWires.get desired by
            calc
              _ = VisualProof.Refinement.Implementation.WireSever.severWireCollapse
                    source.checked.val.diagram wire keep
                    (target.val.rootWires.get index) := rawCollapse.get index
              _ = VisualProof.Refinement.Implementation.WireSever.severWireCollapse
                    source.checked.val.diagram wire keep
                    (target.val.hiddenWires.get localIndex) := by
                rw [indexEq]
                simp [Concrete.OpenDiagram.rootWires]
              _ = source.checked.val.hiddenWires.get
                    (localEquiv localIndex) := (localGet localIndex).symm
              _ = source.checked.val.rootWires.get desired := by
                simp [desired, Concrete.OpenDiagram.rootWires])
      rw [mapped]
      apply Fin.ext
      simp [factor, split, splitEq, desired, extendWireRenaming,
        extendWireEquiv]
  let sourceIntrinsic := sourceItems.castWiresEq sourceRootEq
  let targetIntrinsic := targetItems.castWiresEq targetRootEq
  let normalized := targetIntrinsic.renameWires
    (extendWireRenaming concreteCollapse target.val.hiddenWires.length)
  let totalEquiv := extendWireEquiv
    (FiniteEquiv.refl (Fin source.checked.val.exposedWires.length))
    localEquiv
  have intrinsicEq : sourceIntrinsic =
      normalized.renameWires totalEquiv := by
    dsimp [sourceIntrinsic, normalized, targetIntrinsic, totalEquiv]
    rw [itemsEq]
    simp only [ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.renameWires_comp]
    apply congrArg (fun wireMap => targetItems.renameWires wireMap)
    funext index
    exact coordinateFactor index
  have totalSymm : totalEquiv.symm = extendWireEquiv
      (FiniteEquiv.refl (Fin source.checked.val.exposedWires.length))
      localEquiv.symm := by
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun externalIndex => ?_)
      (fun localIndex => ?_) index
    · apply Fin.ext
      rfl
    · apply Fin.ext
      rfl
  have itemsIso : ItemSeqIso
      (extendWireEquiv
        (FiniteEquiv.refl (Fin source.checked.val.exposedWires.length))
        localEquiv.symm) [] sourceIntrinsic normalized := by
    have renamed := ItemSeqIso.renameWiresEquiv normalized totalEquiv
    rw [← intrinsicEq] at renamed
    have reversed := renamed.symm
    rw [totalSymm] at reversed
    exact reversed
  have concreteBody : Core.Isomorphic source.checked.elaborate.body
      (target.elaborate.body.renameWires concreteCollapse) := by
    rw [sourceBodyEq, targetBodyEq]
    unfold Concrete.Elaboration.finishRoot
    change RegionIso (FiniteEquiv.refl
        (Fin source.checked.val.exposedWires.length)) []
      (.mk source.checked.val.hiddenWires.length sourceIntrinsic)
      (.mk target.val.hiddenWires.length normalized)
    exact RegionIso.mk localEquiv.symm itemsIso
  refine ⟨{
    one_more := oneMore
    collapse := collapse
    collapse_surjective := collapseSurjective
    boundary := collapseBoundary
    body := ?_
  }⟩
  let sourceCast : Fin source.checked.val.exposedWires.length →
      Fin sourceDiagram.externalClasses := Fin.cast sourceExternalEq.symm
  have transported := concreteBody.renameWires_commuting sourceCast sourceCast
    (FiniteEquiv.refl (Fin sourceDiagram.externalClasses)) (by
      funext index
      rfl)
  rw [castBody source.checked.elaborate source.boundary_length sourceExternalEq]
  rw [castBody target.elaborate targetLength targetExternalEq]
  simp only [Region.renameWires_comp] at transported ⊢
  have maps : sourceCast ∘ concreteCollapse =
      collapse ∘ Fin.cast targetExternalEq.symm := by
    funext index
    apply Fin.ext
    rfl
  have targetRegions :
      target.elaborate.body.renameWires (sourceCast ∘ concreteCollapse) =
        target.elaborate.body.renameWires
          (collapse ∘ Fin.cast targetExternalEq.symm) :=
    congrArg (fun wireMap => target.elaborate.body.renameWires wireMap) maps
  exact targetRegions ▸ transported

end VisualProof.Refinement.Implementation.WireSever
