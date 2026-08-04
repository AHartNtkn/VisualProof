import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalRootCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

variable {signature : List Nat}
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
  {raw : ConcreteDiagram}

theorem terminalBoundary_root
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    ∀ wire, wire ∈ boundary.map copyTrace.wireMap →
      ((dropInstantiationAtomsRaw result).wires wire).scope =
        (dropInstantiationAtomsRaw result).root := by
  intro mapped member
  obtain ⟨wire, wireMember, rfl⟩ := List.mem_map.mp member
  rw [InstantiationDrop.raw_wire_scope]
  rw [copyTrace.wireMap_scope]
  have rootScope :
      ((initialInstantiationState payload).diagram.val.wires wire).scope =
        (initialInstantiationState payload).diagram.val.root := by
    simpa [initialInstantiationState] using boundaryRoot wire wireMember
  rw [rootScope, copyTrace.regionMap_root]
  rfl

noncomputable def finalRootContextSimulation
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    let source : CheckedOpenDiagram signature :=
      ⟨copyTrace.finalSourceOpen elimTrace boundary,
        copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
          finalWellFormed boundary boundaryRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨finalTargetOpen input boundary,
        finalTargetOpen_wellFormed input boundary boundaryRoot⟩
    let simulation := copyTrace.finalSemanticSimulation elimTrace
      sourceWellFormed finalWellFormed model named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires := by
  let source : CheckedOpenDiagram signature :=
    ⟨copyTrace.finalSourceOpen elimTrace boundary,
      copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
        finalWellFormed boundary boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨finalTargetOpen input boundary,
      finalTargetOpen_wellFormed input boundary boundaryRoot⟩
  let simulation := copyTrace.finalSemanticSimulation elimTrace
    sourceWellFormed finalWellFormed model named
  let outer := copyTrace.finalOuterContextWitness elimTrace boundary
  let combined := copyTrace.finalRootContextWitness elimTrace finalWellFormed
    boundary boundaryRoot sourceWellFormed
  have sourceRootExact : ConcreteElaboration.WireContext.Exact
      source.val.rootWires
      elimTrace.sourceDiagram.root := by
    simpa [source] using
      ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        source
  have targetRootExact : ConcreteElaboration.WireContext.Exact
      target.val.rootWires input.val.root := by
    simpa [target] using
      ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        target
  refine {
    outer := outer.indexRelation
    context := PLift.up combined
    atRoot := copyTrace.finalRoot_admissible elimTrace finalWellFormed
    atRootChild := ?_
    atFocusedRootChild := ?_
    transport := ?_
    focusedRootKernel := ?_
  }
  · intro regular child childParent
    exact copyTrace.child_admissible_of_regular_parent elimTrace
      finalWellFormed elimTrace.sourceDiagram.root child
      (Classical.not_not.mp regular) childParent
  · intro focused child childParent targetParent
    have rootFocus : elimTrace.sourceDiagram.root =
        elimTrace.targetIndex finalWellFormed := by
      rcases copyTrace.finalRoot_admissible elimTrace finalWellFormed with
        rootRegular | rootFocus
      · exact False.elim (focused rootRegular)
      · exact rootFocus
    rw [rootFocus] at childParent
    left
    by_cases childRegular : copyTrace.FinalRegularPreimage elimTrace
        finalWellFormed child
    · exact childRegular
    · have childFallback : copyTrace.reverseRegionMap elimTrace
          finalWellFormed child = payload.parent := by
        simp [reverseRegionMap, childRegular]
      have parentRoot : payload.parent = input.val.root := by
        calc
          payload.parent = copyTrace.reverseRegionMap elimTrace finalWellFormed
              (elimTrace.targetIndex finalWellFormed) :=
            (copyTrace.reverseRegionMap_targetIndex elimTrace
              finalWellFormed).symm
          _ = copyTrace.reverseRegionMap elimTrace finalWellFormed
              elimTrace.sourceDiagram.root := congrArg
            (copyTrace.reverseRegionMap elimTrace finalWellFormed)
            rootFocus.symm
          _ = input.val.root :=
            copyTrace.reverseRegionMap_root elimTrace finalWellFormed
      have selfParent : (input.val.regions payload.parent).parent? =
          some payload.parent := by
        have targetParent' := targetParent
        change (input.val.regions
            (copyTrace.reverseRegionMap elimTrace finalWellFormed child)).parent? =
          some (copyTrace.reverseRegionMap elimTrace finalWellFormed
            elimTrace.sourceDiagram.root) at targetParent'
        rw [childFallback,
          copyTrace.reverseRegionMap_root elimTrace finalWellFormed]
          at targetParent'
        rw [← parentRoot] at targetParent'
        exact targetParent'
      exact False.elim
        ((ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property selfParent)
          (ConcreteDiagram.Encloses.refl input.val payload.parent))
  · intro regular allowed sourceItems targetItems sourceCompiled
      targetCompiled itemSemantics
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    apply ConcreteElaboration.directionalRootTransport_of_agreement direction
      source.val.exposedWires source.val.hiddenWires target.val.exposedWires
      target.val.hiddenWires outer.indexRelation combined.indexRelation model
      named (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty)) targetItems
    · exact copyTrace.finalRootEnvironmentSelection elimTrace sourceWellFormed
        finalWellFormed boundary boundaryRoot direction
    · exact itemSemantics
  · intro atRoot focused allowed recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    have sourceRootFocus : elimTrace.sourceDiagram.root =
        elimTrace.targetIndex finalWellFormed := by
      rcases atRoot with rootRegular | rootFocus
      · exact False.elim (focused rootRegular)
      · exact rootFocus
    have targetParentRoot : payload.parent = input.val.root := by
      calc
        payload.parent = copyTrace.reverseRegionMap elimTrace finalWellFormed
            (elimTrace.targetIndex finalWellFormed) :=
          (copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed).symm
        _ = copyTrace.reverseRegionMap elimTrace finalWellFormed
            elimTrace.sourceDiagram.root := congrArg
          (copyTrace.reverseRegionMap elimTrace finalWellFormed)
          sourceRootFocus.symm
        _ = input.val.root :=
          copyTrace.reverseRegionMap_root elimTrace finalWellFormed
    have allowedFocus : FinalAllowed elimTrace.sourceDiagram
        (elimTrace.targetIndex finalWellFormed) direction
        (elimTrace.targetIndex finalWellFormed) := by
      exact sourceRootFocus ▸ allowed
    have directionEq := finalAllowed_focus_forward elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction allowedFocus
    subst direction
    let terminalBoundary := boundary.map copyTrace.wireMap
    have terminalBoundaryRoot := copyTrace.terminalBoundary_root
      boundary boundaryRoot
    let terminal : CheckedOpenDiagram signature :=
      ⟨VacuousElimTrace.targetOpen (dropInstantiationAtomsRaw result)
          terminalBoundary,
        VacuousElimTrace.targetOpen_wellFormed finalWellFormed
          terminalBoundary terminalBoundaryRoot⟩
    have terminalParentRoot : elimTrace.parent =
        (dropInstantiationAtomsRaw result).root := by
      calc
        elimTrace.parent = elimTrace.origin
            (elimTrace.targetIndex finalWellFormed) :=
          (elimTrace.targetIndex_origin finalWellFormed).symm
        _ = elimTrace.origin elimTrace.sourceDiagram.root :=
          congrArg elimTrace.origin sourceRootFocus.symm
        _ = (dropInstantiationAtomsRaw result).root :=
          elimTrace.promotion.root_origin
    let terminalContext := elimTrace.rootContextWitness sourceWellFormed
      finalWellFormed terminalBoundary terminalBoundaryRoot
    have terminalExact : ConcreteElaboration.WireContext.Exact
        terminal.val.rootWires elimTrace.parent := by
      have exact :=
        ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          terminal
      simpa [terminal, terminalParentRoot] using exact
    have sourceRootEq : source.val.rootWires =
        (elimTrace.sourceOpen terminalBoundary).rootWires := rfl
    have sourceExactFocus : ConcreteElaboration.WireContext.Exact
        source.val.rootWires
        (elimTrace.targetIndex finalWellFormed) := by
      simpa [sourceRootFocus] using sourceRootExact
    have targetExactParent : ConcreteElaboration.WireContext.Exact
        target.val.rootWires payload.parent := by
      simpa [targetParentRoot] using targetRootExact
    let sourceEmpty : ConcreteElaboration.BinderContext
        elimTrace.sourceDiagram [] := ConcreteElaboration.BinderContext.empty
    let targetEmpty : ConcreteElaboration.BinderContext input.val [] :=
      ConcreteElaboration.BinderContext.empty
    have targetCover : targetEmpty.Covers
        payload.parent := by
      simpa [targetParentRoot] using
        ConcreteElaboration.BinderContext.empty_covers_root input.property
    have targetEnumeration :
        ConcreteElaboration.BinderContext.Enumeration input.val
          targetEmpty payload.parent := by
      simpa [targetParentRoot] using
        ConcreteElaboration.BinderContext.Enumeration.empty input.val
    have sourceCover : sourceEmpty.Covers
        (elimTrace.targetIndex finalWellFormed) := by
      simpa [sourceRootFocus] using
        ConcreteElaboration.BinderContext.empty_covers_root sourceWellFormed
    have sourceEnumeration :
        ConcreteElaboration.BinderContext.Enumeration elimTrace.sourceDiagram
          sourceEmpty
          (elimTrace.targetIndex finalWellFormed) := by
      simpa [sourceRootFocus] using
        ConcreteElaboration.BinderContext.Enumeration.empty
          elimTrace.sourceDiagram
    have itemTransport := copyTrace.focusedRootItems_transport elimTrace
      sourceWellFormed finalWellFormed model named
      elimTrace.sourceDiagram.regionCount input.val.regionCount
      source.val.rootWires target.val.rootWires combined terminal.val.rootWires
      terminalContext terminalExact sourceEmpty
      targetEmpty simulation.binders_empty
      sourceExactFocus targetExactParent sourceCover targetCover
      sourceEnumeration targetEnumeration allowedFocus
      (fun childFuelTarget childSourceContext childTargetContext childContext =>
        recurseAt childFuelTarget childSourceContext childTargetContext
          (PLift.up childContext))
      sourceItems targetItems
      (by simpa [sourceRootEq, sourceRootFocus] using sourceCompiled)
      (by
        have targetCompiled' := targetCompiled
        change ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val
              input.val.regionCount) target.val.rootWires targetEmpty
            (ConcreteElaboration.localOccurrences input.val
              (copyTrace.reverseRegionMap elimTrace finalWellFormed
                elimTrace.sourceDiagram.root)) = some targetItems
          at targetCompiled'
        rw [copyTrace.reverseRegionMap_root elimTrace finalWellFormed]
          at targetCompiled'
        simpa [target, targetEmpty, targetParentRoot] using targetCompiled')
    have relationMapEq :
        (simulation.relationMap simulation.binders_empty :
          RelationRenaming [] []) =
        (fun {arity} (relation : RelVar [] arity) => relation) := rfl
    have itemTransport' :
        ConcreteElaboration.ItemSeqSimulation model named .forward
          combined.indexRelation sourceItems targetItems := by
      change ConcreteElaboration.ItemSeqSimulation model named .forward
        combined.indexRelation
        (sourceItems.renameRelations
          (simulation.relationMap simulation.binders_empty)) targetItems
        at itemTransport
      rw [relationMapEq, ItemSeq.renameRelations_id] at itemTransport
      exact itemTransport
    rw [relationMapEq, Region.renameRelations_id]
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    exact ConcreteElaboration.finishRoot_denote .forward
      source.val.exposedWires source.val.hiddenWires target.val.exposedWires
      target.val.hiddenWires outer.indexRelation model named sourceItems
      targetItems
      (ConcreteElaboration.directionalRootTransport_of_agreement .forward
        source.val.exposedWires source.val.hiddenWires target.val.exposedWires
        target.val.hiddenWires outer.indexRelation combined.indexRelation model
        named sourceItems targetItems
        (copyTrace.finalRootEnvironmentSelection elimTrace sourceWellFormed
          finalWellFormed boundary boundaryRoot .forward)
        itemTransport')

theorem finalBoundaryWitness
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (direction : ConcreteElaboration.SimulationDirection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    let source : CheckedOpenDiagram signature :=
      ⟨copyTrace.finalSourceOpen elimTrace boundary,
        copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
          finalWellFormed boundary boundaryRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨finalTargetOpen input boundary,
        finalTargetOpen_wellFormed input boundary boundaryRoot⟩
    let root := copyTrace.finalRootContextSimulation elimTrace
      sourceWellFormed finalWellFormed boundary boundaryRoot
      model named direction
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction source.elaborate target.elaborate root.outer model named
      (args ∘ Fin.cast
        (copyTrace.finalBoundaryLengthEq elimTrace boundary)) args := by
  dsimp only
  let source : CheckedOpenDiagram signature :=
    ⟨copyTrace.finalSourceOpen elimTrace boundary,
      copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
        finalWellFormed boundary boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨finalTargetOpen input boundary,
      finalTargetOpen_wellFormed input boundary boundaryRoot⟩
  let outer := copyTrace.finalOuterContextWitness elimTrace boundary
  let root := copyTrace.finalRootContextSimulation elimTrace sourceWellFormed
    finalWellFormed boundary boundaryRoot model named direction
  let lengthEq := copyTrace.finalBoundaryLengthEq elimTrace boundary
  have sourceExposedNodup := source.val.exposedWires_nodup
  have targetExposedNodup := target.val.exposedWires_nodup
  have wireInjective := copyTrace.finalWireMap_injective elimTrace
  unfold
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
  cases direction with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      let targetAssignment : BoundaryAssignment target.elaborate
          model.Carrier := {
        args := args
        classes := outer.targetEnvironment sourceAssignment.classes
        agrees := by
          intro position
          let sourcePosition : Fin source.val.boundary.length :=
            Fin.cast lengthEq.symm position
          have classEq := copyTrace.finalOuter_sourceIndex_boundaryClass
            elimTrace boundary position
          change sourceAssignment.classes
              (outer.sourceIndex (target.val.boundaryClass position)) =
            args position
          rw [classEq]
          calc
            sourceAssignment.classes
                (source.val.boundaryClass sourcePosition) =
                sourceAssignment.args sourcePosition :=
              sourceAssignment.agrees sourcePosition
            _ = (args ∘ Fin.cast lengthEq) sourcePosition :=
              congrFun sourceArgsEq sourcePosition
            _ = args position := by
              apply congrArg args
              apply Fin.ext
              rfl
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      exact outer.targetEnvironment_agrees sourceAssignment.classes
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      letI : Nonempty model.Carrier :=
        ConcreteElaboration.lambdaModel_carrier_nonempty model
      let fallback : model.Carrier := Classical.choice inferInstance
      let sourceClasses := outer.sourceEnvironment sourceExposedNodup
        targetExposedNodup wireInjective fallback targetAssignment.classes
      let sourceAssignment : BoundaryAssignment source.elaborate
          model.Carrier := {
        args := args ∘ Fin.cast lengthEq
        classes := sourceClasses
        agrees := by
          intro sourcePosition
          let targetPosition : Fin target.val.boundary.length :=
            Fin.cast lengthEq sourcePosition
          have classEq := copyTrace.finalOuter_sourceIndex_boundaryClass
            elimTrace boundary targetPosition
          have classEq' : outer.sourceIndex
                (target.val.boundaryClass targetPosition) =
              source.val.boundaryClass sourcePosition := by
            simpa [targetPosition] using classEq
          change sourceClasses (source.val.boundaryClass sourcePosition) =
            (args ∘ Fin.cast lengthEq) sourcePosition
          rw [← classEq']
          calc
            sourceClasses
                (outer.sourceIndex (target.val.boundaryClass targetPosition)) =
                targetAssignment.classes
                  (target.val.boundaryClass targetPosition) :=
              outer.sourceEnvironment_sourceIndex sourceExposedNodup
                targetExposedNodup wireInjective fallback
                targetAssignment.classes _
            _ = targetAssignment.args targetPosition :=
              targetAssignment.agrees targetPosition
            _ = args targetPosition := congrFun targetArgsEq targetPosition
            _ = (args ∘ Fin.cast lengthEq) sourcePosition := by
              apply congrArg args
              apply Fin.ext
              rfl
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      exact outer.sourceEnvironment_agrees sourceExposedNodup
        targetExposedNodup wireInjective fallback targetAssignment.classes

theorem finalOpen_denote
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (direction : ConcreteElaboration.SimulationDirection)
    (allowed : FinalAllowed elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction
      elimTrace.sourceDiagram.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    let source : CheckedOpenDiagram signature :=
      ⟨copyTrace.finalSourceOpen elimTrace boundary,
        copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
          finalWellFormed boundary boundaryRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨finalTargetOpen input boundary,
        finalTargetOpen_wellFormed input boundary boundaryRoot⟩
    direction.Entails
      (source.denote model named
          (args ∘ Fin.cast
            (copyTrace.finalBoundaryLengthEq elimTrace boundary)))
      (target.denote model named args) := by
  let source : CheckedOpenDiagram signature :=
    ⟨copyTrace.finalSourceOpen elimTrace boundary,
      copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
        finalWellFormed boundary boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨finalTargetOpen input boundary,
      finalTargetOpen_wellFormed input boundary boundaryRoot⟩
  let simulation := copyTrace.finalSemanticSimulation elimTrace
    sourceWellFormed finalWellFormed model named
  let root := copyTrace.finalRootContextSimulation elimTrace sourceWellFormed
    finalWellFormed boundary boundaryRoot model named direction
  exact ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
    source target model named simulation direction root allowed
    (args ∘ Fin.cast (copyTrace.finalBoundaryLengthEq elimTrace boundary)) args
    (copyTrace.finalBoundaryWitness elimTrace sourceWellFormed finalWellFormed
      boundary boundaryRoot direction model named args)

end InstantiationTrace

end VisualProof.Rule
