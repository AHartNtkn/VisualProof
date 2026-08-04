import VisualProof.Rule.Soundness.AttachmentAliasSemanticBoundary
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Discrete

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

private theorem rootSelection
    (mode : Mode)
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin pattern.val.exposedWires.length → model.Carrier)
      (targetOuter : Fin
        (raw pattern.val attachment spine.bodyContainer).exposedWires.length →
          model.Carrier),
      (indexRelation mode (exposedCollapse pattern attachment spine)).EnvironmentsAgree
        sourceOuter targetOuter →
      match mode.direction with
      | .forward => ∀ sourceLocal,
          ∃ targetLocal,
            (indexRelation mode
              (rootCollapse pattern attachment spine contract targetWellFormed)
            ).EnvironmentsAgree
              (ConcreteElaboration.rootEnvironment pattern.val.exposedWires
                pattern.val.hiddenWires sourceOuter sourceLocal)
              (ConcreteElaboration.rootEnvironment
                (raw pattern.val attachment spine.bodyContainer).exposedWires
                (raw pattern.val attachment spine.bodyContainer).hiddenWires
                targetOuter targetLocal)
      | .backward => ∀ targetLocal,
          ∃ sourceLocal,
            (indexRelation mode
              (rootCollapse pattern attachment spine contract targetWellFormed)
            ).EnvironmentsAgree
              (ConcreteElaboration.rootEnvironment pattern.val.exposedWires
                pattern.val.hiddenWires sourceOuter sourceLocal)
              (ConcreteElaboration.rootEnvironment
                (raw pattern.val attachment spine.bodyContainer).exposedWires
                (raw pattern.val attachment spine.bodyContainer).hiddenWires
                targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgrees
  cases mode with
  | forward =>
      simp only [indexRelation, Mode.direction] at outerAgrees ⊢
      rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap]
        at outerAgrees
      intro sourceLocal
      let targetLocal := forwardTargetLocal pattern attachment spine contract
        targetWellFormed sourceOuter sourceLocal
      refine ⟨targetLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
        _ _ _).mpr
      exact forwardRootEnvironment_agrees pattern attachment spine contract
        targetWellFormed sourceOuter targetOuter outerAgrees sourceLocal
  | backward =>
      simp only [indexRelation, Mode.direction] at outerAgrees ⊢
      rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        at outerAgrees
      intro targetLocal
      let sourceLocal := backwardSourceLocal pattern attachment spine contract
        targetWellFormed targetOuter targetLocal
      refine ⟨sourceLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).mpr
      exact backwardRootEnvironment_agrees pattern attachment spine contract
        targetWellFormed sourceOuter targetOuter outerAgrees targetLocal

noncomputable def rootContext
    (mode : Mode)
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (contract : spine.TerminalBodyContract pattern.val)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    let simulation := concreteSimulation mode pattern attachment spine contract
      targetWellFormed model named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation mode.direction pattern.val.exposedWires pattern.val.hiddenWires
      (raw pattern.val attachment spine.bodyContainer).exposedWires
      (raw pattern.val attachment spine.bodyContainer).hiddenWires := by
  let simulation := concreteSimulation mode pattern attachment spine contract
    targetWellFormed model named
  let exposed := exposedCollapse pattern attachment spine
  let combined := rootCollapse pattern attachment spine contract targetWellFormed
  refine {
    outer := indexRelation mode exposed
    context := ?_
    atRoot := True.intro
    atRootChild := by intros; trivial
    atFocusedRootChild := by intros; trivial
    transport := ?_
    focusedRootKernel := ?_
  }
  · simpa only [OpenConcreteDiagram.rootWires] using combined
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    have relationMapEq :
        (fun {arity} =>
          (concreteSimulation mode pattern attachment spine contract
            targetWellFormed model named).relationMap
            (concreteSimulation mode pattern attachment spine contract
              targetWellFormed model named).binders_empty (arity := arity)) =
          (fun {arity} relation => relation) :=
      identityBinder_relationMap_same
        (source := pattern.val.diagram)
        (target := materializedDiagram pattern.val attachment
          spine.bodyContainer)
        (sourceBinders := ConcreteElaboration.BinderContext.empty)
        (targetBinders := ConcreteElaboration.BinderContext.empty)
        (concreteSimulation mode pattern attachment spine contract
          targetWellFormed model named).binders_empty
    rw [relationMapEq, ItemSeq.renameRelations_id] at itemSemantics ⊢
    exact ConcreteElaboration.directionalRootTransport_of_agreement
      mode.direction pattern.val.exposedWires pattern.val.hiddenWires
      (raw pattern.val attachment spine.bodyContainer).exposedWires
      (raw pattern.val attachment spine.bodyContainer).hiddenWires
      (indexRelation mode exposed) (indexRelation mode combined) model named
      sourceItems targetItems
      (rootSelection mode pattern attachment spine contract targetWellFormed
        model)
      itemSemantics
  · intro atRoot distinguished allowed recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    change pattern.val.diagram.root = spine.bodyContainer at distinguished
    let targetChecked : CheckedOpenDiagram signature :=
      ⟨raw pattern.val attachment spine.bodyContainer, {
        diagram_well_formed := targetWellFormed
        boundary_is_root_scoped :=
          (AttachmentAliasMaterialization.terminalBody pattern attachment spine
            contract).boundary_is_root_scoped
      }⟩
    have sourceExact :=
      ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        pattern
    have targetExact :=
      ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        targetChecked
    have sourceExactBody : ConcreteElaboration.WireContext.Exact
        pattern.val.rootWires spine.bodyContainer := by
      exact distinguished ▸ sourceExact
    have targetExactBody :
        ConcreteElaboration.WireContext.Exact
          (raw pattern.val attachment spine.bodyContainer).rootWires
          spine.bodyContainer := by
      have targetRoot :
          (raw pattern.val attachment spine.bodyContainer).diagram.root =
            spine.bodyContainer := by
        simpa [raw, materializedDiagram] using distinguished
      have targetExact' :
          ConcreteElaboration.WireContext.Exact
            (raw pattern.val attachment spine.bodyContainer).rootWires
            (raw pattern.val attachment spine.bodyContainer).diagram.root := by
        simpa only [targetChecked] using targetExact
      exact Eq.mp (congrArg
        (fun region => ConcreteElaboration.WireContext.Exact
          (raw pattern.val attachment spine.bodyContainer).rootWires region)
        targetRoot) targetExact'
    have sourceCover :=
      ConcreteElaboration.BinderContext.empty_covers_root
        pattern.property.diagram_well_formed
    have targetCover :=
      ConcreteElaboration.BinderContext.empty_covers_root targetWellFormed
    have sourceCoverBody :
        (ConcreteElaboration.BinderContext.empty :
          ConcreteElaboration.BinderContext pattern.val.diagram []).Covers
            spine.bodyContainer := by
      rw [← distinguished]
      exact sourceCover
    have targetCoverBody :
        (ConcreteElaboration.BinderContext.empty :
          ConcreteElaboration.BinderContext
            (materializedDiagram pattern.val attachment spine.bodyContainer)
            []).Covers spine.bodyContainer := by
      have targetRoot :
          (materializedDiagram pattern.val attachment
            spine.bodyContainer).root = spine.bodyContainer := by
        simpa [materializedDiagram] using distinguished
      exact targetRoot ▸ targetCover
    have sourceEnumeration :=
      ConcreteElaboration.BinderContext.Enumeration.empty pattern.val.diagram
    have targetEnumeration :=
      ConcreteElaboration.BinderContext.Enumeration.empty
        (materializedDiagram pattern.val attachment spine.bodyContainer)
    have sourceEnumerationBody :
        ConcreteElaboration.BinderContext.Enumeration pattern.val.diagram
          ConcreteElaboration.BinderContext.empty spine.bodyContainer := by
      exact Eq.mp (congrArg
        (fun region => ConcreteElaboration.BinderContext.Enumeration
          pattern.val.diagram ConcreteElaboration.BinderContext.empty region)
        distinguished) sourceEnumeration
    have targetEnumerationBody :
        ConcreteElaboration.BinderContext.Enumeration
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          ConcreteElaboration.BinderContext.empty spine.bodyContainer := by
      have targetRoot :
          (materializedDiagram pattern.val attachment spine.bodyContainer).root =
            spine.bodyContainer := by
        simpa [materializedDiagram] using distinguished
      exact Eq.mp (congrArg
        (fun region => ConcreteElaboration.BinderContext.Enumeration
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          ConcreteElaboration.BinderContext.empty region)
        targetRoot) targetEnumeration
    have childRecurse : ∀
        {childDirection : ConcreteElaboration.SimulationDirection}
        {child : Fin pattern.val.diagram.regionCount}
        {childRels : RelCtx}
        {childSourceBinders : ConcreteElaboration.BinderContext
          pattern.val.diagram childRels}
        {childTargetBinders : ConcreteElaboration.BinderContext
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          childRels}
        {sourceBody : Region signature pattern.val.rootWires.length childRels}
        {targetBody : Region signature
          (raw pattern.val attachment spine.bodyContainer).rootWires.length
          childRels},
        (pattern.val.diagram.regions child).parent? = some spine.bodyContainer →
        ((materializedDiagram pattern.val attachment spine.bodyContainer).regions
          child).parent? = some spine.bodyContainer →
        True → HEq childSourceBinders childTargetBinders →
        childSourceBinders.Covers child → childTargetBinders.Covers child →
        ConcreteElaboration.BinderContext.Enumeration pattern.val.diagram
          childSourceBinders child →
        ConcreteElaboration.BinderContext.Enumeration
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          childTargetBinders child →
        ConcreteElaboration.compileRegion? signature pattern.val.diagram
            pattern.val.diagram.regionCount child pattern.val.rootWires
            childSourceBinders = some sourceBody →
        ConcreteElaboration.compileRegion? signature
            (materializedDiagram pattern.val attachment spine.bodyContainer)
            (materializedDiagram pattern.val attachment
              spine.bodyContainer).regionCount child
            (raw pattern.val attachment spine.bodyContainer).rootWires
            childTargetBinders = some targetBody →
        ConcreteElaboration.RegionSimulation model named childDirection
          (indexRelation mode combined) sourceBody targetBody := by
      intro childDirection child childRels childSourceBinders childTargetBinders
        sourceBody targetBody sourceParent targetParent _ bindersEqual
        sourceChildCover targetChildCover sourceChildEnumeration
        targetChildEnumeration sourceChildCompiled targetChildCompiled
      have childAllowed : simulation.Allowed childDirection child := by
        intro childSpine
        exact (directChild_body_not_spine spine
          pattern.property.diagram_well_formed child sourceParent childSpine).elim
      let binderWitness : simulation.BinderWitness childSourceBinders
          childTargetBinders := ⟨rfl, bindersEqual⟩
      have childSimulation := recurse
        (by simpa [distinguished] using sourceParent)
        (by simpa [distinguished, materializedDiagram] using targetParent)
        childAllowed binderWitness sourceChildCover targetChildCover
        sourceChildEnumeration targetChildEnumeration sourceChildCompiled
        targetChildCompiled
      change ConcreteElaboration.RegionSimulation model named childDirection
        (indexRelation mode combined)
        (Region.renameRelations (fun {arity} relation => relation) sourceBody)
        targetBody at childSimulation
      simpa only [Region.renameRelations_id] using childSimulation
    have itemSimulation := focusedRootItemsSimulation mode pattern attachment
      spine targetWellFormed model named pattern.val.diagram.regionCount
      (materializedDiagram pattern.val attachment
        spine.bodyContainer).regionCount
      pattern.val.rootWires
      (raw pattern.val attachment spine.bodyContainer).rootWires combined
      sourceExactBody targetExactBody ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty HEq.rfl sourceCoverBody
      targetCoverBody sourceEnumerationBody targetEnumerationBody childRecurse
      sourceItems targetItems
      (by simpa [distinguished, OpenConcreteDiagram.rootWires] using
        sourceCompiled)
      (by simpa [distinguished, materializedDiagram,
        OpenConcreteDiagram.rootWires] using targetCompiled)
    have relationMapEq :
        (fun {arity} =>
          simulation.relationMap simulation.binders_empty (arity := arity)) =
          (fun {arity} relation => relation) :=
      identityBinder_relationMap_same simulation.binders_empty
    rw [relationMapEq, Region.renameRelations_id]
    apply ConcreteElaboration.finishRoot_denote mode.direction
      pattern.val.exposedWires pattern.val.hiddenWires
      (raw pattern.val attachment spine.bodyContainer).exposedWires
      (raw pattern.val attachment spine.bodyContainer).hiddenWires
      (indexRelation mode exposed) model named sourceItems targetItems
    exact ConcreteElaboration.directionalRootTransport_of_agreement
      mode.direction pattern.val.exposedWires pattern.val.hiddenWires
      (raw pattern.val attachment spine.bodyContainer).exposedWires
      (raw pattern.val attachment spine.bodyContainer).hiddenWires
      (indexRelation mode exposed) (indexRelation mode combined) model named
      sourceItems targetItems
      (rootSelection mode pattern attachment spine contract targetWellFormed
        model)
      itemSimulation

end Semantic

namespace Certificate

/-- The exact positional attachment function for using the materialized
boundary as a splice-input boundary. -/
def positionalAttachment {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine) :
    Fin certificate.result.val.boundary.length → Host :=
  attachment ∘ Fin.cast certificate.boundary_length

/-- Equal materialized boundary identities carry equal positional host
attachments.  This is the certificate-level content of
`Splice.Input.AttachmentsRespectBoundary`. -/
theorem positionalAttachment_eq_of_boundary_eq {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine)
    (left right : Fin certificate.result.val.boundary.length)
    (boundaryEq : certificate.result.val.boundary.get left =
      certificate.result.val.boundary.get right) :
    certificate.positionalAttachment left =
      certificate.positionalAttachment right := by
  let left' := Fin.cast certificate.boundary_length left
  let right' := Fin.cast certificate.boundary_length right
  have rawEq :
      (raw pattern.val attachment originalSpine.bodyContainer).boundary.get
          (Fin.cast (raw_boundary_length pattern.val attachment
            originalSpine.bodyContainer).symm left') =
        (raw pattern.val attachment originalSpine.bodyContainer).boundary.get
          (Fin.cast (raw_boundary_length pattern.val attachment
            originalSpine.bodyContainer).symm right') := by
    simpa [Certificate.result, left', right'] using boundaryEq
  exact (raw_boundary_get_eq_iff pattern.val attachment
    originalSpine.bodyContainer left' right').mp rawEq |>.2

/-- Equality-elimination form of the positional theorem, factored away from
the dependent fields of `Splice.Input`. -/
theorem attachmentsRespectExactPattern {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine)
    (inputPattern : CheckedOpenDiagram signature)
    (patternEq : inputPattern = certificate.result)
    (inputAttachment : Fin inputPattern.val.boundary.length → Host)
    (attachmentEq : HEq inputAttachment certificate.positionalAttachment) :
    ∀ left right,
      inputPattern.val.boundary.get left =
          inputPattern.val.boundary.get right →
        inputAttachment left = inputAttachment right := by
  cases patternEq
  cases attachmentEq
  exact certificate.positionalAttachment_eq_of_boundary_eq

/-- A splice input whose pattern and positional attachments are exactly those
of a certificate satisfies the discrete retained-frame boundary contract. -/
theorem attachmentsRespectBoundary {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment) :
    input.AttachmentsRespectBoundary := by
  exact certificate.attachmentsRespectExactPattern input.pattern patternEq
    input.attachment attachmentEq

/-- Certificate-specialized retained-frame quotient cancellation. -/
noncomputable def discreteQuotientWireEquiv {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment) :
    FiniteEquiv input.wireQuotient.Carrier
      (Fin input.frame.val.wireCount) :=
  Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq)

@[simp] theorem discreteQuotientWireEquiv_quotientWire {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment)
    (wire : Fin input.frame.val.wireCount) :
    certificate.discreteQuotientWireEquiv input attachment patternEq
        attachmentEq (input.quotientWire wire) = wire := by
  exact Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary_quotientWire input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq) wire

/-- Certificate-specialized concrete retained-frame cancellation. -/
noncomputable def coalescedFrameIso {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment) :
    ConcreteIso input.coalesceFrameRaw input.frame.val :=
  Splice.Input.coalescedFrameIsoOfAttachmentsRespectBoundary input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq)

/-- Certificate-specialized ordered retained-frame cancellation. -/
noncomputable def coalescedFrameOpenIso {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {originalSpine : BinderSpine pattern.val.diagram}
    (input : Splice.Input signature)
    (attachment : Fin pattern.val.boundary.length →
      Fin input.frame.val.wireCount)
    (certificate : Certificate pattern attachment originalSpine)
    (patternEq : input.pattern = certificate.result)
    (attachmentEq : HEq input.attachment certificate.positionalAttachment)
    (boundary : List (Fin input.frame.val.wireCount)) :
    OpenConcreteIso (Splice.Input.PlugLayout.coalescedOpenRoot input boundary)
      { diagram := input.frame.val, boundary := boundary } :=
  Splice.Input.coalescedFrameOpenIsoOfAttachmentsRespectBoundary input
    (certificate.attachmentsRespectBoundary input attachment patternEq
      attachmentEq) boundary

/-- Attachment-sensitive alias materialization preserves the checked open
denotation positionwise, including the certificate's boundary-length cast. -/
theorem denote_iff {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {originalSpine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment originalSpine)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin pattern.val.boundary.length → model.Carrier) :
    certificate.result.denote model named
        (args ∘ Fin.cast certificate.boundary_length) ↔
      pattern.denote model named args := by
  let targetArgs : Fin certificate.result.val.boundary.length → model.Carrier :=
    args ∘ Fin.cast certificate.boundary_length
  let exposed := Semantic.exposedCollapse pattern attachment originalSpine
  let forwardSimulation := Semantic.concreteSimulation .forward pattern attachment
    originalSpine certificate.sourceTerminalBody
    certificate.wellFormed.diagram_well_formed model named
  let backwardSimulation := Semantic.concreteSimulation .backward pattern attachment
    originalSpine certificate.sourceTerminalBody
    certificate.wellFormed.diagram_well_formed model named
  have forwardAllowed : forwardSimulation.Allowed .forward
      pattern.val.diagram.root := by
    intro _
    rfl
  have backwardAllowed : backwardSimulation.Allowed .backward
      pattern.val.diagram.root := by
    intro _
    rfl
  have forwardBoundary :
      ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness .forward
      pattern.elaborate certificate.result.elaborate
      (Semantic.indexRelation .forward exposed) model named args targetArgs := by
    intro sourceAssignment sourceArgsEq sourceDenotes
    let targetClasses : Fin certificate.result.elaborate.externalClasses →
        model.Carrier := sourceAssignment.classes ∘ exposed.indexMap
    let targetAssignment : BoundaryAssignment certificate.result.elaborate
        model.Carrier := {
      args := targetArgs
      classes := targetClasses
      agrees := by
        intro position
        change sourceAssignment.classes
            (exposed.indexMap
              (certificate.result.val.boundaryClass position)) =
          args (Fin.cast certificate.boundary_length position)
        have classEq : exposed.indexMap
              (certificate.result.val.boundaryClass position) =
            pattern.val.boundaryClass
              (Fin.cast certificate.boundary_length position) := by
          simpa [exposed, Certificate.result] using
            (Semantic.exposedCollapse_boundaryClass pattern attachment
              originalSpine (Fin.cast certificate.boundary_length position))
        rw [classEq]
        calc
          sourceAssignment.classes
              (pattern.val.boundaryClass
                (Fin.cast certificate.boundary_length position)) =
              sourceAssignment.args
                (Fin.cast certificate.boundary_length position) := by
                  simpa only [CheckedOpenDiagram.elaborate_boundary] using
                    sourceAssignment.agrees
                      (Fin.cast certificate.boundary_length position)
          _ = args (Fin.cast certificate.boundary_length position) :=
            congrFun sourceArgsEq _
    }
    refine ⟨targetAssignment, rfl, ?_⟩
    apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
      exposed.indexMap sourceAssignment.classes targetAssignment.classes).mpr
    rfl
  have backwardBoundary :
      ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness .backward
      pattern.elaborate certificate.result.elaborate
      (Semantic.indexRelation .backward exposed) model named args targetArgs := by
    intro targetAssignment targetArgsEq targetDenotes
    let sourceClasses : Fin pattern.elaborate.externalClasses → model.Carrier :=
      targetAssignment.classes ∘ exposed.oldIndex
    let sourceAssignment : BoundaryAssignment pattern.elaborate model.Carrier := {
      args := args
      classes := sourceClasses
      agrees := by
        intro position
        change targetAssignment.classes
            (exposed.oldIndex (pattern.val.boundaryClass position)) = args position
        have targetAgree := targetAssignment.agrees
          (Fin.cast certificate.boundary_length.symm position)
        have targetPositionCast :
            Fin.cast certificate.boundary_length
                (Fin.cast certificate.boundary_length.symm position) = position := by
          apply Fin.ext
          rfl
        rw [show certificate.result.elaborate.boundary
            (Fin.cast certificate.boundary_length.symm position) =
              certificate.result.val.boundaryClass
                (Fin.cast certificate.boundary_length.symm position) by rfl]
          at targetAgree
        have classEq : exposed.indexMap
              (certificate.result.val.boundaryClass
                (Fin.cast certificate.boundary_length.symm position)) =
            pattern.val.boundaryClass position := by
          simpa [exposed, Certificate.result] using
            (Semantic.exposedCollapse_boundaryClass pattern attachment
              originalSpine position)
        have factor := Semantic.materialized_exposed_factor_of_denote pattern
          attachment originalSpine certificate model named targetAssignment
          targetDenotes
        have classValue := congrFun factor
          (certificate.result.val.boundaryClass
            (Fin.cast certificate.boundary_length.symm position))
        simp only [Function.comp_apply] at classValue
        rw [classEq] at classValue
        rw [targetArgsEq] at targetAgree
        change targetAssignment.classes
            (certificate.result.val.boundaryClass
              (Fin.cast certificate.boundary_length.symm position)) =
          targetArgs (Fin.cast certificate.boundary_length.symm position)
          at targetAgree
        change targetAssignment.classes
            (exposed.oldIndex (pattern.val.boundaryClass position)) = args position
        calc
          targetAssignment.classes
              (exposed.oldIndex (pattern.val.boundaryClass position)) =
              targetAssignment.classes
                (certificate.result.val.boundaryClass
                  (Fin.cast certificate.boundary_length.symm position)) := by
                    exact classValue.symm
          _ = targetArgs (Fin.cast certificate.boundary_length.symm position) :=
            targetAgree
          _ = args position := by
            simp [targetArgs, targetPositionCast]
    }
    refine ⟨sourceAssignment, rfl, ?_⟩
    apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      exposed.oldIndex sourceAssignment.classes targetAssignment.classes).mpr
    rfl
  constructor
  · intro targetDenotes
    let backwardRoot := Semantic.rootContext .backward pattern attachment
      originalSpine certificate.sourceTerminalBody
      certificate.wellFormed.diagram_well_formed model named
    have backwardBoundary' :
        ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
          .backward pattern.elaborate certificate.result.elaborate
          backwardRoot.outer model named args targetArgs := by
      rw [show backwardRoot.outer = Semantic.indexRelation .backward exposed by
        rfl]
      exact backwardBoundary
    have backward := ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      pattern certificate.result model named backwardSimulation .backward
      backwardRoot backwardAllowed args targetArgs backwardBoundary'
    exact backward targetDenotes
  · intro sourceDenotes
    let forwardRoot := Semantic.rootContext .forward pattern attachment
      originalSpine certificate.sourceTerminalBody
      certificate.wellFormed.diagram_well_formed model named
    have forwardBoundary' :
        ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
          .forward pattern.elaborate certificate.result.elaborate
          forwardRoot.outer model named args targetArgs := by
      rw [show forwardRoot.outer = Semantic.indexRelation .forward exposed by
        rfl]
      exact forwardBoundary
    have forward := ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      pattern certificate.result model named forwardSimulation .forward
      forwardRoot forwardAllowed args targetArgs forwardBoundary'
    exact forward sourceDenotes

end Certificate

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
