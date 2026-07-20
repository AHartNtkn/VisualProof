import VisualProof.Rule.Soundness.Comprehension.InstantiationParameterValues
import VisualProof.Rule.Soundness.AttachmentAliasSemanticRootFocused
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Alignment.HostProjection

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

private theorem materializedCompilerTrace_terminalLexical
    {signature : List Nat}
    {Host : Type} [DecidableEq Host]
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer).WellFormed signature)
    {sourceStart sourceEnd : Fin pattern.val.diagram.regionCount}
    {targetStart targetEnd : Fin
      (Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer).regionCount}
    {sourcePath targetPath : List Nat} {rels : RelCtx}
    {sourceOuter targetOuter : Nat}
    {sourceBody : Region signature sourceOuter rels}
    {targetBody : Region signature targetOuter rels}
    {sourceRoute : Splice.RegionRoute pattern.val.diagram sourceStart sourceEnd
      sourcePath}
    {targetRoute : Splice.RegionRoute
      (Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer) targetStart targetEnd targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Splice.Region.ContextPath.CompilerLeaf pattern.val.diagram
      sourceStart (.here sourceBody)}
    {targetState : Splice.Region.ContextPath.CompilerLeaf
      (Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer) targetStart (.here targetBody)}
    (sourceTrace : Splice.CompilerTrace signature pattern.val.diagram
      sourceRoute sourceWitness sourceState)
    (targetTrace : Splice.CompilerTrace signature
      (Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer)
      targetRoute targetWitness targetState)
    (sourceEndEq : sourceEnd = spine.bodyContainer)
    (targetEndEq : targetEnd = spine.bodyContainer)
    (startEq : targetStart = sourceStart)
    (hbinders : HEq sourceState.binders targetState.binders) :
    ∃ hrels : sourceWitness.toFocus.holeRels =
        targetWitness.toFocus.holeRels,
      HEq sourceTrace.leaf.binders targetTrace.leaf.binders := by
  induction sourceTrace generalizing targetStart targetEnd targetPath targetOuter with
  | here sourceState =>
      cases targetTrace with
      | here targetState =>
          exact ⟨rfl, hbinders⟩
      | @cut _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _ targetState _ _
          childState childKind inherited binders fuel tailTrace =>
          have hcycle := Splice.Input.RegionRoute.encloses tail targetWellFormed
          rw [targetEndEq] at hcycle
          have parentBody :
              ((Splice.AttachmentAliasMaterialization.materializedDiagram
                pattern.val attachment spine.bodyContainer).regions child).parent? =
                some spine.bodyContainer := by
            simpa [startEq, sourceEndEq] using parent
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              targetWellFormed parentBody hcycle)
      | @bubble _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _ _ targetState _ _
          childState childKind inherited binders fuel tailTrace =>
          have hcycle := Splice.Input.RegionRoute.encloses tail targetWellFormed
          rw [targetEndEq] at hcycle
          have parentBody :
              ((Splice.AttachmentAliasMaterialization.materializedDiagram
                pattern.val attachment spine.bodyContainer).regions child).parent? =
                some spine.bodyContainer := by
            simpa [startEq, sourceEndEq] using parent
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              targetWellFormed parentBody hcycle)
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceItems
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := Splice.Input.RegionRoute.encloses sourceTail
            pattern.property.diagram_well_formed
          rw [sourceEndEq] at hcycle
          have sourceStartBody : sourceStart = spine.bodyContainer :=
            startEq.symm.trans targetEndEq
          have parentBody :
              (pattern.val.diagram.regions sourceChild).parent? =
                some spine.bodyContainer := by
            simpa [sourceStartBody] using sourceParent
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              pattern.property.diagram_well_formed parentBody hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some sourceStart := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            sourceEncloses targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble sourceStart targetArity := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetChildKind)
          have hkind : CRegion.cut sourceStart =
              CRegion.bubble sourceStart targetArity :=
            sourceChildKind.symm.trans targetChildKindSource
          contradiction
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some sourceStart := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            sourceEncloses targetEnclosesSource
          subst targetChild
          have hchildBinders : HEq sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact hbinders
          exact ih targetTailTrace sourceEndEq targetEndEq rfl hchildBinders

/- Placement scratch: moved below the complete ordinary-trace induction.
private theorem materializedOpenCompilerTrace_terminalLexical
    {signature : List Nat}
    {Host : Type} [DecidableEq Host]
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate pattern
      attachment spine)
    {sourcePath targetPath : List Nat}
    {sourceBody : Region signature pattern.val.exposedWires.length []}
    {targetBody : Region signature certificate.result.val.exposedWires.length []}
    {sourceRoute : Splice.RegionRoute pattern.val.diagram pattern.val.diagram.root
      spine.bodyContainer sourcePath}
    {targetRoute : Splice.RegionRoute certificate.result.val.diagram
      certificate.result.val.diagram.root spine.bodyContainer targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Splice.OpenRootCompilerState pattern sourceBody}
    {targetState : Splice.OpenRootCompilerState certificate.result targetBody}
    (sourceTrace : Splice.OpenCompilerTrace pattern sourceRoute sourceWitness
      sourceState)
    (targetTrace : Splice.OpenCompilerTrace certificate.result targetRoute
      targetWitness targetState)
    (sourceProper : spine.bodyContainer ≠ pattern.val.diagram.root)
    (targetProper : spine.bodyContainer ≠ certificate.result.val.diagram.root) :
    ∃ hrels : sourceWitness.toFocus.holeRels =
        targetWitness.toFocus.holeRels,
      HEq (sourceTrace.leaf.nestedOfNe sourceProper).binders
        (targetTrace.leaf.nestedOfNe targetProper).binders := by
  cases sourceTrace with
  | here sourceState => exact False.elim (sourceProper rfl)
  | @cut sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceItems sourceFocus sourceChildBody sourceAt
      sourceIsCut sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (targetProper rfl)
      | @bubble targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some pattern.val.diagram.root := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed) targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble pattern.val.diagram.root targetArity := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetChildKind
          have hkind : CRegion.cut pattern.val.diagram.root =
              CRegion.bubble pattern.val.diagram.root targetArity :=
            sourceChildKind.symm.trans targetChildKindSource
          contradiction
      | @cut targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some pattern.val.diagram.root := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed) targetEnclosesSource
          subst targetChild
          have hchildBinders : HEq sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact HEq.rfl
          obtain ⟨hrels, hleaf⟩ := materializedCompilerTrace_terminalLexical
            pattern attachment spine certificate.wellFormed sourceTailTrace
              targetTailTrace rfl rfl rfl hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [Splice.OpenCompilerTrace.leaf,
            Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Splice.Region.ContextPath.CompilerLeaf.underCut] using hleaf
  | @bubble sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceArity sourceItems sourceFocus sourceChildBody
      sourceAt sourceIsBubble sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (targetProper rfl)
      | @cut targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some pattern.val.diagram.root := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed) targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .cut pattern.val.diagram.root := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetChildKind
          have hkind : CRegion.bubble pattern.val.diagram.root sourceArity =
              CRegion.cut pattern.val.diagram.root :=
            sourceChildKind.symm.trans targetChildKindSource
          contradiction
      | @bubble targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some pattern.val.diagram.root := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed) targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble pattern.val.diagram.root targetArity := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetChildKind
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKindSource.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildBinders : HEq sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact HEq.rfl
          obtain ⟨hrels, hleaf⟩ := materializedCompilerTrace_terminalLexical
            pattern attachment spine certificate.wellFormed sourceTailTrace
              targetTailTrace rfl rfl rfl hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [Splice.OpenCompilerTrace.leaf,
            Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Splice.Region.ContextPath.CompilerLeaf.underBubble] using hleaf
-/
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceItems sourceFocus sourceChildBody sourceAt sourceIsBubble
      sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
      sourceChildState sourceChildKind sourceInherited sourceBinders sourceFuel
      sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := Splice.Input.RegionRoute.encloses sourceTail
            pattern.property.diagram_well_formed
          rw [sourceEndEq] at hcycle
          have sourceStartBody : sourceStart = spine.bodyContainer :=
            startEq.symm.trans targetEndEq
          have parentBody :
              (pattern.val.diagram.regions sourceChild).parent? =
                some spine.bodyContainer := by
            simpa [sourceStartBody] using sourceParent
          exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              pattern.property.diagram_well_formed parentBody hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some sourceStart := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            sourceEncloses targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .cut sourceStart := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetChildKind)
          have hkind : CRegion.bubble sourceStart sourceArity =
              CRegion.cut sourceStart :=
            sourceChildKind.symm.trans targetChildKindSource
          contradiction
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some sourceStart := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            sourceEncloses targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble sourceStart targetArity := by
            simpa only [Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetChildKind)
          have harity : targetArity = sourceArity := by
            exact (CRegion.bubble.inj
              (targetChildKindSource.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildBinders : HEq sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact heq_of_eq (congrArg
              (fun binders => binders.push sourceChild sourceArity)
              (eq_of_heq hbinders))
          exact ih targetTailTrace sourceEndEq targetEndEq rfl hchildBinders

/-- Attachment-alias materialization preserves the nonzero-spine terminal
relation for the exact fixed proxy family.  The ordered boundary remains
positional: repeated source aliases may materialize as distinct exposed wires,
and the inserted identity block must recover precisely the source alias
equalities in the backward direction.

This is deliberately stronger than whole-open denotation preservation, whose
existential relation environment cannot establish preservation for an
arbitrary caller-supplied proxy family. -/
theorem terminalRelationOfParameterValues_materialized_iff
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (relationArguments : Fin payload.arity → model.Carrier) :
    terminalRelationOfParameterValues
        (materializedInstantiationPayload payload
          (instantiationAttachment comprehension attachments binders payload state
            arguments)
          certificate)
        state site arguments hnonempty model named parameterValues values
        relationArguments ↔
      terminalRelationOfParameterValues payload state site arguments hnonempty
        model named parameterValues values relationArguments := by
  let attachment := instantiationAttachment comprehension attachments binders
    payload state arguments
  let sourceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let targetPayload := materializedInstantiationPayload payload attachment
    certificate
  let targetInput := instantiateSpliceInput certificate.result attachments binders
    targetPayload state site arguments
  let sourcePattern := Splice.Input.compiledSpliceTerminalView sourceInput hnonempty
  let targetPattern := Splice.Input.compiledSpliceTerminalView targetInput hnonempty
  let collapse :
      Splice.AttachmentAliasMaterialization.Semantic.ContextCollapse comprehension
        attachment payload.binderSpine targetPattern.leaf.inheritedWires
        sourcePattern.leaf.inheritedWires := {
    indexMap := fun index => Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete (by
        have targetInherited : targetPattern.leaf.inheritedWires.get index ∈
            targetPattern.leaf.inheritedWires := List.get_mem _ index
        have targetExposed : targetPattern.leaf.inheritedWires.get index ∈
            targetInput.pattern.val.exposedWires :=
          (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            targetPattern.witness targetPattern.leaf hnonempty _).1
            targetInherited
        have targetBoundary : targetPattern.leaf.inheritedWires.get index ∈
            targetInput.pattern.val.boundary :=
          (OpenConcreteDiagram.mem_exposedWires _ _).1 targetExposed
        have sourceBoundary :
            Splice.AttachmentAliasMaterialization.Semantic.collapseWire comprehension.val
                attachment (targetPattern.leaf.inheritedWires.get index) ∈
              comprehension.val.boundary :=
          Splice.AttachmentAliasMaterialization.Semantic.collapseWire_mem_boundary_of_mem_rawBoundary
            comprehension.val attachment payload.binderSpine.bodyContainer _
            targetBoundary
        have sourceExposed :
            Splice.AttachmentAliasMaterialization.Semantic.collapseWire comprehension.val
                attachment (targetPattern.leaf.inheritedWires.get index) ∈
              comprehension.val.exposedWires :=
          (OpenConcreteDiagram.mem_exposedWires _ _).2 sourceBoundary
        exact (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          sourcePattern.witness sourcePattern.leaf hnonempty _).2 sourceExposed))
    get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (ConcreteElaboration.WireContext.lookup?_complete (by
            have targetInherited : targetPattern.leaf.inheritedWires.get index ∈
                targetPattern.leaf.inheritedWires := List.get_mem _ index
            have targetExposed : targetPattern.leaf.inheritedWires.get index ∈
                targetInput.pattern.val.exposedWires :=
              (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
                targetPattern.witness targetPattern.leaf hnonempty _).1
                targetInherited
            have targetBoundary : targetPattern.leaf.inheritedWires.get index ∈
                targetInput.pattern.val.boundary :=
              (OpenConcreteDiagram.mem_exposedWires _ _).1 targetExposed
            have sourceBoundary :
                Splice.AttachmentAliasMaterialization.Semantic.collapseWire
                    comprehension.val attachment
                    (targetPattern.leaf.inheritedWires.get index) ∈
                  comprehension.val.boundary :=
              Splice.AttachmentAliasMaterialization.Semantic.collapseWire_mem_boundary_of_mem_rawBoundary
                comprehension.val attachment payload.binderSpine.bodyContainer _
                targetBoundary
            exact (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
              sourcePattern.witness sourcePattern.leaf hnonempty _).2
                ((OpenConcreteDiagram.mem_exposedWires _ _).2 sourceBoundary))))
    oldIndex := fun index => Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete (by
        have sourceInherited : sourcePattern.leaf.inheritedWires.get index ∈
            sourcePattern.leaf.inheritedWires := List.get_mem _ index
        have sourceExposed : sourcePattern.leaf.inheritedWires.get index ∈
            comprehension.val.exposedWires :=
          (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            sourcePattern.witness sourcePattern.leaf hnonempty _).1
            sourceInherited
        have sourceBoundary : sourcePattern.leaf.inheritedWires.get index ∈
            comprehension.val.boundary :=
          (OpenConcreteDiagram.mem_exposedWires _ _).1 sourceExposed
        have targetBoundary :=
          Splice.AttachmentAliasMaterialization.liftOldWire_mem_raw_boundary
            comprehension.val attachment payload.binderSpine.bodyContainer
            (sourcePattern.leaf.inheritedWires.get index) sourceBoundary
        have targetExposed :
            Splice.AttachmentAliasMaterialization.liftOldWire comprehension.val
                attachment (sourcePattern.leaf.inheritedWires.get index) ∈
              targetInput.pattern.val.exposedWires :=
          (OpenConcreteDiagram.mem_exposedWires _ _).2 targetBoundary
        exact (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty _).2 targetExposed))
    old_get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (ConcreteElaboration.WireContext.lookup?_complete (by
            have sourceInherited : sourcePattern.leaf.inheritedWires.get index ∈
                sourcePattern.leaf.inheritedWires := List.get_mem _ index
            have sourceExposed : sourcePattern.leaf.inheritedWires.get index ∈
                comprehension.val.exposedWires :=
              (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
                sourcePattern.witness sourcePattern.leaf hnonempty _).1
                sourceInherited
            have sourceBoundary : sourcePattern.leaf.inheritedWires.get index ∈
                comprehension.val.boundary :=
              (OpenConcreteDiagram.mem_exposedWires _ _).1 sourceExposed
            have targetBoundary :=
              Splice.AttachmentAliasMaterialization.liftOldWire_mem_raw_boundary
                comprehension.val attachment payload.binderSpine.bodyContainer
                (sourcePattern.leaf.inheritedWires.get index) sourceBoundary
            exact (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
              targetPattern.witness targetPattern.leaf hnonempty _).2
                ((OpenConcreteDiagram.mem_exposedWires _ _).2 targetBoundary))))
  }
  sorry

/-- Extensional equality form consumed by the executor-trace simulation. -/
theorem terminalRelationOfParameterValues_materialized
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    terminalRelationOfParameterValues payload state site arguments hnonempty
        model named parameterValues values =
      terminalRelationOfParameterValues
        (materializedInstantiationPayload payload
          (instantiationAttachment comprehension attachments binders payload state
            arguments)
          certificate)
        state site arguments hnonempty model named parameterValues values := by
  funext relationArguments
  apply propext
  exact (terminalRelationOfParameterValues_materialized_iff payload state site
    arguments certificate hnonempty model named parameterValues values
    relationArguments).symm

end InstantiationSemantic

end VisualProof.Rule
