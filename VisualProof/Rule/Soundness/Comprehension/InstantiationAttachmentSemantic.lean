import VisualProof.Rule.Soundness.Comprehension.InstantiationParameterValues
import VisualProof.Rule.Soundness.AttachmentAliasSemanticBoundary
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.HostProjection

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

private theorem materializedCompilerTrace_terminalLexical
    {Host : Type} [DecidableEq Host]
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer).WellFormed )
    {sourceStart sourceEnd : Fin pattern.val.diagram.regionCount}
    {targetStart targetEnd : Fin
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer).regionCount}
    {sourcePath targetPath : List Nat} {rels : RelCtx}
    {sourceOuter targetOuter : Nat}
    {sourceBody : Region  sourceOuter rels}
    {targetBody : Region  targetOuter rels}
    {sourceRoute : Concrete.Splice.RegionRoute pattern.val.diagram sourceStart sourceEnd
      sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer) targetStart targetEnd targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf pattern.val.diagram
      sourceStart (.here sourceBody)}
    {targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer) targetStart (.here targetBody)}
    (sourceTrace : Concrete.Splice.CompilerTrace  pattern.val.diagram
      sourceRoute sourceWitness sourceState)
    (targetTrace : Concrete.Splice.CompilerTrace
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
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
          have hcycle := Concrete.Splice.Input.RegionRoute.encloses tail targetWellFormed
          rw [targetEndEq] at hcycle
          have parentBody :
              ((Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
                pattern.val attachment spine.bodyContainer).regions child).parent? =
                some spine.bodyContainer := by
            simpa [startEq, sourceEndEq] using parent
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              targetWellFormed parentBody hcycle)
      | @bubble _ child _ _ parent _ _ tail _ _ _ _ _ _ _ _ _ _ targetState _ _
          childState childKind inherited binders fuel tailTrace =>
          have hcycle := Concrete.Splice.Input.RegionRoute.encloses tail targetWellFormed
          rw [targetEndEq] at hcycle
          have parentBody :
              ((Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
                pattern.val attachment spine.bodyContainer).regions child).parent? =
                some spine.bodyContainer := by
            simpa [startEq, sourceEndEq] using parent
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              targetWellFormed parentBody hcycle)
  | @cut sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceRels sourceItems
      sourceFocus sourceChildBody sourceAt sourceIsCut sourceNested sourceState
      sourceLocalCanonical sourceItemsCanonical sourceChildState sourceChildKind
      sourceInherited sourceBinders sourceFuel sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := Concrete.Splice.Input.RegionRoute.encloses sourceTail
            pattern.property.diagram_well_formed
          rw [sourceEndEq] at hcycle
          have sourceStartBody : sourceStart = spine.bodyContainer :=
            startEq.symm.trans targetEndEq
          have parentBody :
              (pattern.val.diagram.regions sourceChild).parent? =
                some spine.bodyContainer := by
            simpa [sourceStartBody] using sourceParent
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              pattern.property.diagram_well_formed parentBody hcycle)
      | @bubble _ targetChild _ _ targetParent _ _ targetTail _ _ targetArity
          _ _ _ _ _ _ _ targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some sourceStart := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Concrete.Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            sourceEncloses targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble sourceStart targetArity := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
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
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Concrete.Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
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
    {Host : Type} [DecidableEq Host]
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (certificate : Concrete.Splice.AttachmentAliasMaterialization.Certificate pattern
      attachment spine)
    {sourcePath targetPath : List Nat}
    {sourceBody : Region  pattern.val.exposedWires.length []}
    {targetBody : Region  certificate.result.val.exposedWires.length []}
    {sourceRoute : Concrete.Splice.RegionRoute pattern.val.diagram pattern.val.diagram.root
      spine.bodyContainer sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute certificate.result.val.diagram
      certificate.result.val.diagram.root spine.bodyContainer targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Concrete.Splice.OpenRootCompilerState pattern sourceBody}
    {targetState : Concrete.Splice.OpenRootCompilerState certificate.result targetBody}
    (sourceTrace : Concrete.Splice.OpenCompilerTrace pattern sourceRoute sourceWitness
      sourceState)
    (targetTrace : Concrete.Splice.OpenCompilerTrace certificate.result targetRoute
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
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Concrete.Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Concrete.Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed) targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble pattern.val.diagram.root targetArity := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
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
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Concrete.Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Concrete.Splice.Input.RegionRoute.encloses sourceTail
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
          simpa [Concrete.Splice.OpenCompilerTrace.leaf,
            Concrete.Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Concrete.Splice.Region.ContextPath.CompilerLeaf.underCut] using hleaf
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
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Concrete.Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Concrete.Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed) targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .cut pattern.val.diagram.root := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
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
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetParent
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (Concrete.Splice.Input.RegionRoute.encloses targetTail certificate.wellFormed)
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            (Concrete.Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed) targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble pattern.val.diagram.root targetArity := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
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
          simpa [Concrete.Splice.OpenCompilerTrace.leaf,
            Concrete.Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Concrete.Splice.Region.ContextPath.CompilerLeaf.underBubble] using hleaf
-/
  | @bubble sourceStart sourceChild _ sourceRest sourceParent sourcePosition
      sourcePositionEq sourceTail sourceOuter sourceLocal sourceArity sourceRels
      sourceItems sourceFocus sourceChildBody sourceAt sourceIsBubble
      sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
      sourceChildState sourceChildKind sourceInherited sourceBinders sourceFuel
      sourceTailTrace ih =>
      cases targetTrace with
      | here targetState =>
          have hcycle := Concrete.Splice.Input.RegionRoute.encloses sourceTail
            pattern.property.diagram_well_formed
          rw [sourceEndEq] at hcycle
          have sourceStartBody : sourceStart = spine.bodyContainer :=
            startEq.symm.trans targetEndEq
          have parentBody :
              (pattern.val.diagram.regions sourceChild).parent? =
                some spine.bodyContainer := by
            simpa [sourceStartBody] using sourceParent
          exact False.elim
            (Concrete.Elaboration.checked_direct_child_not_encloses_parent
              pattern.property.diagram_well_formed parentBody hcycle)
      | @cut _ targetChild _ _ targetParent _ _ targetTail _ _ _ _ _ _ _ _ _
          targetState targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have targetParentSource :
              (pattern.val.diagram.regions targetChild).parent? =
                some sourceStart := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Concrete.Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            sourceEncloses targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .cut sourceStart := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
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
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using (startEq ▸ targetParent)
          have targetEnclosesSource : pattern.val.diagram.Encloses targetChild
              spine.bodyContainer :=
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
              pattern.val attachment spine.bodyContainer targetChild
                spine.bodyContainer).mp
              (by
                have h := Concrete.Splice.Input.RegionRoute.encloses targetTail
                  targetWellFormed
                rw [targetEndEq] at h
                exact h)
          have sourceEncloses : pattern.val.diagram.Encloses sourceChild
              spine.bodyContainer := by
            have h := Concrete.Splice.Input.RegionRoute.encloses sourceTail
              pattern.property.diagram_well_formed
            rw [sourceEndEq] at h
            exact h
          have hchild := Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
            pattern.property.diagram_well_formed sourceParent targetParentSource
            sourceEncloses targetEnclosesSource
          subst targetChild
          have targetChildKindSource : pattern.val.diagram.regions sourceChild =
              .bubble sourceStart targetArity := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
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

private theorem materializedRoute_firstChild_eq
    {Host : Type} [DecidableEq Host]
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer).WellFormed )
    {sourceStart sourceChild sourceEnd : Fin pattern.val.diagram.regionCount}
    {targetStart targetChild targetEnd : Fin
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer).regionCount}
    {sourceRest targetRest : List Nat}
    (sourceParent : (pattern.val.diagram.regions sourceChild).parent? =
      some sourceStart)
    (targetParent :
      ((Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer).regions targetChild).parent? =
          some targetStart)
    (sourceTail : Concrete.Splice.RegionRoute pattern.val.diagram sourceChild sourceEnd
      sourceRest)
    (targetTail : Concrete.Splice.RegionRoute
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer) targetChild targetEnd targetRest)
    (sourceEndEq : sourceEnd = spine.bodyContainer)
    (targetEndEq : targetEnd = spine.bodyContainer)
    (startEq : targetStart = sourceStart) :
    targetChild = sourceChild := by
  have targetParentSource :
      (pattern.val.diagram.regions targetChild).parent? = some sourceStart := by
    simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
      using (startEq ▸ targetParent)
  have sourceEncloses : pattern.val.diagram.Encloses sourceChild
      spine.bodyContainer := by
    have h := Concrete.Splice.Input.RegionRoute.encloses sourceTail
      pattern.property.diagram_well_formed
    rw [sourceEndEq] at h
    exact h
  have targetEncloses : pattern.val.diagram.Encloses targetChild
      spine.bodyContainer :=
    (Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_encloses_iff
      pattern.val attachment spine.bodyContainer targetChild
        spine.bodyContainer).mp (by
      have h := Concrete.Splice.Input.RegionRoute.encloses targetTail targetWellFormed
      rw [targetEndEq] at h
      exact h)
  exact (Concrete.Splice.Input.RegionRoute.directChild_eq_of_encloses
    pattern.property.diagram_well_formed sourceParent targetParentSource
    sourceEncloses targetEncloses).symm

private theorem materializedOpenCompilerTrace_terminalLexical_aligned
    {Host : Type} [DecidableEq Host]
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (certificate : Concrete.Splice.AttachmentAliasMaterialization.Certificate pattern
      attachment spine)
    {sourceEnd : Fin pattern.val.diagram.regionCount}
    {targetEnd : Fin certificate.result.val.diagram.regionCount}
    {sourcePath targetPath : List Nat}
    {sourceBody : Region  pattern.val.exposedWires.length []}
    {targetBody : Region  certificate.result.val.exposedWires.length []}
    {sourceRoute : Concrete.Splice.RegionRoute pattern.val.diagram pattern.val.diagram.root
      sourceEnd sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute certificate.result.val.diagram
      certificate.result.val.diagram.root targetEnd targetPath}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    {sourceState : Concrete.Splice.OpenRootCompilerState pattern sourceBody}
    {targetState : Concrete.Splice.OpenRootCompilerState certificate.result targetBody}
    (sourceTrace : Concrete.Splice.OpenCompilerTrace pattern sourceRoute sourceWitness
      sourceState)
    (targetTrace : Concrete.Splice.OpenCompilerTrace certificate.result targetRoute
      targetWitness targetState)
    (sourceEndEq : sourceEnd = spine.bodyContainer)
    (targetEndEq : targetEnd = spine.bodyContainer)
    (sourceProper : spine.bodyContainer ≠ pattern.val.diagram.root)
    (targetProper : spine.bodyContainer ≠ certificate.result.val.diagram.root) :
    ∃ hrels : sourceWitness.toFocus.holeRels =
        targetWitness.toFocus.holeRels,
      HEq (sourceTrace.leaf.nestedOfNe (sourceEndEq ▸ sourceProper)).binders
        (targetTrace.leaf.nestedOfNe (targetEndEq ▸ targetProper)).binders := by
  cases sourceTrace with
  | here sourceState => exact False.elim (sourceProper sourceEndEq.symm)
  | @cut sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceItems sourceFocus sourceChildBody sourceAt
      sourceIsCut sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (targetProper targetEndEq.symm)
      | @bubble targetChild _ _ targetParent targetPosition targetPositionEq
          targetTail targetLocal targetArity targetItems targetFocus
          targetChildBody targetAt targetIsBubble targetNested targetState
          targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have hchild := materializedRoute_firstChild_eq pattern attachment spine
            certificate.wellFormed.diagram_well_formed sourceParent targetParent
              sourceTail targetTail
              sourceEndEq targetEndEq rfl
          subst targetChild
          have targetKind : pattern.val.diagram.regions sourceChild =
              .bubble pattern.val.diagram.root targetArity := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetChildKind
          exact False.elim (by
            have : CRegion.cut pattern.val.diagram.root =
                CRegion.bubble pattern.val.diagram.root targetArity :=
              sourceChildKind.symm.trans targetKind
            contradiction)
      | @cut targetChild _ _ targetParent targetPosition targetPositionEq
          targetTail targetLocal targetItems targetFocus targetChildBody targetAt
          targetIsCut targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          have hchild := materializedRoute_firstChild_eq pattern attachment spine
            certificate.wellFormed.diagram_well_formed sourceParent targetParent
              sourceTail targetTail
              sourceEndEq targetEndEq rfl
          subst targetChild
          have hchildBinders : HEq sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact HEq.rfl
          obtain ⟨hrels, hleaf⟩ := materializedCompilerTrace_terminalLexical
            pattern attachment spine certificate.wellFormed.diagram_well_formed
              sourceTailTrace
              targetTailTrace sourceEndEq targetEndEq rfl hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [Concrete.Splice.OpenCompilerTrace.leaf,
            Concrete.Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Concrete.Splice.Region.ContextPath.CompilerLeaf.underCut] using hleaf
  | @bubble sourceChild _ _ sourceParent sourcePosition sourcePositionEq
      sourceTail sourceLocal sourceArity sourceItems sourceFocus sourceChildBody
      sourceAt sourceIsBubble sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace =>
      cases targetTrace with
      | here targetState => exact False.elim (targetProper targetEndEq.symm)
      | @cut targetChild _ _ targetParent targetPosition targetPositionEq
          targetTail targetLocal targetItems targetFocus targetChildBody targetAt
          targetIsCut targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          have hchild := materializedRoute_firstChild_eq pattern attachment spine
            certificate.wellFormed.diagram_well_formed sourceParent targetParent
              sourceTail targetTail
              sourceEndEq targetEndEq rfl
          subst targetChild
          have targetKind : pattern.val.diagram.regions sourceChild =
              .cut pattern.val.diagram.root := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetChildKind
          exact False.elim (by
            have : CRegion.bubble pattern.val.diagram.root sourceArity =
                CRegion.cut pattern.val.diagram.root :=
              sourceChildKind.symm.trans targetKind
            contradiction)
      | @bubble targetChild _ _ targetParent targetPosition targetPositionEq
          targetTail targetLocal targetArity targetItems targetFocus
          targetChildBody targetAt targetIsBubble targetNested targetState
          targetLocalCanonical targetItemsCanonical targetChildState
          targetChildKind targetInherited targetBinders targetFuel
          targetTailTrace =>
          have hchild := materializedRoute_firstChild_eq pattern attachment spine
            certificate.wellFormed.diagram_well_formed sourceParent targetParent
              sourceTail targetTail
              sourceEndEq targetEndEq rfl
          subst targetChild
          have targetKind : pattern.val.diagram.regions sourceChild =
              .bubble pattern.val.diagram.root targetArity := by
            simpa only [Concrete.Splice.AttachmentAliasMaterialization.materialized_regions]
              using targetChildKind
          have harity : targetArity = sourceArity :=
            (CRegion.bubble.inj (targetKind.symm.trans sourceChildKind)).2
          subst targetArity
          have hchildBinders : HEq sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact HEq.rfl
          obtain ⟨hrels, hleaf⟩ := materializedCompilerTrace_terminalLexical
            pattern attachment spine certificate.wellFormed.diagram_well_formed
              sourceTailTrace
              targetTailTrace sourceEndEq targetEndEq rfl hchildBinders
          refine ⟨hrels, ?_⟩
          simpa [Concrete.Splice.OpenCompilerTrace.leaf,
            Concrete.Splice.Region.ContextPath.OpenCompilerLeaf.nestedOfNe,
            Concrete.Splice.Region.ContextPath.CompilerLeaf.underBubble] using hleaf

private theorem terminalView_producer_holeRels
    {pattern : Concrete.CheckedOpen }
    {spine : BinderSpine pattern.val.diagram}
    (view : Concrete.Splice.Input.PatternTerminalCompilerView pattern spine) :
    view.producer.intrinsicPath.toFocus.holeRels =
      view.witness.toFocus.holeRels := by
  rcases view with ⟨path, witness, leaf, proper, producer, pathEq,
    witnessEq, leafEq⟩
  dsimp
  subst path
  exact congrArg (fun current => current.toFocus.holeRels)
    (eq_of_heq witnessEq)

private theorem terminalView_producer_leaf_binders
    {pattern : Concrete.CheckedOpen }
    {spine : BinderSpine pattern.val.diagram}
    (view : Concrete.Splice.Input.PatternTerminalCompilerView pattern spine) :
    HEq (view.producer.compilerLeaf.nestedOfNe view.proper).binders
      view.leaf.binders := by
  rcases view with ⟨path, witness, leaf, proper, producer, pathEq,
    witnessEq, leafEq⟩
  dsimp
  subst path
  have witnessEq' := eq_of_heq witnessEq
  subst witness
  exact heq_of_eq (congrArg
    (fun current : Concrete.Splice.Region.ContextPath.CompilerLeaf pattern.val.diagram
      spine.bodyContainer producer.intrinsicPath => current.binders)
    (eq_of_heq leafEq))

private def castRelEnv {source target : RelCtx}
    (equality : source = target) (environment : RelEnv D source) :
    RelEnv D target := by
  subst target
  exact environment

private theorem relEnv_eq_of_lookup
    {rels : RelCtx} {left right : RelEnv D rels}
    (equal : ∀ {arity : Nat} (relation : RelVar rels arity),
      left.lookup relation = right.lookup relation) :
    left = right := by
  induction rels with
  | nil => cases left; cases right; rfl
  | cons head tail induction =>
      rcases left with ⟨leftHead, leftTail⟩
      rcases right with ⟨rightHead, rightTail⟩
      have headEq : leftHead = rightHead := by
        simpa [RelEnv.lookup] using
          equal (⟨0, rfl⟩ : RelVar (head :: tail) head)
      have tailEq : leftTail = rightTail := by
        apply induction
        intro arity relation
        simpa [RelEnv.lookup] using
          equal (⟨relation.index.succ, relation.hasArity⟩ :
            RelVar (head :: tail) arity)
      rw [headEq, tailEq]

private theorem pullback_identityRelationRenaming
    (rels : RelCtx) (environment : RelEnv D rels) :
    RelEnv.pullback (Concrete.Elaboration.identityRelationRenaming rels)
      environment = environment := by
  apply relEnv_eq_of_lookup
  intro arity relation
  simpa [Concrete.Elaboration.identityRelationRenaming] using
    (RelEnv.pullback_agrees
      (Concrete.Elaboration.identityRelationRenaming rels) environment arity
        relation)

private theorem identityBinderWitness_pullback_cast
    {source target : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : Concrete.Elaboration.BinderContext source sourceRels}
    {targetBinders : Concrete.Elaboration.BinderContext target targetRels}
    (witness : Concrete.Elaboration.IdentityBinderWitness source target
      sourceBinders targetBinders)
    (environment : RelEnv D sourceRels) :
    RelEnv.pullback
        (Concrete.Elaboration.IdentityBinderWitness.relationMap witness)
        (castRelEnv witness.relationContexts_eq environment) = environment := by
  rcases witness with ⟨relationEq, bindersEq⟩
  subst targetRels
  exact pullback_identityRelationRenaming sourceRels environment

private theorem relationMap_eq_relationRenamingOfEq
    {source target : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : Concrete.Elaboration.BinderContext source sourceRels}
    {targetBinders : Concrete.Elaboration.BinderContext target targetRels}
    (witness : Concrete.Elaboration.IdentityBinderWitness source target
      sourceBinders targetBinders) :
    (fun {arity} => witness.relationMap (arity := arity)) =
      (fun {arity} => Concrete.Splice.Input.relationRenamingOfEq
        witness.relationContexts_eq (arity := arity)) := by
  rcases witness with ⟨hrels, hbinders⟩
  subst targetRels
  rfl

private theorem pullback_relationRenamingOfEq_cast
    {source target : RelCtx} (equality : source = target)
    (environment : RelEnv D source) :
    RelEnv.pullback (Concrete.Splice.Input.relationRenamingOfEq equality)
      (castRelEnv equality environment) = environment := by
  subst target
  exact pullback_identityRelationRenaming source environment

private theorem materialized_binder_owner_eq
    {Host : Type} [DecidableEq Host]
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    {sourceRels targetRels : RelCtx}
    (hrels : sourceRels = targetRels)
    (sourceBinders : Concrete.Elaboration.BinderContext pattern.val.diagram
      sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer) targetRels)
    (hbinders : HEq sourceBinders targetBinders)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      pattern.val.diagram sourceBinders spine.bodyContainer)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram pattern.val
        attachment spine.bodyContainer) targetBinders spine.bodyContainer)
    {arity : Nat} (relation : RelVar sourceRels arity) :
    targetEnumeration.binder
        (Concrete.Splice.Input.relationRenamingOfEq hrels relation).index =
      sourceEnumeration.binder relation.index := by
  subst targetRels
  have hbindersEq : targetBinders = sourceBinders :=
    (eq_of_heq hbinders).symm
  rcases relation with ⟨index, hasArity⟩
  subst arity
  let indexed : RelVar sourceRels (sourceRels.get index) := ⟨index, rfl⟩
  apply targetEnumeration.lookup_owner indexed
  rw [hbindersEq]
  exact sourceEnumeration.lookup index

private theorem fixed_relation_value_eq
    (spine : BinderSpine diagram)
    {D : Type}
    (values : ∀ index, Relation D (spine.arity index))
    {sourceProxy targetProxy : Fin spine.proxyCount}
    (proxyEq : sourceProxy = targetProxy)
    {arity : Nat}
    (sourceArityEq : spine.arity sourceProxy = arity)
    (targetArityEq : spine.arity targetProxy = arity) :
    sourceArityEq ▸ values sourceProxy =
      targetArityEq ▸ values targetProxy := by
  subst targetProxy
  rfl

private theorem materialized_chosenProxy_eq
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (attachment : Fin comprehension.val.boundary.length →
      Fin state.diagram.val.wireCount)
    (certificate : Concrete.Splice.AttachmentAliasMaterialization.Certificate
      comprehension attachment payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (terminalRels :
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels =
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput certificate.result attachments binders
          (materializedInstantiationPayload payload attachment certificate)
          state site arguments) hnonempty).witness.toFocus.holeRels)
    (terminalBinders : HEq
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).leaf.binders
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput certificate.result attachments binders
          (materializedInstantiationPayload payload attachment certificate)
          state site arguments) hnonempty).leaf.binders)
    {arity : Nat}
    (sourceRelation : RelVar
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels arity)
    (targetRelation : RelVar
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput certificate.result attachments binders
          (materializedInstantiationPayload payload attachment certificate)
          state site arguments) hnonempty).witness.toFocus.holeRels arity)
    (relationEq : Concrete.Splice.Input.relationRenamingOfEq terminalRels
      sourceRelation = targetRelation) :
    Classical.choose
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.terminalBodyBinder_is_proxy
          (Concrete.Splice.Input.compiledSpliceTerminalView
            (instantiateSpliceInput comprehension attachments binders payload
              state site arguments) hnonempty).witness
          (Concrete.Splice.Input.compiledSpliceTerminalView
            (instantiateSpliceInput comprehension attachments binders payload
              state site arguments) hnonempty).leaf hnonempty
          sourceRelation.index) =
      Classical.choose
        ((instantiateSpliceInput certificate.result attachments binders
          (materializedInstantiationPayload payload attachment certificate)
          state site arguments).plugLayout.terminalBodyBinder_is_proxy
          (Concrete.Splice.Input.compiledSpliceTerminalView
            (instantiateSpliceInput certificate.result attachments binders
              (materializedInstantiationPayload payload attachment certificate)
              state site arguments) hnonempty).witness
          (Concrete.Splice.Input.compiledSpliceTerminalView
            (instantiateSpliceInput certificate.result attachments binders
              (materializedInstantiationPayload payload attachment certificate)
              state site arguments) hnonempty).leaf hnonempty
          targetRelation.index) := by
  let sourceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let targetPayload := materializedInstantiationPayload payload attachment
    certificate
  let targetInput := instantiateSpliceInput certificate.result attachments
    binders targetPayload state site arguments
  let sourcePattern := Concrete.Splice.Input.compiledSpliceTerminalView sourceInput
    hnonempty
  let targetPattern := Concrete.Splice.Input.compiledSpliceTerminalView targetInput
    hnonempty
  let sourceProxy := Classical.choose
    (sourceInput.plugLayout.terminalBodyBinder_is_proxy sourcePattern.witness
      sourcePattern.leaf hnonempty sourceRelation.index)
  let targetProxy := Classical.choose
    (targetInput.plugLayout.terminalBodyBinder_is_proxy targetPattern.witness
      targetPattern.leaf hnonempty targetRelation.index)
  change sourceProxy = targetProxy
  have ownerEq : targetPattern.leaf.binderEnumeration.binder
      (Concrete.Splice.Input.relationRenamingOfEq terminalRels sourceRelation).index =
      sourcePattern.leaf.binderEnumeration.binder sourceRelation.index :=
    materialized_binder_owner_eq comprehension attachment payload.binderSpine
      terminalRels sourcePattern.leaf.binders targetPattern.leaf.binders
      terminalBinders sourcePattern.leaf.binderEnumeration
      targetPattern.leaf.binderEnumeration sourceRelation
  have targetOwnerEq : targetPattern.leaf.binderEnumeration.binder
      targetRelation.index =
      sourcePattern.leaf.binderEnumeration.binder sourceRelation.index := by
    rw [← relationEq]
    exact ownerEq
  have sourceProxySpec := Classical.choose_spec
    (sourceInput.plugLayout.terminalBodyBinder_is_proxy sourcePattern.witness
      sourcePattern.leaf hnonempty sourceRelation.index)
  have targetProxySpec := Classical.choose_spec
    (targetInput.plugLayout.terminalBodyBinder_is_proxy targetPattern.witness
      targetPattern.leaf hnonempty targetRelation.index)
  apply payload.binderSpine.proxy_injective
  exact sourceProxySpec.symm.trans (targetOwnerEq.symm.trans (by
    simpa [targetInput, targetPayload, materializedInstantiationPayload,
      Concrete.Splice.AttachmentAliasMaterialization.Certificate.spine,
      Concrete.Splice.AttachmentAliasMaterialization.binderSpine] using targetProxySpec))

private theorem terminalRelationsMatch_materialized_iff
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (attachment : Fin comprehension.val.boundary.length →
      Fin state.diagram.val.wireCount)
    (certificate : Concrete.Splice.AttachmentAliasMaterialization.Certificate
      comprehension attachment payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    {model : Model}
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (terminalRels :
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).witness.toFocus.holeRels =
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput certificate.result attachments binders
          (materializedInstantiationPayload payload attachment certificate)
          state site arguments) hnonempty).witness.toFocus.holeRels)
    (terminalBinders : HEq
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments) hnonempty).leaf.binders
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput certificate.result attachments binders
          (materializedInstantiationPayload payload attachment certificate)
          state site arguments) hnonempty).leaf.binders)
    (targetRelEnv : RelEnv model.Carrier
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (instantiateSpliceInput certificate.result attachments binders
          (materializedInstantiationPayload payload attachment certificate)
          state site arguments) hnonempty).witness.toFocus.holeRels) :
    let relationMap : RelationRenaming
        (Concrete.Splice.Input.compiledSpliceTerminalView
          (instantiateSpliceInput comprehension attachments binders payload state
            site arguments) hnonempty).witness.toFocus.holeRels
        (Concrete.Splice.Input.compiledSpliceTerminalView
          (instantiateSpliceInput certificate.result attachments binders
            (materializedInstantiationPayload payload attachment certificate)
            state site arguments) hnonempty).witness.toFocus.holeRels :=
      Concrete.Splice.Input.relationRenamingOfEq terminalRels
    TerminalRelationsMatch payload state site arguments hnonempty values
        (RelEnv.pullback relationMap targetRelEnv) ↔
      TerminalRelationsMatch
        (materializedInstantiationPayload payload attachment certificate)
        state site arguments hnonempty values targetRelEnv := by
  dsimp only
  let sourceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let targetPayload := materializedInstantiationPayload payload attachment
    certificate
  let targetInput := instantiateSpliceInput certificate.result attachments
    binders targetPayload state site arguments
  let sourcePattern := Concrete.Splice.Input.compiledSpliceTerminalView sourceInput
    hnonempty
  let targetPattern := Concrete.Splice.Input.compiledSpliceTerminalView targetInput
    hnonempty
  let relationMap : RelationRenaming sourcePattern.witness.toFocus.holeRels
      targetPattern.witness.toFocus.holeRels :=
    Concrete.Splice.Input.relationRenamingOfEq terminalRels
  change TerminalRelationsMatch payload state site arguments hnonempty values
      (RelEnv.pullback relationMap targetRelEnv) ↔
    TerminalRelationsMatch targetPayload state site arguments hnonempty values
      targetRelEnv
  constructor
  · intro sourceMatches arity targetRelation
    let sourceRelation : RelVar sourcePattern.witness.toFocus.holeRels arity :=
      Concrete.Splice.Input.relationRenamingOfEq terminalRels.symm targetRelation
    have roundtrip : relationMap sourceRelation = targetRelation :=
      Concrete.Splice.Input.relationRenamingOfEq_apply_symm terminalRels targetRelation
    have sourceValue := sourceMatches sourceRelation
    rw [RelEnv.pullback_agrees relationMap targetRelEnv arity sourceRelation]
      at sourceValue
    change targetRelEnv.lookup (relationMap sourceRelation) = _ at sourceValue
    rw [roundtrip] at sourceValue
    let sourceProxy := Classical.choose
      (sourceInput.plugLayout.terminalBodyBinder_is_proxy sourcePattern.witness
        sourcePattern.leaf hnonempty sourceRelation.index)
    let targetProxy := Classical.choose
      (targetInput.plugLayout.terminalBodyBinder_is_proxy targetPattern.witness
        targetPattern.leaf hnonempty targetRelation.index)
    have proxyEqRaw := materialized_chosenProxy_eq payload state site arguments
      attachment certificate hnonempty terminalRels terminalBinders
      sourceRelation targetRelation roundtrip
    have proxyEq : sourceProxy = targetProxy := by
      simpa [sourceProxy, targetProxy, sourceRelation, relationMap, roundtrip]
        using proxyEqRaw
    let sourceArityEq := terminalRelation_proxy_arity payload state site
      arguments hnonempty sourceRelation
    let targetArityEq := terminalRelation_proxy_arity targetPayload state site
      arguments hnonempty targetRelation
    change targetRelEnv.lookup targetRelation =
      sourceArityEq ▸ values sourceProxy at sourceValue
    change targetRelEnv.lookup targetRelation =
      targetArityEq ▸ values targetProxy
    exact sourceValue.trans (fixed_relation_value_eq payload.binderSpine values
      proxyEq sourceArityEq targetArityEq)
  · intro targetMatches arity sourceRelation
    let targetRelation : RelVar targetPattern.witness.toFocus.holeRels arity :=
      relationMap sourceRelation
    have targetValue := targetMatches targetRelation
    let sourceProxy := Classical.choose
      (sourceInput.plugLayout.terminalBodyBinder_is_proxy sourcePattern.witness
        sourcePattern.leaf hnonempty sourceRelation.index)
    let targetProxy := Classical.choose
      (targetInput.plugLayout.terminalBodyBinder_is_proxy targetPattern.witness
        targetPattern.leaf hnonempty targetRelation.index)
    have proxyEqRaw := materialized_chosenProxy_eq payload state site arguments
      attachment certificate hnonempty terminalRels terminalBinders
      sourceRelation targetRelation rfl
    have proxyEq : sourceProxy = targetProxy := by
      simpa [sourceProxy, targetProxy, targetRelation, relationMap] using proxyEqRaw
    rw [RelEnv.pullback_agrees relationMap targetRelEnv arity sourceRelation]
    let sourceArityEq := terminalRelation_proxy_arity payload state site
      arguments hnonempty sourceRelation
    let targetArityEq := terminalRelation_proxy_arity targetPayload state site
      arguments hnonempty targetRelation
    change targetRelEnv.lookup targetRelation =
      targetArityEq ▸ values targetProxy at targetValue
    change targetRelEnv.lookup targetRelation =
      sourceArityEq ▸ values sourceProxy
    exact targetValue.trans (fixed_relation_value_eq payload.binderSpine values
      proxyEq sourceArityEq targetArityEq).symm

/-- Attachment-alias materialization preserves the nonzero-spine terminal
relation for the exact fixed proxy family.  The ordered boundary remains
positional: repeated source aliases may materialize as distinct exposed wires,
and the inserted identity block must recover precisely the source alias
equalities in the backward direction.

This is deliberately stronger than whole-open denotation preservation, whose
existential relation environment cannot establish preservation for an
arbitrary caller-supplied proxy family. -/
theorem terminalRelationOfParameterValues_materialized_iff
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Concrete.Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (relationArguments : Fin payload.arity → model.Carrier) :
    terminalRelationOfParameterValues
        (materializedInstantiationPayload payload
          (instantiationAttachment comprehension attachments binders payload state
            arguments)
          certificate)
        state site arguments hnonempty model  parameterValues values
        relationArguments ↔
      terminalRelationOfParameterValues payload state site arguments hnonempty
        model  parameterValues values relationArguments := by
  let attachment := instantiationAttachment comprehension attachments binders
    payload state arguments
  let sourceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let targetPayload := materializedInstantiationPayload payload attachment
    certificate
  let targetInput := instantiateSpliceInput certificate.result attachments binders
    targetPayload state site arguments
  let sourcePattern := Concrete.Splice.Input.compiledSpliceTerminalView sourceInput hnonempty
  let targetPattern := Concrete.Splice.Input.compiledSpliceTerminalView targetInput hnonempty
  let collapse :
      Concrete.Splice.AttachmentAliasMaterialization.Semantic.ContextCollapse comprehension
        attachment payload.binderSpine targetPattern.leaf.inheritedWires
        sourcePattern.leaf.inheritedWires := {
    indexMap := fun index => Classical.choose
      (Concrete.Elaboration.WireContext.lookup?_complete (by
        have targetInherited : targetPattern.leaf.inheritedWires.get index ∈
            targetPattern.leaf.inheritedWires := List.get_mem _ index
        have targetExposed : targetPattern.leaf.inheritedWires.get index ∈
            targetInput.pattern.val.exposedWires :=
          (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            targetPattern.witness targetPattern.leaf hnonempty _).1
            targetInherited
        have targetBoundary : targetPattern.leaf.inheritedWires.get index ∈
            targetInput.pattern.val.boundary :=
          (Concrete.OpenDiagram.mem_exposedWires _ _).1 targetExposed
        have sourceBoundary :
            Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire comprehension.val
                attachment (targetPattern.leaf.inheritedWires.get index) ∈
              comprehension.val.boundary :=
          Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire_mem_boundary_of_mem_rawBoundary
            comprehension.val attachment payload.binderSpine.bodyContainer _
            targetBoundary
        have sourceExposed :
            Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire comprehension.val
                attachment (targetPattern.leaf.inheritedWires.get index) ∈
              comprehension.val.exposedWires :=
          (Concrete.OpenDiagram.mem_exposedWires _ _).2 sourceBoundary
        exact (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          sourcePattern.witness sourcePattern.leaf hnonempty _).2 sourceExposed))
    get := by
      intro index
      exact Concrete.Elaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (Concrete.Elaboration.WireContext.lookup?_complete (by
            have targetInherited : targetPattern.leaf.inheritedWires.get index ∈
                targetPattern.leaf.inheritedWires := List.get_mem _ index
            have targetExposed : targetPattern.leaf.inheritedWires.get index ∈
                targetInput.pattern.val.exposedWires :=
              (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
                targetPattern.witness targetPattern.leaf hnonempty _).1
                targetInherited
            have targetBoundary : targetPattern.leaf.inheritedWires.get index ∈
                targetInput.pattern.val.boundary :=
              (Concrete.OpenDiagram.mem_exposedWires _ _).1 targetExposed
            have sourceBoundary :
                Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire
                    comprehension.val attachment
                    (targetPattern.leaf.inheritedWires.get index) ∈
                  comprehension.val.boundary :=
              Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire_mem_boundary_of_mem_rawBoundary
                comprehension.val attachment payload.binderSpine.bodyContainer _
                targetBoundary
            exact (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
              sourcePattern.witness sourcePattern.leaf hnonempty _).2
                ((Concrete.OpenDiagram.mem_exposedWires _ _).2 sourceBoundary))))
    oldIndex := fun index => Classical.choose
      (Concrete.Elaboration.WireContext.lookup?_complete (by
        have sourceInherited : sourcePattern.leaf.inheritedWires.get index ∈
            sourcePattern.leaf.inheritedWires := List.get_mem _ index
        have sourceExposed : sourcePattern.leaf.inheritedWires.get index ∈
            comprehension.val.exposedWires :=
          (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            sourcePattern.witness sourcePattern.leaf hnonempty _).1
            sourceInherited
        have sourceBoundary : sourcePattern.leaf.inheritedWires.get index ∈
            comprehension.val.boundary :=
          (Concrete.OpenDiagram.mem_exposedWires _ _).1 sourceExposed
        have targetBoundary :=
          Concrete.Splice.AttachmentAliasMaterialization.liftOldWire_mem_raw_boundary
            comprehension.val attachment payload.binderSpine.bodyContainer
            (sourcePattern.leaf.inheritedWires.get index) sourceBoundary
        have targetExposed :
            Concrete.Splice.AttachmentAliasMaterialization.liftOldWire comprehension.val
                attachment (sourcePattern.leaf.inheritedWires.get index) ∈
              targetInput.pattern.val.exposedWires :=
          (Concrete.OpenDiagram.mem_exposedWires _ _).2 targetBoundary
        exact (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty _).2 targetExposed))
    old_get := by
      intro index
      exact Concrete.Elaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (Concrete.Elaboration.WireContext.lookup?_complete (by
            have sourceInherited : sourcePattern.leaf.inheritedWires.get index ∈
                sourcePattern.leaf.inheritedWires := List.get_mem _ index
            have sourceExposed : sourcePattern.leaf.inheritedWires.get index ∈
                comprehension.val.exposedWires :=
              (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
                sourcePattern.witness sourcePattern.leaf hnonempty _).1
                sourceInherited
            have sourceBoundary : sourcePattern.leaf.inheritedWires.get index ∈
                comprehension.val.boundary :=
              (Concrete.OpenDiagram.mem_exposedWires _ _).1 sourceExposed
            have targetBoundary :=
              Concrete.Splice.AttachmentAliasMaterialization.liftOldWire_mem_raw_boundary
                comprehension.val attachment payload.binderSpine.bodyContainer
                (sourcePattern.leaf.inheritedWires.get index) sourceBoundary
            exact (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
              targetPattern.witness targetPattern.leaf hnonempty _).2
                ((Concrete.OpenDiagram.mem_exposedWires _ _).2 targetBoundary))))
  }
  obtain ⟨producerRels, producerBinders⟩ :=
    materializedOpenCompilerTrace_terminalLexical_aligned comprehension attachment
      payload.binderSpine certificate sourcePattern.producer.result.trace
        targetPattern.producer.result.trace rfl rfl sourcePattern.proper
          targetPattern.proper
  have terminalRels : sourcePattern.witness.toFocus.holeRels =
      targetPattern.witness.toFocus.holeRels :=
    (terminalView_producer_holeRels sourcePattern).symm.trans
      (producerRels.trans (terminalView_producer_holeRels targetPattern))
  have terminalBinders : HEq sourcePattern.leaf.binders
      targetPattern.leaf.binders :=
    (terminalView_producer_leaf_binders sourcePattern).symm.trans
      (producerBinders.trans
        (terminalView_producer_leaf_binders targetPattern))
  let forwardSemantic :=
    Concrete.Splice.AttachmentAliasMaterialization.Semantic.concreteSimulation
      .forward comprehension attachment payload.binderSpine payload.terminalBody
        certificate.wellFormed.diagram_well_formed model
  let forwardBinderWitness : forwardSemantic.BinderWitness
      sourcePattern.leaf.binders targetPattern.leaf.binders :=
    ⟨terminalRels, terminalBinders⟩
  have sourceItemsComputation :
      Concrete.Elaboration.compileOccurrencesWith?
        comprehension.val.diagram
        (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
          sourcePattern.leaf.fuel)
        (sourcePattern.leaf.inheritedWires.extend
          payload.binderSpine.bodyContainer)
        sourcePattern.leaf.binders
        (Concrete.Elaboration.localOccurrences comprehension.val.diagram
          payload.binderSpine.bodyContainer) = some sourcePattern.leaf.items := by
    simpa [sourceInput, sourcePattern] using sourcePattern.leaf.itemsComputation
  have targetItemsComputation :
      Concrete.Elaboration.compileOccurrencesWith?
        (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
          comprehension.val attachment payload.binderSpine.bodyContainer)
        (Concrete.Elaboration.compileRegion?
          (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
            comprehension.val attachment payload.binderSpine.bodyContainer)
          targetPattern.leaf.fuel)
        (targetPattern.leaf.inheritedWires.extend payload.binderSpine.bodyContainer)
        targetPattern.leaf.binders
        (Concrete.Elaboration.localOccurrences
          (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
            comprehension.val attachment payload.binderSpine.bodyContainer)
          payload.binderSpine.bodyContainer) = some targetPattern.leaf.items := by
    simpa [targetInput, targetPayload, targetPattern,
      materializedInstantiationPayload,
      Concrete.Splice.AttachmentAliasMaterialization.Certificate.result] using
        targetPattern.leaf.itemsComputation
  have forwardSimulation := forwardSemantic.compileRegion_denote
    .forward (sourcePattern.leaf.fuel + 1) (targetPattern.leaf.fuel + 1)
    payload.binderSpine.bodyContainer sourcePattern.leaf.inheritedWires
    targetPattern.leaf.inheritedWires collapse trivial sourcePattern.leaf.binders
    targetPattern.leaf.binders (by
      intro _
      rfl) forwardBinderWitness sourcePattern.leaf.bindersCover
    targetPattern.leaf.bindersCover sourcePattern.leaf.binderEnumeration
    targetPattern.leaf.binderEnumeration sourcePattern.leaf.wiresExact
    targetPattern.leaf.wiresExact
    (Concrete.Elaboration.finishRegion comprehension.val.diagram
      sourcePattern.leaf.inheritedWires payload.binderSpine.bodyContainer
      sourcePattern.leaf.items)
    (Concrete.Elaboration.finishRegion certificate.result.val.diagram
      targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
      targetPattern.leaf.items)
    (by
      simp only [Concrete.Elaboration.compileRegion?]
      exact congrArg
        (fun result => result.bind (fun items => some
          (Concrete.Elaboration.finishRegion comprehension.val.diagram
            sourcePattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            items))) sourceItemsComputation)
    (by
      simp only [forwardSemantic, Concrete.Elaboration.compileRegion?]
      change _ = some (Concrete.Elaboration.finishRegion
        (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
          comprehension.val attachment payload.binderSpine.bodyContainer)
        targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
        targetPattern.leaf.items)
      exact congrArg
        (fun result => result.bind (fun items => some
          (Concrete.Elaboration.finishRegion
            (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
              comprehension.val attachment payload.binderSpine.bodyContainer)
            targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            items))) targetItemsComputation)
  let backwardSemantic :=
    Concrete.Splice.AttachmentAliasMaterialization.Semantic.concreteSimulation
      .backward comprehension attachment payload.binderSpine payload.terminalBody
        certificate.wellFormed.diagram_well_formed model
  let backwardBinderWitness : backwardSemantic.BinderWitness
      sourcePattern.leaf.binders targetPattern.leaf.binders :=
    ⟨terminalRels, terminalBinders⟩
  have backwardSimulation := backwardSemantic.compileRegion_denote
    .backward (sourcePattern.leaf.fuel + 1) (targetPattern.leaf.fuel + 1)
    payload.binderSpine.bodyContainer sourcePattern.leaf.inheritedWires
    targetPattern.leaf.inheritedWires collapse trivial sourcePattern.leaf.binders
    targetPattern.leaf.binders (by
      intro _
      rfl) backwardBinderWitness sourcePattern.leaf.bindersCover
    targetPattern.leaf.bindersCover sourcePattern.leaf.binderEnumeration
    targetPattern.leaf.binderEnumeration sourcePattern.leaf.wiresExact
    targetPattern.leaf.wiresExact
    (Concrete.Elaboration.finishRegion comprehension.val.diagram
      sourcePattern.leaf.inheritedWires payload.binderSpine.bodyContainer
      sourcePattern.leaf.items)
    (Concrete.Elaboration.finishRegion certificate.result.val.diagram
      targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
      targetPattern.leaf.items)
    (by
      simp only [Concrete.Elaboration.compileRegion?]
      exact congrArg
        (fun result => result.bind (fun items => some
          (Concrete.Elaboration.finishRegion comprehension.val.diagram
            sourcePattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            items))) sourceItemsComputation)
    (by
      simp only [backwardSemantic, Concrete.Elaboration.compileRegion?]
      change _ = some (Concrete.Elaboration.finishRegion
        (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
          comprehension.val attachment payload.binderSpine.bodyContainer)
        targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
        targetPattern.leaf.items)
      exact congrArg
        (fun result => result.bind (fun items => some
          (Concrete.Elaboration.finishRegion
            (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
              comprehension.val attachment payload.binderSpine.bodyContainer)
            targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            items))) targetItemsComputation)
  simp only [terminalRelationOfParameterValues]
  constructor
  · rintro ⟨targetAssignment, targetArgsEq, targetRelEnv, targetMatch,
      targetDenotes⟩
    have targetDenotesSaved := targetDenotes
    let targetOuter := terminalInheritedEnvironment targetPayload state site
      arguments hnonempty targetAssignment
    change denoteRegion model  targetOuter targetRelEnv
      (Concrete.Elaboration.finishRegion certificate.result.val.diagram
        targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
        targetPattern.leaf.items) at targetDenotes
    unfold Concrete.Elaboration.finishRegion at targetDenotes
    simp only [ItemSeq.castWiresEq_eq_renameWires]
      at targetDenotes
    rcases targetDenotes with ⟨targetLocal, targetItemsDenote⟩
    have targetRawDenote :=
      (denoteItemSeq_renameWires model
        (Fin.cast (Concrete.Elaboration.WireContext.length_extend
          targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer))
        (extendWireEnv targetOuter targetLocal) targetRelEnv
        targetPattern.leaf.items).mp targetItemsDenote
    let targetContext := targetPattern.leaf.inheritedWires.extend
      payload.binderSpine.bodyContainer
    let sourceContext := sourcePattern.leaf.inheritedWires.extend
      payload.binderSpine.bodyContainer
    let extendedCollapse :=
      Concrete.Splice.AttachmentAliasMaterialization.Semantic.extendCollapse comprehension
        attachment payload.binderSpine payload.terminalBody
        targetPattern.leaf.inheritedWires sourcePattern.leaf.inheritedWires
        collapse payload.binderSpine.bodyContainer targetPattern.leaf.wiresExact
        sourcePattern.leaf.wiresExact
    have targetCompiled := targetItemsComputation
    rw [Concrete.Splice.AttachmentAliasMaterialization.Semantic.materialized_focused_localOccurrences]
      at targetCompiled
    have targetCompiled' :
        Concrete.Elaboration.compileOccurrencesWith?
          (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
            comprehension.val attachment payload.binderSpine.bodyContainer)
          (Concrete.Elaboration.compileRegion?
            (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
              comprehension.val attachment payload.binderSpine.bodyContainer)
            targetPattern.leaf.fuel)
          targetContext targetPattern.leaf.binders
          ((Concrete.Splice.AttachmentAliasMaterialization.Semantic.sourceNodeOccurrences
              comprehension.val payload.binderSpine.bodyContainer).map
              (Concrete.Splice.AttachmentAliasMaterialization.Semantic.liftOccurrence
                comprehension.val attachment) ++
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.aliasOccurrences
                comprehension.val attachment ++
              (Concrete.Splice.AttachmentAliasMaterialization.Semantic.sourceChildOccurrences
                comprehension.val payload.binderSpine.bodyContainer).map
                (Concrete.Splice.AttachmentAliasMaterialization.Semantic.liftOccurrence
                  comprehension.val attachment))) =
            some targetPattern.leaf.items := by
      simpa only [List.append_assoc, targetContext] using targetCompiled
    obtain ⟨targetNodeItems, targetRestItems, targetNodeCompiled,
        targetRestCompiled, targetItemsEq⟩ :=
      Concrete.Elaboration.compileOccurrencesWith?_append_split
        (fun {rels} => Concrete.Elaboration.compileRegion?
          (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
            comprehension.val attachment payload.binderSpine.bodyContainer)
          targetPattern.leaf.fuel)
        targetContext targetPattern.leaf.binders
        ((Concrete.Splice.AttachmentAliasMaterialization.Semantic.sourceNodeOccurrences
          comprehension.val payload.binderSpine.bodyContainer).map
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.liftOccurrence
              comprehension.val attachment))
        (Concrete.Splice.AttachmentAliasMaterialization.Semantic.aliasOccurrences
            comprehension.val attachment ++
          (Concrete.Splice.AttachmentAliasMaterialization.Semantic.sourceChildOccurrences
            comprehension.val payload.binderSpine.bodyContainer).map
              (Concrete.Splice.AttachmentAliasMaterialization.Semantic.liftOccurrence
                comprehension.val attachment))
        targetPattern.leaf.items targetCompiled'
    obtain ⟨aliasItems, targetChildItems, aliasCompiled, targetChildCompiled,
        targetRestItemsEq⟩ :=
      Concrete.Elaboration.compileOccurrencesWith?_append_split
        (fun {rels} => Concrete.Elaboration.compileRegion?
          (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
            comprehension.val attachment payload.binderSpine.bodyContainer)
          targetPattern.leaf.fuel)
        targetContext targetPattern.leaf.binders
        (Concrete.Splice.AttachmentAliasMaterialization.Semantic.aliasOccurrences
          comprehension.val attachment)
        ((Concrete.Splice.AttachmentAliasMaterialization.Semantic.sourceChildOccurrences
          comprehension.val payload.binderSpine.bodyContainer).map
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.liftOccurrence
              comprehension.val attachment))
        targetRestItems targetRestCompiled
    rw [targetItemsEq, targetRestItemsEq] at targetRawDenote
    have targetRestDenotes :=
      (denoteItemSeq_append model  _ targetRelEnv targetNodeItems
        (aliasItems.append targetChildItems)).mp targetRawDenote |>.2
    have aliasDenotes :=
      (denoteItemSeq_append model  _ targetRelEnv aliasItems
        targetChildItems).mp targetRestDenotes |>.1
    have terminalFactor :=
      Concrete.Splice.AttachmentAliasMaterialization.Semantic.aliasOccurrences_factor_collapse
        comprehension attachment payload.binderSpine
        certificate.wellFormed.diagram_well_formed targetContext sourceContext
        extendedCollapse targetPattern.leaf.wiresExact
        sourcePattern.leaf.wiresExact.nodup targetPattern.leaf.binders
        (Concrete.Elaboration.compileRegion?
          (Concrete.Splice.AttachmentAliasMaterialization.materializedDiagram
            comprehension.val attachment payload.binderSpine.bodyContainer)
          targetPattern.leaf.fuel)
        aliasItems aliasCompiled model
        (Concrete.Elaboration.extendedEnvironment
          targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
          targetOuter targetLocal) targetRelEnv aliasDenotes
    have outerFactor : targetOuter =
        (targetOuter ∘ collapse.oldIndex) ∘ collapse.indexMap := by
      funext targetIndex
      let extendedTargetIndex := targetPattern.leaf.inheritedWires.outerIndex
        payload.binderSpine.bodyContainer targetIndex
      have factorAt := congrFun terminalFactor extendedTargetIndex
      change Concrete.Elaboration.extendedEnvironment
          targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            targetOuter targetLocal extendedTargetIndex =
        Concrete.Elaboration.extendedEnvironment
          targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            targetOuter targetLocal
            (extendedCollapse.oldIndex
              (extendedCollapse.indexMap extendedTargetIndex)) at factorAt
      rw [show extendedCollapse.indexMap extendedTargetIndex =
          sourcePattern.leaf.inheritedWires.outerIndex
            payload.binderSpine.bodyContainer (collapse.indexMap targetIndex) by
        simpa [extendedTargetIndex, extendedCollapse] using
          (Concrete.Splice.AttachmentAliasMaterialization.Semantic.extendCollapse_index_inherited
            comprehension attachment payload.binderSpine payload.terminalBody
            targetPattern.leaf.inheritedWires sourcePattern.leaf.inheritedWires
            collapse payload.binderSpine.bodyContainer
            targetPattern.leaf.wiresExact sourcePattern.leaf.wiresExact
            targetIndex)] at factorAt
      rw [show extendedCollapse.oldIndex
          (sourcePattern.leaf.inheritedWires.outerIndex
            payload.binderSpine.bodyContainer (collapse.indexMap targetIndex)) =
          targetPattern.leaf.inheritedWires.outerIndex
            payload.binderSpine.bodyContainer
              (collapse.oldIndex (collapse.indexMap targetIndex)) by
        simpa [extendedCollapse] using
          (Concrete.Splice.AttachmentAliasMaterialization.Semantic.extendCollapse_oldIndex_inherited
            comprehension attachment payload.binderSpine payload.terminalBody
            targetPattern.leaf.inheritedWires sourcePattern.leaf.inheritedWires
            collapse payload.binderSpine.bodyContainer
            targetPattern.leaf.wiresExact sourcePattern.leaf.wiresExact
            (collapse.indexMap targetIndex))] at factorAt
      have leftOuter : Concrete.Elaboration.extendedEnvironment
          targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            targetOuter targetLocal extendedTargetIndex =
          targetOuter targetIndex := by
        simpa [extendedTargetIndex,
          Concrete.Splice.AttachmentAliasMaterialization.Semantic.extendedEnv] using
          (Concrete.Splice.AttachmentAliasMaterialization.Semantic.extendedEnv_outer
            targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            targetOuter targetLocal targetIndex)
      have rightOuter : Concrete.Elaboration.extendedEnvironment
          targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            targetOuter targetLocal
            (targetPattern.leaf.inheritedWires.outerIndex
              payload.binderSpine.bodyContainer
                (collapse.oldIndex (collapse.indexMap targetIndex))) =
          targetOuter (collapse.oldIndex (collapse.indexMap targetIndex)) := by
        simpa [Concrete.Splice.AttachmentAliasMaterialization.Semantic.extendedEnv] using
          (Concrete.Splice.AttachmentAliasMaterialization.Semantic.extendedEnv_outer
            targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            targetOuter targetLocal
            (collapse.oldIndex (collapse.indexMap targetIndex)))
      change targetOuter targetIndex = targetOuter
        (collapse.oldIndex (collapse.indexMap targetIndex))
      exact leftOuter.symm.trans (factorAt.trans rightOuter)
    let exposed :=
      Concrete.Splice.AttachmentAliasMaterialization.Semantic.exposedCollapse
        comprehension attachment payload.binderSpine
    have terminalIndexMapExposed : ∀ targetIndex,
        let targetWire := targetPattern.leaf.inheritedWires.get targetIndex
        let targetExposed :=
          (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            targetPattern.witness targetPattern.leaf hnonempty targetWire).1
            (List.get_mem _ targetIndex)
        let sourceIndex := collapse.indexMap targetIndex
        let sourceWire := sourcePattern.leaf.inheritedWires.get sourceIndex
        let sourceExposed :=
          (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            sourcePattern.witness sourcePattern.leaf hnonempty sourceWire).1
            (List.get_mem _ sourceIndex)
        exposed.indexMap
            (Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
              targetExposed) =
          Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
            sourceExposed := by
      intro targetIndex
      let targetWire := targetPattern.leaf.inheritedWires.get targetIndex
      let targetExposed :=
        (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty targetWire).1
          (List.get_mem _ targetIndex)
      let sourceIndex := collapse.indexMap targetIndex
      let sourceWire := sourcePattern.leaf.inheritedWires.get sourceIndex
      let sourceExposed :=
        (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          sourcePattern.witness sourcePattern.leaf hnonempty sourceWire).1
          (List.get_mem _ sourceIndex)
      change exposed.indexMap
          (Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
            targetExposed) =
        Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
          sourceExposed
      apply Concrete.Splice.Input.PlugLayout.exposedWire_get_injective sourceInput
      change comprehension.val.exposedWires.get
          (exposed.indexMap
            (Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
              targetExposed)) =
        comprehension.val.exposedWires.get
          (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
            sourceExposed)
      calc
        comprehension.val.exposedWires.get
            (exposed.indexMap
              (Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput
                targetWire targetExposed)) =
          Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire
            comprehension.val attachment targetWire := by
              calc
                _ = Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire
                    comprehension.val attachment
                    (targetInput.pattern.val.exposedWires.get
                      (Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput
                        targetWire targetExposed)) := by
                          simpa [sourceInput, targetInput, targetPayload, exposed,
                            materializedInstantiationPayload,
                            Concrete.Splice.AttachmentAliasMaterialization.Certificate.result]
                            using exposed.get
                              (Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput
                                targetWire targetExposed)
                _ = _ := by rw [Concrete.Splice.Input.PlugLayout.exposedWireIndex_get]
        _ = comprehension.val.exposedWires.get
            (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
              sourceExposed) := by
                have collapsed :
                    Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire
                        comprehension.val attachment targetWire = sourceWire := by
                  simpa [sourceInput] using (collapse.get targetIndex).symm
                have exposedGet : sourceWire =
                    sourceInput.pattern.val.exposedWires.get
                      (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput
                        sourceWire sourceExposed) :=
                  (Concrete.Splice.Input.PlugLayout.exposedWireIndex_get sourceInput
                    sourceWire sourceExposed).symm
                simpa [sourceInput] using collapsed.trans exposedGet
    have terminalOldIndexExposed : ∀ sourceIndex,
        let sourceWire := sourcePattern.leaf.inheritedWires.get sourceIndex
        let sourceExposed :=
          (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            sourcePattern.witness sourcePattern.leaf hnonempty sourceWire).1
            (List.get_mem _ sourceIndex)
        let targetIndex := collapse.oldIndex sourceIndex
        let targetWire := targetPattern.leaf.inheritedWires.get targetIndex
        let targetExposed :=
          (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
            targetPattern.witness targetPattern.leaf hnonempty targetWire).1
            (List.get_mem _ targetIndex)
        exposed.oldIndex
            (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
              sourceExposed) =
          Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
            targetExposed := by
      intro sourceIndex
      let sourceWire := sourcePattern.leaf.inheritedWires.get sourceIndex
      let sourceExposed :=
        (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          sourcePattern.witness sourcePattern.leaf hnonempty sourceWire).1
          (List.get_mem _ sourceIndex)
      let targetIndex := collapse.oldIndex sourceIndex
      let targetWire := targetPattern.leaf.inheritedWires.get targetIndex
      let targetExposed :=
        (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty targetWire).1
          (List.get_mem _ targetIndex)
      change exposed.oldIndex
          (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
            sourceExposed) =
        Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
          targetExposed
      apply Concrete.Splice.Input.PlugLayout.exposedWire_get_injective targetInput
      have globalOld : targetInput.pattern.val.exposedWires.get
          (exposed.oldIndex
            (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
              sourceExposed)) =
        Concrete.Splice.AttachmentAliasMaterialization.liftOldWire comprehension.val
          attachment sourceWire := by
        have raw := exposed.old_get
          (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
            sourceExposed)
        have sourceGet : comprehension.val.exposedWires.get
            (Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
              sourceExposed) = sourceWire := by
          simpa [sourceInput] using
            (Concrete.Splice.Input.PlugLayout.exposedWireIndex_get sourceInput sourceWire
              sourceExposed)
        rw [sourceGet] at raw
        simpa [sourceInput, targetInput, targetPayload, exposed,
          materializedInstantiationPayload,
          Concrete.Splice.AttachmentAliasMaterialization.Certificate.result] using raw
      have localOld :
          Concrete.Splice.AttachmentAliasMaterialization.liftOldWire comprehension.val
              attachment sourceWire = targetWire := by
        simpa [targetWire, targetIndex, sourceWire] using
          (collapse.old_get sourceIndex).symm
      have targetGet : targetWire = targetInput.pattern.val.exposedWires.get
          (Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
            targetExposed) :=
        (Concrete.Splice.Input.PlugLayout.exposedWireIndex_get targetInput targetWire
          targetExposed).symm
      exact globalOld.trans (localOld.trans targetGet)
    have exposedFactor : targetAssignment.classes =
        (targetAssignment.classes ∘ exposed.oldIndex) ∘ exposed.indexMap := by
      funext targetExposedIndex
      let targetWire := targetInput.pattern.val.exposedWires.get
        targetExposedIndex
      have targetInherited : targetWire ∈ targetPattern.leaf.inheritedWires :=
        (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty targetWire).2
          (List.get_mem _ targetExposedIndex)
      let targetIndex : Fin targetPattern.leaf.inheritedWires.length :=
        Classical.choose
          (Concrete.Elaboration.WireContext.lookup?_complete targetInherited)
      have targetGet : targetPattern.leaf.inheritedWires.get targetIndex =
          targetWire :=
        Concrete.Elaboration.WireContext.lookup?_sound
          (Classical.choose_spec
            (Concrete.Elaboration.WireContext.lookup?_complete targetInherited))
      let targetInheritedExposed :=
        (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty
          (targetPattern.leaf.inheritedWires.get targetIndex)).1
          (List.get_mem _ targetIndex)
      let targetInheritedExposedIndex :=
        Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput
          (targetPattern.leaf.inheritedWires.get targetIndex)
          targetInheritedExposed
      have targetExposedEq : targetInheritedExposedIndex = targetExposedIndex := by
        apply Concrete.Splice.Input.PlugLayout.exposedWire_get_injective targetInput
        rw [Concrete.Splice.Input.PlugLayout.exposedWireIndex_get, targetGet]
      let sourceIndex := collapse.indexMap targetIndex
      let sourceWire := sourcePattern.leaf.inheritedWires.get sourceIndex
      let sourceExposed :=
        (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          sourcePattern.witness sourcePattern.leaf hnonempty sourceWire).1
          (List.get_mem _ sourceIndex)
      let sourceExposedIndex :=
        Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
          sourceExposed
      have sourceExposedEq : sourceExposedIndex =
          exposed.indexMap targetExposedIndex := by
        have mapped := terminalIndexMapExposed targetIndex
        change exposed.indexMap targetInheritedExposedIndex =
          sourceExposedIndex at mapped
        rw [targetExposedEq] at mapped
        exact mapped.symm
      let targetOldIndex := collapse.oldIndex sourceIndex
      let targetOldWire := targetPattern.leaf.inheritedWires.get targetOldIndex
      let targetOldExposed :=
        (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty targetOldWire).1
          (List.get_mem _ targetOldIndex)
      let targetOldExposedIndex :=
        Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetOldWire
          targetOldExposed
      have targetOldExposedEq : exposed.oldIndex sourceExposedIndex =
          targetOldExposedIndex := by
        simpa [sourceIndex, sourceWire, sourceExposed, sourceExposedIndex,
          targetOldIndex, targetOldWire, targetOldExposed,
          targetOldExposedIndex] using terminalOldIndexExposed sourceIndex
      have factorAt := congrFun outerFactor targetIndex
      change targetAssignment.classes targetInheritedExposedIndex =
        targetAssignment.classes targetOldExposedIndex at factorAt
      change targetAssignment.classes targetExposedIndex =
        targetAssignment.classes
          (exposed.oldIndex (exposed.indexMap targetExposedIndex))
      calc
        targetAssignment.classes targetExposedIndex =
            targetAssignment.classes targetInheritedExposedIndex := by
              rw [targetExposedEq]
        _ = targetAssignment.classes targetOldExposedIndex := factorAt
        _ = targetAssignment.classes
            (exposed.oldIndex (exposed.indexMap targetExposedIndex)) := by
              rw [← targetOldExposedEq, sourceExposedEq]
    let sourceArgs : Fin comprehension.val.boundary.length → model.Carrier :=
      Fin.addCases relationArguments parameterValues ∘
        Fin.cast payload.boundarySplit
    let sourceAssignment : BoundaryAssignment comprehension.elaborate
        model.Carrier := {
      args := sourceArgs
      classes := targetAssignment.classes ∘ exposed.oldIndex
      agrees := by
        intro position
        let targetPosition : Fin certificate.result.val.boundary.length :=
          Fin.cast certificate.boundary_length.symm position
        change targetAssignment.classes
            (exposed.oldIndex (comprehension.val.boundaryClass position)) =
          sourceArgs position
        have classEq : exposed.indexMap
              (certificate.result.val.boundaryClass targetPosition) =
            comprehension.val.boundaryClass position := by
          simpa [exposed, targetPosition,
            Concrete.Splice.AttachmentAliasMaterialization.Certificate.result] using
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.exposedCollapse_boundaryClass
              comprehension attachment payload.binderSpine position)
        have factorAt := congrFun exposedFactor
          (certificate.result.val.boundaryClass targetPosition)
        simp only [Function.comp_apply] at factorAt
        rw [classEq] at factorAt
        have targetAgree := targetAssignment.agrees targetPosition
        change targetAssignment.classes
            (certificate.result.val.boundaryClass targetPosition) =
          targetAssignment.args targetPosition at targetAgree
        calc
          targetAssignment.classes
              (exposed.oldIndex (comprehension.val.boundaryClass position)) =
            targetAssignment.classes
              (certificate.result.val.boundaryClass targetPosition) :=
                factorAt.symm
          _ = targetAssignment.args targetPosition := targetAgree
          _ = (Fin.addCases relationArguments parameterValues ∘
              Fin.cast targetPayload.boundarySplit) targetPosition :=
                congrFun targetArgsEq targetPosition
          _ = sourceArgs position := by
                simp [sourceArgs, targetPosition, targetPayload,
                  materializedInstantiationPayload, Function.comp_apply]
    }
    have sourceOuterEq :
        terminalInheritedEnvironment payload state site arguments hnonempty
            sourceAssignment =
          targetOuter ∘ collapse.oldIndex := by
      funext sourceIndex
      let sourceWire := sourcePattern.leaf.inheritedWires.get sourceIndex
      let sourceExposed :=
        (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          sourcePattern.witness sourcePattern.leaf hnonempty sourceWire).1
          (List.get_mem _ sourceIndex)
      let sourceExposedIndex :=
        Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
          sourceExposed
      let targetIndex := collapse.oldIndex sourceIndex
      let targetWire := targetPattern.leaf.inheritedWires.get targetIndex
      let targetExposed :=
        (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
          targetPattern.witness targetPattern.leaf hnonempty targetWire).1
          (List.get_mem _ targetIndex)
      let targetExposedIndex :=
        Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
          targetExposed
      have indexEq : exposed.oldIndex sourceExposedIndex =
          targetExposedIndex := by
        simpa [sourceWire, sourceExposed, sourceExposedIndex, targetIndex,
          targetWire, targetExposed, targetExposedIndex] using
            terminalOldIndexExposed sourceIndex
      change targetAssignment.classes (exposed.oldIndex sourceExposedIndex) =
        targetAssignment.classes targetExposedIndex
      exact congrArg targetAssignment.classes indexEq
    let relationMap : RelationRenaming
        sourcePattern.witness.toFocus.holeRels
        targetPattern.witness.toFocus.holeRels :=
      Concrete.Splice.Input.relationRenamingOfEq terminalRels
    let sourceRelEnv := RelEnv.pullback relationMap targetRelEnv
    refine ⟨sourceAssignment, rfl, sourceRelEnv, ?_, ?_⟩
    · have matchIff := terminalRelationsMatch_materialized_iff payload state site
        arguments attachment certificate hnonempty values terminalRels
        terminalBinders targetRelEnv
      change TerminalRelationsMatch payload state site arguments hnonempty values
          sourceRelEnv ↔
        TerminalRelationsMatch targetPayload state site arguments hnonempty values
          targetRelEnv at matchIff
      intro arity relation
      exact (matchIff.mpr targetMatch) relation
    · have outerAgrees :
          (backwardSemantic.indexRelation collapse).EnvironmentsAgree
            (targetOuter ∘ collapse.oldIndex) targetOuter := by
        apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
          collapse.oldIndex _ _).mpr
        rfl
      have targetDenotes' : denoteRegion model  targetOuter targetRelEnv
          (Concrete.Elaboration.finishRegion certificate.result.val.diagram
            targetPattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            targetPattern.leaf.items) := by
        exact targetDenotesSaved
      have sourceRenamed := backwardSimulation
        (targetOuter ∘ collapse.oldIndex) targetOuter targetRelEnv outerAgrees
          targetDenotes'
      have relationMapEq :
          (fun {arity} => backwardSemantic.relationMap backwardBinderWitness
            (arity := arity)) =
          (fun {arity} => relationMap (arity := arity)) := by
        exact relationMap_eq_relationRenamingOfEq backwardBinderWitness
      rw [relationMapEq] at sourceRenamed
      have sourceDenotes :=
        (denoteRegion_renameRelations model  relationMap sourceRelEnv
          targetRelEnv (RelEnv.pullback_agrees relationMap targetRelEnv)
          (targetOuter ∘ collapse.oldIndex)
          (Concrete.Elaboration.finishRegion comprehension.val.diagram
            sourcePattern.leaf.inheritedWires payload.binderSpine.bodyContainer
            sourcePattern.leaf.items)).mp sourceRenamed
      rw [sourceOuterEq]
      exact sourceDenotes
  · rintro ⟨sourceAssignment, sourceArgsEq, sourceRelEnv, sourceMatch,
      sourceDenotes⟩
    let exposed :=
      Concrete.Splice.AttachmentAliasMaterialization.Semantic.exposedCollapse
        comprehension attachment payload.binderSpine
    let targetArgs : Fin certificate.result.val.boundary.length → model.Carrier :=
      Fin.addCases relationArguments parameterValues ∘
        Fin.cast targetPayload.boundarySplit
    let targetAssignment : BoundaryAssignment certificate.result.elaborate
        model.Carrier := {
      args := targetArgs
      classes := sourceAssignment.classes ∘ exposed.indexMap
      agrees := by
        intro position
        let sourcePosition : Fin comprehension.val.boundary.length :=
          Fin.cast certificate.boundary_length position
        change sourceAssignment.classes
            (exposed.indexMap
              (certificate.result.val.boundaryClass position)) =
          targetArgs position
        have classEq : exposed.indexMap
              (certificate.result.val.boundaryClass position) =
            comprehension.val.boundaryClass sourcePosition := by
          simpa [exposed, sourcePosition,
            Concrete.Splice.AttachmentAliasMaterialization.Certificate.result] using
            (Concrete.Splice.AttachmentAliasMaterialization.Semantic.exposedCollapse_boundaryClass
              comprehension attachment payload.binderSpine sourcePosition)
        rw [classEq]
        calc
          sourceAssignment.classes
              (comprehension.val.boundaryClass sourcePosition) =
              sourceAssignment.args sourcePosition := by
                simpa only [Concrete.CheckedOpen.elaborate_boundary] using
                  sourceAssignment.agrees sourcePosition
          _ = (Fin.addCases relationArguments parameterValues ∘
              Fin.cast payload.boundarySplit) sourcePosition :=
                congrFun sourceArgsEq sourcePosition
          _ = targetArgs position := by
                simp [targetArgs, sourcePosition, targetPayload,
                  materializedInstantiationPayload, Function.comp_apply]
    }
    let targetRelEnv := castRelEnv terminalRels sourceRelEnv
    refine ⟨targetAssignment, rfl, targetRelEnv, ?_, ?_⟩
    · have matchIff := terminalRelationsMatch_materialized_iff payload state site
        arguments attachment certificate hnonempty values terminalRels
        terminalBinders targetRelEnv
      change TerminalRelationsMatch payload state site arguments hnonempty values
          (RelEnv.pullback (Concrete.Splice.Input.relationRenamingOfEq terminalRels)
            targetRelEnv) ↔
        TerminalRelationsMatch targetPayload state site arguments hnonempty values
          targetRelEnv at matchIff
      have pullEq : RelEnv.pullback
          (Concrete.Splice.Input.relationRenamingOfEq terminalRels) targetRelEnv =
          sourceRelEnv := by
        exact pullback_relationRenamingOfEq_cast terminalRels sourceRelEnv
      have sourcePulledMatch : TerminalRelationsMatch payload state site
          arguments hnonempty values
          (RelEnv.pullback (Concrete.Splice.Input.relationRenamingOfEq terminalRels)
            targetRelEnv) := by
        rw [pullEq]
        exact sourceMatch
      intro arity relation
      exact (matchIff.mp sourcePulledMatch) relation
    · have outerEq :
          terminalInheritedEnvironment payload state site arguments hnonempty
              sourceAssignment ∘ collapse.indexMap =
            terminalInheritedEnvironment targetPayload state site arguments
              hnonempty targetAssignment := by
          funext targetIndex
          apply congrArg sourceAssignment.classes
          apply Concrete.Splice.Input.PlugLayout.exposedWire_get_injective sourceInput
          let targetWire := targetPattern.leaf.inheritedWires.get targetIndex
          let targetExposed :=
            (targetInput.plugLayout.terminalBody_inherited_mem_iff_exposed
              targetPattern.witness targetPattern.leaf hnonempty targetWire).1
              (List.get_mem _ targetIndex)
          let sourceIndex := collapse.indexMap targetIndex
          let sourceWire := sourcePattern.leaf.inheritedWires.get sourceIndex
          let sourceExposed :=
            (sourceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
              sourcePattern.witness sourcePattern.leaf hnonempty sourceWire).1
              (List.get_mem _ sourceIndex)
          let targetExposedIndex :=
            Concrete.Splice.Input.PlugLayout.exposedWireIndex targetInput targetWire
              targetExposed
          let sourceExposedIndex :=
            Concrete.Splice.Input.PlugLayout.exposedWireIndex sourceInput sourceWire
              sourceExposed
          symm
          change comprehension.val.exposedWires.get
              (exposed.indexMap targetExposedIndex) =
            comprehension.val.exposedWires.get sourceExposedIndex
          calc
            comprehension.val.exposedWires.get
                (exposed.indexMap targetExposedIndex) =
                Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire
                  comprehension.val attachment targetWire := by
                    calc
                      _ = Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire
                          comprehension.val attachment
                          (targetInput.pattern.val.exposedWires.get
                            targetExposedIndex) := by
                              simpa [sourceInput, targetInput, targetPayload,
                                exposed, materializedInstantiationPayload,
                                Concrete.Splice.AttachmentAliasMaterialization.Certificate.result]
                                using exposed.get targetExposedIndex
                      _ = _ := by
                        rw [show targetInput.pattern.val.exposedWires.get
                            targetExposedIndex = targetWire by
                          exact Concrete.Splice.Input.PlugLayout.exposedWireIndex_get
                            targetInput targetWire targetExposed]
            _ = comprehension.val.exposedWires.get sourceExposedIndex := by
                  have collapsed :
                      Concrete.Splice.AttachmentAliasMaterialization.Semantic.collapseWire
                          comprehension.val attachment targetWire = sourceWire := by
                    simpa [sourceInput] using (collapse.get targetIndex).symm
                  have exposedGet : sourceWire =
                      sourceInput.pattern.val.exposedWires.get
                        sourceExposedIndex :=
                    (Concrete.Splice.Input.PlugLayout.exposedWireIndex_get sourceInput
                      sourceWire sourceExposed).symm
                  simpa [sourceInput] using collapsed.trans exposedGet
      have outerAgrees :
            (forwardSemantic.indexRelation collapse).EnvironmentsAgree
              (terminalInheritedEnvironment payload state site arguments
                hnonempty sourceAssignment)
              (terminalInheritedEnvironment targetPayload state site arguments
                hnonempty targetAssignment) := by
          apply (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_backwardMap
            collapse.indexMap _ _).mpr
          exact outerEq
      have relationAgrees : RelEnv.Agrees
            (forwardSemantic.relationMap forwardBinderWitness) sourceRelEnv
              targetRelEnv := by
          have pulled := identityBinderWitness_pullback_cast forwardBinderWitness
            sourceRelEnv
          rw [← pulled]
          exact RelEnv.pullback_agrees
            (forwardSemantic.relationMap forwardBinderWitness) targetRelEnv
      have sourceRenamed :=
          (denoteRegion_renameRelations model
            (forwardSemantic.relationMap forwardBinderWitness) sourceRelEnv
            targetRelEnv relationAgrees
            (terminalInheritedEnvironment payload state site arguments
              hnonempty sourceAssignment)
            (Concrete.Elaboration.finishRegion comprehension.val.diagram
              sourcePattern.leaf.inheritedWires payload.binderSpine.bodyContainer
              sourcePattern.leaf.items)).mpr sourceDenotes
      exact forwardSimulation
          (terminalInheritedEnvironment payload state site arguments hnonempty
            sourceAssignment)
          (terminalInheritedEnvironment targetPayload state site arguments
            hnonempty targetAssignment)
          targetRelEnv outerAgrees sourceRenamed

/-- Extensional equality form consumed by the executor-trace simulation. -/
theorem terminalRelationOfParameterValues_materialized
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (certificate : Concrete.Splice.AttachmentAliasMaterialization.Certificate
      comprehension
      (instantiationAttachment comprehension attachments binders payload state
        arguments)
      payload.binderSpine)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    terminalRelationOfParameterValues payload state site arguments hnonempty
        model  parameterValues values =
      terminalRelationOfParameterValues
        (materializedInstantiationPayload payload
          (instantiationAttachment comprehension attachments binders payload state
            arguments)
          certificate)
        state site arguments hnonempty model  parameterValues values := by
  funext relationArguments
  apply propext
  exact (terminalRelationOfParameterValues_materialized_iff payload state site
    arguments certificate hnonempty model  parameterValues values
    relationArguments).symm

end InstantiationSemantic

end VisualProof.Rule
