import VisualProof.Rule.Soundness.AttachmentAliasSemanticRootFocused
import VisualProof.Rule.Soundness.Congruence

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- Every route from the sheet to the designated terminal body follows only
the explicitly designated bubble spine. -/
theorem BinderSpine.rootRoute_hasCutDepth_zero
    (checked : CheckedOpenDiagram signature)
    (spine : BinderSpine checked.val.diagram)
    (hnonempty : spine.proxyCount ≠ 0)
    {start : Fin checked.val.diagram.regionCount} {path : List Nat}
    (route : RegionRoute checked.val.diagram start spine.bodyContainer path) :
    route.HasCutDepth 0 := by
  induction path generalizing start with
  | nil =>
      cases route
      exact RegionRoute.HasCutDepth.here _
  | cons positionValue rest induction =>
      cases route with
      | @step start child target rest hparent position hposition tail =>
          let terminal : Fin spine.proxyCount :=
            ⟨spine.proxyCount - 1, by omega⟩
          have childEnclosesBody : checked.val.diagram.Encloses child
              spine.bodyContainer := by
            exact VisualProof.Diagram.Splice.Input.RegionRoute.encloses tail
              checked.property.diagram_well_formed
          have childEnclosesTerminal : checked.val.diagram.Encloses child
              (spine.proxy terminal) := by
            rw [← spine.body_eq_terminal_of_nonempty hnonempty]
            exact childEnclosesBody
          rcases
              VisualProof.Diagram.Splice.BinderSpine.enclosing_proxy_is_root_or_proxy
                checked spine terminal childEnclosesTerminal with
            childRoot | ⟨proxy, _hle, childProxy⟩
          · subst child
            rw [checked.property.diagram_well_formed.root_is_sheet] at hparent
            simp [CRegion.parent?] at hparent
          · have parentEq :
                (if _hzero : proxy.val = 0 then checked.val.diagram.root
                  else spine.proxy ⟨proxy.val - 1, by omega⟩) = start := by
              have parent := hparent
              rw [childProxy, spine.proxy_region] at parent
              simpa [CRegion.parent?] using parent
            have childKind : checked.val.diagram.regions child =
                .bubble start (spine.arity proxy) := by
              rw [childProxy, spine.proxy_region, parentEq]
            exact RegionRoute.HasCutDepth.bubble
              (hparent := hparent) (hposition := hposition) childKind
                (induction tail)

theorem exposedCollapse_boundaryClass
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (position : Fin pattern.val.boundary.length) :
    (exposedCollapse pattern attachment spine).indexMap
        ((raw pattern.val attachment spine.bodyContainer).boundaryClass
          (Fin.cast
            (raw_boundary_length pattern.val attachment
              spine.bodyContainer).symm position)) =
      pattern.val.boundaryClass position := by
  let target := raw pattern.val attachment spine.bodyContainer
  let targetPosition : Fin target.boundary.length :=
    Fin.cast
      (raw_boundary_length pattern.val attachment
        spine.bodyContainer).symm position
  apply pattern.val.boundaryClass_complete position
  calc
    pattern.val.exposedWires.get
        ((exposedCollapse pattern attachment spine).indexMap
          (target.boundaryClass targetPosition)) =
      collapseWire pattern.val attachment
        (target.exposedWires.get (target.boundaryClass targetPosition)) :=
          (exposedCollapse pattern attachment spine).get _
    _ = collapseWire pattern.val attachment
        (target.boundary.get targetPosition) := by
          rw [target.boundaryClass_sound targetPosition]
    _ = pattern.val.boundary.get position := by
      have targetBoundaryGet :
          target.boundary.get targetPosition =
            rawBoundaryWire pattern.val attachment position := by
        simp [target, targetPosition, raw, List.get_eq_getElem]
      rw [targetBoundaryGet]
      exact collapseWire_rawBoundaryWire pattern.val attachment position


theorem materialized_exposed_factor_of_denote_zero
    {signature : List Nat}
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (certificate : Certificate pattern attachment spine)
    (hzero : spine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetAssignment : BoundaryAssignment
      certificate.result.elaborate model.Carrier)
    (targetDenotes : denoteRegion (relCtx := []) model named
      targetAssignment.classes PUnit.unit
      certificate.result.elaborate.body) :
    targetAssignment.classes =
      (targetAssignment.classes ∘
          (exposedCollapse pattern attachment spine).oldIndex) ∘
        (exposedCollapse pattern attachment spine).indexMap := by
  obtain ⟨targetItems, targetHidden, targetCompiled, targetItemsDenote⟩ :=
    VisualProof.Rule.CongruenceSoundness.open_body_denote_root_items
      certificate.result model named
      targetAssignment.classes targetDenotes
  have bodyRoot : spine.bodyContainer = pattern.val.diagram.root :=
    spine.body_eq_root_of_empty hzero
  change ConcreteElaboration.compileOccurrencesWith? signature
      (raw pattern.val attachment spine.bodyContainer).diagram
      (ConcreteElaboration.compileRegion? signature
        (raw pattern.val attachment spine.bodyContainer).diagram
        (raw pattern.val attachment spine.bodyContainer).diagram.regionCount)
      (raw pattern.val attachment spine.bodyContainer).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences
        (raw pattern.val attachment spine.bodyContainer).diagram
        (raw pattern.val attachment spine.bodyContainer).diagram.root) =
      some targetItems at targetCompiled
  rw [show (raw pattern.val attachment spine.bodyContainer).diagram.root =
      spine.bodyContainer by simpa [raw, materializedDiagram] using bodyRoot.symm]
      at targetCompiled
  have targetCompiledFocused :
      ConcreteElaboration.compileOccurrencesWith? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        (ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          (materializedDiagram pattern.val attachment
            spine.bodyContainer).regionCount)
        (raw pattern.val attachment spine.bodyContainer).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          spine.bodyContainer) = some targetItems := by
    simpa only [raw] using targetCompiled
  rw [materialized_focused_localOccurrences] at targetCompiledFocused
  have targetCompiled' :
      ConcreteElaboration.compileOccurrencesWith? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        (ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          (materializedDiagram pattern.val attachment
            spine.bodyContainer).regionCount)
        (raw pattern.val attachment spine.bodyContainer).rootWires
        ConcreteElaboration.BinderContext.empty
        ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
            (liftOccurrence pattern.val attachment) ++
          (aliasOccurrences pattern.val attachment ++
            (sourceChildOccurrences pattern.val spine.bodyContainer).map
              (liftOccurrence pattern.val attachment))) = some targetItems := by
    simpa only [List.append_assoc] using targetCompiledFocused
  obtain ⟨targetNodeItems, targetRestItems, targetNodeCompiled,
      targetRestCompiled, targetItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        (materializedDiagram pattern.val attachment spine.bodyContainer).regionCount)
      (raw pattern.val attachment spine.bodyContainer).rootWires
      ConcreteElaboration.BinderContext.empty
      ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment))
      (aliasOccurrences pattern.val attachment ++
        (sourceChildOccurrences pattern.val spine.bodyContainer).map
          (liftOccurrence pattern.val attachment)) targetItems targetCompiled'
  obtain ⟨aliasItems, targetChildItems, aliasCompiled, targetChildCompiled,
      targetRestItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (materializedDiagram pattern.val attachment spine.bodyContainer)
        (materializedDiagram pattern.val attachment spine.bodyContainer).regionCount)
      (raw pattern.val attachment spine.bodyContainer).rootWires
      ConcreteElaboration.BinderContext.empty
      (aliasOccurrences pattern.val attachment)
      ((sourceChildOccurrences pattern.val spine.bodyContainer).map
        (liftOccurrence pattern.val attachment)) targetRestItems targetRestCompiled
  subst targetItems
  subst targetRestItems
  have targetParts := (denoteItemSeq_append (relCtx := []) model named
    (ConcreteElaboration.rootEnvironment
      certificate.result.val.exposedWires certificate.result.val.hiddenWires
      targetAssignment.classes targetHidden)
    (PUnit.unit : RelEnv model.Carrier []) targetNodeItems
      (aliasItems.append targetChildItems)).mp
      targetItemsDenote
  have targetRestParts := (denoteItemSeq_append (relCtx := []) model named
    (ConcreteElaboration.rootEnvironment
      certificate.result.val.exposedWires certificate.result.val.hiddenWires
      targetAssignment.classes targetHidden)
    (PUnit.unit : RelEnv model.Carrier []) aliasItems targetChildItems).mp
      targetParts.2
  have targetRootExact :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      certificate.result
  have targetExact :
      ConcreteElaboration.WireContext.Exact
        (raw pattern.val attachment spine.bodyContainer).rootWires
        spine.bodyContainer := by
    simpa [Certificate.result, raw, materializedDiagram, bodyRoot] using
      targetRootExact
  have rootFactor := aliasOccurrences_factor_collapse pattern attachment spine
    certificate.wellFormed.diagram_well_formed
    (raw pattern.val attachment spine.bodyContainer).rootWires pattern.val.rootWires
    (rootCollapse pattern attachment spine certificate.sourceTerminalBody
      certificate.wellFormed.diagram_well_formed)
    targetExact
    pattern.val.rootWires_nodup ConcreteElaboration.BinderContext.empty
    (ConcreteElaboration.compileRegion? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      (materializedDiagram pattern.val attachment spine.bodyContainer).regionCount)
    aliasItems aliasCompiled model named
    (ConcreteElaboration.rootEnvironment
      certificate.result.val.exposedWires certificate.result.val.hiddenWires
      targetAssignment.classes targetHidden)
    PUnit.unit targetRestParts.1
  funext index
  have rootAt := congrFun rootFactor
    (combinedOuterIndex
      (raw pattern.val attachment spine.bodyContainer).exposedWires
      (raw pattern.val attachment spine.bodyContainer).hiddenWires index)
  change targetAssignment.classes index =
    targetAssignment.classes
      ((exposedCollapse pattern attachment spine).oldIndex
        ((exposedCollapse pattern attachment spine).indexMap index))
  simpa only [Certificate.result, factoredSourceEnv, Function.comp_apply,
    rootEnvironment_combinedOuterIndex,
    rootCollapse_indexMap_outer, rootCollapse_oldIndex_outer] using rootAt

theorem materialized_exposed_factor_of_denote
    {signature : List Nat}
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (certificate : Certificate pattern attachment spine)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetAssignment : BoundaryAssignment
      certificate.result.elaborate model.Carrier)
    (targetDenotes : denoteRegion (relCtx := []) model named
      targetAssignment.classes PUnit.unit
      certificate.result.elaborate.body) :
    targetAssignment.classes =
      (targetAssignment.classes ∘
          (exposedCollapse pattern attachment spine).oldIndex) ∘
        (exposedCollapse pattern attachment spine).indexMap := by
  by_cases hzero : spine.proxyCount = 0
  · exact materialized_exposed_factor_of_denote_zero pattern attachment spine
      certificate hzero model named targetAssignment targetDenotes
  · obtain ⟨targetItems, targetHidden, targetCompiled, targetItemsDenote⟩ :=
      VisualProof.Rule.CongruenceSoundness.open_body_denote_root_items
        certificate.result model named targetAssignment.classes targetDenotes
    have targetEncloses : certificate.result.val.diagram.Encloses
        certificate.result.val.diagram.root spine.bodyContainer :=
      certificate.wellFormed.diagram_well_formed.all_regions_reach_root
        spine.bodyContainer
    obtain ⟨path, ⟨route⟩⟩ := regionRoute_complete_of_encloses
      certificate.result.val.diagram certificate.result.val.diagram.root
      spine.bodyContainer targetEncloses
    have routeZero : route.HasCutDepth 0 := by
      exact BinderSpine.rootRoute_hasCutDepth_zero certificate.result
        certificate.spine (by simpa [Certificate.spine, binderSpine] using hzero)
        route
    let closed : CheckedDiagram signature :=
      ⟨certificate.result.val.diagram,
        certificate.wellFormed.diagram_well_formed⟩
    let exactContext := ConcreteElaboration.exactScopeWires
      certificate.result.val.diagram certificate.result.val.diagram.root
    have exact : ConcreteElaboration.WireContext.Exact exactContext
        certificate.result.val.diagram.root := by
      simpa [exactContext, ConcreteElaboration.WireContext.extend] using
        ConcreteElaboration.closedRootWires_exact
          certificate.wellFormed.diagram_well_formed
    obtain ⟨closedBody, closedBodyCompiled⟩ :=
      ConcreteElaboration.compileRoot?_complete
        certificate.wellFormed.diagram_well_formed
        ([] : ConcreteElaboration.WireContext certificate.result.val.diagram)
        exactContext (by simpa using exact)
    simp only [ConcreteElaboration.compileRoot?] at closedBodyCompiled
    have closedBodyCompiled' :
        (ConcreteElaboration.compileOccurrencesWith? signature
          certificate.result.val.diagram
          (ConcreteElaboration.compileRegion? signature
            certificate.result.val.diagram
            certificate.result.val.diagram.regionCount)
          exactContext ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences certificate.result.val.diagram
            certificate.result.val.diagram.root)).bind
          (fun items => some
            (ConcreteElaboration.finishRoot [] exactContext items)) =
          some closedBody := by
      simpa [Certificate.result, raw] using closedBodyCompiled
    cases exactItemsResult : ConcreteElaboration.compileOccurrencesWith?
        signature certificate.result.val.diagram
        (ConcreteElaboration.compileRegion? signature
          certificate.result.val.diagram
          certificate.result.val.diagram.regionCount)
        exactContext ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences certificate.result.val.diagram
          certificate.result.val.diagram.root) with
    | none =>
      rw [exactItemsResult] at closedBodyCompiled'
      simp at closedBodyCompiled'
    | some exactItems =>
      let wireEquiv := Diagram.exactContextToOpenRootWireEquiv certificate.result
        exactContext exact
      have itemIso := Diagram.compiledOpenRootItemsIsoFromExactContext
        certificate.result exactContext exact exactItemsResult targetCompiled
      let rootRaw := ConcreteElaboration.rootEnvironment
        certificate.result.val.exposedWires certificate.result.val.hiddenWires
        targetAssignment.classes targetHidden
      let exactRaw : Fin exactContext.length → model.Carrier :=
        rootRaw ∘ wireEquiv
      have environmentsAgree : EnvironmentsAgree wireEquiv exactRaw rootRaw := by
        intro index
        rfl
      have exactDenotes : denoteItemSeq (relCtx := []) model named exactRaw
          PUnit.unit exactItems :=
        (itemIso.denotation model named exactRaw rootRaw PUnit.unit
          environmentsAgree).mpr targetItemsDenote
      have exactCompiled : ConcreteElaboration.compileOccurrencesWith? signature
          closed.val
          (ConcreteElaboration.compileRegion? signature closed.val
            closed.val.regionCount)
          (ConcreteElaboration.WireContext.extend
            ([] : ConcreteElaboration.WireContext closed.val) closed.val.root)
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences closed.val closed.val.root) =
            some exactItems := by
        simpa [closed, exactContext, ConcreteElaboration.WireContext.extend] using
          exactItemsResult
      obtain ⟨descendant⟩ :=
        VisualProof.Rule.CongruenceSoundness.denoted_descendant_leaf closed
          route routeZero
          ([] : ConcreteElaboration.WireContext closed.val)
          ConcreteElaboration.BinderContext.empty closed.val.regionCount
          exactItems exactCompiled
          (by simpa [closed, exactContext,
            ConcreteElaboration.WireContext.extend] using exact)
          (ConcreteElaboration.BinderContext.empty_covers_root closed.property)
          (ConcreteElaboration.BinderContext.Enumeration.empty closed.val)
          model named Fin.elim0 exactRaw PUnit.unit
          (by
            rw [ConcreteElaboration.extendedEnvironment_nil_eq_cast]
            exact exactDenotes)
      let sourceView := Splice.Input.compiledPatternTerminalView pattern spine
        certificate.sourceTerminalBody hzero
      let targetContext := descendant.leaf.inheritedWires.extend
        spine.bodyContainer
      let sourceContext := sourceView.leaf.inheritedWires.extend
        spine.bodyContainer
      let terminalCollapse := ContextCollapse.ofExact pattern attachment spine
        certificate.sourceTerminalBody spine.bodyContainer targetContext
        sourceContext descendant.leaf.wiresExact sourceView.leaf.wiresExact
      have targetLeafCompiled := descendant.leaf.itemsComputation
      change ConcreteElaboration.compileOccurrencesWith? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          (ConcreteElaboration.compileRegion? signature
            (materializedDiagram pattern.val attachment spine.bodyContainer)
            descendant.leaf.fuel)
          targetContext descendant.leaf.binders
          (ConcreteElaboration.localOccurrences
            (materializedDiagram pattern.val attachment spine.bodyContainer)
            spine.bodyContainer) = some descendant.leaf.items at targetLeafCompiled
      rw [materialized_focused_localOccurrences] at targetLeafCompiled
      have targetLeafCompiled' :
          ConcreteElaboration.compileOccurrencesWith? signature
            (materializedDiagram pattern.val attachment spine.bodyContainer)
            (ConcreteElaboration.compileRegion? signature
              (materializedDiagram pattern.val attachment spine.bodyContainer)
              descendant.leaf.fuel)
            targetContext descendant.leaf.binders
            ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
                (liftOccurrence pattern.val attachment) ++
              (aliasOccurrences pattern.val attachment ++
                (sourceChildOccurrences pattern.val spine.bodyContainer).map
                  (liftOccurrence pattern.val attachment))) =
              some descendant.leaf.items := by
        simpa only [List.append_assoc] using targetLeafCompiled
      obtain ⟨targetNodeItems, targetRestItems, targetNodeCompiled,
          targetRestCompiled, targetItemsEq⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (fun {rels} => ConcreteElaboration.compileRegion? signature
            (materializedDiagram pattern.val attachment spine.bodyContainer)
            descendant.leaf.fuel)
          targetContext descendant.leaf.binders
          ((sourceNodeOccurrences pattern.val spine.bodyContainer).map
            (liftOccurrence pattern.val attachment))
          (aliasOccurrences pattern.val attachment ++
            (sourceChildOccurrences pattern.val spine.bodyContainer).map
              (liftOccurrence pattern.val attachment))
          descendant.leaf.items targetLeafCompiled'
      obtain ⟨aliasItems, targetChildItems, aliasCompiled, targetChildCompiled,
          targetRestItemsEq⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (fun {rels} => ConcreteElaboration.compileRegion? signature
            (materializedDiagram pattern.val attachment spine.bodyContainer)
            descendant.leaf.fuel)
          targetContext descendant.leaf.binders
          (aliasOccurrences pattern.val attachment)
          ((sourceChildOccurrences pattern.val spine.bodyContainer).map
            (liftOccurrence pattern.val attachment))
          targetRestItems targetRestCompiled
      have targetLeafDenotes := descendant.itemsDenote
      rw [targetItemsEq, targetRestItemsEq] at targetLeafDenotes
      have targetRestDenotes :=
        (denoteItemSeq_append model named _ descendant.relEnv targetNodeItems
          (aliasItems.append targetChildItems)).mp targetLeafDenotes |>.2
      have aliasDenotes :=
        (denoteItemSeq_append model named _ descendant.relEnv aliasItems
          targetChildItems).mp targetRestDenotes |>.1
      have terminalFactor := aliasOccurrences_factor_collapse pattern attachment
        spine certificate.wellFormed.diagram_well_formed targetContext
        sourceContext terminalCollapse descendant.leaf.wiresExact
        sourceView.leaf.wiresExact.nodup descendant.leaf.binders
        (ConcreteElaboration.compileRegion? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          descendant.leaf.fuel)
        aliasItems aliasCompiled model named
        (ConcreteElaboration.extendedEnvironment descendant.leaf.inheritedWires
          spine.bodyContainer descendant.outerEnv descendant.localEnv)
        descendant.relEnv aliasDenotes
      sorry

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
