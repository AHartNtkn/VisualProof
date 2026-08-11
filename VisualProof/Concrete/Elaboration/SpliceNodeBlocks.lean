import VisualProof.Concrete.Elaboration.SpliceBinderContext
import VisualProof.Concrete.Elaboration.SpliceCompilerBlocks

/-! Exact node-block compiler transport for a source-derived splice. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

/-- Stable source frame position transport into the host prefix of the
combined target site context. -/
noncomputable def frameSiteIndexMap (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (hostContext : WireContext input.frame.val) :
    Fin hostContext.length →
      Fin (layout.patternSiteWires consistent hostContext).length :=
  fun index => Fin.cast (by
    simp [patternSiteWires, mapFrameContext])
      (Fin.castAdd layout.bodyLocalWires.length
        (layout.mapFrameContextEquiv consistent hostContext index))

theorem frameSiteIndexMap_get (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (hostContext : WireContext input.frame.val)
    (index : Fin hostContext.length) :
    (layout.patternSiteWires consistent hostContext).get
        (layout.frameSiteIndexMap consistent hostContext index) =
      layout.frameWireEmbedding consistent (hostContext.get index) := by
  unfold frameSiteIndexMap
  change (layout.mapFrameContext consistent hostContext ++
      layout.bodyLocalWires).get
      (Fin.cast _ (Fin.castAdd layout.bodyLocalWires.length
        (layout.mapFrameContextEquiv consistent hostContext index))) = _
  calc
    _ = (layout.mapFrameContext consistent hostContext ++
          layout.bodyLocalWires).get
        (Fin.cast (by simp)
          (Fin.castAdd layout.bodyLocalWires.length
            (layout.mapFrameContextEquiv consistent hostContext index))) := by
      congr 1
    _ = (layout.mapFrameContext consistent hostContext).get
        (layout.mapFrameContextEquiv consistent hostContext index) :=
      get_append_castAdd (layout.mapFrameContext consistent hostContext)
        layout.bodyLocalWires _
    _ = _ := layout.mapFrameContext_get consistent hostContext index

private theorem resolvePort?_context_eq
    {diagram : Concrete.Diagram}
    (first second : WireContext diagram) (contextEq : first = second)
    (node : Fin diagram.nodeCount) (port : CPort) :
    (resolvePort? diagram first node port).map
        (Fin.cast (congrArg List.length contextEq)) =
      resolvePort? diagram second node port := by
  subst second
  simp

/-- Sequence compilation with simultaneous wire and relation renaming. -/
private theorem compileOccurrencesWith?_mapBoth
    {sourceDiagram targetDiagram : Concrete.Diagram}
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin sourceDiagram.regionCount) →
      (context : WireContext sourceDiagram) →
      BinderContext sourceDiagram rels →
      Option (Region context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin targetDiagram.regionCount) →
      (context : WireContext targetDiagram) →
      BinderContext targetDiagram rels →
      Option (Region context.length rels))
    (sourceContext : WireContext sourceDiagram)
    (targetContext : WireContext targetDiagram)
    (sourceBinders : BinderContext sourceDiagram sourceRels)
    (targetBinders : BinderContext targetDiagram targetRels)
    (mapOccurrence : LocalOccurrence sourceDiagram.regionCount
        sourceDiagram.nodeCount →
      LocalOccurrence targetDiagram.regionCount targetDiagram.nodeCount)
    (wire : Fin sourceContext.length → Fin targetContext.length)
    (relation : RelationRenaming sourceRels targetRels)
    (sourceOccurrences : List
      (LocalOccurrence sourceDiagram.regionCount sourceDiagram.nodeCount))
    (hoccurrence : ∀ occurrence, occurrence ∈ sourceOccurrences →
      compileOccurrenceWith? targetDiagram targetRecurse
          targetContext targetBinders (mapOccurrence occurrence) =
        (compileOccurrenceWith? sourceDiagram sourceRecurse
          sourceContext sourceBinders occurrence).map (fun item =>
            (item.renameWires wire).renameRelations relation)) :
    compileOccurrencesWith? targetDiagram targetRecurse
        targetContext targetBinders (sourceOccurrences.map mapOccurrence) =
      (compileOccurrencesWith? sourceDiagram sourceRecurse
        sourceContext sourceBinders sourceOccurrences).map (fun items =>
          (items.renameWires wire).renameRelations relation) := by
  induction sourceOccurrences with
  | nil => rfl
  | cons occurrence tail inductionHypothesis =>
      have head := hoccurrence occurrence (by simp)
      have tailOccurrence : ∀ current, current ∈ tail →
          compileOccurrenceWith? targetDiagram targetRecurse
              targetContext targetBinders (mapOccurrence current) =
            (compileOccurrenceWith? sourceDiagram sourceRecurse
              sourceContext sourceBinders current).map (fun item =>
                (item.renameWires wire).renameRelations relation) := by
        intro current member
        exact hoccurrence current (by simp [member])
      specialize inductionHypothesis tailOccurrence
      cases sourceHead : compileOccurrenceWith? sourceDiagram sourceRecurse
          sourceContext sourceBinders occurrence with
      | none =>
          simp [sourceHead] at head
          simp [compileOccurrencesWith?, sourceHead, head]
      | some sourceItem =>
          simp [sourceHead] at head
          cases sourceTail : compileOccurrencesWith? sourceDiagram
              sourceRecurse sourceContext sourceBinders tail with
          | none =>
              simp [sourceTail] at inductionHypothesis
              simp [compileOccurrencesWith?, sourceHead, sourceTail,
                head, inductionHypothesis]
          | some sourceItems =>
              simp [sourceTail] at inductionHypothesis
              simp [compileOccurrencesWith?, sourceHead, sourceTail,
                head, inductionHypothesis, ItemSeq.renameWires,
                ItemSeq.renameRelations]

/-- Direct terminal-body nodes use only proxy binders, and their binder
lookups commute with the source-derived relation substitution. -/
theorem patternNode_binderMapped
    (layout : PlugLayout input) (admissible : input.Admissible)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (nodeRegion : (input.pattern.val.diagram.nodes node).region =
      input.binderSpine.bodyContainer) :
    ∀ region binder,
      input.pattern.val.diagram.nodes node = .atom region binder →
      layout.mapFrameBinders hostBinders (layout.binderRegion binder) =
        (compiled.siteBinders binder).map fun sourceRelation =>
          ⟨sourceRelation.1,
            compiled.spliceRelationMap input admissible hostBinders
              hostCovers sourceRelation.2⟩ := by
  intro region binder nodeEq
  have regionEq : region = input.binderSpine.bodyContainer :=
    (congrArg CNode.region nodeEq).symm.trans nodeRegion
  subst region
  have binderEncloses : input.pattern.val.diagram.Encloses binder
      input.binderSpine.bodyContainer := by
    have atomEncloses := input.pattern.property.diagram_well_formed
      |>.atom_binders_enclose node
    simpa [nodeEq] using atomEncloses
  obtain ⟨parent, arity, bubble⟩ :=
    BinderContext.checked_atom_binder_is_bubble
      input.pattern.property.diagram_well_formed nodeEq
  obtain ⟨proxy, binderEq, arityEq⟩ :=
    input.binderSpine.enclosing_body_bubble
      input.pattern.property.diagram_well_formed bubble binderEncloses
  subst binder
  rw [layout.binderRegion_proxy, layout.mapFrameBinders_frameRegion]
  cases sourceLookup : compiled.siteBinders
      (input.binderSpine.proxy proxy) with
  | none =>
      obtain ⟨sourceRelation, covered⟩ := compiled.binder_covers
        (input.binderSpine.proxy proxy) parent arity bubble binderEncloses
      simp [sourceLookup] at covered
  | some sourceRelation =>
      rcases sourceRelation with ⟨sourceArity, sourceRelation⟩
      obtain ⟨mappedProxy, mappedBinderEq, hostLookup⟩ :=
        compiled.spliceRelationMap_of_lookup input admissible
          hostBinders hostCovers sourceLookup
      have proxyEq : mappedProxy = proxy :=
        input.binderSpine.proxy_injective
          mappedBinderEq.symm
      subst mappedProxy
      simpa only [Option.map_some] using hostLookup

/-- Compile one direct pattern node through the splice wire and relation
substitutions. -/
theorem compileNode?_patternNode_map
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    (targetDisjoint : layout.plugRaw.WireEndpointsAreDisjoint)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (nodeRegion : (input.pattern.val.diagram.nodes node).region =
      input.binderSpine.bodyContainer) :
    compileNode? layout.plugRaw
        (layout.patternSiteWires consistent hostContext)
        (layout.mapFrameBinders hostBinders) (layout.patternNode node) =
      (compileNode? input.pattern.val.diagram
        (compiled.siteContext ++ compiled.siteLocals)
        compiled.siteBinders node).map (fun item =>
          (item.renameWires
            (layout.patternContextIndexMap consistent admissible compiled
              hostContext hostExact)).renameRelations
                (compiled.spliceRelationMap input admissible hostBinders
                  hostCovers)) := by
  apply compileNode?_map
    (compiled.siteContext ++ compiled.siteLocals)
    (layout.patternSiteWires consistent hostContext)
    compiled.siteBinders (layout.mapFrameBinders hostBinders)
    node (layout.patternNode node) layout.bodyRegion layout.binderRegion
    (layout.patternContextIndexMap consistent admissible compiled
      hostContext hostExact)
    (compiled.spliceRelationMap input admissible hostBinders hostCovers)
  · cases nodeEq : input.pattern.val.diagram.nodes node <;>
      simp [Splice.Input.patternState, PlugLayout.plugRaw,
        PlugLayout.plugNode, PlugLayout.patternNode,
        PlugLayout.mapPatternNode, nodeEq]
  · intro port
    have mapped := layout.resolvePort?_patternNode consistent admissible compiled
      hostContext hostExact targetDisjoint node nodeRegion port
    change resolvePort? layout.plugRaw
        (layout.patternSiteWires consistent hostContext)
        (layout.patternNode node) port =
      (resolvePort? input.pattern.val.diagram
        (compiled.siteContext ++ compiled.siteLocals) node port).map
          (layout.patternContextIndexMap consistent admissible compiled
            hostContext hostExact)
    calc
      _ = (resolvePort? input.pattern.val.diagram compiled.fullWires
          node port).map
            (layout.patternFullIndexMap consistent admissible compiled
              hostContext hostExact) := mapped
      _ = ((resolvePort? input.pattern.val.diagram compiled.fullWires
            node port).map
              (Fin.cast (congrArg List.length compiled.fullWires_eq))).map
            (layout.patternContextIndexMap consistent admissible compiled
              hostContext hostExact) := by
        simp only [Option.map_map]
        rfl
      _ = _ := congrArg (Option.map
        (layout.patternContextIndexMap consistent admissible compiled
          hostContext hostExact))
        (resolvePort?_context_eq compiled.fullWires
          (compiled.siteContext ++ compiled.siteLocals)
          compiled.fullWires_eq node port)
  · exact layout.patternNode_binderMapped admissible compiled
      hostBinders hostCovers node nodeRegion

/-- Exact target compilation of the retained frame-node block. -/
theorem compileFrameNodeBlock
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (sourceContext : WireContext input.frame.val)
    (sourceExact : sourceContext.Exact input.site)
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceFuel : Nat) (sourceItems : ItemSeq sourceContext.length rels)
    (sourceCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val sourceFuel) sourceContext sourceBinders
      (localNodeOccurrences input.frame.val input.site) = some sourceItems)
    (targetFuel : Nat)
    (targetWellFormed : layout.plugRaw.WellFormed) :
    compileOccurrencesWith? layout.plugRaw
        (compileRegion? layout.plugRaw targetFuel)
        (layout.patternSiteWires consistent
          sourceContext)
        (layout.mapFrameBinders sourceBinders)
        (layout.frameNodeOccurrences input.site) =
      some (sourceItems.renameWires
        (layout.frameSiteIndexMap consistent sourceContext)) := by
  rw [← show
      (localNodeOccurrences input.frame.val input.site).map
          layout.mapFrameOccurrence =
        layout.frameNodeOccurrences input.site by
          unfold localNodeOccurrences frameNodeOccurrences mapFrameOccurrence
          simp only [List.map_map]
          rfl]
  have mapped := compileOccurrencesWith?_mapBoth
    (compileRegion? input.frame.val sourceFuel)
    (compileRegion? layout.plugRaw targetFuel)
    sourceContext (layout.patternSiteWires consistent sourceContext)
    sourceBinders (layout.mapFrameBinders sourceBinders)
    layout.mapFrameOccurrence
    (layout.frameSiteIndexMap consistent sourceContext)
    (fun relation => relation)
    (localNodeOccurrences input.frame.val input.site) (by
      intro occurrence member
      obtain ⟨node, nodeMember, occurrenceEq⟩ := List.mem_map.mp member
      subst occurrence
      have nodeRegion :
          (input.frame.val.nodes node).region = input.site :=
        of_decide_eq_true (List.mem_filter.mp nodeMember).2
      simp only [compileOccurrenceWith?, mapFrameOccurrence]
      apply layout.compileNode?_frameNode_map consistent
        sourceContext (layout.patternSiteWires consistent sourceContext)
        sourceBinders (layout.mapFrameBinders sourceBinders)
        node
        (layout.frameSiteIndexMap consistent sourceContext)
        (fun relation => relation)
      · exact layout.patternSiteWires_nodup consistent _ sourceExact
      · exact layout.frameSiteIndexMap_get consistent _
      · intro wire port occurs _
        have wireEncloses := input.frame.property
          |>.wire_scopes_enclose wire ⟨node, port⟩ occurs
        exact (sourceExact.mem_iff wire).2
          (by simpa [nodeRegion] using wireEncloses)
      · exact targetWellFormed.wire_endpoints_are_disjoint
      · intro region binder _
        simp)
  rw [sourceCompiled] at mapped
  simpa only [Option.map_some, ItemSeq.renameRelations_id] using mapped

/-- Exact target compilation of the inserted terminal-body node block. -/
theorem compilePatternNodeBlock
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer)
    (kernel : compiled.Kernel) (blocks : kernel.Blocks)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    (targetFuel : Nat)
    (targetWellFormed : layout.plugRaw.WellFormed) :
    compileOccurrencesWith? layout.plugRaw
        (compileRegion? layout.plugRaw targetFuel)
        (layout.patternSiteWires consistent hostContext)
        (layout.mapFrameBinders hostBinders)
        layout.bodyNodeOccurrences =
      some ((blocks.nodeItems.renameWires
        (layout.patternContextIndexMap consistent admissible compiled
          hostContext hostExact)).renameRelations
            (compiled.spliceRelationMap input admissible hostBinders
              hostCovers)) := by
  rw [← show
      (localNodeOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer).map layout.mapPatternOccurrence =
          layout.bodyNodeOccurrences by
            unfold localNodeOccurrences bodyNodeOccurrences
              mapPatternOccurrence
            simp only [List.map_map]
            rfl]
  have mapped := compileOccurrencesWith?_mapBoth
    (compileRegion? input.pattern.val.diagram kernel.recurseFuel)
    (compileRegion? layout.plugRaw targetFuel)
    (compiled.siteContext ++ compiled.siteLocals)
    (layout.patternSiteWires consistent hostContext)
    compiled.siteBinders (layout.mapFrameBinders hostBinders)
    layout.mapPatternOccurrence
    (layout.patternContextIndexMap consistent admissible compiled
      hostContext hostExact)
    (compiled.spliceRelationMap input admissible hostBinders hostCovers)
    (localNodeOccurrences input.pattern.val.diagram
      input.binderSpine.bodyContainer) (by
        intro occurrence member
        obtain ⟨node, nodeMember, occurrenceEq⟩ := List.mem_map.mp member
        subst occurrence
        have nodeRegion : (input.pattern.val.diagram.nodes node).region =
            input.binderSpine.bodyContainer :=
          of_decide_eq_true (List.mem_filter.mp nodeMember).2
        simp only [compileOccurrenceWith?, mapPatternOccurrence]
        exact layout.compileNode?_patternNode_map consistent admissible
          compiled hostContext hostExact hostBinders hostCovers
          targetWellFormed.wire_endpoints_are_disjoint node nodeRegion)
  have sourceNodeCompiled : compileOccurrencesWith?
      input.pattern.val.diagram
      (compileRegion? input.pattern.val.diagram kernel.recurseFuel)
      (compiled.siteContext ++ compiled.siteLocals) compiled.siteBinders
      (localNodeOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer) = some blocks.nodeItems := by
    simpa [Splice.Input.patternState] using blocks.node_compiled
  rw [sourceNodeCompiled] at mapped
  simpa only [Option.map_some] using mapped

end Splice.Input.PlugLayout

end VisualProof.Concrete
