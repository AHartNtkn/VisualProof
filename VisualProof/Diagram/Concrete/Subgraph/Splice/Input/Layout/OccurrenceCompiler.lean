import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.RootCompiler

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace PlugLayout

/-- Exact compilation transport for one coalesced-host node at the splice
site.  All hypotheses are discharged from checked compiler leaves and concrete
endpoint/binder provenance. -/
theorem compileHostNode_at_site
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Region.ContextPath.CompilerLeaf input.coalesceFrameRaw
      input.site hostWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (node : Fin input.coalesceFrameRaw.nodeCount)
    (hnodeAtSite : (input.coalesceFrameRaw.nodes node).region = input.site) :
    ConcreteElaboration.compileNode? signature layout.plugRaw
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.frameNode node) =
      (ConcreteElaboration.compileNode? signature
        (input.coalesceFrame hadmissible).val
        (hostLeaf.inheritedWires.extend input.site) hostLeaf.binders node).map
          (fun item : Item signature
              (hostLeaf.inheritedWires.extend input.site).length
              hostWitness.toFocus.holeRels =>
            (item.renameWires
              (layout.hostSiteWireIndexMap hostWitness hostLeaf outputWitness
                outputLeaf)).renameRelations
              (layout.hostRelationRenaming hostWitness hostLeaf outputWitness
                outputLeaf)) := by
  apply ConcreteElaboration.compileNode?_map
    (regionMap := layout.frameRegion)
    (binderMap := layout.frameRegion)
    (wireMap := layout.hostSiteWireIndexMap hostWitness hostLeaf outputWitness
      outputLeaf)
    (relationMap := layout.hostRelationRenaming hostWitness hostLeaf
      outputWitness outputLeaf)
  · change layout.plugNode (layout.frameNode node) = _
    rw [layout.plugNode_frameNode]
    cases hsource : input.coalesceFrameRaw.nodes node with
    | term region freePorts term =>
        change input.frame.val.nodes node = .term region freePorts term
          at hsource
        rw [hsource]
        rfl
    | atom region binder =>
        change input.frame.val.nodes node = .atom region binder at hsource
        rw [hsource]
        rfl
    | named region definition arity =>
        change input.frame.val.nodes node = .named region definition arity
          at hsource
        rw [hsource]
        rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence
      (concreteWireMap := layout.frameWire)
      (targetNodup := outputLeaf.wiresExact.nodup)
      (hget := layout.hostSiteWireIndexMap_spec hostWitness hostLeaf
        outputWitness outputLeaf)
      (hmem := layout.frameWire_mem_outputSiteContext_iff hostWitness hostLeaf
        outputWitness outputLeaf)
      (targetDisjoint :=
        (layout.plugRaw_wellFormed signature input hadmissible)
          |>.wire_endpoints_are_disjoint)
    · intro wire requested hoccurs
      simpa [mapFrameEndpoint] using
        layout.plugRaw_frameEndpoint_forward wire
          ⟨node, requested⟩ hoccurs
    · intro targetWire requested hoccurs
      obtain ⟨sourceWire, hwire, hsource⟩ :=
        layout.plugRaw_frameEndpoint_backward targetWire
          ⟨node, requested⟩ (by
            simpa [mapFrameEndpoint] using hoccurs)
      exact ⟨sourceWire, hwire, hsource⟩
  · intro region binder hnode
    have hnodeRegion : (input.coalesceFrameRaw.nodes node).region = region :=
      congrArg CNode.region hnode
    have hregion : region = input.site := by
      exact hnodeRegion.symm.trans hnodeAtSite
    obtain ⟨parent, arity, hbubble⟩ :=
      ConcreteElaboration.BinderContext.checked_atom_binder_is_bubble
        (input.coalesceFrameRaw_wellFormed hadmissible) hnode
    have hencloses : input.coalesceFrameRaw.Encloses binder input.site := by
      have hraw := (input.coalesceFrameRaw_wellFormed hadmissible)
        |>.atom_binders_enclose node
      simp only [hnode] at hraw
      rw [hregion] at hraw
      exact hraw
    obtain ⟨relation, hrelation⟩ := hostLeaf.bindersCover binder parent arity
      hbubble hencloses
    rw [hrelation]
    simp only [Option.map_some]
    have howner := hostLeaf.binderEnumeration.lookup_owner relation hrelation
    rw [← howner]
    exact layout.hostRelationRenaming_lookup hostWitness hostLeaf
      outputWitness outputLeaf relation

/-- Exact compilation transport for one pattern node in the terminal body. -/
theorem compilePatternNode_at_site
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (hnodeAtSite : (input.pattern.val.diagram.nodes node).region =
      input.binderSpine.bodyContainer) :
    ConcreteElaboration.compileNode? signature layout.plugRaw
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders (layout.patternNode node) =
      (ConcreteElaboration.compileNode? signature input.pattern.val.diagram
        (patternLeaf.inheritedWires.extend input.binderSpine.bodyContainer)
        patternLeaf.binders node).map
          (fun item : Item signature
              (patternLeaf.inheritedWires.extend
                input.binderSpine.bodyContainer).length
              patternWitness.toFocus.holeRels =>
            (item.renameWires
              (layout.patternSiteWireIndexMap hadmissible patternWitness
                patternLeaf outputWitness outputLeaf)).renameRelations
              (layout.patternRelationRenaming hadmissible patternWitness
                patternLeaf outputWitness outputLeaf)) := by
  apply ConcreteElaboration.compileNode?_map
    (regionMap := layout.bodyRegion)
    (binderMap := layout.binderRegion)
    (wireMap := layout.patternSiteWireIndexMap hadmissible patternWitness
      patternLeaf outputWitness outputLeaf)
    (relationMap := layout.patternRelationRenaming hadmissible patternWitness
      patternLeaf outputWitness outputLeaf)
  · change layout.plugNode (layout.patternNode node) = _
    rw [layout.plugNode_patternNode]
    cases hsource : input.pattern.val.diagram.nodes node with
    | term => rfl
    | atom => rfl
    | named => rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence
      (concreteWireMap := layout.patternPlugWire)
      (targetNodup := outputLeaf.wiresExact.nodup)
      (hget := layout.patternSiteWireIndexMap_spec hadmissible patternWitness
        patternLeaf outputWitness outputLeaf)
      (hmem := layout.patternPlugWire_mem_outputSiteContext_iff hadmissible
        patternWitness patternLeaf outputWitness outputLeaf)
      (targetDisjoint :=
        (layout.plugRaw_wellFormed signature input hadmissible)
          |>.wire_endpoints_are_disjoint)
    · intro wire requested hoccurs
      simpa [mapPatternEndpoint] using
        layout.plugRaw_patternEndpoint_forward wire
          ⟨node, requested⟩ hoccurs
    · intro targetWire requested hoccurs
      obtain ⟨sourceWire, hwire, hsource⟩ :=
        layout.plugRaw_patternEndpoint_backward targetWire
          ⟨node, requested⟩ (by
            simpa [mapPatternEndpoint] using hoccurs)
      exact ⟨sourceWire, hwire, hsource⟩
  · intro region binder hnode
    have hnodeRegion : (input.pattern.val.diagram.nodes node).region = region :=
      congrArg CNode.region hnode
    have hregion : region = input.binderSpine.bodyContainer :=
      hnodeRegion.symm.trans hnodeAtSite
    obtain ⟨parent, arity, hbubble⟩ :=
      ConcreteElaboration.BinderContext.checked_atom_binder_is_bubble
        input.pattern.property.diagram_well_formed hnode
    have hencloses : input.pattern.val.diagram.Encloses binder
        input.binderSpine.bodyContainer := by
      have hraw := input.pattern.property.diagram_well_formed
        |>.atom_binders_enclose node
      simp only [hnode] at hraw
      rw [hregion] at hraw
      exact hraw
    obtain ⟨relation, hrelation⟩ :=
      patternLeaf.bindersCover binder parent arity hbubble hencloses
    rw [hrelation]
    simp only [Option.map_some]
    have howner :=
      patternLeaf.binderEnumeration.lookup_owner relation hrelation
    rw [← howner]
    exact layout.patternRelationRenaming_lookup hadmissible patternWitness
      patternLeaf outputWitness outputLeaf relation

theorem compileHostNode_at_seam_iso_of_maps
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {preparedWires : Nat}
    (combined : FiniteEquiv (Fin preparedWires)
      (Fin (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)))
    (sourcePreparedMap : Fin
        (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin preparedWires)
    (hfactor : combined.toFun ∘ sourcePreparedMap =
      Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)) ∘
        layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
    (node : Fin input.coalesceFrameRaw.nodeCount)
    (hnodeAtSite : (input.coalesceFrameRaw.nodes node).region = input.site)
    (sourceItem : Item signature
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels)
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileNode? signature
      (input.coalesceFrame hadmissible).val
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders node = some sourceItem)
    (htarget : ConcreteElaboration.compileNode? signature layout.plugRaw
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.frameNode node) = some targetItem) :
    ItemIso signature
      combined
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        sourcePreparedMap).renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  have htransport := layout.compileHostNode_at_site signature input hadmissible
    host.intrinsicPath host.compilerLeaf outputWitness outputLeaf node
    hnodeAtSite
  rw [htarget] at htransport
  let transform := fun item : Item signature
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels =>
    (item.renameWires
      (layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  have hmapped : Option.map transform
        (ConcreteElaboration.compileNode? signature
          (input.coalesceFrame hadmissible).val
          (host.compilerLeaf.inheritedWires.extend input.site)
          host.compilerLeaf.binders node) =
      some (transform sourceItem) := by
    exact (congrArg (Option.map transform) hsource).trans rfl
  have htransport' : targetItem = transform sourceItem :=
    Option.some.inj (htransport.trans hmapped)
  rw [htransport']
  subst targetItem
  let sourcePrepared :=
    (sourceItem.renameWires
      sourcePreparedMap).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
  have hiso := ItemIso.renameWiresEquiv sourcePrepared
    combined
  simpa only [sourcePrepared, transform, Item.castWiresEq_eq_renameWires,
    Item.renameWires_renameRelations, Item.renameWires_comp, hfactor] using hiso

theorem compileHostNode_at_seam_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (node : Fin input.coalesceFrameRaw.nodeCount)
    (hnodeAtSite : (input.coalesceFrameRaw.nodes node).region = input.site)
    (sourceItem : Item signature
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels)
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileNode? signature
      (input.coalesceFrame hadmissible).val
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders node = some sourceItem)
    (htarget : ConcreteElaboration.compileNode? signature layout.plugRaw
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.frameNode node) = some targetItem) :
    ItemIso signature
      (layout.siteCombinedWireEquivOfNonempty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  refine layout.compileHostNode_at_seam_iso_of_maps signature input hadmissible
    host outputWitness outputLeaf
    (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
      outputLeaf hnonempty)
    (layout.hostSeamPreparedWireOfNonempty hadmissible host) ?_
    node hnodeAtSite sourceItem targetItem hsource htarget
  funext index
  have hseam := congrFun
    (layout.hostSeamWireMapOfNonempty_eq hadmissible host outputWitness
      outputLeaf hnonempty) index
  apply Fin.ext
  simpa [Function.comp_def, hostSeamWireMapOfNonempty] using
    congrArg Fin.val hseam

theorem compilePatternNode_at_seam_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (hnodeAtSite : (input.pattern.val.diagram.nodes node).region =
      input.binderSpine.bodyContainer)
    (sourceItem : Item signature
      (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).length
      patternWitness.toFocus.holeRels)
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileNode? signature
      input.pattern.val.diagram
      (patternLeaf.inheritedWires.extend input.binderSpine.bodyContainer)
      patternLeaf.binders node = some sourceItem)
    (htarget : ConcreteElaboration.compileNode? signature layout.plugRaw
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.patternNode node) = some targetItem) :
    ItemIso signature
      (layout.siteCombinedWireEquivOfNonempty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)).renameRelations
        (fun {arity} relation =>
          layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf
            (layout.coalescedTerminalRelationRenaming hadmissible
              host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
              hnonempty relation)))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  have htransport := layout.compilePatternNode_at_site signature input
    hadmissible patternWitness patternLeaf outputWitness outputLeaf node
    hnodeAtSite
  rw [htarget] at htransport
  let transform := fun item : Item signature
      (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).length
      patternWitness.toFocus.holeRels =>
    (item.renameWires
      (layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
        outputWitness outputLeaf)).renameRelations
      (layout.patternRelationRenaming hadmissible patternWitness patternLeaf
        outputWitness outputLeaf)
  have hmapped : Option.map transform
        (ConcreteElaboration.compileNode? signature input.pattern.val.diagram
          (patternLeaf.inheritedWires.extend input.binderSpine.bodyContainer)
          patternLeaf.binders node) = some (transform sourceItem) := by
    exact (congrArg (Option.map transform) hsource).trans rfl
  have htransport' : targetItem = transform sourceItem :=
    Option.some.inj (htransport.trans hmapped)
  rw [htransport']
  let terminalRelations : RelationRenaming
      patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
    fun {arity} relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
  let sourcePrepared :=
    (sourceItem.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty)).renameRelations terminalRelations
  have hiso := ItemIso.renameWiresEquiv sourcePrepared
    (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
      outputLeaf hnonempty)
  have hfactor :
      (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
          outputLeaf hnonempty).toFun ∘
        layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty =
      Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)) ∘
        layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
          outputWitness outputLeaf := by
    funext index
    have hseam := congrFun
      (layout.patternSeamWireMapOfNonempty_eq hadmissible host patternWitness
        patternLeaf outputWitness outputLeaf hnonempty) index
    apply Fin.ext
    simpa [Function.comp_def, patternSeamWireMapOfNonempty] using
      congrArg Fin.val hseam
  have hrelations := layout.terminalRelationRenaming_factor hadmissible
    host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
    outputWitness outputLeaf hnonempty
  simpa only [sourcePrepared, terminalRelations, transform,
    Item.castWiresEq_eq_renameWires, Item.renameWires_renameRelations,
    Item.renameWires_comp, hfactor, hrelations] using hiso

theorem seamRecursiveRegionIso_of_maps
    (combined : FiniteEquiv (Fin sourceCombined) (Fin targetCombined))
    (targetEq : targetOuter = targetCombined)
    (preparedWire : Fin sourceOuter → Fin sourceCombined)
    (directWire : Fin sourceOuter → Fin targetOuter)
    (hwire :
      (combined.trans (FiniteEquiv.finCast targetEq.symm)).toFun ∘
          preparedWire = directWire)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceBody : Region signature sourceOuter sourceRels)
    (targetBody : Region signature targetOuter targetRels)
    (hrecursive : RegionIso signature
      (FiniteEquiv.refl (Fin targetOuter)) targetRels
      ((sourceBody.renameWires directWire).renameRelations relationMap)
      targetBody) :
    RegionIso signature combined targetRels
      ((sourceBody.renameWires preparedWire).renameRelations relationMap)
      (targetBody.castWiresEq targetEq) := by
  let toTargetContext := combined.trans (FiniteEquiv.finCast targetEq.symm)
  let sourcePrepared :=
    (sourceBody.renameWires preparedWire).renameRelations relationMap
  change toTargetContext.toFun ∘ preparedWire = directWire at hwire
  have hfirstRaw := RegionIso.renameWiresEquiv sourcePrepared toTargetContext
  have hfirst : RegionIso signature toTargetContext targetRels sourcePrepared
      ((sourceBody.renameWires directWire).renameRelations relationMap) := by
    simpa only [sourcePrepared, Region.renameWires_renameRelations,
      Region.renameWires_comp, hwire] using hfirstRaw
  have hlastRaw := RegionIso.renameWiresEquiv targetBody
    (FiniteEquiv.finCast targetEq)
  have hlast : RegionIso signature (FiniteEquiv.finCast targetEq) targetRels
      targetBody (targetBody.castWiresEq targetEq) := by
    simpa only [Region.castWiresEq_eq_renameWires,
      FiniteEquiv.finCast] using hlastRaw
  have hcombined := (hfirst.trans hrecursive).trans hlast
  have hequiv :
      (toTargetContext.trans (FiniteEquiv.refl (Fin targetOuter))).trans
          (FiniteEquiv.finCast targetEq) = combined := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  rw [hequiv] at hcombined
  exact hcombined

theorem hostSeamRecursiveRegionIso
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceBody : Region signature
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels)
    (targetBody : Region signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hrecursive : RegionIso signature
      (FiniteEquiv.refl (Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length))
      outputWitness.toFocus.holeRels
      ((sourceBody.renameWires
        (layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
      targetBody) :
    RegionIso signature
      (layout.siteCombinedWireEquivOfNonempty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty)
      outputWitness.toFocus.holeRels
      ((sourceBody.renameWires
        (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
      (Region.castWiresEq
        (target := outputLeaf.inheritedWires.length +
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length)
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))
        targetBody) := by
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let toTargetContext := combined.trans (FiniteEquiv.finCast targetEq.symm)
  let sourcePrepared :=
    (sourceBody.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  have hmap : toTargetContext.toFun ∘
        layout.hostSeamPreparedWireOfNonempty hadmissible host =
      layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf := by
    simpa only [toTargetContext, combined, FiniteEquiv.trans_apply,
      FiniteEquiv.finCast, Function.comp_def] using
      layout.hostSeamWireMapOfNonempty_eq hadmissible host outputWitness
        outputLeaf hnonempty
  have hfirstRaw := RegionIso.renameWiresEquiv sourcePrepared toTargetContext
  have hfirst : RegionIso signature toTargetContext
      outputWitness.toFocus.holeRels sourcePrepared
      ((sourceBody.renameWires
        (layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)) := by
    simpa only [sourcePrepared, Region.renameWires_renameRelations,
      Region.renameWires_comp, hmap] using hfirstRaw
  have hlastRaw := RegionIso.renameWiresEquiv targetBody
    (FiniteEquiv.finCast targetEq)
  have hlast : RegionIso signature (FiniteEquiv.finCast targetEq)
      outputWitness.toFocus.holeRels targetBody
      (targetBody.castWiresEq targetEq) := by
    simpa only [Region.castWiresEq_eq_renameWires,
      FiniteEquiv.finCast] using hlastRaw
  have hcombined := (hfirst.trans hrecursive).trans hlast
  have hequiv :
      (toTargetContext.trans
        (FiniteEquiv.refl
          (Fin (outputLeaf.inheritedWires.extend
            (layout.frameRegion input.site)).length))).trans
          (FiniteEquiv.finCast targetEq) = combined := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  rw [hequiv] at hcombined
  exact hcombined

theorem patternSeamRecursiveRegionIso
    {signature : List Nat} {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (sourceBody : Region signature
      (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).length
      patternWitness.toFocus.holeRels)
    (targetBody : Region signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hrecursive : RegionIso signature
      (FiniteEquiv.refl (Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length))
      outputWitness.toFocus.holeRels
      ((sourceBody.renameWires
        (layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
          outputWitness outputLeaf)).renameRelations
        (layout.patternRelationRenaming hadmissible patternWitness patternLeaf
          outputWitness outputLeaf))
      targetBody) :
    RegionIso signature
      (layout.siteCombinedWireEquivOfNonempty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty)
      outputWitness.toFocus.holeRels
      ((sourceBody.renameWires
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)).renameRelations
        (fun {arity} relation =>
          layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf
            (layout.coalescedTerminalRelationRenaming hadmissible
              host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
              hnonempty relation)))
      (Region.castWiresEq
        (target := outputLeaf.inheritedWires.length +
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion input.site)).length)
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))
        targetBody) := by
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let toTargetContext := combined.trans (FiniteEquiv.finCast targetEq.symm)
  let terminalRelations : RelationRenaming
      patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
    fun {arity} relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
  let sourcePrepared :=
    (sourceBody.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty)).renameRelations terminalRelations
  have hmap : toTargetContext.toFun ∘
        layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty =
      layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
        outputWitness outputLeaf := by
    simpa only [toTargetContext, combined, FiniteEquiv.trans_apply,
      FiniteEquiv.finCast, Function.comp_def] using
      layout.patternSeamWireMapOfNonempty_eq hadmissible host patternWitness
        patternLeaf outputWitness outputLeaf hnonempty
  have hrelations := layout.terminalRelationRenaming_factor hadmissible
    host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
    outputWitness outputLeaf hnonempty
  have hfirstRaw := RegionIso.renameWiresEquiv sourcePrepared toTargetContext
  have hfirst : RegionIso signature toTargetContext
      outputWitness.toFocus.holeRels sourcePrepared
      ((sourceBody.renameWires
        (layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
          outputWitness outputLeaf)).renameRelations
        (layout.patternRelationRenaming hadmissible patternWitness patternLeaf
          outputWitness outputLeaf)) := by
    simpa only [sourcePrepared, terminalRelations,
      Region.renameWires_renameRelations, Region.renameWires_comp, hmap,
      hrelations] using hfirstRaw
  have hlastRaw := RegionIso.renameWiresEquiv targetBody
    (FiniteEquiv.finCast targetEq)
  have hlast : RegionIso signature (FiniteEquiv.finCast targetEq)
      outputWitness.toFocus.holeRels targetBody
      (targetBody.castWiresEq targetEq) := by
    simpa only [Region.castWiresEq_eq_renameWires,
      FiniteEquiv.finCast] using hlastRaw
  have hcombined := (hfirst.trans hrecursive).trans hlast
  have hequiv :
      (toTargetContext.trans
        (FiniteEquiv.refl
          (Fin (outputLeaf.inheritedWires.extend
            (layout.frameRegion input.site)).length))).trans
          (FiniteEquiv.finCast targetEq) = combined := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  rw [hequiv] at hcombined
  exact hcombined

/-- Empty-proxy counterpart of `compilePatternNode_at_site`, using the open
sheet-root compiler context. -/
theorem compilePatternRootNode_at_site
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (hzero : input.binderSpine.proxyCount = 0)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (hnodeAtRoot : (input.pattern.val.diagram.nodes node).region =
      input.pattern.val.diagram.root) :
    ConcreteElaboration.compileNode? signature layout.plugRaw
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders (layout.patternNode node) =
      (ConcreteElaboration.compileNode? signature input.pattern.val.diagram
        (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty node).map
          (fun item : Item signature
              (input.pattern.val.exposedWires ++
                input.pattern.val.hiddenWires).length [] =>
            (item.renameWires
              (layout.patternRootWireIndexMap hadmissible hzero outputWitness
                outputLeaf)).renameRelations
              (emptyRelationRenaming outputWitness.toFocus.holeRels)) := by
  apply ConcreteElaboration.compileNode?_map
    (regionMap := layout.bodyRegion)
    (binderMap := layout.binderRegion)
    (wireMap := layout.patternRootWireIndexMap hadmissible hzero outputWitness
      outputLeaf)
    (relationMap := emptyRelationRenaming outputWitness.toFocus.holeRels)
  · change layout.plugNode (layout.patternNode node) = _
    rw [layout.plugNode_patternNode]
    cases hsource : input.pattern.val.diagram.nodes node with
    | term => rfl
    | atom => rfl
    | named => rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence
      (concreteWireMap := layout.patternPlugWire)
      (targetNodup := outputLeaf.wiresExact.nodup)
      (hget := layout.patternRootWireIndexMap_spec hadmissible hzero
        outputWitness outputLeaf)
      (hmem := layout.patternPlugWire_mem_outputRootContext_iff hadmissible
        hzero outputWitness outputLeaf)
      (targetDisjoint :=
        (layout.plugRaw_wellFormed signature input hadmissible)
          |>.wire_endpoints_are_disjoint)
    · intro wire requested hoccurs
      simpa [mapPatternEndpoint] using
        layout.plugRaw_patternEndpoint_forward wire
          ⟨node, requested⟩ hoccurs
    · intro targetWire requested hoccurs
      obtain ⟨sourceWire, hwire, hsource⟩ :=
        layout.plugRaw_patternEndpoint_backward targetWire
          ⟨node, requested⟩ (by
            simpa [mapPatternEndpoint] using hoccurs)
      exact ⟨sourceWire, hwire, hsource⟩
  · intro region binder hnode
    have hregion : region = input.pattern.val.diagram.root :=
      (congrArg CNode.region hnode).symm.trans hnodeAtRoot
    have hencloses : input.pattern.val.diagram.Encloses binder
        input.pattern.val.diagram.root := by
      have hraw := input.pattern.property.diagram_well_formed
        |>.atom_binders_enclose node
      simp only [hnode] at hraw
      rw [hregion] at hraw
      exact hraw
    have hbinderRoot : binder = input.pattern.val.diagram.root :=
      ConcreteElaboration.encloses_sheet_eq
        input.pattern.property.diagram_well_formed.root_is_sheet hencloses
    obtain ⟨parent, arity, hbubble⟩ :=
      ConcreteElaboration.BinderContext.checked_atom_binder_is_bubble
        input.pattern.property.diagram_well_formed hnode
    rw [hbinderRoot,
      input.pattern.property.diagram_well_formed.root_is_sheet] at hbubble
    contradiction

/-- Empty-proxy root-node compilation, transported through the same seam
equivalence used by the host items. -/
theorem compilePatternRootNode_at_seam_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (hnodeAtRoot : (input.pattern.val.diagram.nodes node).region =
      input.pattern.val.diagram.root)
    (sourceItem : Item signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileNode? signature
      input.pattern.val.diagram
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty node = some sourceItem)
    (htarget : ConcreteElaboration.compileNode? signature layout.plugRaw
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.patternNode node) = some targetItem) :
    ItemIso signature
      (layout.siteCombinedWireEquivOfEmpty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
          |>.renameRelations
            (emptyRelationRenaming outputWitness.toFocus.holeRels))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  have htransport := layout.compilePatternRootNode_at_site signature input
    hadmissible hzero outputWitness outputLeaf node hnodeAtRoot
  rw [htarget] at htransport
  let transform := fun item : Item signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [] =>
    (item.renameWires
      (layout.patternRootWireIndexMap hadmissible hzero outputWitness
        outputLeaf)).renameRelations
      (emptyRelationRenaming outputWitness.toFocus.holeRels)
  have hmapped : Option.map transform
        (ConcreteElaboration.compileNode? signature input.pattern.val.diagram
          (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
          ConcreteElaboration.BinderContext.empty node) =
      some (transform sourceItem) := by
    exact (congrArg (Option.map transform) hsource).trans rfl
  have htransport' : targetItem = transform sourceItem :=
    Option.some.inj (htransport.trans hmapped)
  rw [htransport']
  subst targetItem
  let sourcePrepared :=
    (sourceItem.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        |>.renameRelations
          (emptyRelationRenaming outputWitness.toFocus.holeRels)
  have hiso := ItemIso.renameWiresEquiv sourcePrepared
    (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
      outputLeaf hzero)
  have hfactor :
      (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
          outputLeaf hzero).toFun ∘
        layout.patternRootSeamPreparedWireOfEmpty hadmissible host =
      Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            outputLeaf.inheritedWires (layout.frameRegion input.site)) ∘
        layout.patternRootWireIndexMap hadmissible hzero outputWitness
          outputLeaf := by
    funext index
    have hseam := congrFun
      (layout.patternRootSeamWireMapOfEmpty_eq hadmissible host outputWitness
        outputLeaf hzero) index
    apply Fin.ext
    simpa [Function.comp_def, patternRootSeamWireMapOfEmpty] using
      congrArg Fin.val hseam
  simpa only [sourcePrepared, transform, Item.castWiresEq_eq_renameWires,
    Item.renameWires_renameRelations, Item.renameWires_comp, hfactor] using hiso

/-- Node-kernel transport at every retained material region.  This is the
recursive step used for nested cuts and bubbles. -/
theorem compilePatternNode_at_material
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.bodyRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (hnodeAtRegion : (input.pattern.val.diagram.nodes node).region = region) :
    ConcreteElaboration.compileNode? signature layout.plugRaw targetContext
        targetBinders (layout.patternNode node) =
      (ConcreteElaboration.compileNode? signature input.pattern.val.diagram
        sourceContext sourceBinders node).map
          (fun item : Item signature sourceContext.length sourceRels =>
            (item.renameWires
              (layout.patternMaterialWireIndexMap hadmissible region hregion
                sourceContext targetContext sourceExact targetExact)).renameRelations
                (layout.patternMaterialRelationRenaming hadmissible region
                  hregion sourceBinders targetBinders sourceCover targetCover
                  sourceEnumeration)) := by
  apply ConcreteElaboration.compileNode?_map
    (regionMap := layout.bodyRegion)
    (binderMap := layout.binderRegion)
    (wireMap := layout.patternMaterialWireIndexMap hadmissible region hregion
      sourceContext targetContext sourceExact targetExact)
    (relationMap := layout.patternMaterialRelationRenaming hadmissible region
      hregion sourceBinders targetBinders sourceCover targetCover
      sourceEnumeration)
  · change layout.plugNode (layout.patternNode node) = _
    rw [layout.plugNode_patternNode]
    cases hsource : input.pattern.val.diagram.nodes node with
    | term => rfl
    | atom => rfl
    | named => rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence
      (concreteWireMap := layout.patternPlugWire)
      (targetNodup := targetExact.nodup)
      (hget := layout.patternMaterialWireIndexMap_spec hadmissible region
        hregion sourceContext targetContext sourceExact targetExact)
      (hmem := layout.patternPlugWire_mem_materialContext_iff hadmissible
        region hregion sourceContext targetContext sourceExact targetExact)
      (targetDisjoint :=
        (layout.plugRaw_wellFormed signature input hadmissible)
          |>.wire_endpoints_are_disjoint)
    · intro wire requested hoccurs
      simpa [mapPatternEndpoint] using
        layout.plugRaw_patternEndpoint_forward wire
          ⟨node, requested⟩ hoccurs
    · intro targetWire requested hoccurs
      obtain ⟨sourceWire, hwire, hsource⟩ :=
        layout.plugRaw_patternEndpoint_backward targetWire
          ⟨node, requested⟩ (by
            simpa [mapPatternEndpoint] using hoccurs)
      exact ⟨sourceWire, hwire, hsource⟩
  · intro nodeRegion binder hnode
    have hactualRegion : nodeRegion = region :=
      (congrArg CNode.region hnode).symm.trans hnodeAtRegion
    obtain ⟨parent, arity, hbubble⟩ :=
      ConcreteElaboration.BinderContext.checked_atom_binder_is_bubble
        input.pattern.property.diagram_well_formed hnode
    have hencloses : input.pattern.val.diagram.Encloses binder region := by
      have hraw := input.pattern.property.diagram_well_formed
        |>.atom_binders_enclose node
      simp only [hnode] at hraw
      rw [hactualRegion] at hraw
      exact hraw
    obtain ⟨relation, hrelation⟩ :=
      sourceCover binder parent arity hbubble hencloses
    rw [hrelation]
    simp only [Option.map_some]
    have howner := sourceEnumeration.lookup_owner relation hrelation
    rw [← howner]
    exact layout.patternMaterialRelationRenaming_lookup hadmissible region
      hregion sourceBinders targetBinders sourceCover targetCover
      sourceEnumeration relation

/-- Choice-independent form of `compilePatternNode_at_material`.  Recursive
compiler proofs can carry concrete lookup contracts and recover the canonical
maps only at this kernel boundary. -/
theorem compilePatternNode_at_material_of_maps
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.bodyRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      layout.patternPlugWire (sourceContext.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (hnodeAtRegion : (input.pattern.val.diagram.nodes node).region = region) :
    ConcreteElaboration.compileNode? signature layout.plugRaw targetContext
        targetBinders (layout.patternNode node) =
      (ConcreteElaboration.compileNode? signature input.pattern.val.diagram
        sourceContext sourceBinders node).map
          (fun item : Item signature sourceContext.length sourceRels =>
            (item.renameWires wireMap).renameRelations relationMap) := by
  have hwire : wireMap =
      layout.patternMaterialWireIndexMap hadmissible region hregion
        sourceContext targetContext sourceExact targetExact :=
    layout.patternMaterialWireIndexMap_eq hadmissible region hregion
      sourceContext targetContext sourceExact targetExact wireMap wireSpec
  have hrelation :
      ((fun {arity} (relation : Theory.RelVar sourceRels arity) =>
        relationMap relation) : RelationRenaming sourceRels targetRels) =
      ((fun {arity} (relation : Theory.RelVar sourceRels arity) =>
        layout.patternMaterialRelationRenaming hadmissible region hregion
          sourceBinders targetBinders sourceCover targetCover sourceEnumeration
          relation) : RelationRenaming sourceRels targetRels) := by
    apply @funext
    intro arity
    funext relation
    exact layout.patternMaterialRelationRenaming_eq hadmissible region hregion
      sourceBinders targetBinders sourceCover targetCover sourceEnumeration
      relationMap relationSpec relation
  rw [hwire, hrelation]
  exact layout.compilePatternNode_at_material signature input hadmissible region
    hregion sourceContext targetContext sourceExact targetExact sourceBinders
    targetBinders sourceCover targetCover sourceEnumeration node hnodeAtRegion

theorem compilePatternNode_at_material_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceOuter : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.bodyRegion region)).Exact
        (layout.bodyRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.patternPlugWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (hnodeAtRegion : (input.pattern.val.diagram.nodes node).region = region)
    (sourceItem : Item signature (sourceOuter.extend region).length sourceRels)
    (targetItem : Item signature
      (targetOuter.extend (layout.bodyRegion region)).length targetRels)
    (hsource : ConcreteElaboration.compileNode? signature
      input.pattern.val.diagram (sourceOuter.extend region) sourceBinders node =
        some sourceItem)
    (htarget : ConcreteElaboration.compileNode? signature layout.plugRaw
      (targetOuter.extend (layout.bodyRegion region)) targetBinders
        (layout.patternNode node) =
        some targetItem) :
    ItemIso signature
      (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
        (layout.materialLocalWireEquiv region hregion)) targetRels
      ((sourceItem.renameWires
        (layout.materialSourceExtendedWireMap region sourceOuter targetOuter
          outerMap)).renameRelations relationMap)
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.bodyRegion region))) := by
  let extendedMap := layout.materialExtendedWireMap region hregion
    sourceOuter targetOuter outerMap
  have hextendedSpec := layout.materialExtendedWireMap_spec region hregion
    sourceOuter targetOuter outerMap outerSpec
  have htransport := layout.compilePatternNode_at_material_of_maps signature
    input hadmissible region hregion (sourceOuter.extend region)
    (targetOuter.extend (layout.bodyRegion region)) sourceExact targetExact
    sourceBinders targetBinders sourceCover targetCover
    sourceEnumeration extendedMap hextendedSpec relationMap relationSpec node
    hnodeAtRegion
  rw [hsource, htarget] at htransport
  simp only [Option.map_some, Option.some.injEq] at htransport
  subst targetItem
  have hiso := ItemIso.renameWiresEquiv
    ((sourceItem.renameWires
      (layout.materialSourceExtendedWireMap region sourceOuter targetOuter
        outerMap)).renameRelations relationMap)
    (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
      (layout.materialLocalWireEquiv region hregion))
  have hfactor :
      (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
          (layout.materialLocalWireEquiv region hregion)).toFun ∘
          layout.materialSourceExtendedWireMap region sourceOuter targetOuter
            outerMap =
        Fin.cast
            (ConcreteElaboration.WireContext.length_extend targetOuter
              (layout.bodyRegion region)) ∘
          extendedMap := by
    funext index
    have h := congrFun
      (layout.materialExtendedWireMap_factor region hregion sourceOuter
        targetOuter outerMap) index
    apply Fin.ext
    simpa using congrArg (fun mapped => mapped.val) h
  simpa only [Item.castWiresEq_eq_renameWires,
    Item.renameWires_renameRelations, Item.renameWires_comp,
    hfactor] using hiso

theorem materialRecursiveRegionIso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceOuter : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceBody : Region signature (sourceOuter.extend region).length sourceRels)
    (targetBody : Region signature
      (targetOuter.extend (layout.bodyRegion region)).length targetRels)
    (hrecursive : RegionIso signature
      (FiniteEquiv.refl
        (Fin (targetOuter.extend (layout.bodyRegion region)).length)) targetRels
      ((sourceBody.renameWires
        (layout.materialExtendedWireMap region hregion sourceOuter targetOuter
          outerMap)).renameRelations relationMap)
      targetBody) :
    RegionIso signature
      (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
        (layout.materialLocalWireEquiv region hregion)) targetRels
      ((sourceBody.renameWires
        (layout.materialSourceExtendedWireMap region sourceOuter targetOuter
          outerMap)).renameRelations relationMap)
      (targetBody.castWiresEq
        (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.bodyRegion region))) := by
  let extended := extendWireEquiv
    (FiniteEquiv.refl (Fin targetOuter.length))
    (layout.materialLocalWireEquiv region hregion)
  let targetEq := ConcreteElaboration.WireContext.length_extend targetOuter
    (layout.bodyRegion region)
  let toTargetContext := extended.trans (FiniteEquiv.finCast targetEq.symm)
  let sourcePrepared :=
    (sourceBody.renameWires
      (layout.materialSourceExtendedWireMap region sourceOuter targetOuter
        outerMap)).renameRelations relationMap
  have hmap : toTargetContext.toFun ∘
        layout.materialSourceExtendedWireMap region sourceOuter targetOuter
          outerMap =
      layout.materialExtendedWireMap region hregion sourceOuter targetOuter
        outerMap := by
    simpa only [toTargetContext, extended, FiniteEquiv.trans_apply,
      FiniteEquiv.finCast] using
      layout.materialExtendedWireMap_factor region hregion sourceOuter
        targetOuter outerMap
  have hfirstRaw := RegionIso.renameWiresEquiv sourcePrepared toTargetContext
  have hfirst : RegionIso signature toTargetContext targetRels sourcePrepared
      ((sourceBody.renameWires
        (layout.materialExtendedWireMap region hregion sourceOuter targetOuter
          outerMap)).renameRelations relationMap) := by
    simpa only [sourcePrepared, Region.renameWires_renameRelations,
      Region.renameWires_comp, hmap] using hfirstRaw
  have hlastRaw := RegionIso.renameWiresEquiv targetBody
    (FiniteEquiv.finCast targetEq)
  have hlast : RegionIso signature (FiniteEquiv.finCast targetEq) targetRels
      targetBody (targetBody.castWiresEq targetEq) := by
    simpa only [Region.castWiresEq_eq_renameWires,
      FiniteEquiv.finCast] using hlastRaw
  have hcombined := (hfirst.trans hrecursive).trans hlast
  have hextended :
      (toTargetContext.trans
        (FiniteEquiv.refl
          (Fin (targetOuter.extend (layout.bodyRegion region)).length))).trans
          (FiniteEquiv.finCast targetEq) = extended := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  rw [hextended] at hcombined
  exact hcombined

theorem compilePatternRegion_at_material
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceOuter : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.bodyRegion region)).Exact
        (layout.bodyRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.pattern.val.diagram sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.patternPlugWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (sourceBody : Region signature sourceOuter.length sourceRels)
    (targetBody : Region signature targetOuter.length targetRels)
    (hsource : ConcreteElaboration.compileRegion? signature
      input.pattern.val.diagram sourceFuel region sourceOuter sourceBinders =
        some sourceBody)
    (htarget : ConcreteElaboration.compileRegion? signature layout.plugRaw
      targetFuel (layout.bodyRegion region) targetOuter targetBinders =
        some targetBody) :
    RegionIso signature (FiniteEquiv.refl (Fin targetOuter.length)) targetRels
      ((sourceBody.renameWires outerMap).renameRelations relationMap)
      targetBody := by
  induction sourceFuel generalizing targetFuel region sourceOuter targetOuter
      sourceRels targetRels sourceBinders targetBinders sourceBody targetBody with
  | zero => simp [ConcreteElaboration.compileRegion?] at hsource
  | succ sourceFuel ih =>
      cases targetFuel with
      | zero => simp [ConcreteElaboration.compileRegion?] at htarget
      | succ targetFuel =>
          let sourceExtended := sourceOuter.extend region
          let targetExtended := targetOuter.extend (layout.bodyRegion region)
          let localEquiv := layout.materialLocalWireEquiv region hregion
          let extended := extendWireEquiv
            (FiniteEquiv.refl (Fin targetOuter.length)) localEquiv
          let sourceWireMap := layout.materialSourceExtendedWireMap region
            sourceOuter targetOuter outerMap
          let targetEq := ConcreteElaboration.WireContext.length_extend targetOuter
            (layout.bodyRegion region)
          have hoccurrence : ∀
              (occurrence : ConcreteElaboration.LocalOccurrence
                input.pattern.val.diagram.regionCount
                input.pattern.val.diagram.nodeCount),
              occurrence ∈ ConcreteElaboration.localOccurrences
                input.pattern.val.diagram region →
              ∀ (sourceItem : Item signature sourceExtended.length sourceRels)
                (targetItem : Item signature targetExtended.length targetRels),
              ConcreteElaboration.compileOccurrenceWith? signature
                  input.pattern.val.diagram
                  (ConcreteElaboration.compileRegion? signature
                    input.pattern.val.diagram sourceFuel)
                  sourceExtended sourceBinders occurrence = some sourceItem →
              ConcreteElaboration.compileOccurrenceWith? signature layout.plugRaw
                  (ConcreteElaboration.compileRegion? signature layout.plugRaw
                    targetFuel)
                  targetExtended targetBinders
                  (layout.mapPatternOccurrence occurrence) = some targetItem →
              ItemIso signature extended targetRels
                ((sourceItem.renameWires sourceWireMap).renameRelations relationMap)
                (targetItem.castWiresEq targetEq) := by
            intro occurrence hoccurrenceMem sourceItem targetItem
              hsourceItem htargetItem
            cases occurrence with
            | node node =>
                have hnodeRegion :=
                  (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
                    hoccurrenceMem
                exact layout.compilePatternNode_at_material_iso signature input
                  hadmissible region hregion sourceOuter targetOuter sourceExact
                  targetExact sourceBinders targetBinders sourceCover targetCover
                  sourceEnumeration outerMap outerSpec relationMap relationSpec node
                  hnodeRegion sourceItem targetItem
                  (by simpa [sourceExtended,
                    ConcreteElaboration.compileOccurrenceWith?] using hsourceItem)
                  (by simpa [targetExtended, mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?] using htargetItem)
            | child child =>
                have hparent :=
                  (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
                    hoccurrenceMem
                have hchildMaterial := directChildOfMaterial_material input region
                  child hregion hparent
                cases hchild : input.pattern.val.diagram.regions child with
                | sheet => simp [ConcreteElaboration.compileOccurrenceWith?, hchild]
                    at hsourceItem
                | cut parent =>
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparent
                    subst parent
                    have htargetChild := layout.plugRaw_bodyRegion_cut child region
                      hchildMaterial hchild
                    have hsourceChildExact := sourceExact.extend_child
                      input.pattern.property.diagram_well_formed hparent
                    have htargetChildExact := targetExact.extend_child
                      (layout.plugRaw_wellFormed signature input hadmissible)
                      (layout.bodyRegion_parent_exact child region hchildMaterial
                        hparent)
                    cases hsourceChild : ConcreteElaboration.compileRegion? signature
                        input.pattern.val.diagram sourceFuel child sourceExtended
                        sourceBinders with
                    | none =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                    | some compiledSource =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                        subst sourceItem
                        cases htargetChildResult :
                            ConcreteElaboration.compileRegion? signature layout.plugRaw
                              targetFuel (layout.bodyRegion child) targetExtended
                              targetBinders with
                        | none =>
                            simp [mapPatternOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                        | some compiledTarget =>
                            simp [mapPatternOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                            subst targetItem
                            have hrecursive := ih targetFuel child hchildMaterial sourceExtended
                              targetExtended hsourceChildExact htargetChildExact
                              sourceBinders targetBinders
                              (ConcreteElaboration.BinderContext.covers_cut_child
                                sourceCover hchild)
                              (ConcreteElaboration.BinderContext.covers_cut_child
                                targetCover htargetChild)
                              (sourceEnumeration.cutChild
                                input.pattern.property.diagram_well_formed hchild)
                              (layout.materialExtendedWireMap region hregion sourceOuter
                                targetOuter outerMap)
                              (layout.materialExtendedWireMap_spec region hregion
                                sourceOuter targetOuter outerMap outerSpec)
                              relationMap
                              (layout.materialRelationLookup_cutChild region child
                                sourceBinders targetBinders sourceEnumeration hchild
                                relationMap relationSpec)
                              compiledSource compiledTarget hsourceChild
                              htargetChildResult
                            have htransport :=
                              layout.materialRecursiveRegionIso signature input region
                                hregion sourceOuter targetOuter outerMap
                                relationMap compiledSource compiledTarget hrecursive
                            simpa [Item.renameWires, Item.renameRelations] using
                              ItemIso.cut htransport
                | bubble parent arity =>
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparent
                    subst parent
                    have htargetChild := layout.plugRaw_bodyRegion_bubble child region
                      arity hchildMaterial hchild
                    have hsourceChildExact := sourceExact.extend_child
                      input.pattern.property.diagram_well_formed hparent
                    have htargetChildExact := targetExact.extend_child
                      (layout.plugRaw_wellFormed signature input hadmissible)
                      (layout.bodyRegion_parent_exact child region hchildMaterial
                        hparent)
                    cases hsourceChild : ConcreteElaboration.compileRegion? signature
                        input.pattern.val.diagram sourceFuel child sourceExtended
                        (sourceBinders.push child arity) with
                    | none =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                    | some compiledSource =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                        subst sourceItem
                        cases htargetChildResult :
                            ConcreteElaboration.compileRegion? signature layout.plugRaw
                              targetFuel (layout.bodyRegion child) targetExtended
                              (targetBinders.push (layout.bodyRegion child) arity) with
                        | none =>
                            simp [mapPatternOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                        | some compiledTarget =>
                            simp [mapPatternOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                            subst targetItem
                            have hrecursive := ih targetFuel child hchildMaterial sourceExtended
                              targetExtended hsourceChildExact htargetChildExact
                              (sourceBinders.push child arity)
                              (targetBinders.push (layout.bodyRegion child) arity)
                              (ConcreteElaboration.BinderContext.push_covers_bubble_child
                                sourceCover hchild)
                              (ConcreteElaboration.BinderContext.push_covers_bubble_child
                                targetCover htargetChild)
                              (sourceEnumeration.bubbleChild
                                input.pattern.property.diagram_well_formed hchild)
                              (layout.materialExtendedWireMap region hregion sourceOuter
                                targetOuter outerMap)
                              (layout.materialExtendedWireMap_spec region hregion
                                sourceOuter targetOuter outerMap outerSpec)
                              (RelationRenaming.lift relationMap arity)
                              (layout.materialRelationLookup_bubbleChild region child
                                hregion sourceBinders targetBinders sourceEnumeration
                                arity hchild relationMap relationSpec)
                              compiledSource compiledTarget hsourceChild
                              htargetChildResult
                            have htransport :=
                              layout.materialRecursiveRegionIso signature input region
                                hregion sourceOuter targetOuter outerMap
                                (RelationRenaming.lift relationMap arity)
                                compiledSource compiledTarget hrecursive
                            simpa [Item.renameWires, Item.renameRelations] using
                              ItemIso.bubble htransport
          simp only [ConcreteElaboration.compileRegion?] at hsource htarget
          cases hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
              input.pattern.val.diagram
              (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
                sourceFuel) sourceExtended sourceBinders
              (ConcreteElaboration.localOccurrences input.pattern.val.diagram region) with
          | none => simp [sourceExtended, hsourceItems] at hsource
          | some sourceItems =>
              simp [sourceExtended, hsourceItems] at hsource
              subst sourceBody
              cases htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
                  layout.plugRaw
                  (ConcreteElaboration.compileRegion? signature layout.plugRaw targetFuel)
                  targetExtended targetBinders
                  (ConcreteElaboration.localOccurrences layout.plugRaw
                    (layout.bodyRegion region)) with
              | none => simp [targetExtended, htargetItems] at htarget
              | some targetItems =>
                  simp [targetExtended, htargetItems] at htarget
                  subst targetBody
                  let sourcePrepared :=
                    (sourceItems.renameWires sourceWireMap).renameRelations relationMap
                  let targetPrepared := targetItems.castWiresEq targetEq
                  have hsourceLength :=
                    ConcreteElaboration.compileOccurrencesWith?_length
                      (ConcreteElaboration.compileRegion? signature
                        input.pattern.val.diagram sourceFuel)
                      sourceExtended sourceBinders hsourceItems
                  have htargetLength :=
                    ConcreteElaboration.compileOccurrencesWith?_length
                      (ConcreteElaboration.compileRegion? signature layout.plugRaw
                        targetFuel) targetExtended targetBinders htargetItems
                  have hsourcePreparedLength : sourcePrepared.length =
                      (ConcreteElaboration.localOccurrences
                        input.pattern.val.diagram region).length := by
                    simp [sourcePrepared, hsourceLength]
                  have htargetPreparedLength : targetPrepared.length =
                      (ConcreteElaboration.localOccurrences layout.plugRaw
                        (layout.bodyRegion region)).length := by
                    simp [targetPrepared, htargetLength]
                  let positions :=
                    (FiniteEquiv.finCast hsourcePreparedLength).trans
                      ((layout.materialOccurrenceEquiv region hregion).trans
                        (FiniteEquiv.finCast htargetPreparedLength.symm))
                  have hitems : ItemSeqIso signature extended targetRels
                      sourcePrepared targetPrepared := by
                    apply ItemSeqIso.permute positions
                    intro sourceIndex
                    let occurrenceIndex := Fin.cast hsourcePreparedLength sourceIndex
                    let targetOccurrenceIndex :=
                      layout.materialOccurrenceEquiv region hregion occurrenceIndex
                    let sourceOriginalIndex := Fin.cast hsourceLength.symm occurrenceIndex
                    let targetOriginalIndex :=
                      Fin.cast htargetLength.symm targetOccurrenceIndex
                    have hsourceGet :=
                      ConcreteElaboration.compileOccurrencesWith?_get
                        (ConcreteElaboration.compileRegion? signature
                          input.pattern.val.diagram sourceFuel)
                        sourceExtended sourceBinders hsourceItems occurrenceIndex
                    have htargetGet :=
                      ConcreteElaboration.compileOccurrencesWith?_get
                        (ConcreteElaboration.compileRegion? signature layout.plugRaw
                          targetFuel) targetExtended targetBinders htargetItems
                          targetOccurrenceIndex
                    rw [layout.materialOccurrenceEquiv_spec region hregion
                      occurrenceIndex] at htargetGet
                    have hitem := hoccurrence
                      ((ConcreteElaboration.localOccurrences
                        input.pattern.val.diagram region).get occurrenceIndex)
                      (List.get_mem _ occurrenceIndex)
                      (sourceItems.get sourceOriginalIndex)
                      (targetItems.get targetOriginalIndex) hsourceGet htargetGet
                    have hsourcePosition :
                        Fin.cast
                          (ItemSeq.renameRelations_length
                            (sourceItems.renameWires sourceWireMap) relationMap).symm
                          (sourceItems.renameWiresPositionEquiv sourceWireMap
                            sourceOriginalIndex) = sourceIndex := by
                      apply Fin.ext
                      rfl
                    have htargetPosition :
                        Fin.cast
                          (ItemSeq.castWiresEq_length targetEq targetItems).symm
                          targetOriginalIndex = positions sourceIndex := by
                      apply Fin.ext
                      rfl
                    rw [← htargetPosition, ← hsourcePosition]
                    simpa only [sourcePrepared, targetPrepared,
                      ItemSeq.get_renameRelations, ItemSeq.get_renameWires,
                      ItemSeq.get_castWiresEq] using hitem
                  rw [layout.finishRegion_renameWires_renameRelations region
                    sourceOuter targetOuter outerMap relationMap sourceItems]
                  simpa only [ConcreteElaboration.finishRegion, sourcePrepared,
                    targetPrepared, localEquiv, extended, targetEq] using
                    RegionIso.mk (layout.materialLocalWireEquiv region hregion) hitems

/-- Exact compiler simulation for any retained frame region whose subtree
cannot cross the splice site.  The two admissible geometries are strict
descent below the site and a disjoint sibling subtree. -/
theorem compileFrameRegion_off_site
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (hposition :
      input.coalesceFrameRaw.Encloses input.site region ∨
        ¬ input.coalesceFrameRaw.Encloses region input.site)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.frameRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (sourceBody : Region signature sourceOuter.length sourceRels)
    (targetBody : Region signature targetOuter.length targetRels)
    (hsource : ConcreteElaboration.compileRegion? signature
      input.coalesceFrameRaw sourceFuel region sourceOuter sourceBinders =
        some sourceBody)
    (htarget : ConcreteElaboration.compileRegion? signature layout.plugRaw
      targetFuel (layout.frameRegion region) targetOuter targetBinders =
        some targetBody) :
    Nonempty (RegionIsoPresentation signature
      (FiniteEquiv.refl (Fin targetOuter.length)) targetRels
      ((sourceBody.renameWires outerMap).renameRelations relationMap)
      targetBody) := by
  induction sourceFuel generalizing targetFuel region sourceOuter targetOuter
      sourceRels targetRels sourceBinders targetBinders sourceBody targetBody with
  | zero => simp [ConcreteElaboration.compileRegion?] at hsource
  | succ sourceFuel ih =>
      cases targetFuel with
      | zero => simp [ConcreteElaboration.compileRegion?] at htarget
      | succ targetFuel =>
          let sourceExtended := sourceOuter.extend region
          let targetExtended := targetOuter.extend (layout.frameRegion region)
          let localEquiv := layout.frameLocalWireEquiv region hne
          let extended := extendWireEquiv
            (FiniteEquiv.refl (Fin targetOuter.length)) localEquiv
          let sourceWireMap := layout.frameSourceExtendedWireMap region
            sourceOuter targetOuter outerMap
          let targetEq := ConcreteElaboration.WireContext.length_extend targetOuter
            (layout.frameRegion region)
          have hoccurrence : ∀
              (occurrence : ConcreteElaboration.LocalOccurrence
                input.coalesceFrameRaw.regionCount
                input.coalesceFrameRaw.nodeCount),
              occurrence ∈ ConcreteElaboration.localOccurrences
                input.coalesceFrameRaw region →
              ∀ (sourceItem : Item signature sourceExtended.length sourceRels)
                (targetItem : Item signature targetExtended.length targetRels),
              ConcreteElaboration.compileOccurrenceWith? signature
                  input.coalesceFrameRaw
                  (ConcreteElaboration.compileRegion? signature
                    input.coalesceFrameRaw sourceFuel)
                  sourceExtended sourceBinders occurrence = some sourceItem →
              ConcreteElaboration.compileOccurrenceWith? signature layout.plugRaw
                  (ConcreteElaboration.compileRegion? signature layout.plugRaw
                    targetFuel)
                  targetExtended targetBinders
                  (layout.mapFrameOccurrence occurrence) = some targetItem →
              ItemIso signature extended targetRels
                ((sourceItem.renameWires sourceWireMap).renameRelations relationMap)
                (targetItem.castWiresEq targetEq) := by
            intro occurrence hoccurrenceMem sourceItem targetItem
              hsourceItem htargetItem
            cases occurrence with
            | node node =>
                have hnodeRegion :=
                  (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
                    hoccurrenceMem
                exact layout.compileFrameNode_at_region_iso signature input
                  hadmissible region hne sourceOuter targetOuter sourceExact
                  targetExact sourceBinders targetBinders sourceCover
                  sourceEnumeration outerMap outerSpec relationMap relationSpec node
                  hnodeRegion sourceItem targetItem
                  (by simpa [sourceExtended,
                    ConcreteElaboration.compileOccurrenceWith?] using hsourceItem)
                  (by simpa [targetExtended, mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?] using htargetItem)
            | child child =>
                have hparent :=
                  (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
                    hoccurrenceMem
                change (input.frame.val.regions child).parent? =
                  some region at hparent
                have hparentChild : input.coalesceFrameRaw.Encloses region child := by
                  refine ⟨⟨1, by
                    have := child.isLt
                    omega⟩, ?_⟩
                  simp [ConcreteDiagram.climb, hparent]
                have hchildPosition :
                    input.coalesceFrameRaw.Encloses input.site child ∨
                      ¬ input.coalesceFrameRaw.Encloses child input.site := by
                  rcases hposition with hbelow | haway
                  · exact Or.inl (ConcreteElaboration.checked_encloses_trans
                      (input.coalesceFrameRaw_wellFormed hadmissible)
                      hbelow hparentChild)
                  · exact Or.inr fun hchildSite => haway
                      (ConcreteElaboration.checked_encloses_trans
                        (input.coalesceFrameRaw_wellFormed hadmissible)
                        hparentChild hchildSite)
                have hchildNeSite : child ≠ input.site := by
                  rcases hposition with hbelow | haway
                  · intro heq
                    subst child
                    exact ConcreteElaboration.checked_direct_child_not_encloses_parent
                      (input.coalesceFrameRaw_wellFormed hadmissible) hparent hbelow
                  · intro heq
                    exact haway (heq ▸ hparentChild)
                cases hchild : input.frame.val.regions child with
                | sheet => simp [ConcreteElaboration.compileOccurrenceWith?, hchild]
                    at hsourceItem
                | cut parent =>
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparent
                    subst parent
                    have htargetChild := layout.plugRaw_frameRegion_cut child region
                      hchild
                    have htargetParent :
                        (layout.plugRaw.regions
                          (layout.frameRegion child)).parent? =
                            some (layout.frameRegion region) := by
                      simpa [CRegion.parent?] using
                        congrArg CRegion.parent? htargetChild
                    have hsourceChildExact := sourceExact.extend_child
                      (input.coalesceFrameRaw_wellFormed hadmissible) hparent
                    have htargetChildExact := targetExact.extend_child
                      (layout.plugRaw_wellFormed signature input hadmissible)
                      htargetParent
                    cases hsourceChild : ConcreteElaboration.compileRegion? signature
                        input.coalesceFrameRaw sourceFuel child sourceExtended
                        sourceBinders with
                    | none =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                    | some compiledSource =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                        subst sourceItem
                        cases htargetChildResult :
                            ConcreteElaboration.compileRegion? signature layout.plugRaw
                              targetFuel (layout.frameRegion child) targetExtended
                              targetBinders with
                        | none =>
                            simp [mapFrameOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                        | some compiledTarget =>
                            simp [mapFrameOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                            subst targetItem
                            obtain ⟨hrecursive⟩ := ih targetFuel child hchildNeSite
                              hchildPosition sourceExtended targetExtended
                              hsourceChildExact htargetChildExact sourceBinders
                              targetBinders
                              (ConcreteElaboration.BinderContext.covers_cut_child
                                sourceCover hchild)
                              (ConcreteElaboration.BinderContext.covers_cut_child
                                targetCover htargetChild)
                              (sourceEnumeration.cutChild
                                (input.coalesceFrameRaw_wellFormed hadmissible)
                                hchild)
                              (layout.frameExtendedWireMap region hne sourceOuter
                                targetOuter outerMap)
                              (layout.frameExtendedWireMap_spec region hne
                                sourceOuter targetOuter outerMap outerSpec)
                              relationMap
                              (layout.frameRelationLookup_cutChild hadmissible
                                region child sourceBinders targetBinders
                                sourceEnumeration hchild relationMap relationSpec)
                              compiledSource compiledTarget hsourceChild
                              htargetChildResult
                            have htransport :=
                              layout.frameRecursiveRegionIso signature input region
                                hne sourceOuter targetOuter outerMap relationMap
                                compiledSource compiledTarget hrecursive.iso
                            simpa [Item.renameWires, Item.renameRelations] using
                              ItemIso.cut htransport
                | bubble parent arity =>
                    have hparentEq : parent = region := by
                      simpa [hchild, CRegion.parent?] using hparent
                    subst parent
                    have htargetChild := layout.plugRaw_frameRegion_bubble child
                      region arity hchild
                    have htargetParent :
                        (layout.plugRaw.regions
                          (layout.frameRegion child)).parent? =
                            some (layout.frameRegion region) := by
                      simpa [CRegion.parent?] using
                        congrArg CRegion.parent? htargetChild
                    have hsourceChildExact := sourceExact.extend_child
                      (input.coalesceFrameRaw_wellFormed hadmissible) hparent
                    have htargetChildExact := targetExact.extend_child
                      (layout.plugRaw_wellFormed signature input hadmissible)
                      htargetParent
                    cases hsourceChild : ConcreteElaboration.compileRegion? signature
                        input.coalesceFrameRaw sourceFuel child sourceExtended
                        (sourceBinders.push child arity) with
                    | none =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                    | some compiledSource =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                          hsourceChild] at hsourceItem
                        subst sourceItem
                        cases htargetChildResult :
                            ConcreteElaboration.compileRegion? signature layout.plugRaw
                              targetFuel (layout.frameRegion child) targetExtended
                              (targetBinders.push (layout.frameRegion child) arity) with
                        | none =>
                            simp [mapFrameOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                        | some compiledTarget =>
                            simp [mapFrameOccurrence,
                              ConcreteElaboration.compileOccurrenceWith?,
                              htargetChild, htargetChildResult] at htargetItem
                            subst targetItem
                            obtain ⟨hrecursive⟩ := ih targetFuel child hchildNeSite
                              hchildPosition sourceExtended targetExtended
                              hsourceChildExact htargetChildExact
                              (sourceBinders.push child arity)
                              (targetBinders.push (layout.frameRegion child) arity)
                              (ConcreteElaboration.BinderContext.push_covers_bubble_child
                                sourceCover hchild)
                              (ConcreteElaboration.BinderContext.push_covers_bubble_child
                                targetCover htargetChild)
                              (sourceEnumeration.bubbleChild
                                (input.coalesceFrameRaw_wellFormed hadmissible)
                                hchild)
                              (layout.frameExtendedWireMap region hne sourceOuter
                                targetOuter outerMap)
                              (layout.frameExtendedWireMap_spec region hne
                                sourceOuter targetOuter outerMap outerSpec)
                              (RelationRenaming.lift relationMap arity)
                              (layout.frameRelationLookup_bubbleChild hadmissible
                                region child sourceBinders targetBinders
                                sourceEnumeration arity hchild relationMap
                                relationSpec)
                              compiledSource compiledTarget hsourceChild
                              htargetChildResult
                            have htransport :=
                              layout.frameRecursiveRegionIso signature input region
                                hne sourceOuter targetOuter outerMap
                                (RelationRenaming.lift relationMap arity)
                                compiledSource compiledTarget hrecursive.iso
                            simpa [Item.renameWires, Item.renameRelations] using
                              ItemIso.bubble htransport
          simp only [ConcreteElaboration.compileRegion?] at hsource htarget
          cases hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
              input.coalesceFrameRaw
              (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
                sourceFuel) sourceExtended sourceBinders
              (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region) with
          | none => simp [sourceExtended, hsourceItems] at hsource
          | some sourceItems =>
              simp [sourceExtended, hsourceItems] at hsource
              subst sourceBody
              cases htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
                  layout.plugRaw
                  (ConcreteElaboration.compileRegion? signature layout.plugRaw
                    targetFuel)
                  targetExtended targetBinders
                  (ConcreteElaboration.localOccurrences layout.plugRaw
                    (layout.frameRegion region)) with
              | none => simp [targetExtended, htargetItems] at htarget
              | some targetItems =>
                  simp [targetExtended, htargetItems] at htarget
                  subst targetBody
                  let sourcePrepared :=
                    (sourceItems.renameWires sourceWireMap).renameRelations relationMap
                  let targetPrepared := targetItems.castWiresEq targetEq
                  have hsourceLength :=
                    ConcreteElaboration.compileOccurrencesWith?_length
                      (ConcreteElaboration.compileRegion? signature
                        input.coalesceFrameRaw sourceFuel)
                      sourceExtended sourceBinders hsourceItems
                  have htargetLength :=
                    ConcreteElaboration.compileOccurrencesWith?_length
                      (ConcreteElaboration.compileRegion? signature layout.plugRaw
                        targetFuel) targetExtended targetBinders htargetItems
                  have hsourcePreparedLength : sourcePrepared.length =
                      (ConcreteElaboration.localOccurrences
                        input.coalesceFrameRaw region).length := by
                    simpa [sourcePrepared] using hsourceLength
                  have htargetPreparedLength : targetPrepared.length =
                      (ConcreteElaboration.localOccurrences layout.plugRaw
                        (layout.frameRegion region)).length := by
                    simpa [targetPrepared] using htargetLength
                  let positions :=
                    (FiniteEquiv.finCast hsourcePreparedLength).trans
                      ((layout.frameOccurrenceEquiv region hne).trans
                        (FiniteEquiv.finCast htargetPreparedLength.symm))
                  have hitemAt : ∀ sourceIndex,
                      ItemIso signature extended targetRels
                        (sourcePrepared.get sourceIndex)
                        (targetPrepared.get (positions sourceIndex)) := by
                    intro sourceIndex
                    let occurrenceIndex := Fin.cast hsourcePreparedLength sourceIndex
                    let targetOccurrenceIndex :=
                      layout.frameOccurrenceEquiv region hne occurrenceIndex
                    let sourceOriginalIndex := Fin.cast hsourceLength.symm occurrenceIndex
                    let targetOriginalIndex :=
                      Fin.cast htargetLength.symm targetOccurrenceIndex
                    have hsourceGet :=
                      ConcreteElaboration.compileOccurrencesWith?_get
                        (ConcreteElaboration.compileRegion? signature
                          input.coalesceFrameRaw sourceFuel)
                        sourceExtended sourceBinders hsourceItems occurrenceIndex
                    have htargetGet :=
                      ConcreteElaboration.compileOccurrencesWith?_get
                        (ConcreteElaboration.compileRegion? signature layout.plugRaw
                          targetFuel) targetExtended targetBinders htargetItems
                          targetOccurrenceIndex
                    rw [layout.frameOccurrenceEquiv_spec region hne
                      occurrenceIndex] at htargetGet
                    have hitem := hoccurrence
                      ((ConcreteElaboration.localOccurrences
                        input.coalesceFrameRaw region).get occurrenceIndex)
                      (List.get_mem _ occurrenceIndex)
                      (sourceItems.get sourceOriginalIndex)
                      (targetItems.get targetOriginalIndex) hsourceGet htargetGet
                    have hsourcePosition :
                        Fin.cast
                          (ItemSeq.renameRelations_length
                            (sourceItems.renameWires sourceWireMap) relationMap).symm
                          (sourceItems.renameWiresPositionEquiv sourceWireMap
                            sourceOriginalIndex) = sourceIndex := by
                      apply Fin.ext
                      rfl
                    have htargetPosition :
                        Fin.cast
                          (ItemSeq.castWiresEq_length targetEq targetItems).symm
                          targetOriginalIndex = positions sourceIndex := by
                      apply Fin.ext
                      rfl
                    rw [← htargetPosition, ← hsourcePosition]
                    simpa only [sourcePrepared, targetPrepared,
                      ItemSeq.get_renameRelations, ItemSeq.get_renameWires,
                      ItemSeq.get_castWiresEq] using hitem
                  rw [layout.frameFinishRegion_renameWires_renameRelations region
                    sourceOuter targetOuter outerMap relationMap sourceItems]
                  simpa only [ConcreteElaboration.finishRegion, sourcePrepared,
                    targetPrepared, localEquiv, extended, targetEq] using
                    (⟨RegionIsoPresentation.mk
                      (layout.frameLocalWireEquiv region hne) positions hitemAt⟩ :
                      Nonempty (RegionIsoPresentation signature
                        (FiniteEquiv.refl (Fin targetOuter.length)) targetRels
                        (.mk (ConcreteElaboration.exactScopeWires
                          input.coalesceFrameRaw region).length sourcePrepared)
                        (.mk (ConcreteElaboration.exactScopeWires layout.plugRaw
                          (layout.frameRegion region)).length targetPrepared)))

/-- Strict-descendant specialization of `compileFrameRegion_off_site`. -/
theorem compileFrameRegion_below_site
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (hbelow : input.coalesceFrameRaw.Encloses input.site region)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.frameRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (sourceBody : Region signature sourceOuter.length sourceRels)
    (targetBody : Region signature targetOuter.length targetRels)
    (hsource : ConcreteElaboration.compileRegion? signature
      input.coalesceFrameRaw sourceFuel region sourceOuter sourceBinders =
        some sourceBody)
    (htarget : ConcreteElaboration.compileRegion? signature layout.plugRaw
      targetFuel (layout.frameRegion region) targetOuter targetBinders =
        some targetBody) :
    RegionIso signature (FiniteEquiv.refl (Fin targetOuter.length)) targetRels
      ((sourceBody.renameWires outerMap).renameRelations relationMap)
      targetBody := by
  exact (Classical.choice (layout.compileFrameRegion_off_site signature input hadmissible
    sourceFuel targetFuel region hne (Or.inl hbelow) sourceOuter targetOuter
    sourceExact targetExact sourceBinders targetBinders sourceCover targetCover
    sourceEnumeration outerMap outerSpec relationMap relationSpec sourceBody
    targetBody hsource htarget)).iso

/-- Disjoint-subtree specialization of `compileFrameRegion_off_site`, used
for siblings of the distinguished root-to-site route. -/
theorem compileFrameRegion_away_from_site
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (haway : ¬ input.coalesceFrameRaw.Encloses region input.site)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.frameRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (sourceBody : Region signature sourceOuter.length sourceRels)
    (targetBody : Region signature targetOuter.length targetRels)
    (hsource : ConcreteElaboration.compileRegion? signature
      input.coalesceFrameRaw sourceFuel region sourceOuter sourceBinders =
        some sourceBody)
    (htarget : ConcreteElaboration.compileRegion? signature layout.plugRaw
      targetFuel (layout.frameRegion region) targetOuter targetBinders =
        some targetBody) :
    RegionIso signature (FiniteEquiv.refl (Fin targetOuter.length)) targetRels
      ((sourceBody.renameWires outerMap).renameRelations relationMap)
      targetBody := by
  have hne : region ≠ input.site := by
    intro heq
    subst region
    exact haway
      (ConcreteDiagram.Encloses.refl input.coalesceFrameRaw input.site)
  exact (Classical.choice (layout.compileFrameRegion_off_site signature input hadmissible
    sourceFuel targetFuel region hne (Or.inr haway) sourceOuter targetOuter
    sourceExact targetExact sourceBinders targetBinders sourceCover targetCover
    sourceEnumeration outerMap outerSpec relationMap relationSpec sourceBody
    targetBody hsource htarget)).iso

/-- Every retained route witnesses concrete enclosure. -/
theorem RegionRoute.encloses
    (route : RegionRoute d start target path)
    (hwf : d.WellFormed signature) : d.Encloses start target := by
  induction route with
  | here => exact ConcreteDiagram.Encloses.refl _ _
  | @step start child target rest hparent position hposition tail ih =>
      have hdirect : d.Encloses start child := by
        refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
        simp [ConcreteDiagram.climb, hparent]
      exact ConcreteElaboration.checked_encloses_trans hwf hdirect ih

/-- A distinct direct sibling of the first route child cannot contain the
route target. -/
theorem RegionRoute.distinctSibling_away
    (hwf : d.WellFormed signature)
    (route : RegionRoute d child target rest)
    (childParent : (d.regions child).parent? = some parent)
    (siblingParent : (d.regions sibling).parent? = some parent)
    (hne : sibling ≠ child) :
    ¬ d.Encloses sibling target := by
  intro hsiblingTarget
  have hchildTarget := RegionRoute.encloses route hwf
  rcases ConcreteDiagram.enclosingRegions_comparable
      hsiblingTarget hchildTarget with hsiblingChild | hchildSibling
  · rcases ConcreteElaboration.encloses_direct_child childParent
        hsiblingChild with heq | hcycle
    · exact hne heq
    · exact ConcreteElaboration.checked_direct_child_not_encloses_parent
        hwf siblingParent hcycle
  · rcases ConcreteElaboration.encloses_direct_child siblingParent
        hchildSibling with heq | hcycle
    · exact hne heq.symm
    · exact ConcreteElaboration.checked_direct_child_not_encloses_parent
        hwf childParent hcycle

/-- Exact simulation of one nonfocused occurrence in an enclosing frame.  A
node is transported directly; a child occurrence is compiled by the
disjoint-subtree theorem using the caller-supplied sibling geometry. -/
theorem compileFrameOccurrence_away_from_site
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.frameRegion region))
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.coalesceFrameRaw.regionCount input.coalesceFrameRaw.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw region)
    (childAway : ∀ child, occurrence = .child child →
      ¬ input.coalesceFrameRaw.Encloses child input.site)
    (sourceItem : Item signature (sourceOuter.extend region).length sourceRels)
    (targetItem : Item signature
      (targetOuter.extend (layout.frameRegion region)).length targetRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        sourceFuel)
      (sourceOuter.extend region) sourceBinders occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw targetFuel)
      (targetOuter.extend (layout.frameRegion region)) targetBinders
      (layout.mapFrameOccurrence occurrence) = some targetItem) :
    ItemIso signature
      (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
        (layout.frameLocalWireEquiv region hne)) targetRels
      ((sourceItem.renameWires
        (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
          outerMap)).renameRelations relationMap)
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion region))) := by
  cases occurrence with
  | node node =>
      have hnodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hoccurrence
      exact layout.compileFrameNode_at_region_iso signature input hadmissible
        region hne sourceOuter targetOuter sourceExact targetExact
        sourceBinders targetBinders sourceCover sourceEnumeration outerMap
        outerSpec relationMap relationSpec node hnodeRegion sourceItem targetItem
        (by simpa [ConcreteElaboration.compileOccurrenceWith?] using hsource)
        (by simpa [mapFrameOccurrence,
          ConcreteElaboration.compileOccurrenceWith?] using htarget)
  | child child =>
      have haway := childAway child rfl
      have hchildNeSite : child ≠ input.site := by
        intro heq
        subst child
        exact haway (ConcreteDiagram.Encloses.refl _ _)
      have hparent :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hoccurrence
      change (input.frame.val.regions child).parent? = some region at hparent
      cases hchild : input.frame.val.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
      | cut parent =>
          have hparentEq : parent = region := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have htargetChild := layout.plugRaw_frameRegion_cut child region hchild
          have htargetParent :
              (layout.plugRaw.regions (layout.frameRegion child)).parent? =
                some (layout.frameRegion region) := by
            simpa [CRegion.parent?] using congrArg CRegion.parent? htargetChild
          have hsourceChildExact := sourceExact.extend_child
            (input.coalesceFrameRaw_wellFormed hadmissible) hparent
          have htargetChildExact := targetExact.extend_child
            (layout.plugRaw_wellFormed signature input hadmissible) htargetParent
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.coalesceFrameRaw sourceFuel child (sourceOuter.extend region)
              sourceBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw targetFuel (layout.frameRegion child)
                  (targetOuter.extend (layout.frameRegion region)) targetBinders with
              | none =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  subst targetItem
                  have hrecursive := layout.compileFrameRegion_away_from_site
                    signature input hadmissible sourceFuel targetFuel child haway
                    (sourceOuter.extend region)
                    (targetOuter.extend (layout.frameRegion region))
                    hsourceChildExact htargetChildExact sourceBinders targetBinders
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      sourceCover hchild)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      targetCover htargetChild)
                    (sourceEnumeration.cutChild
                      (input.coalesceFrameRaw_wellFormed hadmissible) hchild)
                    (layout.frameExtendedWireMap region hne sourceOuter
                      targetOuter outerMap)
                    (layout.frameExtendedWireMap_spec region hne sourceOuter
                      targetOuter outerMap outerSpec)
                    relationMap
                    (layout.frameRelationLookup_cutChild hadmissible region child
                      sourceBinders targetBinders sourceEnumeration hchild
                      relationMap relationSpec)
                    compiledSource compiledTarget hsourceChild htargetChildResult
                  have htransport := layout.frameRecursiveRegionIso signature input
                    region hne sourceOuter targetOuter outerMap relationMap
                    compiledSource compiledTarget hrecursive
                  simpa [Item.renameWires, Item.renameRelations] using
                    ItemIso.cut htransport
      | bubble parent arity =>
          have hparentEq : parent = region := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have htargetChild :=
            layout.plugRaw_frameRegion_bubble child region arity hchild
          have htargetParent :
              (layout.plugRaw.regions (layout.frameRegion child)).parent? =
                some (layout.frameRegion region) := by
            simpa [CRegion.parent?] using congrArg CRegion.parent? htargetChild
          have hsourceChildExact := sourceExact.extend_child
            (input.coalesceFrameRaw_wellFormed hadmissible) hparent
          have htargetChildExact := targetExact.extend_child
            (layout.plugRaw_wellFormed signature input hadmissible) htargetParent
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.coalesceFrameRaw sourceFuel child (sourceOuter.extend region)
              (sourceBinders.push child arity) with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw targetFuel (layout.frameRegion child)
                  (targetOuter.extend (layout.frameRegion region))
                  (targetBinders.push (layout.frameRegion child) arity) with
              | none =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  subst targetItem
                  have hrecursive := layout.compileFrameRegion_away_from_site
                    signature input hadmissible sourceFuel targetFuel child haway
                    (sourceOuter.extend region)
                    (targetOuter.extend (layout.frameRegion region))
                    hsourceChildExact htargetChildExact
                    (sourceBinders.push child arity)
                    (targetBinders.push (layout.frameRegion child) arity)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceCover hchild)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      targetCover htargetChild)
                    (sourceEnumeration.bubbleChild
                      (input.coalesceFrameRaw_wellFormed hadmissible) hchild)
                    (layout.frameExtendedWireMap region hne sourceOuter
                      targetOuter outerMap)
                    (layout.frameExtendedWireMap_spec region hne sourceOuter
                      targetOuter outerMap outerSpec)
                    (RelationRenaming.lift relationMap arity)
                    (layout.frameRelationLookup_bubbleChild hadmissible region child
                      sourceBinders targetBinders sourceEnumeration arity hchild
                      relationMap relationSpec)
                    compiledSource compiledTarget hsourceChild htargetChildResult
                  have htransport := layout.frameRecursiveRegionIso signature input
                    region hne sourceOuter targetOuter outerMap
                    (RelationRenaming.lift relationMap arity)
                    compiledSource compiledTarget hrecursive
                  simpa [Item.renameWires, Item.renameRelations] using
                    ItemIso.bubble htransport

/-- The exact permutation and sibling isomorphisms for one enclosing compiler
frame, expressed in the target outer-wire coordinates.  The distinguished
route child is deliberately omitted. -/
theorem compileFrameSiblings_targetCoordinates
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceFuel targetFuel : Nat)
    (region child : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (hparent : (input.coalesceFrameRaw.regions child).parent? = some region)
    (sourcePosition : Fin (ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw region).length)
    (hposition : indexOf? (ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw region) (.child child) = some sourcePosition)
    (tail : RegionRoute input.coalesceFrameRaw child input.site rest)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (layout.frameRegion region))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.coalesceFrameRaw sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (sourceItems : ItemSeq signature
      (sourceOuter.extend region).length sourceRels)
    (targetItems : ItemSeq signature
      (targetOuter.extend (layout.frameRegion region)).length targetRels)
    (hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        sourceFuel)
      (sourceOuter.extend region) sourceBinders
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region) =
        some sourceItems)
    (htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw targetFuel)
      (targetOuter.extend (layout.frameRegion region)) targetBinders
      (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion region)) = some targetItems) :
    let sourcePrepared :=
      (sourceItems.renameWires
        (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
          outerMap)).renameRelations relationMap
    let targetPrepared := targetItems.castWiresEq
      (ConcreteElaboration.WireContext.length_extend targetOuter
        (layout.frameRegion region))
    ∃ sourceIndex : Fin sourcePrepared.length,
      ∃ targetIndex : Fin targetPrepared.length,
        sourceIndex.val = sourcePosition.val ∧
        targetIndex.val =
          (layout.frameOccurrenceEquiv region hne sourcePosition).val ∧
        Nonempty (ItemSeqIso.Frame
          (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
            (layout.frameLocalWireEquiv region hne))
          sourceIndex targetIndex) := by
  dsimp only
  let sourcePrepared :=
    (sourceItems.renameWires
      (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
        outerMap)).renameRelations relationMap
  let targetEq := ConcreteElaboration.WireContext.length_extend targetOuter
    (layout.frameRegion region)
  let targetPrepared := targetItems.castWiresEq targetEq
  have hsourceLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        sourceFuel)
      (sourceOuter.extend region) sourceBinders hsourceItems
  have htargetLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature layout.plugRaw targetFuel)
      (targetOuter.extend (layout.frameRegion region)) targetBinders htargetItems
  have hsourcePreparedLength : sourcePrepared.length =
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region).length := by
    simpa [sourcePrepared] using hsourceLength
  have htargetPreparedLength : targetPrepared.length =
      (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion region)).length := by
    simpa [targetPrepared] using htargetLength
  let positions :=
    (FiniteEquiv.finCast hsourcePreparedLength).trans
      ((layout.frameOccurrenceEquiv region hne).trans
        (FiniteEquiv.finCast htargetPreparedLength.symm))
  let sourceIndex := Fin.cast hsourcePreparedLength.symm sourcePosition
  let targetPosition := layout.frameOccurrenceEquiv region hne sourcePosition
  let targetIndex := Fin.cast htargetPreparedLength.symm targetPosition
  have hmapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    rfl
  refine ⟨sourceIndex, targetIndex, rfl, rfl, ⟨{
    positions := positions
    mapped := hmapped
    siblings := ?_
  }⟩⟩
  intro index hindex
  let occurrenceIndex := Fin.cast hsourcePreparedLength index
  let targetOccurrenceIndex :=
    layout.frameOccurrenceEquiv region hne occurrenceIndex
  let sourceOriginalIndex := Fin.cast hsourceLength.symm occurrenceIndex
  let targetOriginalIndex := Fin.cast htargetLength.symm targetOccurrenceIndex
  have hoccurrenceNe : occurrenceIndex ≠ sourcePosition := by
    intro heq
    apply hindex
    apply Fin.ext
    simpa [occurrenceIndex, sourceIndex] using congrArg Fin.val heq
  have hsourceGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
      sourceFuel)
    (sourceOuter.extend region) sourceBinders hsourceItems occurrenceIndex
  have htargetGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature layout.plugRaw targetFuel)
    (targetOuter.extend (layout.frameRegion region)) targetBinders htargetItems
    targetOccurrenceIndex
  rw [layout.frameOccurrenceEquiv_spec region hne occurrenceIndex] at htargetGet
  let occurrence := (ConcreteElaboration.localOccurrences
    input.coalesceFrameRaw region).get occurrenceIndex
  have hitem := layout.compileFrameOccurrence_away_from_site signature input
    hadmissible sourceFuel targetFuel region hne sourceOuter targetOuter
    sourceExact targetExact sourceBinders targetBinders sourceCover targetCover
    sourceEnumeration outerMap outerSpec relationMap relationSpec occurrence
    (List.get_mem _ occurrenceIndex) (by
      intro sibling hsibling
      change (ConcreteElaboration.localOccurrences
        input.coalesceFrameRaw region).get occurrenceIndex =
          .child sibling at hsibling
      have hsiblingParent :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
          (show ConcreteElaboration.LocalOccurrence.child sibling ∈
            ConcreteElaboration.localOccurrences input.coalesceFrameRaw region by
              rw [← hsibling]
              exact List.get_mem _ occurrenceIndex)
      have hsiblingNe : sibling ≠ child := by
        intro heq
        subst sibling
        have hindexOf := indexOf?_get_eq_some_of_nodup
          (ConcreteElaboration.localOccurrences_nodup _ _) occurrenceIndex
        rw [hsibling] at hindexOf
        have hsame : indexOf?
            (ConcreteElaboration.localOccurrences input.coalesceFrameRaw region)
            (.child child) = some occurrenceIndex := by
          exact hindexOf
        exact hoccurrenceNe (Option.some.inj (hsame.symm.trans hposition))
      exact RegionRoute.distinctSibling_away
        (input.coalesceFrameRaw_wellFormed hadmissible) tail hparent
        hsiblingParent hsiblingNe)
    (sourceItems.get sourceOriginalIndex) (targetItems.get targetOriginalIndex)
    hsourceGet htargetGet
  have hsourcePosition :
      Fin.cast
        (ItemSeq.renameRelations_length
          (sourceItems.renameWires
            (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
              outerMap)) relationMap).symm
        (sourceItems.renameWiresPositionEquiv
          (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
            outerMap) sourceOriginalIndex) = index := by
    apply Fin.ext
    rfl
  have htargetPosition :
      Fin.cast (ItemSeq.castWiresEq_length targetEq targetItems).symm
        targetOriginalIndex = positions index := by
    apply Fin.ext
    rfl
  rw [← htargetPosition, ← hsourcePosition]
  simpa only [sourcePrepared, targetPrepared,
    ItemSeq.get_renameRelations, ItemSeq.get_renameWires,
    ItemSeq.get_castWiresEq] using hitem

end PlugLayout

end VisualProof.Diagram.Splice.Input
