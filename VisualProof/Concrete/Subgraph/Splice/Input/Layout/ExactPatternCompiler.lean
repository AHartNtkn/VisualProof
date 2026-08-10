import VisualProof.Concrete.Subgraph.Splice.Input.Layout.PatternCompilerEvidence

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Concrete.Elaboration

namespace PlugLayout

/-- The output compiler coordinate of a wire from any exact presentation of
the pattern body.  This is the common map used by both open-root and terminal
pattern compilers. -/
noncomputable def patternExactSiteWireIndexMap
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Fin sourceContext.length →
      Fin (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length := fun index =>
  outputLeaf.siteWireIndex outputWitness
    (layout.patternPlugWire (sourceContext.get index))
    ((layout.patternPlugWire_visible_at_site_iff hadmissible _).2
      ((sourceExact.mem_iff _).1 (List.get_mem _ index)))

theorem patternExactSiteWireIndexMap_spec
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (index : Fin sourceContext.length) :
    (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).get
        (layout.patternExactSiteWireIndexMap hadmissible sourceContext
          sourceExact outputWitness outputLeaf index) =
      layout.patternPlugWire (sourceContext.get index) := by
  unfold patternExactSiteWireIndexMap
  exact outputLeaf.siteWireIndex_spec outputWitness _ _

private theorem patternBinderTarget_existsOfEnumeration
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {arity : Nat} (relation : Theory.RelVar sourceRels arity) :
    ∃ target : Theory.RelVar outputWitness.toFocus.holeRels arity,
      outputLeaf.binders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, target⟩ := by
  let binder := sourceEnumeration.binder relation.index
  obtain ⟨parent, bubble⟩ := sourceEnumeration.bubble relation.index
  have bubbleArity : input.pattern.val.diagram.regions binder =
      .bubble parent arity := by
    simpa only [binder, relation.hasArity] using bubble
  obtain ⟨plugParent, targetBubble⟩ :=
    layout.plugRaw_binderRegion_isBubble hadmissible binder parent arity
      bubbleArity
  have sourceEncloses : input.pattern.val.diagram.Encloses binder
      input.binderSpine.bodyContainer :=
    sourceEnumeration.encloses relation.index
  have notRoot : binder ≠ input.pattern.val.diagram.root := by
    intro rootEq
    rw [rootEq, input.pattern.property.diagram_well_formed.root_is_sheet]
      at bubbleArity
    contradiction
  have targetEncloses : layout.plugRaw.Encloses
      (layout.binderRegion binder) (layout.frameRegion input.site) := by
    rcases material_or_proxy_of_ne_root input binder notRoot with
      material | ⟨proxy, proxyEq⟩
    · exact False.elim
        (layout.material_not_encloses_bodyContainer binder material
          sourceEncloses)
    · rw [proxyEq, layout.binderRegion_proxy]
      exact layout.frame_encloses
        (hadmissible.binder_targets_enclose proxy)
  exact outputLeaf.bindersCover _ plugParent arity targetBubble targetEncloses

/-- Binder transport for any compiler package whose relation variables are
enumerated at the pattern body. -/
noncomputable def patternBinderWitnessOfEnumeration
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    PatternBinderWitness layout sourceBinders outputLeaf.binders where
  relationMap := fun relation => Classical.choose
    (layout.patternBinderTarget_existsOfEnumeration hadmissible sourceBinders
      sourceEnumeration outputWitness outputLeaf relation)
  lookup := by
    intro binder arity relation sourceLookup
    have owner := sourceEnumeration.lookup_owner relation sourceLookup
    rw [← owner]
    exact Classical.choose_spec
      (layout.patternBinderTarget_existsOfEnumeration hadmissible sourceBinders
        sourceEnumeration outputWitness outputLeaf relation)

/-- Local equivalence for the common compiler presentation: host locals are
followed directly by the plug layout's surviving body-internal carriers. -/
def siteLocalWireEquivOfExactPattern
    (layout : PlugLayout input) :
    FiniteEquiv
      (Fin ((Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length + layout.bodyInternalCarriers.length))
      (Fin (Elaboration.exactScopeWires layout.plugRaw
        (layout.frameRegion input.site)).length) :=
  (FiniteEquiv.finCast layout.semanticSiteWires_length.symm).trans
    layout.siteWireEquiv

noncomputable def siteCombinedWireEquivOfExactPattern
    (layout : PlugLayout input)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    FiniteEquiv
      (Fin (host.compilerLeaf.inheritedWires.length +
        ((Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length +
          layout.bodyInternalCarriers.length)))
      (Fin (outputLeaf.inheritedWires.length +
        (Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)) :=
  extendWireEquiv
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf)
    layout.siteLocalWireEquivOfExactPattern

noncomputable def hostPreparedWireOfExactPattern
    (layout : PlugLayout input)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Fin (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin (host.compilerLeaf.inheritedWires.length +
        ((Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length +
          layout.bodyInternalCarriers.length)) :=
  (layout.siteCombinedWireEquivOfExactPattern host outputWitness outputLeaf).symm ∘
    Fin.cast (Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)) ∘
    layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf

/-- The generic exact-pattern coordinate retains the coalesced host block and
only appends the layout's body-internal carrier block. -/
theorem hostPreparedWireOfExactPattern_eq_adjoinHost
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf =
      Region.adjoinHostWire host.compilerLeaf.inheritedWires.length
        (Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length
        layout.bodyInternalCarriers.length ∘
      Fin.cast (Elaboration.WireContext.length_extend
        host.compilerLeaf.inheritedWires input.site) := by
  funext index
  let combined := layout.siteCombinedWireEquivOfExactPattern host
    outputWitness outputLeaf
  let targetEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  apply combined.injective
  dsimp only [combined, hostPreparedWireOfExactPattern,
    Function.comp_apply]
  rw [FiniteEquiv.apply_symm_apply]
  change Fin.cast targetEq
      (layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf index) = _
  let sourceEq := Elaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  by_cases hzero : input.binderSpine.proxyCount = 0
  · have factor := congrFun
      (layout.hostSeamWireMapOfEmpty_eq hadmissible host outputWitness
        outputLeaf hzero) index
    have casted := congrArg (Fin.cast targetEq) factor
    calc
      _ = (layout.siteCombinedWireEquivOfEmpty hadmissible host
            outputWitness outputLeaf hzero)
          (layout.hostSeamPreparedWireOfEmpty hadmissible host index) := by
        simpa only [hostSeamWireMapOfEmpty, Fin.cast_cast,
          Function.comp_apply] using casted.symm
      _ = _ := by
        have bridge := congrFun
          (Region.extendWireEquiv_adjoinHostWire
            (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf)
            (layout.bodyInternalHiddenEquiv hzero).symm
            ((FiniteEquiv.finCast layout.semanticSiteWires_length.symm).trans
              layout.siteWireEquiv))
          (Fin.cast sourceEq index)
        simpa only [siteCombinedWireEquivOfEmpty,
          siteCombinedWireEquivOfExactPattern, siteLocalWireEquivOfEmpty,
          siteLocalWireEquivOfExactPattern, hostSeamPreparedWireOfEmpty,
          Function.comp_apply] using bridge
  · have factor := congrFun
      (layout.hostSeamWireMapOfNonempty_eq hadmissible host outputWitness
        outputLeaf hzero) index
    have casted := congrArg (Fin.cast targetEq) factor
    calc
      _ = (layout.siteCombinedWireEquivOfNonempty hadmissible host
            outputWitness outputLeaf hzero)
          (layout.hostSeamPreparedWireOfNonempty hadmissible host index) := by
        simpa only [hostSeamWireMapOfNonempty, Fin.cast_cast,
          Function.comp_apply] using casted.symm
      _ = _ := by
        have bridge := congrFun
          (Region.extendWireEquiv_adjoinHostWire
            (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf)
            (layout.bodyInternalExactEquiv hzero).symm
            ((FiniteEquiv.finCast layout.semanticSiteWires_length.symm).trans
              layout.siteWireEquiv))
          (Fin.cast sourceEq index)
        simpa only [siteCombinedWireEquivOfNonempty,
          siteCombinedWireEquivOfExactPattern, siteLocalWireEquivOfNonempty,
          siteLocalWireEquivOfExactPattern, hostSeamPreparedWireOfNonempty,
          Function.comp_apply] using bridge

noncomputable def patternPreparedWireOfExactPattern
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Fin sourceContext.length →
      Fin (host.compilerLeaf.inheritedWires.length +
        ((Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length +
          layout.bodyInternalCarriers.length)) :=
  (layout.siteCombinedWireEquivOfExactPattern host outputWitness outputLeaf).symm ∘
    Fin.cast (Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)) ∘
    layout.patternExactSiteWireIndexMap hadmissible sourceContext sourceExact
      outputWitness outputLeaf

private noncomputable def compilePatternNodeIsoOfExactMaps
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.pattern.val.diagram.regionCount)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (targetContext : Elaboration.WireContext layout.plugRaw)
    (targetExact : targetContext.Exact (layout.bodyRegion region))
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : Elaboration.BinderContext layout.plugRaw targetRels)
    (binderWitness : PatternBinderWitness layout sourceBinders targetBinders)
    {preparedWires targetWires : Nat}
    (combined : FiniteEquiv (Fin preparedWires) (Fin targetWires))
    (targetEq : targetContext.length = targetWires)
    (preparedWire : Fin sourceContext.length → Fin preparedWires)
    (directWire : Fin sourceContext.length → Fin targetContext.length)
    (wireFactor :
      (combined.trans (FiniteEquiv.finCast targetEq.symm)).toFun ∘
          preparedWire = directWire)
    (wireSpec : ∀ index, targetContext.get (directWire index) =
      layout.patternPlugWire (sourceContext.get index))
    (wireMem : ∀ wire, layout.patternPlugWire wire ∈ targetContext ↔
      wire ∈ sourceContext)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (nodeAtRegion : (input.pattern.val.diagram.nodes node).region = region)
    (sourceItem : Item sourceContext.length sourceRels)
    (targetItem : Item targetContext.length targetRels)
    (sourceComputation : Elaboration.compileNode?
      input.pattern.val.diagram sourceContext sourceBinders node =
        some sourceItem)
    (targetComputation : Elaboration.compileNode? layout.plugRaw targetContext
      targetBinders (layout.patternNode node) = some targetItem) :
    ItemIso combined targetRels
      ((sourceItem.renameWires preparedWire).renameRelations
        binderWitness.relationMap)
      (targetItem.castWiresEq targetEq) := by
  let transform := fun item : Item sourceContext.length sourceRels =>
    (item.renameWires directWire).renameRelations binderWitness.relationMap
  have transported :
      Elaboration.compileNode? layout.plugRaw targetContext targetBinders
          (layout.patternNode node) =
        (Elaboration.compileNode? input.pattern.val.diagram sourceContext
          sourceBinders node).map transform := by
    apply Elaboration.compileNode?_map
      (regionMap := layout.bodyRegion)
      (binderMap := layout.binderRegion)
      (wireMap := directWire)
      (relationMap := binderWitness.relationMap)
    · change layout.plugNode (layout.patternNode node) = _
      rw [layout.plugNode_patternNode]
      cases input.pattern.val.diagram.nodes node <;> rfl
    · intro port
      apply Elaboration.resolvePort?_map_of_occurrence
        (concreteWireMap := layout.patternPlugWire)
        (targetNodup := targetExact.nodup)
        (hget := wireSpec)
        (hmem := wireMem)
        (targetDisjoint :=
          (layout.plugRaw_wellFormed input hadmissible)
            |>.wire_endpoints_are_disjoint)
      · intro wire requested occurs
        simpa [mapPatternEndpoint] using
          layout.plugRaw_patternEndpoint_forward wire ⟨node, requested⟩ occurs
      · intro targetWire requested occurs
        obtain ⟨sourceWire, wireEq, sourceOccurs⟩ :=
          layout.plugRaw_patternEndpoint_backward targetWire
            ⟨node, requested⟩ (by
              simpa [mapPatternEndpoint] using occurs)
        exact ⟨sourceWire, wireEq, sourceOccurs⟩
    · intro nodeRegion binder nodeEq
      have actualRegion : nodeRegion = region :=
        (congrArg CNode.region nodeEq).symm.trans nodeAtRegion
      cases sourceLookup : sourceBinders binder with
      | none =>
          have impossible := sourceComputation
          simp [Elaboration.compileNode?, nodeEq, sourceLookup] at impossible
      | some payload =>
          rcases payload with ⟨arity, relation⟩
          simp only [Option.map_some]
          exact binderWitness.lookup binder relation sourceLookup
  rw [sourceComputation, targetComputation] at transported
  simp only [Option.map_some, Option.some.injEq] at transported
  subst targetItem
  have renamed := ItemIso.renameWiresEquiv
    ((sourceItem.renameWires preparedWire).renameRelations
      binderWitness.relationMap) combined
  have finalFactor : combined.toFun ∘ preparedWire =
      Fin.cast targetEq ∘ directWire := by
    funext index
    have factorAt := congrFun wireFactor index
    apply Fin.ext
    simpa only [FiniteEquiv.trans_apply, FiniteEquiv.finCast,
      Function.comp_apply] using congrArg Fin.val factorAt
  simpa only [transform, Item.castWiresEq_eq_renameWires,
    Item.renameWires_renameRelations, Item.renameWires_comp,
    finalFactor] using renamed

/-- The one recursive pattern compiler simulation used by every exact pattern
package.  It carries only the concrete binder-lookup witness required by the
successful compiler computations. -/
private noncomputable def compilePatternRegionOfBinderWitness
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.pattern.val.diagram.regionCount)
    (material : input.binderSpine.IsMaterialRegion region)
    (sourceOuter : Elaboration.WireContext input.pattern.val.diagram)
    (targetOuter : Elaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact : (targetOuter.extend (layout.bodyRegion region)).Exact
      (layout.bodyRegion region))
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : Elaboration.BinderContext layout.plugRaw targetRels)
    (binderWitness : PatternBinderWitness layout sourceBinders targetBinders)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.patternPlugWire (sourceOuter.get index))
    (sourceBody : Region sourceOuter.length sourceRels)
    (targetBody : Region targetOuter.length targetRels)
    (sourceComputation : Elaboration.compileRegion?
      input.pattern.val.diagram sourceFuel region sourceOuter sourceBinders =
        some sourceBody)
    (targetComputation : Elaboration.compileRegion? layout.plugRaw targetFuel
      (layout.bodyRegion region) targetOuter targetBinders = some targetBody) :
    RegionIso (FiniteEquiv.refl (Fin targetOuter.length)) targetRels
      ((sourceBody.renameWires outerMap).renameRelations
        binderWitness.relationMap)
      targetBody := by
  induction sourceFuel generalizing targetFuel region sourceOuter targetOuter
      sourceRels targetRels sourceBinders targetBinders sourceBody targetBody with
  | zero => simp [Elaboration.compileRegion?] at sourceComputation
  | succ sourceFuel ih =>
      cases targetFuel with
      | zero => simp [Elaboration.compileRegion?] at targetComputation
      | succ targetFuel =>
          let sourceExtended := sourceOuter.extend region
          let targetExtended := targetOuter.extend (layout.bodyRegion region)
          let localEquiv := layout.materialLocalWireEquiv region material
          let extended := extendWireEquiv
            (FiniteEquiv.refl (Fin targetOuter.length)) localEquiv
          let sourceWireMap := layout.materialSourceExtendedWireMap region
            sourceOuter targetOuter outerMap
          let directWire := layout.materialExtendedWireMap region material
            sourceOuter targetOuter outerMap
          let targetEq := Elaboration.WireContext.length_extend targetOuter
            (layout.bodyRegion region)
          have occurrenceIso : ∀
              (occurrence : Elaboration.LocalOccurrence
                input.pattern.val.diagram.regionCount
                input.pattern.val.diagram.nodeCount),
              occurrence ∈ Elaboration.localOccurrences
                input.pattern.val.diagram region →
              ∀ (sourceItem : Item sourceExtended.length sourceRels)
                (targetItem : Item targetExtended.length targetRels),
              Elaboration.compileOccurrenceWith?
                  input.pattern.val.diagram
                  (Elaboration.compileRegion?
                    input.pattern.val.diagram sourceFuel)
                  sourceExtended sourceBinders occurrence = some sourceItem →
              Elaboration.compileOccurrenceWith? layout.plugRaw
                  (Elaboration.compileRegion? layout.plugRaw targetFuel)
                  targetExtended targetBinders
                  (layout.mapPatternOccurrence occurrence) = some targetItem →
              ItemIso extended targetRels
                ((sourceItem.renameWires sourceWireMap).renameRelations
                  binderWitness.relationMap)
                (targetItem.castWiresEq targetEq) := by
            intro occurrence occurrenceMem sourceItem targetItem
              sourceItemComputation targetItemComputation
            cases occurrence with
            | node node =>
                have nodeRegion :=
                  (Elaboration.mem_localOccurrences_node _ _ _).1 occurrenceMem
                apply layout.compilePatternNodeIsoOfExactMaps input
                  hadmissible region sourceExtended targetExtended targetExact
                  sourceBinders targetBinders binderWitness extended targetEq
                  sourceWireMap directWire
                · simpa only [directWire, sourceWireMap, extended,
                    FiniteEquiv.trans_apply, FiniteEquiv.finCast,
                    Function.comp_def] using
                    layout.materialExtendedWireMap_factor region material
                      sourceOuter targetOuter outerMap
                · exact layout.materialExtendedWireMap_spec region material
                    sourceOuter targetOuter outerMap outerSpec
                · exact layout.patternPlugWire_mem_materialContext_iff
                    hadmissible region material sourceExtended targetExtended
                    sourceExact targetExact
                · exact nodeRegion
                · simpa [sourceExtended,
                    Elaboration.compileOccurrenceWith?] using
                    sourceItemComputation
                · simpa [targetExtended, mapPatternOccurrence,
                    Elaboration.compileOccurrenceWith?] using
                    targetItemComputation
            | child child =>
                have parent :=
                  (Elaboration.mem_localOccurrences_child _ _ _).1 occurrenceMem
                have childMaterial := directChildOfMaterial_material input region
                  child material parent
                cases childKind : input.pattern.val.diagram.regions child with
                | sheet =>
                    simp [Elaboration.compileOccurrenceWith?, childKind]
                      at sourceItemComputation
                | cut childParent =>
                    have parentEq : childParent = region := by
                      simpa [childKind, CRegion.parent?] using parent
                    subst childParent
                    have targetChild := layout.plugRaw_bodyRegion_cut child region
                      childMaterial childKind
                    have sourceChildExact := sourceExact.extend_child
                      input.pattern.property.diagram_well_formed parent
                    have targetChildExact := targetExact.extend_child
                      (layout.plugRaw_wellFormed input hadmissible)
                      (layout.bodyRegion_parent_exact child region childMaterial
                        parent)
                    cases sourceChildComputation : Elaboration.compileRegion?
                        input.pattern.val.diagram sourceFuel child sourceExtended
                        sourceBinders with
                    | none =>
                        simp [Elaboration.compileOccurrenceWith?, childKind,
                          sourceChildComputation] at sourceItemComputation
                    | some compiledSource =>
                        simp [Elaboration.compileOccurrenceWith?, childKind,
                          sourceChildComputation] at sourceItemComputation
                        subst sourceItem
                        cases targetChildComputation :
                            Elaboration.compileRegion? layout.plugRaw targetFuel
                              (layout.bodyRegion child) targetExtended
                              targetBinders with
                        | none =>
                            simp [mapPatternOccurrence,
                              Elaboration.compileOccurrenceWith?, targetChild,
                              targetChildComputation] at targetItemComputation
                        | some compiledTarget =>
                            simp [mapPatternOccurrence,
                              Elaboration.compileOccurrenceWith?, targetChild,
                              targetChildComputation] at targetItemComputation
                            subst targetItem
                            have recursive := ih targetFuel child childMaterial
                              sourceExtended targetExtended sourceChildExact
                              targetChildExact sourceBinders targetBinders
                              binderWitness directWire
                              (layout.materialExtendedWireMap_spec region material
                                sourceOuter targetOuter outerMap outerSpec)
                              compiledSource compiledTarget
                              sourceChildComputation targetChildComputation
                            have transported := layout.materialRecursiveRegionIso
                              input region material sourceOuter targetOuter outerMap
                              binderWitness.relationMap compiledSource
                              compiledTarget recursive
                            simpa [Item.renameWires, Item.renameRelations] using
                              ItemIso.cut transported
                | bubble childParent arity =>
                    have parentEq : childParent = region := by
                      simpa [childKind, CRegion.parent?] using parent
                    subst childParent
                    have targetChild := layout.plugRaw_bodyRegion_bubble child
                      region arity childMaterial childKind
                    have sourceChildExact := sourceExact.extend_child
                      input.pattern.property.diagram_well_formed parent
                    have targetChildExact := targetExact.extend_child
                      (layout.plugRaw_wellFormed input hadmissible)
                      (layout.bodyRegion_parent_exact child region childMaterial
                        parent)
                    let childWitness := PatternBinderWitness.pushMaterial layout
                      binderWitness child arity childMaterial
                    cases sourceChildComputation : Elaboration.compileRegion?
                        input.pattern.val.diagram sourceFuel child sourceExtended
                        (sourceBinders.push child arity) with
                    | none =>
                        simp [Elaboration.compileOccurrenceWith?, childKind,
                          sourceChildComputation] at sourceItemComputation
                    | some compiledSource =>
                        simp [Elaboration.compileOccurrenceWith?, childKind,
                          sourceChildComputation] at sourceItemComputation
                        subst sourceItem
                        cases targetChildComputation :
                            Elaboration.compileRegion? layout.plugRaw targetFuel
                              (layout.bodyRegion child) targetExtended
                              (targetBinders.push
                                (layout.bodyRegion child) arity) with
                        | none =>
                            simp [mapPatternOccurrence,
                              Elaboration.compileOccurrenceWith?, targetChild,
                              targetChildComputation] at targetItemComputation
                        | some compiledTarget =>
                            simp [mapPatternOccurrence,
                              Elaboration.compileOccurrenceWith?, targetChild,
                              targetChildComputation] at targetItemComputation
                            subst targetItem
                            have recursive := ih targetFuel child childMaterial
                              sourceExtended targetExtended sourceChildExact
                              targetChildExact (sourceBinders.push child arity)
                              (targetBinders.push
                                (layout.bodyRegion child) arity)
                              childWitness directWire
                              (layout.materialExtendedWireMap_spec region material
                                sourceOuter targetOuter outerMap outerSpec)
                              compiledSource compiledTarget
                              sourceChildComputation targetChildComputation
                            have transported := layout.materialRecursiveRegionIso
                              input region material sourceOuter targetOuter outerMap
                              childWitness.relationMap compiledSource
                              compiledTarget recursive
                            simpa [childWitness, Item.renameWires,
                              Item.renameRelations] using
                              ItemIso.bubble transported
          simp only [Elaboration.compileRegion?]
            at sourceComputation targetComputation
          cases sourceItemsComputation : Elaboration.compileOccurrencesWith?
              input.pattern.val.diagram
              (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
              sourceExtended sourceBinders
              (Elaboration.localOccurrences input.pattern.val.diagram region) with
          | none =>
              simp [sourceExtended, sourceItemsComputation]
                at sourceComputation
          | some sourceItems =>
              simp [sourceExtended, sourceItemsComputation]
                at sourceComputation
              subst sourceBody
              cases targetItemsComputation : Elaboration.compileOccurrencesWith?
                  layout.plugRaw
                  (Elaboration.compileRegion? layout.plugRaw targetFuel)
                  targetExtended targetBinders
                  (Elaboration.localOccurrences layout.plugRaw
                    (layout.bodyRegion region)) with
              | none =>
                  simp [targetExtended, targetItemsComputation]
                    at targetComputation
              | some targetItems =>
                  simp [targetExtended, targetItemsComputation]
                    at targetComputation
                  subst targetBody
                  let sourcePrepared :=
                    (sourceItems.renameWires sourceWireMap).renameRelations
                      binderWitness.relationMap
                  let targetPrepared := targetItems.castWiresEq targetEq
                  have sourceLength :=
                    Elaboration.compileOccurrencesWith?_length
                      (Elaboration.compileRegion?
                        input.pattern.val.diagram sourceFuel)
                      sourceExtended sourceBinders sourceItemsComputation
                  have targetLength :=
                    Elaboration.compileOccurrencesWith?_length
                      (Elaboration.compileRegion? layout.plugRaw targetFuel)
                      targetExtended targetBinders targetItemsComputation
                  have sourcePreparedLength : sourcePrepared.length =
                      (Elaboration.localOccurrences
                        input.pattern.val.diagram region).length := by
                    simp [sourcePrepared, sourceLength]
                  have targetPreparedLength : targetPrepared.length =
                      (Elaboration.localOccurrences layout.plugRaw
                        (layout.bodyRegion region)).length := by
                    simp [targetPrepared, targetLength]
                  let positions :=
                    (FiniteEquiv.finCast sourcePreparedLength).trans
                      ((layout.materialOccurrenceEquiv region material).trans
                        (FiniteEquiv.finCast targetPreparedLength.symm))
                  have itemsIso : ItemSeqIso extended targetRels
                      sourcePrepared targetPrepared := by
                    apply ItemSeqIso.permute positions
                    intro sourceIndex
                    let occurrenceIndex :=
                      Fin.cast sourcePreparedLength sourceIndex
                    let targetOccurrenceIndex :=
                      layout.materialOccurrenceEquiv region material
                        occurrenceIndex
                    let sourceOriginalIndex :=
                      Fin.cast sourceLength.symm occurrenceIndex
                    let targetOriginalIndex :=
                      Fin.cast targetLength.symm targetOccurrenceIndex
                    have sourceGet :=
                      Elaboration.compileOccurrencesWith?_get
                        (Elaboration.compileRegion?
                          input.pattern.val.diagram sourceFuel)
                        sourceExtended sourceBinders sourceItemsComputation
                        occurrenceIndex
                    have targetGet :=
                      Elaboration.compileOccurrencesWith?_get
                        (Elaboration.compileRegion? layout.plugRaw targetFuel)
                        targetExtended targetBinders targetItemsComputation
                        targetOccurrenceIndex
                    rw [layout.materialOccurrenceEquiv_spec region material
                      occurrenceIndex] at targetGet
                    have itemIso := occurrenceIso
                      ((Elaboration.localOccurrences
                        input.pattern.val.diagram region).get occurrenceIndex)
                      (List.get_mem _ occurrenceIndex)
                      (sourceItems.get sourceOriginalIndex)
                      (targetItems.get targetOriginalIndex) sourceGet targetGet
                    have sourcePosition :
                        Fin.cast
                          (ItemSeq.renameRelations_length
                            (sourceItems.renameWires sourceWireMap)
                            binderWitness.relationMap).symm
                          (sourceItems.renameWiresPositionEquiv sourceWireMap
                            sourceOriginalIndex) = sourceIndex := by
                      apply Fin.ext
                      rfl
                    have targetPosition :
                        Fin.cast
                          (ItemSeq.castWiresEq_length targetEq targetItems).symm
                          targetOriginalIndex = positions sourceIndex := by
                      apply Fin.ext
                      rfl
                    rw [← targetPosition, ← sourcePosition]
                    simpa only [sourcePrepared, targetPrepared,
                      ItemSeq.get_renameRelations, ItemSeq.get_renameWires,
                      ItemSeq.get_castWiresEq] using itemIso
                  rw [layout.finishRegion_renameWires_renameRelations region
                    sourceOuter targetOuter outerMap binderWitness.relationMap
                    sourceItems]
                  simpa only [Elaboration.finishRegion, sourcePrepared,
                    targetPrepared, localEquiv, extended, targetEq] using
                    RegionIso.mk
                      (layout.materialLocalWireEquiv region material) itemsIso

noncomputable def compilePatternOccurrence_at_seam_iso_of_exact
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (sourceFuel : Nat)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (occurrence : Elaboration.LocalOccurrence
      input.pattern.val.diagram.regionCount input.pattern.val.diagram.nodeCount)
    (occurrenceMem : occurrence ∈ Elaboration.localOccurrences
      input.pattern.val.diagram input.binderSpine.bodyContainer)
    (sourceItem : Item sourceContext.length sourceRels)
    (targetItem : Item
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (sourceComputation : Elaboration.compileOccurrenceWith?
      input.pattern.val.diagram
      (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
      sourceContext sourceBinders occurrence = some sourceItem)
    (targetComputation : Elaboration.compileOccurrenceWith? layout.plugRaw
      (Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
        some targetItem) :
    let binderWitness := layout.patternBinderWitnessOfEnumeration hadmissible
      sourceBinders sourceEnumeration outputWitness outputLeaf
    ItemIso
      (layout.siteCombinedWireEquivOfExactPattern host outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.patternPreparedWireOfExactPattern hadmissible host sourceContext
          sourceExact outputWitness outputLeaf)).renameRelations
        binderWitness.relationMap)
      (targetItem.castWiresEq
        (Elaboration.WireContext.length_extend outputLeaf.inheritedWires
          (layout.frameRegion input.site))) := by
  dsimp only
  let targetContext := outputLeaf.inheritedWires.extend
    (layout.frameRegion input.site)
  let combined := layout.siteCombinedWireEquivOfExactPattern host
    outputWitness outputLeaf
  let preparedWire := layout.patternPreparedWireOfExactPattern hadmissible host
    sourceContext sourceExact outputWitness outputLeaf
  let directWire := layout.patternExactSiteWireIndexMap hadmissible
    sourceContext sourceExact outputWitness outputLeaf
  let targetEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let binderWitness := layout.patternBinderWitnessOfEnumeration hadmissible
    sourceBinders sourceEnumeration outputWitness outputLeaf
  have wireFactor :
      (combined.trans (FiniteEquiv.finCast targetEq.symm)).toFun ∘
          preparedWire = directWire := by
    funext index
    change Fin.cast targetEq.symm
        (combined.toFun (combined.invFun
          (Fin.cast targetEq (directWire index)))) = directWire index
    rw [combined.right_inv]
    apply Fin.ext
    rfl
  have wireMem : ∀ wire, layout.patternPlugWire wire ∈ targetContext ↔
      wire ∈ sourceContext := by
    intro wire
    calc
      layout.patternPlugWire wire ∈ targetContext ↔
          layout.plugRaw.Encloses
            (layout.plugRaw.wires (layout.patternPlugWire wire)).scope
            (layout.frameRegion input.site) :=
        outputLeaf.wiresExact.mem_iff _
      _ ↔ input.pattern.val.diagram.Encloses
            (input.pattern.val.diagram.wires wire).scope
            input.binderSpine.bodyContainer :=
        layout.patternPlugWire_visible_at_site_iff hadmissible wire
      _ ↔ wire ∈ sourceContext := (sourceExact.mem_iff wire).symm
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (Elaboration.mem_localOccurrences_node _ _ _).1 occurrenceMem
      have targetBodyExact : targetContext.Exact
          (layout.bodyRegion input.binderSpine.bodyContainer) := by
        simpa only [layout.bodyRegion_bodyContainer] using outputLeaf.wiresExact
      exact layout.compilePatternNodeIsoOfExactMaps input hadmissible
        input.binderSpine.bodyContainer sourceContext targetContext
        targetBodyExact sourceBinders outputLeaf.binders binderWitness
        combined targetEq preparedWire directWire wireFactor
        (layout.patternExactSiteWireIndexMap_spec hadmissible sourceContext
          sourceExact outputWitness outputLeaf) wireMem node nodeRegion
        sourceItem targetItem
        (by simpa [Elaboration.compileOccurrenceWith?] using sourceComputation)
        (by simpa [targetContext, mapPatternOccurrence,
          Elaboration.compileOccurrenceWith?] using targetComputation)
  | child child =>
      have parent :=
        (Elaboration.mem_localOccurrences_child _ _ _).1 occurrenceMem
      have childMaterial := directChildOfBody_material input child parent
      have sourceChildExact := sourceExact.extend_child
        input.pattern.property.diagram_well_formed parent
      have targetParent :
          (layout.plugRaw.regions (layout.bodyRegion child)).parent? =
            some (layout.frameRegion input.site) := by
        simpa only [layout.bodyRegion_bodyContainer] using
          layout.bodyRegion_parent_exact child input.binderSpine.bodyContainer
            childMaterial parent
      have targetChildExact := outputLeaf.wiresExact.extend_child
        (layout.plugRaw_wellFormed input hadmissible) targetParent
      cases childKind : input.pattern.val.diagram.regions child with
      | sheet =>
          simp [Elaboration.compileOccurrenceWith?, childKind]
            at sourceComputation
      | cut childParent =>
          have parentEq : childParent = input.binderSpine.bodyContainer := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          have targetChild := layout.plugRaw_bodyRegion_cut child
            input.binderSpine.bodyContainer childMaterial childKind
          have targetChildAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                .cut (layout.frameRegion input.site) := by
            simpa only [layout.bodyRegion_bodyContainer] using targetChild
          cases sourceChildComputation : Elaboration.compileRegion?
              input.pattern.val.diagram sourceFuel child sourceContext
              sourceBinders with
          | none =>
              simp [Elaboration.compileOccurrenceWith?, childKind,
                sourceChildComputation] at sourceComputation
          | some compiledSource =>
              simp [Elaboration.compileOccurrenceWith?, childKind,
                sourceChildComputation] at sourceComputation
              subst sourceItem
              cases targetChildComputation :
                  Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel
                    (layout.bodyRegion child) targetContext outputLeaf.binders with
              | none =>
                  simp [mapPatternOccurrence,
                    Elaboration.compileOccurrenceWith?, targetContext,
                    targetChildAtSite,
                    targetChildComputation] at targetComputation
              | some compiledTarget =>
                  simp [mapPatternOccurrence,
                    Elaboration.compileOccurrenceWith?, targetContext,
                    targetChildAtSite,
                    targetChildComputation] at targetComputation
                  subst targetItem
                  have recursive := layout.compilePatternRegionOfBinderWitness
                    input hadmissible sourceFuel outputLeaf.fuel child
                    childMaterial sourceContext targetContext sourceChildExact
                    targetChildExact sourceBinders outputLeaf.binders
                    binderWitness directWire
                    (layout.patternExactSiteWireIndexMap_spec hadmissible
                      sourceContext sourceExact outputWitness outputLeaf)
                    compiledSource compiledTarget sourceChildComputation
                    targetChildComputation
                  have transported := seamRecursiveRegionIso_of_maps combined
                    targetEq preparedWire directWire wireFactor
                    binderWitness.relationMap compiledSource compiledTarget
                    recursive
                  simpa [Item.renameWires, Item.renameRelations] using
                    ItemIso.cut transported
      | bubble childParent arity =>
          have parentEq : childParent = input.binderSpine.bodyContainer := by
            simpa [childKind, CRegion.parent?] using parent
          subst childParent
          have targetChild := layout.plugRaw_bodyRegion_bubble child
            input.binderSpine.bodyContainer arity childMaterial childKind
          have targetChildAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                .bubble (layout.frameRegion input.site) arity := by
            simpa only [layout.bodyRegion_bodyContainer] using targetChild
          let childWitness := PatternBinderWitness.pushMaterial layout
            binderWitness child arity childMaterial
          cases sourceChildComputation : Elaboration.compileRegion?
              input.pattern.val.diagram sourceFuel child sourceContext
              (sourceBinders.push child arity) with
          | none =>
              simp [Elaboration.compileOccurrenceWith?, childKind,
                sourceChildComputation] at sourceComputation
          | some compiledSource =>
              simp [Elaboration.compileOccurrenceWith?, childKind,
                sourceChildComputation] at sourceComputation
              subst sourceItem
              cases targetChildComputation :
                  Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel
                    (layout.bodyRegion child) targetContext
                    (outputLeaf.binders.push
                      (layout.bodyRegion child) arity) with
              | none =>
                  simp [mapPatternOccurrence,
                    Elaboration.compileOccurrenceWith?, targetContext,
                    targetChildAtSite,
                    targetChildComputation] at targetComputation
              | some compiledTarget =>
                  simp [mapPatternOccurrence,
                    Elaboration.compileOccurrenceWith?, targetContext,
                    targetChildAtSite,
                    targetChildComputation] at targetComputation
                  subst targetItem
                  have recursive := layout.compilePatternRegionOfBinderWitness
                    input hadmissible sourceFuel outputLeaf.fuel child
                    childMaterial sourceContext targetContext sourceChildExact
                    targetChildExact (sourceBinders.push child arity)
                    (outputLeaf.binders.push
                      (layout.bodyRegion child) arity)
                    childWitness directWire
                    (layout.patternExactSiteWireIndexMap_spec hadmissible
                      sourceContext sourceExact outputWitness outputLeaf)
                    compiledSource compiledTarget sourceChildComputation
                    targetChildComputation
                  have transported := seamRecursiveRegionIso_of_maps combined
                    targetEq preparedWire directWire wireFactor
                    childWitness.relationMap compiledSource compiledTarget
                    recursive
                  simpa [childWitness, Item.renameWires,
                    Item.renameRelations] using ItemIso.bubble transported

noncomputable def compiledSiteItemsIsoOfMaps
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (sourceFuel : Nat)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceItems : ItemSeq sourceContext.length sourceRels)
    (sourceItemsComputation : Elaboration.compileOccurrencesWith?
      input.pattern.val.diagram
      (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
      sourceContext sourceBinders
      (Elaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer) = some sourceItems)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {preparedWires : Nat}
    (combined : FiniteEquiv (Fin preparedWires)
      (Fin (outputLeaf.inheritedWires.length +
        (Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)))
    (hostWire : Fin (host.compilerLeaf.inheritedWires.extend
      input.site).length → Fin preparedWires)
    (patternWire : Fin sourceContext.length → Fin preparedWires)
    (binderWitness : PatternBinderWitness layout sourceBinders
      outputLeaf.binders)
    (hostFactor :
      (combined.trans (FiniteEquiv.finCast
        (Elaboration.WireContext.length_extend outputLeaf.inheritedWires
          (layout.frameRegion input.site)).symm)).toFun ∘ hostWire =
        layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
    (patternItemIso : ∀
      (occurrence : Elaboration.LocalOccurrence
        input.pattern.val.diagram.regionCount input.pattern.val.diagram.nodeCount)
      (_occurrenceMem : occurrence ∈ Elaboration.localOccurrences
        input.pattern.val.diagram input.binderSpine.bodyContainer)
      (sourceItem : Item sourceContext.length sourceRels)
      (targetItem : Item
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).length
        outputWitness.toFocus.holeRels),
      Elaboration.compileOccurrenceWith? input.pattern.val.diagram
          (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
          sourceContext sourceBinders occurrence = some sourceItem →
      Elaboration.compileOccurrenceWith? layout.plugRaw
          (Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel)
          (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
          outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
            some targetItem →
      ItemIso combined outputWitness.toFocus.holeRels
        ((sourceItem.renameWires patternWire).renameRelations
          binderWitness.relationMap)
        (targetItem.castWiresEq
          (Elaboration.WireContext.length_extend outputLeaf.inheritedWires
            (layout.frameRegion input.site)))) :
    let hostPrepared :=
      (host.compilerLeaf.items.renameWires
        hostWire)
        |>.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf)
    let patternPrepared :=
      (sourceItems.renameWires
        patternWire).renameRelations
        binderWitness.relationMap
    ItemSeqIso
      combined
      outputWitness.toFocus.holeRels
      (hostPrepared.append patternPrepared)
      (outputLeaf.items.castWiresEq
        (Elaboration.WireContext.length_extend outputLeaf.inheritedWires
          (layout.frameRegion input.site))) := by
  dsimp only
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires hostWire).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (sourceItems.renameWires patternWire).renameRelations
      binderWitness.relationMap
  let sourcePrepared := hostPrepared.append patternPrepared
  let targetEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetPrepared := outputLeaf.items.castWiresEq targetEq
  have hostLength := Elaboration.compileOccurrencesWith?_length
    (Elaboration.compileRegion? input.coalesceFrameRaw host.compilerLeaf.fuel)
    (host.compilerLeaf.inheritedWires.extend input.site)
    host.compilerLeaf.binders host.compilerLeaf.itemsComputation
  have patternLength := Elaboration.compileOccurrencesWith?_length
    (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
    sourceContext sourceBinders sourceItemsComputation
  have targetLength := Elaboration.compileOccurrencesWith?_length
    (Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
    outputLeaf.binders outputLeaf.itemsComputation
  have hostRawLength : host.compilerLeaf.items.length =
      (Elaboration.localOccurrences input.coalesceFrameRaw input.site).length := by
    simpa [coalesceFrame] using hostLength
  have sourcePreparedLength : sourcePrepared.length =
      layout.semanticSiteOccurrences.length := by
    simp [sourcePrepared, hostPrepared, patternPrepared,
      semanticSiteOccurrences, hostRawLength, patternLength,
      ItemSeq.length_append]
  have targetPreparedLength : targetPrepared.length =
      (Elaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.site)).length := by
    simp [targetPrepared, targetLength]
  let positions :=
    (FiniteEquiv.finCast sourcePreparedLength).trans
      (layout.siteOccurrenceEquiv.trans
        (FiniteEquiv.finCast targetPreparedLength.symm))
  apply ItemSeqIso.permute positions
  intro sourceIndex
  let splitIndex := Fin.cast
    (ItemSeq.length_append hostPrepared patternPrepared) sourceIndex
  have sourceFromSplit :
      Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          splitIndex = sourceIndex := by
    apply Fin.ext
    rfl
  revert sourceFromSplit
  refine Fin.addCases (m := hostPrepared.length) (n := patternPrepared.length)
    (fun hostPreparedIndex sourcePosition => ?_)
    (fun patternPreparedIndex sourcePosition => ?_) splitIndex
  · let hostOriginalIndex : Fin host.compilerLeaf.items.length :=
      Fin.cast (by simp [hostPrepared]) hostPreparedIndex
    let hostOccurrenceIndex := Fin.cast hostRawLength hostOriginalIndex
    let occurrenceIndex : Fin layout.semanticSiteOccurrences.length :=
      Fin.cast (by simp [semanticSiteOccurrences])
        (Fin.castAdd
          (Elaboration.localOccurrences input.pattern.val.diagram
            input.binderSpine.bodyContainer).length hostOccurrenceIndex)
    let targetOccurrenceIndex := layout.siteOccurrenceEquiv occurrenceIndex
    let targetOriginalIndex := Fin.cast targetLength.symm
      targetOccurrenceIndex
    have sourceGet := Elaboration.compileOccurrencesWith?_get
      (Elaboration.compileRegion? input.coalesceFrameRaw
        host.compilerLeaf.fuel)
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders host.compilerLeaf.itemsComputation
      hostOccurrenceIndex
    have targetGet := Elaboration.compileOccurrencesWith?_get
      (Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
    rw [layout.siteOccurrenceEquiv_spec occurrenceIndex] at targetGet
    have targetGet' : Elaboration.compileOccurrenceWith? layout.plugRaw
        (Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders
        (layout.mapFrameOccurrence
          ((Elaboration.localOccurrences input.coalesceFrameRaw input.site).get
            hostOccurrenceIndex)) =
          some (outputLeaf.items.get targetOriginalIndex) := by
      simpa [semanticSiteOccurrences, occurrenceIndex] using targetGet
    have itemIso := layout.compileHostOccurrence_at_seam_iso_of_maps input
      hadmissible host outputWitness outputLeaf combined hostWire hostFactor
      ((Elaboration.localOccurrences input.coalesceFrameRaw input.site).get
        hostOccurrenceIndex)
      (List.get_mem _ hostOccurrenceIndex)
      (host.compilerLeaf.items.get hostOriginalIndex)
      (outputLeaf.items.get targetOriginalIndex) sourceGet targetGet'
    have sourcePosition' :
        Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          (Fin.castAdd patternPrepared.length hostPreparedIndex) =
            sourceIndex := by
      rw [← sourcePosition]
    have semanticPosition :
        Fin.cast sourcePreparedLength sourceIndex = occurrenceIndex := by
      rw [← sourcePosition']
      apply Fin.ext
      rfl
    have targetPosition :
        Fin.cast (ItemSeq.castWiresEq_length targetEq outputLeaf.items).symm
          targetOriginalIndex = positions sourceIndex := by
      simp only [positions, FiniteEquiv.trans_apply, FiniteEquiv.finCast]
      rw [semanticPosition]
      apply Fin.ext
      rfl
    have preparedGet : hostPrepared.get hostPreparedIndex =
        Item.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf)
          (Item.renameWires hostWire
            (host.compilerLeaf.items.get hostOriginalIndex)) := by
      have wireGet := ItemSeq.get_renameWires host.compilerLeaf.items hostWire
        hostOriginalIndex
      have relationGet := ItemSeq.get_renameRelations
        (host.compilerLeaf.items.renameWires hostWire)
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
        (host.compilerLeaf.items.renameWiresPositionEquiv hostWire
          hostOriginalIndex)
      rw [wireGet] at relationGet
      have indexEq :
          Fin.cast
              (ItemSeq.renameRelations_length
                (host.compilerLeaf.items.renameWires hostWire)
                (layout.hostRelationRenaming host.intrinsicPath
                  host.compilerLeaf outputWitness outputLeaf)).symm
              (host.compilerLeaf.items.renameWiresPositionEquiv hostWire
                hostOriginalIndex) = hostPreparedIndex := by
        apply Fin.ext
        rfl
      simpa only [hostPrepared, indexEq] using relationGet
    rw [← targetPosition, ← sourcePosition', ItemSeq.get_append_left]
    rw [preparedGet]
    simpa only [targetPrepared, ItemSeq.get_castWiresEq] using itemIso
  · let patternOriginalIndex : Fin sourceItems.length :=
      Fin.cast (by simp [patternPrepared]) patternPreparedIndex
    let patternOccurrenceIndex := Fin.cast patternLength patternOriginalIndex
    let occurrenceIndex : Fin layout.semanticSiteOccurrences.length :=
      Fin.cast (by simp [semanticSiteOccurrences])
        (Fin.natAdd
          (Elaboration.localOccurrences input.coalesceFrameRaw
            input.site).length patternOccurrenceIndex)
    let targetOccurrenceIndex := layout.siteOccurrenceEquiv occurrenceIndex
    let targetOriginalIndex := Fin.cast targetLength.symm
      targetOccurrenceIndex
    have sourceGet := Elaboration.compileOccurrencesWith?_get
      (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
      sourceContext sourceBinders sourceItemsComputation patternOccurrenceIndex
    have targetGet := Elaboration.compileOccurrencesWith?_get
      (Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
    rw [layout.siteOccurrenceEquiv_spec occurrenceIndex] at targetGet
    have targetGet' : Elaboration.compileOccurrenceWith? layout.plugRaw
        (Elaboration.compileRegion? layout.plugRaw outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders
        (layout.mapPatternOccurrence
          ((Elaboration.localOccurrences input.pattern.val.diagram
            input.binderSpine.bodyContainer).get patternOccurrenceIndex)) =
          some (outputLeaf.items.get targetOriginalIndex) := by
      simpa [semanticSiteOccurrences, occurrenceIndex] using targetGet
    have itemIso := patternItemIso
      ((Elaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer).get patternOccurrenceIndex)
      (List.get_mem _ patternOccurrenceIndex)
      (sourceItems.get patternOriginalIndex)
      (outputLeaf.items.get targetOriginalIndex) sourceGet targetGet'
    have sourcePosition' :
        Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          (Fin.natAdd hostPrepared.length patternPreparedIndex) =
            sourceIndex := by
      rw [← sourcePosition]
    have semanticPosition :
        Fin.cast sourcePreparedLength sourceIndex = occurrenceIndex := by
      rw [← sourcePosition']
      apply Fin.ext
      simp [occurrenceIndex, patternOccurrenceIndex, patternOriginalIndex,
        hostPrepared, hostRawLength]
    have targetPosition :
        Fin.cast (ItemSeq.castWiresEq_length targetEq outputLeaf.items).symm
          targetOriginalIndex = positions sourceIndex := by
      simp only [positions, FiniteEquiv.trans_apply, FiniteEquiv.finCast]
      rw [semanticPosition]
      apply Fin.ext
      rfl
    have preparedGet : patternPrepared.get patternPreparedIndex =
        Item.renameRelations binderWitness.relationMap
          (Item.renameWires patternWire
            (sourceItems.get patternOriginalIndex)) := by
      have wireGet := ItemSeq.get_renameWires sourceItems patternWire
        patternOriginalIndex
      have relationGet := ItemSeq.get_renameRelations
        (sourceItems.renameWires patternWire) binderWitness.relationMap
        (sourceItems.renameWiresPositionEquiv patternWire patternOriginalIndex)
      rw [wireGet] at relationGet
      have indexEq :
          Fin.cast
              (ItemSeq.renameRelations_length
                (sourceItems.renameWires patternWire)
                binderWitness.relationMap).symm
              (sourceItems.renameWiresPositionEquiv patternWire
                patternOriginalIndex) = patternPreparedIndex := by
        apply Fin.ext
        rfl
      simpa only [patternPrepared, indexEq] using relationGet
    rw [← targetPosition, ← sourcePosition', ItemSeq.get_append_right]
    rw [preparedGet]
    simpa only [targetPrepared, ItemSeq.get_castWiresEq] using itemIso

noncomputable def compiledSiteItemsIsoOfExactPattern
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (sourceFuel : Nat)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    (sourceItems : ItemSeq sourceContext.length sourceRels)
    (sourceItemsComputation : Elaboration.compileOccurrencesWith?
      input.pattern.val.diagram
      (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
      sourceContext sourceBinders
      (Elaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer) = some sourceItems)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    let binderWitness := layout.patternBinderWitnessOfEnumeration hadmissible
      sourceBinders sourceEnumeration outputWitness outputLeaf
    let hostPrepared :=
      (host.compilerLeaf.items.renameWires
        (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf))
        |>.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf)
    let patternPrepared :=
      (sourceItems.renameWires
        (layout.patternPreparedWireOfExactPattern hadmissible host sourceContext
          sourceExact outputWitness outputLeaf)).renameRelations
        binderWitness.relationMap
    ItemSeqIso
      (layout.siteCombinedWireEquivOfExactPattern host outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      (hostPrepared.append patternPrepared)
      (outputLeaf.items.castWiresEq
        (Elaboration.WireContext.length_extend outputLeaf.inheritedWires
          (layout.frameRegion input.site))) := by
  dsimp only
  let binderWitness := layout.patternBinderWitnessOfEnumeration hadmissible
    sourceBinders sourceEnumeration outputWitness outputLeaf
  let combined := layout.siteCombinedWireEquivOfExactPattern host
    outputWitness outputLeaf
  let hostWire := layout.hostPreparedWireOfExactPattern host
    outputWitness outputLeaf
  let patternWire := layout.patternPreparedWireOfExactPattern hadmissible host
    sourceContext sourceExact outputWitness outputLeaf
  let targetEq := Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  have hostFactor :
      (combined.trans (FiniteEquiv.finCast targetEq.symm)).toFun ∘
          hostWire =
        layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf := by
    funext index
    change Fin.cast targetEq.symm
        (combined.toFun (combined.invFun
          (Fin.cast targetEq
            (layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf index)))) = _
    rw [combined.right_inv]
    apply Fin.ext
    rfl
  apply layout.compiledSiteItemsIsoOfMaps input hadmissible host sourceFuel
    sourceContext sourceBinders sourceItems
    sourceItemsComputation outputWitness outputLeaf combined hostWire
    patternWire binderWitness hostFactor
  intro occurrence occurrenceMem sourceItem targetItem sourceComputation
    targetComputation
  exact layout.compilePatternOccurrence_at_seam_iso_of_exact input
    hadmissible host sourceFuel sourceContext sourceExact sourceBinders
    sourceEnumeration outputWitness outputLeaf occurrence occurrenceMem
    sourceItem targetItem sourceComputation targetComputation

/-- The branch-neutral source presentation for any exact compiler package of
the pattern body. -/
noncomputable def compiledSiteSourceOfExactPattern
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    (sourceItems : ItemSeq sourceContext.length sourceRels)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Region host.compilerLeaf.inheritedWires.length
      outputWitness.toFocus.holeRels :=
  let binderWitness := layout.patternBinderWitnessOfEnumeration hadmissible
    sourceBinders sourceEnumeration outputWitness outputLeaf
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostPreparedWireOfExactPattern host outputWitness outputLeaf))
      |>.renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
  let patternPrepared :=
    (sourceItems.renameWires
      (layout.patternPreparedWireOfExactPattern hadmissible host sourceContext
        sourceExact outputWitness outputLeaf)).renameRelations
      binderWitness.relationMap
  Region.mk
    ((Elaboration.exactScopeWires input.coalesceFrameRaw input.site).length +
      layout.bodyInternalCarriers.length)
    (hostPrepared.append patternPrepared)

/-- The exact-pattern compiler normalization at a nested splice site.  Its
source is the branch-neutral compiler presentation: host items followed by
the items of any exact compiler package for the pattern body. -/
noncomputable def compiledSiteRegionIsoOfExactPattern
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (sourceFuel : Nat)
    (sourceContext : Elaboration.WireContext input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    (sourceItems : ItemSeq sourceContext.length sourceRels)
    (sourceItemsComputation : Elaboration.compileOccurrencesWith?
      input.pattern.val.diagram
      (Elaboration.compileRegion? input.pattern.val.diagram sourceFuel)
      sourceContext sourceBinders
      (Elaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer) = some sourceItems)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    RegionIso
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      (layout.compiledSiteSourceOfExactPattern input hadmissible host
        sourceContext sourceExact sourceBinders sourceEnumeration sourceItems
        outputWitness outputLeaf)
      (Elaboration.finishRegion layout.plugRaw outputLeaf.inheritedWires
        (layout.frameRegion input.site) outputLeaf.items) := by
  unfold compiledSiteSourceOfExactPattern
  dsimp only
  have itemsIso := layout.compiledSiteItemsIsoOfExactPattern input hadmissible
    host sourceFuel sourceContext sourceExact sourceBinders sourceEnumeration
    sourceItems sourceItemsComputation outputWitness outputLeaf
  have regionIso := RegionIso.mk layout.siteLocalWireEquivOfExactPattern itemsIso
  simpa only [Elaboration.finishRegion] using regionIso

/-- The semantic nested-site source selected by the concrete compiler.  The
selection is owned here so downstream closure and refinement code sees one
site source rather than two compiler APIs. -/
noncomputable def compiledSiteSource
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    Region host.compilerLeaf.inheritedWires.length
      outputWitness.toFocus.holeRels :=
  let pattern := compiledSplicePatternBodyEvidence input
  layout.compiledSiteSourceOfExactPattern input hadmissible host
    pattern.context pattern.exact pattern.binders pattern.enumeration
    pattern.items outputWitness outputLeaf

/-- The one nested exact-site normalization exposed by the concrete compiler. -/
noncomputable def compiledSiteRegionIso
    (input : Input)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness) :
    RegionIso
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      (layout.compiledSiteSource input hadmissible host outputWitness outputLeaf)
      (Elaboration.finishRegion layout.plugRaw outputLeaf.inheritedWires
        (layout.frameRegion input.site) outputLeaf.items) := by
  let pattern := compiledSplicePatternBodyEvidence input
  have iso := layout.compiledSiteRegionIsoOfExactPattern input hadmissible
    host pattern.fuel pattern.context pattern.exact pattern.binders
    pattern.enumeration pattern.items pattern.computation outputWitness
    outputLeaf
  simpa [compiledSiteSource, pattern] using iso

end PlugLayout

end VisualProof.Concrete.Splice.Input
