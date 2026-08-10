import VisualProof.Concrete.Step
import VisualProof.Concrete.Subgraph.Splice.Input.Discrete
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.HostProjection
import VisualProof.Concrete.Subgraph.Splice.Input.Layout.RootFactor
import VisualProof.Diagram.RenamingIsomorphism
import VisualProof.Refinement.Represents
import VisualProof.Rule.Erasure

namespace VisualProof.Refinement.Erasure

open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Concrete.Elaboration

private noncomputable def materialFromTail
    {outer hostLocal extra : Nat} {rels : RelCtx}
    (tail : ItemSeq (outer + (hostLocal + extra)) rels) :
    Region (outer + hostLocal) rels :=
  .mk extra
    (tail.renameWires
      (FiniteEquiv.finCast (Nat.add_assoc outer hostLocal extra)).symm)

private theorem splice_materialFromTail
    {outer hostLocal extra : Nat} {rels : RelCtx}
    (hostItems : ItemSeq (outer + hostLocal) rels)
    (tail : ItemSeq (outer + (hostLocal + extra)) rels) :
    Region.spliceAt hostLocal hostItems (materialFromTail tail)
        id (fun relation => relation) =
      .mk (hostLocal + extra)
        ((hostItems.renameWires
          (Region.adjoinHostWire outer hostLocal extra)).append tail) := by
  unfold Region.spliceAt Region.adjoinAt materialFromTail
  simp only [Region.renameWires, Region.renameRelations,
    ItemSeq.renameRelations_id, ItemSeq.renameWires_comp]
  congr 2
  have hmap :
      Region.adjoinMaterialWire outer hostLocal extra ∘
          extendWireRenaming id extra ∘
            (FiniteEquiv.finCast (Nat.add_assoc outer hostLocal extra)).symm =
        id := by
    rw [extendWireRenaming_id]
    funext index
    apply Fin.ext
    rfl
  rw [hmap, ItemSeq.renameWires_id]

private theorem rootFromParts
    {arity hostLocal extra : Nat}
    (target : OpenDiagram arity)
    (hostItems : ItemSeq (target.externalClasses + hostLocal) [])
    (sourceHost tail : ItemSeq
      (target.externalClasses + (hostLocal + extra)) [])
    (targetBody : target.body = .mk hostLocal hostItems)
    (hostIso : ItemSeqIso
      (FiniteEquiv.refl
        (Fin (target.externalClasses + (hostLocal + extra)))) []
      sourceHost
      (hostItems.renameWires
        (Region.adjoinHostWire target.externalClasses hostLocal extra))) :
    Rule.Erasure
      (target.withBody (.mk (hostLocal + extra) (sourceHost.append tail)))
      target := by
  let material := materialFromTail (outer := target.externalClasses)
    (hostLocal := hostLocal) tail
  let before := Region.spliceAt hostLocal hostItems material id
    (fun relation => relation)
  have beforeEq : before = .mk (hostLocal + extra)
      ((hostItems.renameWires
        (Region.adjoinHostWire target.externalClasses hostLocal extra)).append
        tail) := by
    exact splice_materialFromTail hostItems tail
  have tailIso := ItemSeqIso.refl tail
  have bodyItems := hostIso.append tailIso
  let outerRefl := FiniteEquiv.refl (Fin target.externalClasses)
  let localRefl := FiniteEquiv.refl (Fin (hostLocal + extra))
  let totalRefl := FiniteEquiv.refl
    (Fin (target.externalClasses + (hostLocal + extra)))
  have extendedEq : extendWireEquiv outerRefl localRefl = totalRefl := by
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) index <;>
      simp [outerRefl, localRefl, totalRefl, extendWireEquiv,
        FiniteEquiv.refl]
  have bodyIso : RegionIso outerRefl []
      (.mk (hostLocal + extra) (sourceHost.append tail)) before := by
    rw [beforeEq]
    refine RegionIso.mk localRefl ?_
    rw [extendedEq]
    exact bodyItems
  let occurrence : Occurrence before
      (target.withBody (.mk (hostLocal + extra) (sourceHost.append tail))) := {
    interface := target
    context := .hole
    host_iso := {
      external := outerRefl
      boundary := fun _ => rfl
      body := bodyIso
    }
  }
  have localProof : Rule.Erasure.Local before target.body := by
    rw [targetBody]
    exact .erase hostLocal hostItems material id (fun relation => relation)
  exact ⟨_, _, before, target.body, occurrence, OpenDiagramIso.refl _, by
    simpa [Rule.atPolarity, DiagramContext.polarity] using localProof⟩

private def frameOpen
    (input : Concrete.Splice.Input)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    Concrete.CheckedOpen := {
  val := { diagram := input.frame.val, boundary := boundary }
  property := {
    diagram_well_formed := input.frame.property
    boundary_is_root_scoped := rootScoped
  }
}

private theorem root_exact
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (siteRoot : input.site = input.frame.val.root)
    (sourceContext : Concrete.Elaboration.WireContext
      input.pattern.val.diagram)
    (sourceExact : sourceContext.Exact input.binderSpine.bodyContainer)
    (sourceBinders : Concrete.Elaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders input.binderSpine.bodyContainer)
    (sourceItems : ItemSeq sourceContext.length sourceRels) :
    Rule.Erasure
      (input.compiledSpliceRootSourceOfExactPattern layout admissible boundary
        rootScoped siteRoot sourceContext sourceExact sourceBinders
        sourceEnumeration sourceItems)
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot input
        admissible boundary rootScoped).elaborate := by
  let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    input admissible boundary rootScoped
  let target := checked.elaborate
  let hostPrepared :=
    input.compiledSpliceRootHostPreparedOfExactPattern layout admissible
      siteRoot
  let patternPrepared :=
    input.compiledSpliceRootPatternPreparedOfExactPattern layout admissible
      siteRoot sourceContext sourceExact sourceBinders sourceEnumeration
      sourceItems
  let reindex := layout.rootReindexOfExactPattern input admissible boundary
    rootScoped siteRoot
  let extra := layout.bodyInternalCarriers.length
  let tail := patternPrepared.renameWires reindex
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let openItems := Concrete.Splice.Input.compiledSpliceOpenRootItems checked
  let targetItems := openItems.items.castWiresEq rootEq
  let hostEmbedding := Region.adjoinHostWire checked.val.exposedWires.length
    checked.val.hiddenWires.length extra
  have targetBody : target.body =
      .mk checked.val.hiddenWires.length targetItems := by
    exact openItems.elaborate_body
  let outputRefl := FiniteEquiv.refl
    (Fin (checked.val.exposedWires.length +
      (checked.val.hiddenWires.length + extra)))
  have hostIso : ItemSeqIso outputRefl []
      (hostPrepared.renameWires reindex)
      (targetItems.renameWires hostEmbedding) := by
    simpa [hostPrepared, reindex, checked, rootEq, openItems, targetItems,
      hostEmbedding, outputRefl, extra] using
      (Concrete.Splice.Input.PlugLayout.compiledSpliceRootHostNormalizationIso
        input layout admissible boundary rootScoped siteRoot)
  have canonicalStep := rootFromParts target targetItems
    (hostPrepared.renameWires reindex)
    tail targetBody hostIso
  let source := input.compiledSpliceRootSourceOfExactPattern layout admissible
    boundary rootScoped siteRoot sourceContext sourceExact sourceBinders
    sourceEnumeration sourceItems
  have sourceBody : source.body =
      .mk (checked.val.hiddenWires.length + extra)
        ((hostPrepared.renameWires reindex).append tail) := by
    unfold source
    unfold Concrete.Splice.Input.compiledSpliceRootSourceOfExactPattern
    simp only [
      Concrete.Splice.Input.compiledSpliceRootSourceFromItems,
      Concrete.Splice.replaceOpenBody]
    change Region.mk _
        ((hostPrepared.append patternPrepared).renameWires reindex) = _
    rw [ItemSeq.renameWires_append]
    rfl
  have bodyEq : source.body =
      .mk (checked.val.hiddenWires.length + extra)
        ((hostPrepared.renameWires reindex).append tail) := sourceBody
  have sourceIso : OpenDiagramIso source
      (target.withBody
        (.mk (checked.val.hiddenWires.length + extra)
          ((hostPrepared.renameWires reindex).append tail))) := {
    external := FiniteEquiv.refl (Fin source.externalClasses)
    boundary := by intro position; rfl
    body := by rw [bodyEq]; exact RegionIso.refl _
  }
  exact Rule.Erasure.iso sourceIso.symm canonicalStep
    (OpenDiagramIso.refl target)

private theorem atPolarity_castArity
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    {polarity : Polarity}
    (step : Rule.atPolarity polarity Rule.Erasure source target) :
    Rule.atPolarity polarity Rule.Erasure
      (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using step

private def openIso_castArity
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem atPolarity_iso
    {arity : Nat} {polarity : Polarity}
    {source target source' target' : OpenDiagram arity}
    (sourceIso : OpenDiagramIso source source')
    (step : Rule.atPolarity polarity Rule.Erasure source target)
    (targetIso : OpenDiagramIso target target') :
    Rule.atPolarity polarity Rule.Erasure source' target' := by
  cases polarity <;> simp only [Rule.atPolarity, Rule.converse] at step ⊢
  · exact Rule.Erasure.iso sourceIso step targetIso
  · exact Rule.Erasure.iso targetIso step sourceIso

private theorem refineBranch
    {canonicalArity actualArity : Nat}
    (arityEq : canonicalArity = actualArity)
    {polarity : Polarity}
    {canonicalSource canonicalTarget : OpenDiagram canonicalArity}
    {actualSource actualTarget : OpenDiagram actualArity}
    (sourceIso : OpenDiagramIso canonicalSource
      (actualSource.castArity arityEq.symm))
    (step : Rule.atPolarity polarity Rule.Erasure
      canonicalSource canonicalTarget)
    (targetIso : OpenDiagramIso canonicalTarget
      (actualTarget.castArity arityEq.symm)) :
    Rule.atPolarity polarity Rule.Erasure actualSource actualTarget := by
  subst actualArity
  simpa using atPolarity_iso sourceIso step targetIso

private noncomputable def transportIsoCheckedOpenEq
    {arity : Nat} {left right : Concrete.CheckedOpen}
    (equality : left = right)
    (leftArity : arity = left.val.boundary.length)
    (rightArity : arity = right.val.boundary.length)
    {source : OpenDiagram arity}
    (iso : OpenDiagramIso source
      (left.elaborate.castArity leftArity.symm)) :
    OpenDiagramIso source
      (right.elaborate.castArity rightArity.symm) := by
  subst right
  simpa using iso

private theorem castArity_castArity
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

private theorem contextualAtPolarity
    {arity hole : Nat} {holeRels : RelCtx}
    (interface : OpenDiagram arity)
    (context : DiagramContext interface.externalClasses hole [] holeRels)
    (actualBefore actualAfter before after : Region hole holeRels)
    (beforeIso : RegionIso (FiniteEquiv.refl (Fin hole)) holeRels
      actualBefore before)
    (afterIso : RegionIso (FiniteEquiv.refl (Fin hole)) holeRels
      actualAfter after)
    (localProof : Rule.Erasure.Local before after) :
    Rule.atPolarity context.polarity Rule.Erasure
      (interface.withBody (context.fill actualBefore))
      (interface.withBody (context.fill actualAfter)) := by
  cases polarityEq : context.polarity with
  | positive =>
      simp only [Rule.atPolarity]
      let actualOccurrence : Occurrence actualBefore
          (interface.withBody (context.fill actualBefore)) := {
        interface := interface
        context := context
        host_iso := OpenDiagramIso.refl _
      }
      let occurrence := actualOccurrence.transportPattern beforeIso
      let targetIso : OpenDiagramIso
          (interface.withBody (context.fill actualAfter))
          (interface.withBody (context.fill after)) :=
        OpenDiagram.withBody_iso (context.fillIso afterIso)
      exact ⟨_, _, before, after, occurrence, targetIso, by
        change Rule.atPolarity context.polarity Rule.Erasure.Local before after
        rw [polarityEq]
        exact localProof⟩
  | negative =>
      simp only [Rule.atPolarity, Rule.converse]
      let actualOccurrence : Occurrence actualAfter
          (interface.withBody (context.fill actualAfter)) := {
        interface := interface
        context := context
        host_iso := OpenDiagramIso.refl _
      }
      let occurrence := actualOccurrence.transportPattern afterIso
      let targetIso : OpenDiagramIso
          (interface.withBody (context.fill actualBefore))
          (interface.withBody (context.fill before)) :=
        OpenDiagram.withBody_iso (context.fillIso beforeIso)
      exact ⟨_, _, after, before, occurrence, targetIso, by
        change Rule.atPolarity context.polarity Rule.Erasure.Local after before
        rw [polarityEq]
        exact localProof⟩

private theorem nestedFromPrepared
    {arity sourceOuter targetOuter hostLocal extra : Nat}
    {rels : RelCtx}
    (interface : OpenDiagram arity)
    (context : DiagramContext interface.externalClasses targetOuter [] rels)
    (hostItems : ItemSeq (sourceOuter + hostLocal) rels)
    (sourceHost tail : ItemSeq
      (sourceOuter + (hostLocal + extra)) rels)
    (rootWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (hostIso : ItemSeqIso
      (FiniteEquiv.refl (Fin (sourceOuter + (hostLocal + extra)))) rels
      sourceHost
      (hostItems.renameWires
        (Region.adjoinHostWire sourceOuter hostLocal extra))) :
    Rule.atPolarity context.polarity Rule.Erasure
      (interface.withBody (context.fill
        ((Region.mk (hostLocal + extra) (sourceHost.append tail)
          ).renameWires rootWire)))
      (interface.withBody (context.fill
        ((Region.mk hostLocal hostItems).renameWires rootWire))) := by
  let totalWire := extendWireEquiv rootWire
    (FiniteEquiv.refl (Fin (hostLocal + extra)))
  let hostWire := extendWireEquiv rootWire
    (FiniteEquiv.refl (Fin hostLocal))
  let targetHost := hostItems.renameWires hostWire
  let targetTail := tail.renameWires totalWire
  let material := materialFromTail (outer := targetOuter)
    (hostLocal := hostLocal) targetTail
  let before := Region.spliceAt hostLocal targetHost material id
    (fun relation => relation)
  let after := Region.mk hostLocal targetHost
  have beforeEq : before = .mk (hostLocal + extra)
      ((targetHost.renameWires
        (Region.adjoinHostWire targetOuter hostLocal extra)).append
        targetTail) := by
    exact splice_materialFromTail targetHost targetTail
  have lifted := hostIso.renameWires_commuting totalWire totalWire
    (FiniteEquiv.refl (Fin (targetOuter + (hostLocal + extra)))) (by
      funext index
      rfl)
  have hostCommutes := Region.extendWireEquiv_adjoinHostWire_commutes
    rootWire hostLocal extra
  have targetHostIso : ItemSeqIso
      (FiniteEquiv.refl (Fin (targetOuter + (hostLocal + extra)))) rels
      (sourceHost.renameWires totalWire)
      (targetHost.renameWires
        (Region.adjoinHostWire targetOuter hostLocal extra)) := by
    simpa only [targetHost, ItemSeq.renameWires_comp, hostCommutes,
      totalWire, hostWire] using lifted
  have bodyItems := targetHostIso.append (ItemSeqIso.refl targetTail)
  let actualBefore :=
    (Region.mk (hostLocal + extra) (sourceHost.append tail)).renameWires
      rootWire
  let actualAfter := (Region.mk hostLocal hostItems).renameWires rootWire
  have totalWireEq :
      extendWireRenaming rootWire.toFun (hostLocal + extra) =
        totalWire.toFun := by
    rfl
  have actualBeforeEq : actualBefore =
      Region.mk (hostLocal + extra)
        ((sourceHost.renameWires totalWire).append targetTail) := by
    simp only [actualBefore, Region.renameWires,
      ItemSeq.renameWires_append, targetTail, totalWireEq]
  have totalRefl : extendWireEquiv
      (FiniteEquiv.refl (Fin targetOuter))
      (FiniteEquiv.refl (Fin (hostLocal + extra))) =
      FiniteEquiv.refl (Fin (targetOuter + (hostLocal + extra))) := by
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) index <;>
      simp [extendWireEquiv, FiniteEquiv.refl]
  have actualBeforeIso : RegionIso
      (FiniteEquiv.refl (Fin targetOuter)) rels actualBefore before := by
    rw [actualBeforeEq, beforeEq]
    refine RegionIso.mk (FiniteEquiv.refl (Fin (hostLocal + extra))) ?_
    rw [totalRefl]
    exact bodyItems
  have actualAfterEq : actualAfter = after := by
    unfold actualAfter after targetHost hostWire
    rfl
  have actualAfterIso : RegionIso
      (FiniteEquiv.refl (Fin targetOuter)) rels actualAfter after := by
    rw [actualAfterEq]
    exact RegionIso.refl after
  have localProof : Rule.Erasure.Local before after := by
    unfold before after
    exact .erase hostLocal targetHost material id
      (fun relation => relation)
  exact contextualAtPolarity interface context actualBefore actualAfter
    before after actualBeforeIso actualAfterIso localProof

theorem nested
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (nested : input.site ≠ input.frame.val.root) :
    let view := input.compiledSpliceOutputOpenView layout admissible
      boundary rootScoped
    Rule.atPolarity view.focus.context.polarity Rule.Erasure
      (input.compiledSpliceNestedSource layout admissible boundary
        rootScoped nested)
      (input.compiledSpliceNestedHostOpen layout admissible boundary
        rootScoped nested) := by
  dsimp only
  let host := input.compiledSpliceHostView admissible
  let output := (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    input layout admissible boundary rootScoped).elaborate
  let view := input.compiledSpliceOutputOpenView layout admissible
    boundary rootScoped
  let outputLeaf := input.compiledSpliceOutputNestedLeaf layout admissible
    boundary rootScoped nested
  let localEq := Concrete.Elaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  let hostRelation : RelationRenaming host.intrinsicPath.toFocus.holeRels
      view.intrinsicPath.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf relation
  let hostItems :=
    (host.compilerLeaf.items.castWiresEq localEq).renameRelations hostRelation
  let sourceHost :=
    (host.compilerLeaf.items.renameWires
      (layout.hostPreparedWireOfExactPattern host view.intrinsicPath
        outputLeaf)).renameRelations hostRelation
  let extra := layout.bodyInternalCarriers.length
  let hostAdjoin := Region.adjoinHostWire
    host.compilerLeaf.inheritedWires.length
    (Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
      input.site).length extra
  have hostItemsEq : sourceHost = hostItems.renameWires hostAdjoin := by
    unfold sourceHost hostItems hostAdjoin
    rw [layout.hostPreparedWireOfExactPattern_eq_adjoinHost admissible host
      view.intrinsicPath outputLeaf]
    simp only [ItemSeq.castWiresEq_eq_renameWires]
    simp only [ItemSeq.renameWires_renameRelations]
    simpa only [extra, hostAdjoin] using
      (ItemSeq.renameWires_comp
        (host.compilerLeaf.items.renameRelations hostRelation)
        (Fin.cast localEq)
        (Region.adjoinHostWire host.compilerLeaf.inheritedWires.length
          (Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length layout.bodyInternalCarriers.length)).symm
  have hostIso : ItemSeqIso
      (FiniteEquiv.refl (Fin
        (host.compilerLeaf.inheritedWires.length +
          ((Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length + extra))))
      view.intrinsicPath.toFocus.holeRels sourceHost
      (hostItems.renameWires hostAdjoin) := by
    rw [hostItemsEq]
    exact ItemSeqIso.refl _
  let rootWire :=
    (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf).trans
      (FiniteEquiv.finCast outputLeaf.inheritedLength)
  let arityEq :
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot input admissible
        boundary rootScoped).val.boundary.length =
      (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot input layout
        admissible boundary rootScoped).val.boundary.length := by
    simp [Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
  let pattern := Concrete.Splice.Input.compiledSplicePatternBodyEvidence input
  let binderWitness := layout.patternBinderWitnessOfEnumeration admissible
    pattern.binders pattern.enumeration view.intrinsicPath outputLeaf
  let tail :=
    (pattern.items.renameWires
      (layout.patternPreparedWireOfExactPattern admissible host
        pattern.context pattern.exact view.intrinsicPath outputLeaf)
      ).renameRelations binderWitness.relationMap
  have uncastStep := nestedFromPrepared (interface := output)
    (context := view.focus.context) hostItems sourceHost tail rootWire hostIso
  have step := atPolarity_castArity arityEq.symm uncastStep
  simpa [Concrete.Splice.Input.compiledSpliceNestedSource,
    Concrete.Splice.Input.PlugLayout.compiledSiteSource,
    Concrete.Splice.Input.PlugLayout.compiledSiteSourceOfExactPattern,
    Concrete.Splice.Input.compiledSpliceNestedHostOpen,
    Concrete.Splice.replaceOpenBody, OpenDiagram.withBody,
    host, output, view, outputLeaf, localEq, hostRelation, hostItems,
    sourceHost, extra, hostAdjoin, rootWire, arityEq, pattern,
    binderWitness, tail] using step

private noncomputable def nestedSourceIso
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (nested : input.site ≠ input.frame.val.root) :
    let arityEq :
        (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot input
          admissible boundary rootScoped).val.boundary.length =
        (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot input layout
          admissible boundary rootScoped).val.boundary.length := by
      simp [Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
        Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot,
        Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
        Concrete.Splice.Input.PlugLayout.outputOpenRoot]
    OpenDiagramIso
      (input.compiledSpliceNestedSource layout admissible boundary
        rootScoped nested)
      ((Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot input layout
        admissible boundary rootScoped).elaborate.castArity arityEq.symm) := by
  dsimp only
  let host := input.compiledSpliceHostView admissible
  let output := (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    input layout admissible boundary rootScoped).elaborate
  let view := input.compiledSpliceOutputOpenView layout admissible
    boundary rootScoped
  let outputLeaf := input.compiledSpliceOutputNestedLeaf layout admissible
    boundary rootScoped nested
  let source := layout.compiledSiteSource input admissible host
    view.intrinsicPath outputLeaf
  let inherited := layout.inheritedWireEquiv host.intrinsicPath
    host.compilerLeaf view.intrinsicPath outputLeaf
  let rootWire := inherited.trans
    (FiniteEquiv.finCast outputLeaf.inheritedLength)
  have siteIso := layout.compiledSiteRegionIso input admissible host
    view.intrinsicPath outputLeaf
  have focusIso : RegionIso (FiniteEquiv.refl (Fin view.focus.holeWires))
      view.intrinsicPath.toFocus.holeRels
      (source.renameWires rootWire) view.focus.body := by
    have lifted := siteIso.renameWires_commuting rootWire
      (Fin.cast outputLeaf.inheritedLength)
      (FiniteEquiv.refl (Fin view.focus.holeWires)) (by
        funext index
        rfl)
    have focusBodyEq : view.focus.body =
        (Concrete.Elaboration.finishRegion layout.plugRaw
          outputLeaf.inheritedWires (layout.frameRegion input.site)
          outputLeaf.items).renameWires
            (Fin.cast outputLeaf.inheritedLength) := by
      simpa [view, outputLeaf, Concrete.Splice.OpenSiteView.focus,
        Region.castWiresEq_eq_renameWires] using outputLeaf.bodyComputation
    rw [focusBodyEq]
    simpa [source, inherited, rootWire] using lifted
  have bodyIso := view.focus.context.fillIso focusIso
  have outputEta : output.withBody output.body = output := by
    cases output
    rfl
  have rebuilt : output.withBody
      (view.focus.context.fill view.focus.body) = output := by
    rw [view.rebuild]
    exact outputEta
  have uncastIso : OpenDiagramIso
      (Concrete.Splice.replaceOpenBody output
        (view.focus.context.fill (source.renameWires rootWire))) output := by
    have iso := OpenDiagram.withBody_iso bodyIso
    rw [rebuilt] at iso
    simpa [Concrete.Splice.replaceOpenBody] using iso
  let arityEq :
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot input admissible
        boundary rootScoped).val.boundary.length =
      (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot input layout
        admissible boundary rootScoped).val.boundary.length := by
    simp [Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
  have castIso := openIso_castArity arityEq.symm uncastIso
  simpa [Concrete.Splice.Input.compiledSpliceNestedSource,
    host, output, view, outputLeaf, source, inherited, rootWire,
    arityEq] using castIso

/-- The structural bridge needed by both insertion and erasure. -/
theorem splice_refines
    (input : Concrete.Splice.Input)
    (respects : input.AttachmentsRespectBoundary)
    {result : Concrete.Checked}
    (success : input.spliceChecked = .ok result)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    let arityEq :
        (frameOpen input boundary rootScoped).val.boundary.length =
          (input.spliceCheckedResultOpen success boundary rootScoped).val.boundary.length := by
      simp [frameOpen, Concrete.Splice.Input.spliceCheckedResultOpen,
        Concrete.Splice.Input.spliceCheckedResultOpenRaw,
        Concrete.Splice.Input.PlugLayout.outputOpenRoot]
    let admissible := (Concrete.Splice.Input.spliceChecked_sound success).2.1
    let polarity :=
      if input.site = input.frame.val.root then Polarity.positive
      else (input.compiledSpliceOutputOpenView input.plugLayout admissible
        boundary rootScoped).focus.context.polarity
    Rule.atPolarity polarity Rule.Erasure
      (input.spliceCheckedResultOpen success boundary rootScoped).elaborate
      ((frameOpen input boundary rootScoped).elaborate.castArity arityEq) := by
  dsimp only
  let admissible := (Concrete.Splice.Input.spliceChecked_sound success).2.1
  let layout := input.plugLayout
  let resultOpen := input.spliceCheckedResultOpen success boundary rootScoped
  let outputOpen := Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    input layout admissible boundary rootScoped
  let coalescedOpen :=
    Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot input admissible
      boundary rootScoped
  let targetOpen := frameOpen input boundary rootScoped
  let targetArity : targetOpen.val.boundary.length =
      resultOpen.val.boundary.length := by
    simp [targetOpen, resultOpen, frameOpen,
      Concrete.Splice.Input.spliceCheckedResultOpen,
      Concrete.Splice.Input.spliceCheckedResultOpenRaw,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
  let canonicalArity : coalescedOpen.val.boundary.length =
      resultOpen.val.boundary.length := by
    simp [coalescedOpen, resultOpen,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
      Concrete.Splice.Input.spliceCheckedResultOpen,
      Concrete.Splice.Input.spliceCheckedResultOpenRaw,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
  let outputArity : coalescedOpen.val.boundary.length =
      outputOpen.val.boundary.length := by
    simp [coalescedOpen, outputOpen,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.outputOpenRoot]
  let frameArity : coalescedOpen.val.boundary.length =
      targetOpen.val.boundary.length := by
    simp [coalescedOpen, targetOpen, frameOpen,
      Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Concrete.Splice.Input.PlugLayout.coalescedOpenRoot]
  have resultOpenEq : resultOpen = outputOpen := by
    exact Concrete.Splice.Input.spliceCheckedResultOpen_eq_checkedOutputOpenRoot
      input success boundary rootScoped
  let rawFrameIso :=
    Concrete.Splice.Input.coalescedFrameOpenIsoOfAttachmentsRespectBoundary
      input respects boundary
  have coalescedToFrame : OpenDiagramIso coalescedOpen.elaborate
      ((targetOpen.elaborate.castArity targetArity).castArity
        canonicalArity.symm) := by
    have iso := rawFrameIso.elaborate_isomorphic
      coalescedOpen.property targetOpen.property
    have base : OpenDiagramIso coalescedOpen.elaborate
        (targetOpen.elaborate.castArity frameArity.symm) := by
      simpa [rawFrameIso, coalescedOpen, targetOpen, frameOpen] using iso
    rw [castArity_castArity]
    simpa using base
  by_cases siteRoot : input.site = input.frame.val.root
  · let pattern :=
      Concrete.Splice.Input.compiledSplicePatternBodyEvidence input
    let rootSource := input.compiledSpliceRootSourceOfExactPattern layout
      admissible boundary rootScoped siteRoot pattern.context pattern.exact
      pattern.binders pattern.enumeration pattern.items
    have step : Rule.atPolarity Polarity.positive Rule.Erasure rootSource
        coalescedOpen.elaborate := by
      simpa [Rule.atPolarity, rootSource, coalescedOpen] using
        root_exact input layout admissible boundary rootScoped siteRoot
          pattern.context pattern.exact pattern.binders pattern.enumeration
          pattern.items
    have sourceIso : OpenDiagramIso
        rootSource
        (resultOpen.elaborate.castArity canonicalArity.symm) := by
      have iso := input.compiledSpliceRootIsoOfExactPattern layout admissible
        boundary rootScoped siteRoot pattern.fuel pattern.context pattern.exact
        pattern.binders pattern.enumeration pattern.items pattern.computation
      have base : OpenDiagramIso
          rootSource
          (outputOpen.elaborate.castArity outputArity.symm) := by
        simpa [outputOpen, rootSource] using iso
      exact transportIsoCheckedOpenEq resultOpenEq.symm outputArity
        canonicalArity base
    have branch := refineBranch canonicalArity sourceIso step
      coalescedToFrame
    simpa [admissible, layout, siteRoot, resultOpen, targetOpen,
      targetArity, pattern] using branch
  · let view := input.compiledSpliceOutputOpenView layout admissible boundary
      rootScoped
    let hostOpen := input.compiledSpliceNestedHostOpen layout admissible
      boundary rootScoped siteRoot
    have hostToFrame : OpenDiagramIso hostOpen
        ((targetOpen.elaborate.castArity targetArity).castArity
          canonicalArity.symm) := by
      exact (input.compiledSpliceNestedHostIso layout admissible boundary
        rootScoped siteRoot).symm.trans coalescedToFrame
    let nestedSource := input.compiledSpliceNestedSource layout admissible
      boundary rootScoped siteRoot
    have sourceIso : OpenDiagramIso nestedSource
        (resultOpen.elaborate.castArity canonicalArity.symm) := by
      have iso := nestedSourceIso input layout admissible boundary rootScoped
        siteRoot
      have base : OpenDiagramIso nestedSource
          (outputOpen.elaborate.castArity outputArity.symm) := by
        simpa [outputOpen, nestedSource] using iso
      exact transportIsoCheckedOpenEq resultOpenEq.symm outputArity
        canonicalArity base
    have step : Rule.atPolarity view.focus.context.polarity Rule.Erasure
        nestedSource hostOpen := by
      simpa [view, hostOpen, nestedSource] using
        nested input layout admissible boundary rootScoped siteRoot
    have branch := refineBranch canonicalArity sourceIso step hostToFrame
    simpa [admissible, layout, siteRoot, view, hostOpen, resultOpen,
      targetOpen, targetArity, nestedSource] using branch

end VisualProof.Refinement.Erasure
