import VisualProof.Concrete.Step
import VisualProof.Concrete.Subgraph.Splice.Input.Discrete
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.HostProjectionEmpty
import VisualProof.Diagram.RenamingIsomorphism
import VisualProof.Refinement.Represents
import VisualProof.Rule.Erasure

namespace VisualProof.Refinement.Erasure

open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Concrete.Elaboration

private theorem renameRelationsToNilEqCast
    (items : ItemSeq wires rels)
    (hrels : rels = []) (rho : RelationRenaming rels []) :
    items.renameRelations rho =
      cast (congrArg (ItemSeq wires) hrels) items := by
  subst rels
  have hrho :
      ((fun {arity} (relation : Theory.RelVar [] arity) => rho relation) :
        RelationRenaming [] []) =
      ((fun {arity} (relation : Theory.RelVar [] arity) => relation) :
        RelationRenaming [] []) := by
    apply @funext
    intro arity
    funext relation
    exact Fin.elim0 relation.index
  change items.renameRelations
    ((fun {arity} (relation : Theory.RelVar [] arity) => rho relation) :
      RelationRenaming [] []) = _
  rw [hrho, ItemSeq.renameRelations_id]
  rfl

private theorem conjoinLeftWireEqAdjoinHostWire
    (outer hostLocal extra : Nat) :
    Region.conjoinLeftWire outer hostLocal extra =
      Region.adjoinHostWire outer hostLocal extra := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun localWire => ?_) wire
  · apply Fin.ext
    simp [Region.conjoinLeftWire, Region.adjoinHostWire]
  · apply Fin.ext
    simp [Region.conjoinLeftWire, Region.adjoinHostWire]

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

private noncomputable def rootHostItemsIso
    (input : Concrete.Splice.Input)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (siteRoot : input.site = input.frame.val.root) :
    let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      input admissible boundary rootScoped
    let host := input.compiledSpliceHostView admissible
    let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible
      siteRoot
    let hostItems : ItemSeq
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
        hrels) host.compilerLeaf.items
    let context := host.compilerLeaf.inheritedWires.extend input.site
    let exact : context.Exact input.coalesceFrameRaw.root := by
      change context.Exact input.frame.val.root
      rw [← siteRoot]
      exact host.compilerLeaf.wiresExact
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let openItems := Concrete.Splice.Input.compiledSpliceOpenRootItems checked
    let transport :=
      (Concrete.exactContextToOpenRootWireEquiv checked context exact).trans
        (FiniteEquiv.finCast rootEq)
    ItemSeqIso
      (FiniteEquiv.refl
        (Fin (checked.val.exposedWires.length + checked.val.hiddenWires.length))) []
      (hostItems.renameWires transport)
      (openItems.items.castWiresEq rootEq) := by
  dsimp only
  let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    input admissible boundary rootScoped
  let host := input.compiledSpliceHostView admissible
  let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible
    siteRoot
  let hostItems : ItemSeq
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
      hrels) host.compilerLeaf.items
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let exact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← siteRoot]
    exact host.compilerLeaf.wiresExact
  let openItems := Concrete.Splice.Input.compiledSpliceOpenRootItems checked
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let contextToOpen := Concrete.exactContextToOpenRootWireEquiv checked context exact
  let transport := contextToOpen.trans (FiniteEquiv.finCast rootEq)
  have hclosed : Concrete.Elaboration.compileOccurrencesWith?
      input.coalesceFrameRaw
      (Concrete.Elaboration.compileRegion? input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      context Concrete.Elaboration.BinderContext.empty
      (Concrete.Elaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some hostItems := by
    exact input.compiledSpliceRootHostItems_computation admissible siteRoot
  have hopen := Concrete.Splice.Input.PlugLayout.compiledCoalescedRootItemsIsoFromExactContext
    input admissible boundary rootScoped context exact hclosed
      openItems.computation
  have hopenCast : ItemSeqIso transport [] hostItems
      (openItems.items.castWiresEq rootEq) := by
    rw [ItemSeq.castWiresEq_eq_renameWires]
    exact hopen.trans
      (ItemSeqIso.renameWiresEquiv openItems.items
        (FiniteEquiv.finCast rootEq))
  let totalRefl := FiniteEquiv.refl
    (Fin (checked.val.exposedWires.length + checked.val.hiddenWires.length))
  have hitems : ItemSeqIso totalRefl []
      (hostItems.renameWires transport)
      (openItems.items.castWiresEq rootEq) := by
    have renamed :=
      (ItemSeqIso.renameWiresEquiv hostItems transport).symm.trans hopenCast
    have hwire : transport.symm.trans transport = totalRefl := by
      apply FiniteEquiv.ext
      intro index
      exact transport.right_inv index
    exact hwire ▸ renamed
  exact hitems

private theorem rootEmptyBodyEqSplice
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (siteRoot : input.site = input.frame.val.root)
    (empty : input.binderSpine.proxyCount = 0) :
    let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      input admissible boundary rootScoped
    let host := input.compiledSpliceHostView admissible
    let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible
      siteRoot
    let hostItems : ItemSeq
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
        hrels) host.compilerLeaf.items
    let context := host.compilerLeaf.inheritedWires.extend input.site
    let exact : context.Exact input.coalesceFrameRaw.root := by
      change context.Exact input.frame.val.root
      rw [← siteRoot]
      exact host.compilerLeaf.wiresExact
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let transport :=
      (Concrete.exactContextToOpenRootWireEquiv checked context exact).trans
        (FiniteEquiv.finCast rootEq)
    let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems input.pattern
    let outputWitness := input.compiledSpliceOutputRootWitness layout admissible
      siteRoot
    let outputLeaf := input.compiledSpliceOutputRootLeaf layout admissible
      siteRoot
    let patternPrepared :=
      (pattern.items.renameWires
        (layout.patternRootSeamPreparedWireOfEmpty admissible host))
          |>.renameRelations
            (Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
              outputWitness.toFocus.holeRels)
    let castEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfEmpty admissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) empty).trans
        (FiniteEquiv.finCast castEq).symm
    let outputRootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [siteRoot] using outputLeaf.wiresExact
    let outputEq :
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).rootWires.length =
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).exposedWires.length +
            (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let outputTransport :=
      (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
        input layout admissible boundary rootScoped
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputRootExact).trans (FiniteEquiv.finCast outputEq)
    let reindex :=
      Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex closedWire
        outputTransport
        (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout boundary)
        (layout.rootLocalWireEquivOfEmpty input boundary siteRoot empty)
    let tail := patternPrepared.renameWires reindex
    (input.compiledSpliceRootSourceOfEmpty layout admissible boundary
      rootScoped siteRoot empty).body =
      Region.spliceAt checked.val.hiddenWires.length
        (hostItems.renameWires transport) (materialFromTail tail)
        id (fun relation => relation) := by
  dsimp only
  let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    input admissible boundary rootScoped
  let host := input.compiledSpliceHostView admissible
  let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible
    siteRoot
  let hostItems : ItemSeq
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
      hrels) host.compilerLeaf.items
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let exact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← siteRoot]
    exact host.compilerLeaf.wiresExact
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let transport :=
    (Concrete.exactContextToOpenRootWireEquiv checked context exact).trans
      (FiniteEquiv.finCast rootEq)
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems input.pattern
  let outputWitness := input.compiledSpliceOutputRootWitness layout admissible
    siteRoot
  let outputLeaf := input.compiledSpliceOutputRootLeaf layout admissible
    siteRoot
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfEmpty admissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (pattern.items.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty admissible host))
        |>.renameRelations
          (Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
            outputWitness.toFocus.holeRels)
  let castEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfEmpty admissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) empty).trans
      (FiniteEquiv.finCast castEq).symm
  let outputRootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [siteRoot] using outputLeaf.wiresExact
  let outputEq :
      (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).rootWires.length =
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).exposedWires.length +
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let outputTransport :=
    (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
      input layout admissible boundary rootScoped
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputRootExact).trans (FiniteEquiv.finCast outputEq)
  let reindex :=
    Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex closedWire
      outputTransport
      (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout boundary)
      (layout.rootLocalWireEquivOfEmpty input boundary siteRoot empty)
  let tail := patternPrepared.renameWires reindex
  have hsplice := splice_materialFromTail
    (hostItems.renameWires transport) tail
  change (input.compiledSpliceRootSourceOfEmpty layout admissible boundary
      rootScoped siteRoot empty).body =
    Region.spliceAt checked.val.hiddenWires.length
      (hostItems.renameWires transport) (materialFromTail tail)
      id (fun relation => relation)
  apply Eq.trans (b := Region.mk
    (checked.val.hiddenWires.length + input.pattern.val.hiddenWires.length)
    ((hostItems.renameWires transport |>.renameWires
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length input.pattern.val.hiddenWires.length))
      |>.append tail))
  · unfold Concrete.Splice.Input.compiledSpliceRootSourceOfEmpty
    unfold Concrete.Splice.Input.compiledSpliceRootSourceFromItems
      Concrete.Splice.replaceOpenBody
    dsimp only
    change Region.mk (checked.val.hiddenWires.length +
        input.pattern.val.hiddenWires.length)
      ((hostPrepared.append patternPrepared).renameWires reindex) = _
    rw [ItemSeq.renameWires_append]
    congr 2
    dsimp [hostPrepared]
    have hrelation := renameRelationsToNilEqCast
      host.compilerLeaf.items hrels
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
    have hprepared :
        (host.compilerLeaf.items.renameWires
          (layout.hostSeamPreparedWireOfEmpty admissible host)).renameRelations
            (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf) =
          hostItems.renameWires
            (layout.hostSeamPreparedWireOfEmpty admissible host) := by
      rw [ItemSeq.renameWires_renameRelations]
      exact congrArg
        (fun items => items.renameWires
          (layout.hostSeamPreparedWireOfEmpty admissible host)) hrelation
    apply Eq.trans (b :=
      (hostItems.renameWires
        (layout.hostSeamPreparedWireOfEmpty admissible host)).renameWires
          reindex)
    · exact congrArg (fun items => items.renameWires reindex) hprepared
    · rw [ItemSeq.renameWires_comp]
      rw [ItemSeq.renameWires_comp]
      apply congrArg (fun wireMap => hostItems.renameWires wireMap)
      funext index
      have hfactor :=
        Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_host_factor_empty
          input layout admissible boundary rootScoped siteRoot empty index
      change reindex
          (layout.hostSeamPreparedWireOfEmpty admissible host index) = _ at hfactor
      change reindex
          (layout.hostSeamPreparedWireOfEmpty admissible host index) =
        Region.adjoinHostWire checked.val.exposedWires.length
          checked.val.hiddenWires.length input.pattern.val.hiddenWires.length
          (transport index)
      rw [hfactor]
      unfold Concrete.Splice.Input.PlugLayout.rootHostOpenEmbedding
      dsimp [checked, context, exact, transport]
      rw [conjoinLeftWireEqAdjoinHostWire]
      apply congrArg (Region.adjoinHostWire
        checked.val.exposedWires.length checked.val.hiddenWires.length
        input.pattern.val.hiddenWires.length)
      apply Fin.ext
      rfl
  · exact hsplice.symm

private theorem rootNonemptyBodyEqSplice
    (input : Concrete.Splice.Input) (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (siteRoot : input.site = input.frame.val.root)
    (nonempty : input.binderSpine.proxyCount ≠ 0) :
    let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      input admissible boundary rootScoped
    let host := input.compiledSpliceHostView admissible
    let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible siteRoot
    let hostItems : ItemSeq
        (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
      cast (congrArg
        (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
        hrels) host.compilerLeaf.items
    let context := host.compilerLeaf.inheritedWires.extend input.site
    let exact : context.Exact input.coalesceFrameRaw.root := by
      change context.Exact input.frame.val.root
      rw [← siteRoot]
      exact host.compilerLeaf.wiresExact
    let rootEq : checked.val.rootWires.length =
        checked.val.exposedWires.length + checked.val.hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let transport :=
      (Concrete.exactContextToOpenRootWireEquiv checked context exact).trans
        (FiniteEquiv.finCast rootEq)
    let pattern := Concrete.Splice.Input.compiledSpliceTerminalView input nonempty
    let outputWitness := input.compiledSpliceOutputRootWitness layout admissible siteRoot
    let outputLeaf := input.compiledSpliceOutputRootLeaf layout admissible siteRoot
    let patternPrepared :=
      (pattern.leaf.items.renameWires
        (layout.patternSeamPreparedWireOfNonempty admissible host
          pattern.witness pattern.leaf nonempty)).renameRelations
        (fun {arity} relation =>
          layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf
            (layout.coalescedTerminalRelationRenaming admissible
              host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
              nonempty relation))
    let castEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion input.site)
    let closedWire :=
      (layout.siteCombinedWireEquivOfNonempty admissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) nonempty).trans
        (FiniteEquiv.finCast castEq).symm
    let outputRootExact :
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
      simpa [siteRoot] using outputLeaf.wiresExact
    let outputEq :
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).rootWires.length =
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).exposedWires.length +
            (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).hiddenWires.length := by
      simp [Concrete.OpenDiagram.rootWires]
    let outputTransport :=
      (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
        input layout admissible boundary rootScoped
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputRootExact).trans (FiniteEquiv.finCast outputEq)
    let reindex :=
      Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex closedWire
        outputTransport
        (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout boundary)
        (layout.rootLocalWireEquivOfNonempty input boundary siteRoot nonempty)
    let tail := patternPrepared.renameWires reindex
    (input.compiledSpliceRootSourceOfNonempty layout admissible boundary
      rootScoped siteRoot nonempty).body =
      Region.spliceAt checked.val.hiddenWires.length
        (hostItems.renameWires transport) (materialFromTail tail)
        id (fun relation => relation) := by
  dsimp only
  let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    input admissible boundary rootScoped
  let host := input.compiledSpliceHostView admissible
  let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible siteRoot
  let hostItems : ItemSeq
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
      hrels) host.compilerLeaf.items
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let exact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← siteRoot]
    exact host.compilerLeaf.wiresExact
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let transport :=
    (Concrete.exactContextToOpenRootWireEquiv checked context exact).trans
      (FiniteEquiv.finCast rootEq)
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView input nonempty
  let outputWitness := input.compiledSpliceOutputRootWitness layout admissible siteRoot
  let outputLeaf := input.compiledSpliceOutputRootLeaf layout admissible siteRoot
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty admissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (pattern.leaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty admissible host
        pattern.witness pattern.leaf nonempty)).renameRelations
      (fun {arity} relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming admissible
            host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
            nonempty relation))
  let castEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfNonempty admissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) nonempty).trans
      (FiniteEquiv.finCast castEq).symm
  let outputRootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [siteRoot] using outputLeaf.wiresExact
  let outputEq :
      (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).rootWires.length =
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).exposedWires.length +
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let outputTransport :=
    (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
      input layout admissible boundary rootScoped
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputRootExact).trans (FiniteEquiv.finCast outputEq)
  let reindex :=
    Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex closedWire
      outputTransport
      (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout boundary)
      (layout.rootLocalWireEquivOfNonempty input boundary siteRoot nonempty)
  let tail := patternPrepared.renameWires reindex
  let extra := (Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
    input.binderSpine.bodyContainer).length
  have hsplice := splice_materialFromTail
    (hostItems.renameWires transport) tail
  change (input.compiledSpliceRootSourceOfNonempty layout admissible boundary
      rootScoped siteRoot nonempty).body =
    Region.spliceAt checked.val.hiddenWires.length
      (hostItems.renameWires transport) (materialFromTail tail)
      id (fun relation => relation)
  apply Eq.trans (b := Region.mk (checked.val.hiddenWires.length + extra)
    (((hostItems.renameWires transport).renameWires
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length extra)).append tail))
  · unfold Concrete.Splice.Input.compiledSpliceRootSourceOfNonempty
    unfold Concrete.Splice.Input.compiledSpliceRootSourceFromItems
      Concrete.Splice.replaceOpenBody
    dsimp only
    change Region.mk (checked.val.hiddenWires.length + extra)
      ((hostPrepared.append patternPrepared).renameWires reindex) = _
    rw [ItemSeq.renameWires_append]
    congr 2
    dsimp [hostPrepared]
    have hrelation := renameRelationsToNilEqCast
      host.compilerLeaf.items hrels
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
    have hprepared :
        (host.compilerLeaf.items.renameWires
          (layout.hostSeamPreparedWireOfNonempty admissible host)).renameRelations
            (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf) =
          hostItems.renameWires
            (layout.hostSeamPreparedWireOfNonempty admissible host) := by
      rw [ItemSeq.renameWires_renameRelations]
      exact congrArg
        (fun items => items.renameWires
          (layout.hostSeamPreparedWireOfNonempty admissible host)) hrelation
    apply Eq.trans (b :=
      (hostItems.renameWires
        (layout.hostSeamPreparedWireOfNonempty admissible host)).renameWires
          reindex)
    · exact congrArg (fun items => items.renameWires reindex) hprepared
    · rw [ItemSeq.renameWires_comp]
      rw [ItemSeq.renameWires_comp]
      apply congrArg (fun wireMap => hostItems.renameWires wireMap)
      funext index
      have hfactor :=
        Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex_host_factor_nonempty
          input layout admissible boundary rootScoped siteRoot nonempty index
      change reindex
          (layout.hostSeamPreparedWireOfNonempty admissible host index) = _ at hfactor
      change reindex
          (layout.hostSeamPreparedWireOfNonempty admissible host index) =
        Region.adjoinHostWire checked.val.exposedWires.length
          checked.val.hiddenWires.length extra (transport index)
      rw [hfactor]
      unfold Concrete.Splice.Input.PlugLayout.rootHostOpenEmbedding
      dsimp [checked, context, exact, transport]
      rw [conjoinLeftWireEqAdjoinHostWire]
      apply congrArg (Region.adjoinHostWire
        checked.val.exposedWires.length checked.val.hiddenWires.length extra)
      apply Fin.ext
      rfl
  · exact hsplice.symm

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

theorem root_empty
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (siteRoot : input.site = input.frame.val.root)
    (empty : input.binderSpine.proxyCount = 0) :
    Rule.Erasure
      (input.compiledSpliceRootSourceOfEmpty layout admissible boundary
        rootScoped siteRoot empty)
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot input
        admissible boundary rootScoped).elaborate := by
  let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    input admissible boundary rootScoped
  let target := checked.elaborate
  let host := input.compiledSpliceHostView admissible
  let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible
    siteRoot
  let hostItems : ItemSeq
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
      hrels) host.compilerLeaf.items
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let exact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← siteRoot]
    exact host.compilerLeaf.wiresExact
  let openItems := Concrete.Splice.Input.compiledSpliceOpenRootItems checked
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let transport :=
    (Concrete.exactContextToOpenRootWireEquiv checked context exact).trans
      (FiniteEquiv.finCast rootEq)
  let targetItems := openItems.items.castWiresEq rootEq
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems input.pattern
  let outputWitness := input.compiledSpliceOutputRootWitness layout admissible
    siteRoot
  let outputLeaf := input.compiledSpliceOutputRootLeaf layout admissible
    siteRoot
  let patternPrepared :=
    (pattern.items.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty admissible host))
        |>.renameRelations
          (Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
            outputWitness.toFocus.holeRels)
  let castEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfEmpty admissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) empty).trans
      (FiniteEquiv.finCast castEq).symm
  let outputRootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [siteRoot] using outputLeaf.wiresExact
  let outputEq :
      (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).rootWires.length =
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).exposedWires.length +
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let outputTransport :=
    (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
      input layout admissible boundary rootScoped
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputRootExact).trans (FiniteEquiv.finCast outputEq)
  let reindex :=
    Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex closedWire
      outputTransport
      (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout boundary)
      (layout.rootLocalWireEquivOfEmpty input boundary siteRoot empty)
  let tail := patternPrepared.renameWires reindex
  have targetBody : target.body =
      .mk checked.val.hiddenWires.length targetItems := by
    exact openItems.elaborate_body
  have baseIso := rootHostItemsIso input admissible boundary rootScoped siteRoot
  let outputRefl := FiniteEquiv.refl
    (Fin (checked.val.exposedWires.length +
      (checked.val.hiddenWires.length + input.pattern.val.hiddenWires.length)))
  have hostIso : ItemSeqIso outputRefl []
      ((hostItems.renameWires transport).renameWires
        (Region.adjoinHostWire checked.val.exposedWires.length
          checked.val.hiddenWires.length input.pattern.val.hiddenWires.length))
      (targetItems.renameWires
        (Region.adjoinHostWire checked.val.exposedWires.length
          checked.val.hiddenWires.length input.pattern.val.hiddenWires.length)) := by
    have lifted := baseIso.renameWires_commuting
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length input.pattern.val.hiddenWires.length)
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length input.pattern.val.hiddenWires.length)
      outputRefl (by
        funext index
        rfl)
    exact lifted
  have canonicalStep := rootFromParts target targetItems
    ((hostItems.renameWires transport).renameWires
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length input.pattern.val.hiddenWires.length))
    tail targetBody hostIso
  let source := input.compiledSpliceRootSourceOfEmpty layout admissible boundary
    rootScoped siteRoot empty
  have sourceBody := rootEmptyBodyEqSplice input layout admissible boundary
    rootScoped siteRoot empty
  have spliceEq := splice_materialFromTail
    (hostItems.renameWires transport) tail
  have bodyEq : source.body =
      .mk (checked.val.hiddenWires.length + input.pattern.val.hiddenWires.length)
        (((hostItems.renameWires transport).renameWires
          (Region.adjoinHostWire checked.val.exposedWires.length
            checked.val.hiddenWires.length input.pattern.val.hiddenWires.length)).append
          tail) := sourceBody.trans spliceEq
  have sourceIso : OpenDiagramIso source
      (target.withBody
        (.mk (checked.val.hiddenWires.length + input.pattern.val.hiddenWires.length)
          (((hostItems.renameWires transport).renameWires
            (Region.adjoinHostWire checked.val.exposedWires.length
              checked.val.hiddenWires.length input.pattern.val.hiddenWires.length)).append
            tail))) := {
    external := FiniteEquiv.refl (Fin source.externalClasses)
    boundary := by
      intro position
      rfl
    body := by
      rw [bodyEq]
      exact RegionIso.refl _
  }
  exact Rule.Erasure.iso sourceIso.symm canonicalStep
    (OpenDiagramIso.refl target)

theorem root_nonempty
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (siteRoot : input.site = input.frame.val.root)
    (nonempty : input.binderSpine.proxyCount ≠ 0) :
    Rule.Erasure
      (input.compiledSpliceRootSourceOfNonempty layout admissible boundary
        rootScoped siteRoot nonempty)
      (Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot input
        admissible boundary rootScoped).elaborate := by
  let checked := Concrete.Splice.Input.PlugLayout.checkedCoalescedOpenRoot
    input admissible boundary rootScoped
  let target := checked.elaborate
  let host := input.compiledSpliceHostView admissible
  let hrels := input.compiledSpliceHostView_root_holeRels_eq_nil admissible
    siteRoot
  let hostItems : ItemSeq
      (host.compilerLeaf.inheritedWires.extend input.site).length [] :=
    cast (congrArg
      (ItemSeq (host.compilerLeaf.inheritedWires.extend input.site).length)
      hrels) host.compilerLeaf.items
  let context := host.compilerLeaf.inheritedWires.extend input.site
  let exact : context.Exact input.coalesceFrameRaw.root := by
    change context.Exact input.frame.val.root
    rw [← siteRoot]
    exact host.compilerLeaf.wiresExact
  let openItems := Concrete.Splice.Input.compiledSpliceOpenRootItems checked
  let rootEq : checked.val.rootWires.length =
      checked.val.exposedWires.length + checked.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let transport :=
    (Concrete.exactContextToOpenRootWireEquiv checked context exact).trans
      (FiniteEquiv.finCast rootEq)
  let targetItems := openItems.items.castWiresEq rootEq
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView input nonempty
  let outputWitness := input.compiledSpliceOutputRootWitness layout admissible
    siteRoot
  let outputLeaf := input.compiledSpliceOutputRootLeaf layout admissible
    siteRoot
  let patternPrepared :=
    (pattern.leaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty admissible host
        pattern.witness pattern.leaf nonempty)).renameRelations
      (fun {arity} relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming admissible
            host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
            nonempty relation))
  let castEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let closedWire :=
    (layout.siteCombinedWireEquivOfNonempty admissible host
      (outputWitness := outputWitness) (outputLeaf := outputLeaf) nonempty).trans
      (FiniteEquiv.finCast castEq).symm
  let outputRootExact :
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).Exact layout.plugRaw.root := by
    simpa [siteRoot] using outputLeaf.wiresExact
  let outputEq :
      (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).rootWires.length =
        (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).exposedWires.length +
          (Concrete.Splice.Input.PlugLayout.outputOpenRoot input layout boundary).hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let outputTransport :=
    (Concrete.Splice.Input.PlugLayout.outputExactContextToOpenRootWireEquiv
      input layout admissible boundary rootScoped
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputRootExact).trans (FiniteEquiv.finCast outputEq)
  let reindex :=
    Concrete.Splice.Input.PlugLayout.closedSourceToOpenRootReindex closedWire
      outputTransport
      (Concrete.Splice.Input.PlugLayout.rootExposedWireEquiv input layout boundary)
      (layout.rootLocalWireEquivOfNonempty input boundary siteRoot nonempty)
  let tail := patternPrepared.renameWires reindex
  let extra := (Concrete.Elaboration.exactScopeWires input.pattern.val.diagram
    input.binderSpine.bodyContainer).length
  have targetBody : target.body =
      .mk checked.val.hiddenWires.length targetItems := by
    exact openItems.elaborate_body
  have baseIso := rootHostItemsIso input admissible boundary rootScoped siteRoot
  let outputRefl := FiniteEquiv.refl
    (Fin (checked.val.exposedWires.length +
      (checked.val.hiddenWires.length + extra)))
  have hostIso : ItemSeqIso outputRefl []
      ((hostItems.renameWires transport).renameWires
        (Region.adjoinHostWire checked.val.exposedWires.length
          checked.val.hiddenWires.length extra))
      (targetItems.renameWires
        (Region.adjoinHostWire checked.val.exposedWires.length
          checked.val.hiddenWires.length extra)) := by
    have lifted := baseIso.renameWires_commuting
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length extra)
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length extra)
      outputRefl (by
        funext index
        rfl)
    exact lifted
  have canonicalStep := rootFromParts target targetItems
    ((hostItems.renameWires transport).renameWires
      (Region.adjoinHostWire checked.val.exposedWires.length
        checked.val.hiddenWires.length extra))
    tail targetBody hostIso
  let source := input.compiledSpliceRootSourceOfNonempty layout admissible
    boundary rootScoped siteRoot nonempty
  have sourceBody := rootNonemptyBodyEqSplice input layout admissible boundary
    rootScoped siteRoot nonempty
  have spliceEq := splice_materialFromTail
    (hostItems.renameWires transport) tail
  have bodyEq : source.body =
      .mk (checked.val.hiddenWires.length + extra)
        (((hostItems.renameWires transport).renameWires
          (Region.adjoinHostWire checked.val.exposedWires.length
            checked.val.hiddenWires.length extra)).append tail) :=
    sourceBody.trans spliceEq
  have sourceIso : OpenDiagramIso source
      (target.withBody
        (.mk (checked.val.hiddenWires.length + extra)
          (((hostItems.renameWires transport).renameWires
            (Region.adjoinHostWire checked.val.exposedWires.length
              checked.val.hiddenWires.length extra)).append tail))) := {
    external := FiniteEquiv.refl (Fin source.externalClasses)
    boundary := by
      intro position
      rfl
    body := by
      rw [bodyEq]
      exact RegionIso.refl _
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

private theorem nestedFromSplice
    {arity sourceOuter targetOuter hostLocal patternWires : Nat}
    {sourceRels targetRels patternRels : RelCtx}
    (interface : OpenDiagram arity)
    (context : DiagramContext interface.externalClasses targetOuter [] targetRels)
    (hostItems : ItemSeq (sourceOuter + hostLocal) sourceRels)
    (material : Region patternWires patternRels)
    (wireMap : Fin patternWires → Fin (sourceOuter + hostLocal))
    (relationMap : RelationRenaming patternRels sourceRels)
    (hostRelation : RelationRenaming sourceRels targetRels)
    (rootWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)) :
    let actualBefore :=
      ((Region.spliceAt hostLocal hostItems material wireMap relationMap
        ).renameRelations hostRelation).renameWires rootWire
    let actualAfter :=
      ((Region.mk hostLocal hostItems).renameRelations hostRelation
        ).renameWires rootWire
    Rule.atPolarity context.polarity Rule.Erasure
      (interface.withBody (context.fill actualBefore))
      (interface.withBody (context.fill actualAfter)) := by
  dsimp only
  let localWire := FiniteEquiv.refl (Fin hostLocal)
  let hostWire := extendWireEquiv rootWire localWire
  let targetHostItems :=
    (hostItems.renameRelations hostRelation).renameWires hostWire
  let targetWireMap := hostWire ∘ wireMap
  let targetRelationMap : RelationRenaming patternRels targetRels :=
    fun relation => hostRelation (relationMap relation)
  let sourceBefore :=
    (Region.spliceAt hostLocal hostItems material wireMap relationMap
      ).renameRelations hostRelation
  let sourceAfter :=
    (Region.mk hostLocal hostItems).renameRelations hostRelation
  let actualBefore := sourceBefore.renameWires rootWire
  let actualAfter := sourceAfter.renameWires rootWire
  let before := Region.spliceAt hostLocal targetHostItems material
    targetWireMap targetRelationMap
  let after := Region.mk hostLocal targetHostItems
  have hostItemsIso : ItemSeqIso hostWire targetRels
      (hostItems.renameRelations hostRelation) targetHostItems := by
    exact ItemSeqIso.renameWiresEquiv
      (hostItems.renameRelations hostRelation) hostWire
  have sourceBeforeIso : RegionIso rootWire targetRels sourceBefore before := by
    exact RegionIso.spliceAt_renameRelations hostItemsIso material
      wireMap targetWireMap rfl relationMap targetRelationMap (fun _ => rfl)
  have actualBeforeIso : RegionIso (FiniteEquiv.refl (Fin targetOuter))
      targetRels actualBefore before := by
    have renamed := RegionIso.renameWiresEquiv sourceBefore rootWire
    have combined := renamed.symm.trans sourceBeforeIso
    have wireEq : rootWire.symm.trans rootWire =
        FiniteEquiv.refl (Fin targetOuter) := by
      apply FiniteEquiv.ext
      intro index
      exact rootWire.right_inv index
    simpa only [wireEq] using combined
  have sourceAfterIso : RegionIso rootWire targetRels sourceAfter after := by
    unfold sourceAfter after
    simp only [Region.renameRelations]
    exact RegionIso.mk localWire hostItemsIso
  have actualAfterIso : RegionIso (FiniteEquiv.refl (Fin targetOuter))
      targetRels actualAfter after := by
    have renamed := RegionIso.renameWiresEquiv sourceAfter rootWire
    have combined := renamed.symm.trans sourceAfterIso
    have wireEq : rootWire.symm.trans rootWire =
        FiniteEquiv.refl (Fin targetOuter) := by
      apply FiniteEquiv.ext
      intro index
      exact rootWire.right_inv index
    simpa only [wireEq] using combined
  have localProof : Rule.Erasure.Local before after :=
    .erase hostLocal targetHostItems material targetWireMap targetRelationMap
  exact contextualAtPolarity interface context actualBefore actualAfter
    before after actualBeforeIso actualAfterIso localProof

theorem nested_empty
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (nested : input.site ≠ input.frame.val.root)
    (empty : input.binderSpine.proxyCount = 0) :
    let view := input.compiledSpliceOutputOpenView layout admissible
      boundary rootScoped
    Rule.atPolarity view.focus.context.polarity Rule.Erasure
      (input.compiledSpliceNestedSourceOfEmpty layout admissible boundary
        rootScoped nested empty)
      (input.compiledSpliceNestedHostOpen layout admissible boundary
        rootScoped nested) := by
  dsimp only
  let host := input.compiledSpliceHostView admissible
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems input.pattern
  let output := (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    input layout admissible boundary rootScoped).elaborate
  let view := input.compiledSpliceOutputOpenView layout admissible
    boundary rootScoped
  let outputLeaf := input.compiledSpliceOutputNestedLeaf layout admissible
    boundary rootScoped nested
  let localEq := Concrete.Elaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  let hostItems := host.compilerLeaf.items.castWiresEq localEq
  let material := Concrete.Elaboration.finishRoot
    input.pattern.val.exposedWires input.pattern.val.hiddenWires pattern.items
  let wireMap := fun index => Fin.cast localEq
    (layout.exposedWireRenaming admissible host index)
  let relationMap : RelationRenaming [] host.intrinsicPath.toFocus.holeRels :=
    fun relation => Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
      host.intrinsicPath.toFocus.holeRels relation
  let hostRelation : RelationRenaming host.intrinsicPath.toFocus.holeRels
      view.intrinsicPath.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf relation
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
  have uncastStep := nestedFromSplice (interface := output)
    (context := view.focus.context) hostItems material wireMap relationMap
    hostRelation rootWire
  have step := atPolarity_castArity arityEq.symm uncastStep
  simpa [Concrete.Splice.Input.compiledSpliceNestedSourceOfEmpty,
    Concrete.Splice.Input.compiledSpliceNestedHostOpen,
    Concrete.Splice.replaceOpenBody, OpenDiagram.withBody,
    host, pattern, output, view, outputLeaf, localEq, hostItems, material,
    wireMap, relationMap, hostRelation, rootWire, arityEq] using step

theorem nested_nonempty
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (nested : input.site ≠ input.frame.val.root)
    (nonempty : input.binderSpine.proxyCount ≠ 0) :
    let view := input.compiledSpliceOutputOpenView layout admissible
      boundary rootScoped
    Rule.atPolarity view.focus.context.polarity Rule.Erasure
      (input.compiledSpliceNestedSourceOfNonempty layout admissible boundary
        rootScoped nested nonempty)
      (input.compiledSpliceNestedHostOpen layout admissible boundary
        rootScoped nested) := by
  dsimp only
  let host := input.compiledSpliceHostView admissible
  let pattern := input.compiledSpliceTerminalView nonempty
  let output := (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    input layout admissible boundary rootScoped).elaborate
  let view := input.compiledSpliceOutputOpenView layout admissible
    boundary rootScoped
  let outputLeaf := input.compiledSpliceOutputNestedLeaf layout admissible
    boundary rootScoped nested
  let localEq := Concrete.Elaboration.WireContext.length_extend
    host.compilerLeaf.inheritedWires input.site
  let hostItems := host.compilerLeaf.items.castWiresEq localEq
  let material := Concrete.Elaboration.finishRegion input.pattern.val.diagram
    pattern.leaf.inheritedWires input.binderSpine.bodyContainer
    pattern.leaf.items
  let wireMap := fun index => Fin.cast localEq
    (layout.bodyTerminalWireRenaming admissible host pattern.witness
      pattern.leaf nonempty index)
  let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
      host.intrinsicPath.toFocus.holeRels := fun relation =>
    layout.coalescedTerminalRelationRenaming admissible host.intrinsicPath
      host.compilerLeaf pattern.witness pattern.leaf nonempty relation
  let hostRelation : RelationRenaming host.intrinsicPath.toFocus.holeRels
      view.intrinsicPath.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      view.intrinsicPath outputLeaf relation
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
  have uncastStep := nestedFromSplice (interface := output)
    (context := view.focus.context) hostItems material wireMap relationMap
    hostRelation rootWire
  have step := atPolarity_castArity arityEq.symm uncastStep
  simpa [Concrete.Splice.Input.compiledSpliceNestedSourceOfNonempty,
    Concrete.Splice.Input.compiledSpliceNestedHostOpen,
    Concrete.Splice.replaceOpenBody, OpenDiagram.withBody,
    host, pattern, output, view, outputLeaf, localEq, hostItems, material,
    wireMap, relationMap, hostRelation, rootWire, arityEq] using step

private noncomputable def nestedNonemptySourceIso
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (nested : input.site ≠ input.frame.val.root)
    (nonempty : input.binderSpine.proxyCount ≠ 0) :
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
      (input.compiledSpliceNestedSourceOfNonempty layout admissible boundary
        rootScoped nested nonempty)
      ((Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot input layout
        admissible boundary rootScoped).elaborate.castArity arityEq.symm) := by
  dsimp only
  let host := input.compiledSpliceHostView admissible
  let pattern := input.compiledSpliceTerminalView nonempty
  let output := (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    input layout admissible boundary rootScoped).elaborate
  let view := input.compiledSpliceOutputOpenView layout admissible
    boundary rootScoped
  let outputLeaf := input.compiledSpliceOutputNestedLeaf layout admissible
    boundary rootScoped nested
  let source :=
    ((Region.spliceAt
        (Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (Concrete.Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))
        (Concrete.Elaboration.finishRegion input.pattern.val.diagram
          pattern.leaf.inheritedWires input.binderSpine.bodyContainer
          pattern.leaf.items)
        (fun index => Fin.cast
          (Concrete.Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site)
          (layout.bodyTerminalWireRenaming admissible host pattern.witness
            pattern.leaf nonempty index))
        (layout.coalescedTerminalRelationRenaming admissible
          host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
          nonempty)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        view.intrinsicPath outputLeaf))
  let inherited := layout.inheritedWireEquiv host.intrinsicPath
    host.compilerLeaf view.intrinsicPath outputLeaf
  let rootWire := inherited.trans
    (FiniteEquiv.finCast outputLeaf.inheritedLength)
  have siteIso := layout.compiledSiteRegionIsoOfNonempty input admissible host
    pattern.witness pattern.leaf view.intrinsicPath outputLeaf nonempty
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
  simpa [Concrete.Splice.Input.compiledSpliceNestedSourceOfNonempty,
    host, pattern, output, view, outputLeaf, source, inherited, rootWire,
    arityEq] using castIso

private noncomputable def nestedEmptySourceIso
    (input : Concrete.Splice.Input)
    (layout : input.PlugLayout)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (rootScoped : ∀ wire, wire ∈ boundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (nested : input.site ≠ input.frame.val.root)
    (empty : input.binderSpine.proxyCount = 0) :
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
      (input.compiledSpliceNestedSourceOfEmpty layout admissible boundary
        rootScoped nested empty)
      ((Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot input layout
        admissible boundary rootScoped).elaborate.castArity arityEq.symm) := by
  dsimp only
  let host := input.compiledSpliceHostView admissible
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems input.pattern
  let output := (Concrete.Splice.Input.PlugLayout.checkedOutputOpenRoot
    input layout admissible boundary rootScoped).elaborate
  let view := input.compiledSpliceOutputOpenView layout admissible
    boundary rootScoped
  let outputLeaf := input.compiledSpliceOutputNestedLeaf layout admissible
    boundary rootScoped nested
  let source :=
    ((Region.spliceAt
        (Concrete.Elaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length
        (host.compilerLeaf.items.castWiresEq
          (Concrete.Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site))
        (Concrete.Elaboration.finishRoot input.pattern.val.exposedWires
          input.pattern.val.hiddenWires pattern.items)
        (fun index => Fin.cast
          (Concrete.Elaboration.WireContext.length_extend
            host.compilerLeaf.inheritedWires input.site)
          (layout.exposedWireRenaming admissible host index))
        (Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
          host.intrinsicPath.toFocus.holeRels)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        view.intrinsicPath outputLeaf))
  let inherited := layout.inheritedWireEquiv host.intrinsicPath
    host.compilerLeaf view.intrinsicPath outputLeaf
  let rootWire := inherited.trans
    (FiniteEquiv.finCast outputLeaf.inheritedLength)
  have siteIso := layout.compiledSiteRegionIsoOfEmpty input admissible host
    view.intrinsicPath outputLeaf empty pattern.items pattern.computation
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
  simpa [Concrete.Splice.Input.compiledSpliceNestedSourceOfEmpty,
    host, pattern, output, view, outputLeaf, source, inherited, rootWire,
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
  · by_cases empty : input.binderSpine.proxyCount = 0
    · have step : Rule.atPolarity Polarity.positive Rule.Erasure
          (input.compiledSpliceRootSourceOfEmpty layout admissible boundary
            rootScoped siteRoot empty) coalescedOpen.elaborate := by
        simpa [Rule.atPolarity] using
          root_empty input layout admissible boundary rootScoped siteRoot empty
      have sourceIso : OpenDiagramIso
          (input.compiledSpliceRootSourceOfEmpty layout admissible boundary
            rootScoped siteRoot empty)
          (resultOpen.elaborate.castArity canonicalArity.symm) := by
        have iso := input.compiledSpliceRootIsoOfEmpty layout admissible
          boundary rootScoped siteRoot empty
        have base : OpenDiagramIso
            (input.compiledSpliceRootSourceOfEmpty layout admissible boundary
              rootScoped siteRoot empty)
            (outputOpen.elaborate.castArity outputArity.symm) := by
          simpa [outputOpen] using iso
        exact transportIsoCheckedOpenEq resultOpenEq.symm outputArity
          canonicalArity base
      have branch := refineBranch canonicalArity sourceIso step
        coalescedToFrame
      simpa [admissible, layout, siteRoot, resultOpen, targetOpen,
        targetArity] using branch
    · have step : Rule.atPolarity Polarity.positive Rule.Erasure
          (input.compiledSpliceRootSourceOfNonempty layout admissible boundary
            rootScoped siteRoot empty) coalescedOpen.elaborate := by
        simpa [Rule.atPolarity] using
          root_nonempty input layout admissible boundary rootScoped siteRoot
            empty
      have sourceIso : OpenDiagramIso
          (input.compiledSpliceRootSourceOfNonempty layout admissible boundary
            rootScoped siteRoot empty)
          (resultOpen.elaborate.castArity canonicalArity.symm) := by
        have iso := input.compiledSpliceRootIsoOfNonempty layout admissible
          boundary rootScoped siteRoot empty
        have base : OpenDiagramIso
            (input.compiledSpliceRootSourceOfNonempty layout admissible boundary
              rootScoped siteRoot empty)
            (outputOpen.elaborate.castArity outputArity.symm) := by
          simpa [outputOpen] using iso
        exact transportIsoCheckedOpenEq resultOpenEq.symm outputArity
          canonicalArity base
      have branch := refineBranch canonicalArity sourceIso step
        coalescedToFrame
      simpa [admissible, layout, siteRoot, resultOpen, targetOpen,
        targetArity] using branch
  · let view := input.compiledSpliceOutputOpenView layout admissible boundary
      rootScoped
    let hostOpen := input.compiledSpliceNestedHostOpen layout admissible
      boundary rootScoped siteRoot
    have hostToFrame : OpenDiagramIso hostOpen
        ((targetOpen.elaborate.castArity targetArity).castArity
          canonicalArity.symm) := by
      exact (input.compiledSpliceNestedHostIso layout admissible boundary
        rootScoped siteRoot).symm.trans coalescedToFrame
    by_cases empty : input.binderSpine.proxyCount = 0
    · have step : Rule.atPolarity view.focus.context.polarity Rule.Erasure
          (input.compiledSpliceNestedSourceOfEmpty layout admissible boundary
            rootScoped siteRoot empty) hostOpen := by
        simpa [view, hostOpen] using nested_empty input layout admissible
          boundary rootScoped siteRoot empty
      have sourceIso : OpenDiagramIso
          (input.compiledSpliceNestedSourceOfEmpty layout admissible boundary
            rootScoped siteRoot empty)
          (resultOpen.elaborate.castArity canonicalArity.symm) := by
        have iso := nestedEmptySourceIso input layout admissible boundary
          rootScoped siteRoot empty
        have base : OpenDiagramIso
            (input.compiledSpliceNestedSourceOfEmpty layout admissible boundary
              rootScoped siteRoot empty)
            (outputOpen.elaborate.castArity outputArity.symm) := by
          simpa [outputOpen] using iso
        exact transportIsoCheckedOpenEq resultOpenEq.symm outputArity
          canonicalArity base
      have branch := refineBranch canonicalArity sourceIso step hostToFrame
      simpa [admissible, layout, siteRoot, view, hostOpen, resultOpen,
        targetOpen, targetArity] using branch
    · have step : Rule.atPolarity view.focus.context.polarity Rule.Erasure
          (input.compiledSpliceNestedSourceOfNonempty layout admissible boundary
            rootScoped siteRoot empty) hostOpen := by
        simpa [view, hostOpen] using nested_nonempty input layout admissible
          boundary rootScoped siteRoot empty
      have sourceIso : OpenDiagramIso
          (input.compiledSpliceNestedSourceOfNonempty layout admissible boundary
            rootScoped siteRoot empty)
          (resultOpen.elaborate.castArity canonicalArity.symm) := by
        have iso := nestedNonemptySourceIso input layout admissible boundary
          rootScoped siteRoot empty
        have base : OpenDiagramIso
            (input.compiledSpliceNestedSourceOfNonempty layout admissible
              boundary rootScoped siteRoot empty)
            (outputOpen.elaborate.castArity outputArity.symm) := by
          simpa [outputOpen] using iso
        exact transportIsoCheckedOpenEq resultOpenEq.symm outputArity
          canonicalArity base
      have branch := refineBranch canonicalArity sourceIso step hostToFrame
      simpa [admissible, layout, siteRoot, view, hostOpen, resultOpen,
        targetOpen, targetArity] using branch

end VisualProof.Refinement.Erasure
