import VisualProof.Concrete.Elaboration.SpliceSiteCompiler
import VisualProof.Concrete.Elaboration.SpliceItems

/-! Intrinsic identification of the exact compiler body at a splice site. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input

/-- The primitive splice input viewed in the exact open execution source.
The frame is supplied by `source.diagram`; every remaining field is retained
without semantic reconstruction. -/
structure SourceNormalized (source : State arity) where
  pattern : CheckedOpen
  site : Fin source.checked.val.diagram.regionCount
  attachment : Fin pattern.val.boundary.length →
    Fin source.checked.val.diagram.wireCount
  binderSpine : BinderSpine pattern.val.diagram
  binderTarget : Fin binderSpine.proxyCount →
    Fin source.checked.val.diagram.regionCount

/-- Rebuild the primitive splice input with a frame definitionally equal to
the execution source diagram. -/
def SourceNormalized.toInput (normalized : SourceNormalized source) :
    Splice.Input where
  frame := source.diagram
  pattern := normalized.pattern
  site := normalized.site
  attachment := normalized.attachment
  binderSpine := normalized.binderSpine
  binderTarget := normalized.binderTarget

/-- Transport an exact supplied splice input across its execution frame
equality, retaining all five non-frame fields. -/
def sourceNormalized (source : State arity) (input : Splice.Input)
    (frameEq : input.frame = source.diagram) : SourceNormalized source := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  exact ⟨pattern, site, attachment, binderSpine, binderTarget⟩

/-- Normalizing and rebuilding is exactly equality transport of the supplied
primitive input. -/
theorem sourceNormalized_toInput (source : State arity)
    (input : Splice.Input) (frameEq : input.frame = source.diagram) :
    (sourceNormalized source input frameEq).toInput = input := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  rfl

end Splice.Input

namespace Splice.Input.PlugLayout

private noncomputable def renameRelationsSame
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : ItemSeq sourceWires sourceRels}
    {target : ItemSeq targetWires sourceRels}
    (iso : ItemSeqIso wire sourceRels source target)
    (relation : RelationRenaming sourceRels targetRels) :
    ItemSeqIso wire targetRels
      (source.renameRelations relation) (target.renameRelations relation) := by
  have extendedEq : extendWireEquiv wire
      (FiniteEquiv.refl (Fin 0)) = wire := by
    apply FiniteEquiv.ext
    intro index
    refine Fin.addCases (fun inherited => ?_)
      (fun impossible => Fin.elim0 impossible) index
    apply Fin.ext
    calc
      _ = (Fin.castAdd 0 (wire inherited)).val := congrArg Fin.val
        (extendWireEquiv_outer wire (FiniteEquiv.refl (Fin 0)) inherited)
      _ = (wire inherited).val := rfl
      _ = (wire (Fin.castAdd 0 inherited)).val := by
        congr 2
  have lifted : ItemSeqIso
      (extendWireEquiv wire (FiniteEquiv.refl (Fin 0))) sourceRels
      source target := by
    rw [extendedEq]
    exact iso
  let regionIso : RegionIso wire sourceRels
      (.mk 0 source) (.mk 0 target) :=
    .mk (FiniteEquiv.refl (Fin 0)) lifted
  have renamed := regionIso.renameRelations relation
  cases renamed with
  | mk localEquiv items =>
      have outputEq : extendWireEquiv wire localEquiv = wire := by
        apply FiniteEquiv.ext
        intro index
        refine Fin.addCases (fun inherited => ?_)
          (fun impossible => Fin.elim0 impossible) index
        apply Fin.ext
        calc
          _ = (Fin.castAdd 0 (wire inherited)).val := congrArg Fin.val
            (extendWireEquiv_outer wire localEquiv inherited)
          _ = (wire inherited).val := rfl
          _ = (wire (Fin.castAdd 0 inherited)).val := by
            congr 2
      rw [outputEq] at items
      exact items

/-- The direct source kernel items are the items of its retained abstract site
body under the retained local-count equality. -/
theorem kernel_siteBody_itemsCast_eq
    {source : State arity} {site : Fin source.checked.val.diagram.regionCount}
    {compiled : LocalCompiledSite source site} (kernel : compiled.Kernel) :
    compiled.siteBody.itemsCast compiled.siteBody_localCount =
      kernel.items.castWiresEq (by simp) := by
  have bodyEq : Region.mk compiled.siteLocals.length
      (kernel.items.castWiresEq (by simp)) = compiled.siteBody :=
    kernel.body_eq.symm
  have itemsEq := Region.itemsCast_eq_of_mk_eq
    (kernel.items.castWiresEq (by simp)) compiled.siteBody bodyEq
  simpa only [Subsingleton.elim compiled.siteBody_localCount
    (congrArg Region.localCount bodyEq).symm] using itemsEq

/-- The complete output-wire transport at a splice site: retained inherited
wires, retained host locals, then the terminal body's dense internal locals. -/
noncomputable def siteOutputWireEquiv {source : State arity}
    (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput) :
    FiniteEquiv
      (Fin (host.siteContext.length +
        (host.siteLocals.length + material.siteLocals.length)))
      (Fin ((layout.mapFrameContext consistent host.siteContext).length +
        ((layout.mapFrameContext consistent host.siteLocals).length +
          layout.bodyLocalWires.length))) :=
  extendWireEquiv
    (layout.mapFrameContextEquiv consistent host.siteContext)
    (extendWireEquiv
      (layout.mapFrameContextEquiv consistent host.siteLocals)
      (layout.bodyLocalEquiv material))

@[simp] theorem siteOutputWireEquiv_val {source : State arity}
    (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput)
    (index : Fin (host.siteContext.length +
      (host.siteLocals.length + material.siteLocals.length))) :
    (layout.siteOutputWireEquiv normalized consistent host material index).val =
      index.val := by
  refine Fin.addCases (fun inherited => ?_) (fun remaining => ?_) index
  · simp [siteOutputWireEquiv, mapFrameContextEquiv]
    rfl
  · refine Fin.addCases (fun hostLocal => ?_)
      (fun materialLocal => ?_) remaining
    · simp [siteOutputWireEquiv, mapFrameContextEquiv]
      have outerLength :
          (layout.mapFrameContext consistent host.siteContext).length =
            host.siteContext.length := List.length_map _
      change (layout.mapFrameContext consistent host.siteContext).length +
        hostLocal.val = host.siteContext.length + hostLocal.val
      omega
    · simp [siteOutputWireEquiv, bodyLocalEquiv, FiniteEquiv.finCast]
      have outerLength :
          (layout.mapFrameContext consistent host.siteContext).length =
            host.siteContext.length := List.length_map _
      have localLength :
          (layout.mapFrameContext consistent host.siteLocals).length =
            host.siteLocals.length := List.length_map _
      omega

private theorem patternSiteWires_split_length
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (first second : WireContext input.frame.val) :
    (layout.patternSiteWires consistent (first ++ second)).length =
      (layout.mapFrameContext consistent first).length +
        ((layout.mapFrameContext consistent second).length +
          layout.bodyLocalWires.length) := by
  change (layout.mapFrameContext consistent (first ++ second) ++
      layout.bodyLocalWires).length = _
  calc
    _ = (layout.mapFrameContext consistent (first ++ second)).length +
        layout.bodyLocalWires.length := List.length_append
    _ = (layout.mapFrameContext consistent first ++
          layout.mapFrameContext consistent second).length +
        layout.bodyLocalWires.length := congrArg
          (fun context => context.length + layout.bodyLocalWires.length)
          (layout.mapFrameContext_append consistent first second)
    _ = ((layout.mapFrameContext consistent first).length +
          (layout.mapFrameContext consistent second).length) +
        layout.bodyLocalWires.length := congrArg
          (fun length => length + layout.bodyLocalWires.length)
          List.length_append
    _ = _ := Nat.add_assoc _ _ _

/-- The target site body in the compiler's node-before-child order, with each
block expressed directly as the corresponding source block transport. -/
noncomputable def spliceCompilerSiteBody {source : State arity}
    (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (hostKernel : host.local.Kernel) (hostBlocks : hostKernel.Blocks)
    (material : CompiledMaterial normalized.toInput)
    (materialKernel : material.Kernel)
    (materialBlocks : materialKernel.Blocks) :
    Region (layout.mapFrameContext consistent host.siteContext).length
      host.siteRels :=
  let hostContext := host.siteContext ++ host.siteLocals
  let hostMap := layout.frameSiteIndexMap consistent hostContext
  let materialMap := layout.patternContextIndexMap consistent admissible
    material hostContext host.local.completeContext_exact
  let relationMap : RelationRenaming material.siteRels host.siteRels :=
    fun relation => material.spliceRelationMap normalized.toInput admissible
      host.siteBinders host.binder_covers relation
  let items :=
    ((hostBlocks.nodeItems.renameWires hostMap).append
      ((materialBlocks.nodeItems.renameWires materialMap).renameRelations
        relationMap)).append
    ((hostBlocks.childItems.renameWires hostMap).append
      ((materialBlocks.childItems.renameWires materialMap).renameRelations
        relationMap))
  .mk ((layout.mapFrameContext consistent host.siteLocals).length +
      layout.bodyLocalWires.length)
    (items.castWiresEq (by
      exact layout.patternSiteWires_split_length consistent
        host.siteContext host.siteLocals))

private theorem siteOutputWireEquiv_frameSiteIndexMap
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput) :
    layout.siteOutputWireEquiv normalized consistent host material ∘
        Region.adjoinHostWire host.siteContext.length host.siteLocals.length
          material.siteLocals.length ∘
        Fin.cast (List.length_append) =
      Fin.cast (layout.patternSiteWires_split_length consistent
        host.siteContext host.siteLocals) ∘
        layout.frameSiteIndexMap consistent
          (host.siteContext ++ host.siteLocals) := by
  funext index
  apply Fin.ext
  simp only [Function.comp_apply]
  rw [layout.siteOutputWireEquiv_val normalized]
  rfl

private theorem siteOutputWireEquiv_patternContextIndexMap
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput) :
    layout.siteOutputWireEquiv normalized consistent host material ∘
        Region.adjoinMaterialWire host.siteContext.length
          host.siteLocals.length material.siteLocals.length ∘
        extendWireRenaming
          (Fin.cast (List.length_append) ∘
            material.spliceWireMap normalized.toInput layout admissible
              (host.siteContext ++ host.siteLocals)
              host.local.completeContext_exact)
          material.siteLocals.length ∘
        Fin.cast (List.length_append) =
      Fin.cast (layout.patternSiteWires_split_length consistent
        host.siteContext host.siteLocals) ∘
        layout.patternContextIndexMap consistent admissible material
          (host.siteContext ++ host.siteLocals)
          host.local.completeContext_exact := by
  funext index
  apply Fin.ext
  simp only [Function.comp_apply]
  rw [layout.siteOutputWireEquiv_val normalized]
  let split : Fin
      (material.siteContext.length + material.siteLocals.length) :=
    Fin.cast List.length_append index
  have indexEq : Fin.cast List.length_append.symm split = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  refine Fin.addCases (fun inherited => ?_) (fun materialLocal => ?_) split
  · simp [extendWireRenaming, Region.adjoinMaterialWire,
      patternContextIndexMap]
  · simp [extendWireRenaming, Region.adjoinMaterialWire,
      patternContextIndexMap]
    have hostLength : (host.siteContext ++ host.siteLocals).length =
        host.siteContext.length + host.siteLocals.length :=
      List.length_append
    have materialVal : (layout.bodyLocalEquiv material materialLocal).val =
        materialLocal.val := rfl
    exact (congrArg (fun length => length + materialLocal.val)
      hostLength.symm).trans (congrArg
        (fun value => (host.siteContext ++ host.siteLocals).length + value)
        materialVal.symm)

private noncomputable def frameItemsIso
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (host : CompiledSite source normalized.site)
    (hostKernel : host.local.Kernel) (hostBlocks : hostKernel.Blocks)
    (material : CompiledMaterial normalized.toInput) :
    ItemSeqIso (layout.siteOutputWireEquiv normalized consistent host material)
      host.siteRels
      ((hostKernel.items.castWiresEq List.length_append).renameWires
        (Region.adjoinHostWire host.siteContext.length host.siteLocals.length
          material.siteLocals.length))
      (((hostBlocks.nodeItems.renameWires
          (layout.frameSiteIndexMap consistent
            (host.siteContext ++ host.siteLocals))).append
        (hostBlocks.childItems.renameWires
          (layout.frameSiteIndexMap consistent
            (host.siteContext ++ host.siteLocals)))).castWiresEq
              (layout.patternSiteWires_split_length consistent
                host.siteContext host.siteLocals)) := by
  let sourceItems := hostBlocks.nodeItems.append hostBlocks.childItems
  let sourceMap :=
    Region.adjoinHostWire host.siteContext.length host.siteLocals.length
        material.siteLocals.length ∘
      Fin.cast List.length_append
  let targetMap :=
    Fin.cast (layout.patternSiteWires_split_length consistent
      host.siteContext host.siteLocals) ∘
      layout.frameSiteIndexMap consistent
        (host.siteContext ++ host.siteLocals)
  have commutes :
      (layout.siteOutputWireEquiv normalized consistent host material).toFun ∘
          sourceMap =
        targetMap ∘
          (FiniteEquiv.refl
            (Fin (host.siteContext ++ host.siteLocals).length)).toFun := by
    simpa only [sourceMap, targetMap, FiniteEquiv.refl,
      Function.comp_id] using
        layout.siteOutputWireEquiv_frameSiteIndexMap normalized consistent
          host material
  have mapped := (ItemSeqIso.refl sourceItems).renameWires_commuting
    sourceMap targetMap
      (layout.siteOutputWireEquiv normalized consistent host material) commutes
  have sourceEq :
      (hostKernel.items.castWiresEq List.length_append).renameWires
          (Region.adjoinHostWire host.siteContext.length
            host.siteLocals.length material.siteLocals.length) =
        sourceItems.renameWires sourceMap := by
    rw [hostBlocks.items_eq]
    dsimp only [sourceItems, sourceMap]
    rw [ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.renameWires_comp]
  have targetEq :
      ((hostBlocks.nodeItems.renameWires
          (layout.frameSiteIndexMap consistent
            (host.siteContext ++ host.siteLocals))).append
        (hostBlocks.childItems.renameWires
          (layout.frameSiteIndexMap consistent
            (host.siteContext ++ host.siteLocals)))).castWiresEq
              (layout.patternSiteWires_split_length consistent
                host.siteContext host.siteLocals) =
        sourceItems.renameWires targetMap := by
    rw [ItemSeq.castWiresEq_eq_renameWires]
    let frameMap := layout.frameSiteIndexMap consistent
      (host.siteContext ++ host.siteLocals)
    let outputCast := Fin.cast
      (layout.patternSiteWires_split_length consistent
        host.siteContext host.siteLocals)
    have distributed :
        ((hostBlocks.nodeItems.renameWires frameMap).append
            (hostBlocks.childItems.renameWires frameMap)).renameWires
              outputCast =
          (hostBlocks.nodeItems.renameWires targetMap).append
            (hostBlocks.childItems.renameWires targetMap) := by
      calc
        _ = ((hostBlocks.nodeItems.renameWires frameMap).renameWires
                outputCast).append
              ((hostBlocks.childItems.renameWires frameMap).renameWires
                outputCast) := ItemSeq.renameWires_append _ _ _
        _ = _ := by
          dsimp only [targetMap]
          let nodeTarget := hostBlocks.nodeItems.renameWires
            (outputCast ∘ frameMap)
          let childSource := (hostBlocks.childItems.renameWires
            frameMap).renameWires outputCast
          calc
            _ = nodeTarget.append childSource := congrArg
              (fun first => first.append childSource)
              (ItemSeq.renameWires_comp hostBlocks.nodeItems
                frameMap outputCast)
            _ = nodeTarget.append
                (hostBlocks.childItems.renameWires
                  (outputCast ∘ frameMap)) := congrArg
              (fun second => nodeTarget.append second)
              (ItemSeq.renameWires_comp hostBlocks.childItems
                frameMap outputCast)
    have combined : sourceItems.renameWires targetMap =
        (hostBlocks.nodeItems.renameWires targetMap).append
          (hostBlocks.childItems.renameWires targetMap) := by
      dsimp only [sourceItems]
      exact ItemSeq.renameWires_append _ _ _
    exact distributed.trans combined.symm
  rw [sourceEq, targetEq]
  exact mapped

private noncomputable def materialItemsIso
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledMaterial normalized.toInput)
    (materialKernel : material.Kernel)
    (materialBlocks : materialKernel.Blocks) :
    let sourceWireMap := Fin.cast List.length_append ∘
      material.spliceWireMap normalized.toInput layout admissible
        (host.siteContext ++ host.siteLocals)
          host.local.completeContext_exact
    let relationMap : RelationRenaming material.siteRels host.siteRels :=
      fun relation => material.spliceRelationMap normalized.toInput admissible
        host.siteBinders host.binder_covers relation
    let materialMap := layout.patternContextIndexMap consistent admissible
      material (host.siteContext ++ host.siteLocals)
        host.local.completeContext_exact
    ItemSeqIso (layout.siteOutputWireEquiv normalized consistent host material)
      host.siteRels
      ((((materialKernel.items.castWiresEq List.length_append).renameWires
          (extendWireRenaming sourceWireMap material.siteLocals.length)
          ).renameRelations relationMap).renameWires
          (Region.adjoinMaterialWire host.siteContext.length
            host.siteLocals.length material.siteLocals.length))
      ((((materialBlocks.nodeItems.renameWires materialMap).renameRelations
          relationMap).append
        ((materialBlocks.childItems.renameWires materialMap).renameRelations
          relationMap)).castWiresEq
          (layout.patternSiteWires_split_length consistent
            host.siteContext host.siteLocals)) := by
  dsimp only
  let sourceItems := materialBlocks.nodeItems.append materialBlocks.childItems
  let sourceWireMap := Fin.cast List.length_append ∘
    material.spliceWireMap normalized.toInput layout admissible
      (host.siteContext ++ host.siteLocals) host.local.completeContext_exact
  let relationMap : RelationRenaming material.siteRels host.siteRels :=
    fun relation => material.spliceRelationMap normalized.toInput admissible
      host.siteBinders host.binder_covers relation
  let sourceMap :=
    Region.adjoinMaterialWire host.siteContext.length host.siteLocals.length
        material.siteLocals.length ∘
      extendWireRenaming sourceWireMap material.siteLocals.length ∘
      Fin.cast List.length_append
  let materialMap := layout.patternContextIndexMap consistent admissible
    material (host.siteContext ++ host.siteLocals)
      host.local.completeContext_exact
  let targetMap :=
    Fin.cast (layout.patternSiteWires_split_length consistent
      host.siteContext host.siteLocals) ∘ materialMap
  have commutes :
      (layout.siteOutputWireEquiv normalized consistent host material).toFun ∘
          sourceMap =
        targetMap ∘
          (FiniteEquiv.refl
            (Fin (material.siteContext ++ material.siteLocals).length)
          ).toFun := by
    simpa only [sourceMap, targetMap, materialMap, sourceWireMap,
      FiniteEquiv.refl, Function.comp_id] using
        layout.siteOutputWireEquiv_patternContextIndexMap normalized
          consistent admissible host material
  have wireMapped := (ItemSeqIso.refl sourceItems).renameWires_commuting
    sourceMap targetMap
      (layout.siteOutputWireEquiv normalized consistent host material) commutes
  have mapped := renameRelationsSame wireMapped relationMap
  have sourceWireEq :
      ((materialKernel.items.castWiresEq List.length_append).renameWires
          (extendWireRenaming sourceWireMap material.siteLocals.length)
        ).renameWires
          (Region.adjoinMaterialWire host.siteContext.length
            host.siteLocals.length material.siteLocals.length) =
        sourceItems.renameWires sourceMap := by
    rw [materialBlocks.items_eq]
    rw [ItemSeq.castWiresEq_eq_renameWires]
    let initialCast : Fin
        (material.siteContext ++ material.siteLocals).length →
          Fin (material.siteContext.length + material.siteLocals.length) :=
      Fin.cast List.length_append
    let extendedMap := extendWireRenaming sourceWireMap
      material.siteLocals.length
    let outputMap := Region.adjoinMaterialWire host.siteContext.length
      host.siteLocals.length material.siteLocals.length
    calc
      _ = (sourceItems.renameWires (extendedMap ∘ initialCast)).renameWires
          outputMap := congrArg (fun items => items.renameWires outputMap)
            (ItemSeq.renameWires_comp sourceItems initialCast extendedMap)
      _ = sourceItems.renameWires
          (outputMap ∘ (extendedMap ∘ initialCast)) :=
        ItemSeq.renameWires_comp sourceItems
          (extendedMap ∘ initialCast) outputMap
      _ = _ := rfl
  have sourceEq :
      ((((materialKernel.items.castWiresEq List.length_append).renameWires
          (extendWireRenaming sourceWireMap material.siteLocals.length)
        ).renameRelations relationMap).renameWires
          (Region.adjoinMaterialWire host.siteContext.length
            host.siteLocals.length material.siteLocals.length)) =
        (sourceItems.renameWires sourceMap).renameRelations relationMap := by
    calc
      _ = (((materialKernel.items.castWiresEq
              List.length_append).renameWires
            (extendWireRenaming sourceWireMap material.siteLocals.length)
          ).renameWires
            (Region.adjoinMaterialWire host.siteContext.length
              host.siteLocals.length material.siteLocals.length)
          ).renameRelations relationMap :=
        (ItemSeq.renameWires_renameRelations
          ((materialKernel.items.castWiresEq
            List.length_append).renameWires
              (extendWireRenaming sourceWireMap material.siteLocals.length))
          (Region.adjoinMaterialWire host.siteContext.length
            host.siteLocals.length material.siteLocals.length)
          relationMap).symm
      _ = _ := congrArg (fun items => items.renameRelations relationMap)
        sourceWireEq
  let outputCast := Fin.cast
    (layout.patternSiteWires_split_length consistent
      host.siteContext host.siteLocals)
  have targetEq :
      ((((materialBlocks.nodeItems.renameWires materialMap).renameRelations
          relationMap).append
        ((materialBlocks.childItems.renameWires materialMap).renameRelations
          relationMap)).castWiresEq
            (layout.patternSiteWires_split_length consistent
              host.siteContext host.siteLocals)) =
        (sourceItems.renameWires targetMap).renameRelations relationMap := by
    rw [ItemSeq.castWiresEq_eq_renameWires]
    have nodeEq :
        ((materialBlocks.nodeItems.renameWires materialMap).renameRelations
            relationMap).renameWires outputCast =
          (materialBlocks.nodeItems.renameWires targetMap).renameRelations
            relationMap := by
      calc
        _ = ((materialBlocks.nodeItems.renameWires materialMap).renameWires
              outputCast).renameRelations relationMap :=
          (ItemSeq.renameWires_renameRelations
            (materialBlocks.nodeItems.renameWires materialMap) outputCast
            relationMap).symm
        _ = _ := congrArg (fun items => items.renameRelations relationMap)
          (ItemSeq.renameWires_comp materialBlocks.nodeItems
            materialMap outputCast)
    have childEq :
        ((materialBlocks.childItems.renameWires materialMap).renameRelations
            relationMap).renameWires outputCast =
          (materialBlocks.childItems.renameWires targetMap).renameRelations
            relationMap := by
      calc
        _ = ((materialBlocks.childItems.renameWires materialMap).renameWires
              outputCast).renameRelations relationMap :=
          (ItemSeq.renameWires_renameRelations
            (materialBlocks.childItems.renameWires materialMap) outputCast
            relationMap).symm
        _ = _ := congrArg (fun items => items.renameRelations relationMap)
          (ItemSeq.renameWires_comp materialBlocks.childItems
            materialMap outputCast)
    calc
      _ = (((materialBlocks.nodeItems.renameWires materialMap).renameRelations
              relationMap).renameWires outputCast).append
            (((materialBlocks.childItems.renameWires
              materialMap).renameRelations relationMap).renameWires
                outputCast) := ItemSeq.renameWires_append _ _ _
      _ = ((materialBlocks.nodeItems.renameWires targetMap).renameRelations
              relationMap).append
            ((materialBlocks.childItems.renameWires targetMap).renameRelations
              relationMap) := by rw [nodeEq, childEq]
      _ = ((materialBlocks.nodeItems.renameWires targetMap).append
            (materialBlocks.childItems.renameWires targetMap)
          ).renameRelations relationMap :=
        (ItemSeq.renameRelations_append _ _ _).symm
      _ = _ := by
        dsimp only [sourceItems]
        have wiresEq :
            (materialBlocks.nodeItems.renameWires targetMap).append
                (materialBlocks.childItems.renameWires targetMap) =
              (materialBlocks.nodeItems.append
                materialBlocks.childItems).renameWires targetMap :=
          (ItemSeq.renameWires_append materialBlocks.nodeItems
            materialBlocks.childItems targetMap).symm
        exact congrArg
          (fun (items : ItemSeq
            ((layout.mapFrameContext consistent host.siteContext).length +
              ((layout.mapFrameContext consistent host.siteLocals).length +
                layout.bodyLocalWires.length)) material.siteRels) =>
              items.renameRelations relationMap)
          wiresEq
  rw [sourceEq, targetEq]
  exact mapped

private noncomputable def castItemSeqIso
    {source target : ItemSeq wires rels}
    (iso : ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels source target)
    (wiresEq : wires = outputWires) :
    ItemSeqIso (FiniteEquiv.refl (Fin outputWires)) rels
      (source.castWiresEq wiresEq) (target.castWiresEq wiresEq) := by
  have commutes :
      (FiniteEquiv.refl (Fin outputWires)).toFun ∘ Fin.cast wiresEq =
        Fin.cast wiresEq ∘
          (FiniteEquiv.refl (Fin wires)).toFun := by
    funext index
    rfl
  have mapped := iso.renameWires_commuting (Fin.cast wiresEq)
    (Fin.cast wiresEq) (FiniteEquiv.refl (Fin outputWires)) commutes
  simpa only [ItemSeq.castWiresEq_eq_renameWires] using mapped

/-- The exact target site compiler body is the intrinsic capture-avoiding
splice of the two retained abstract source site bodies.  Its only wire
transport is the source-derived retained-frame/dense-material equivalence. -/
noncomputable def spliceCompilerSiteBodyIso
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (hostKernel : host.local.Kernel) (hostBlocks : hostKernel.Blocks)
    (material : CompiledMaterial normalized.toInput)
    (materialKernel : material.Kernel)
    (materialBlocks : materialKernel.Blocks) :
    RegionIso (layout.mapFrameContextEquiv consistent host.siteContext)
      host.siteRels
      (Region.spliceAt host.siteLocals.length
        (host.siteBody.itemsCast host.siteBody_localCount)
        material.siteBody
        (Fin.cast List.length_append ∘
          material.spliceWireMap normalized.toInput layout admissible
            (host.siteContext ++ host.siteLocals)
            host.local.completeContext_exact)
        (fun relation => material.spliceRelationMap normalized.toInput admissible
          host.siteBinders host.binder_covers relation))
      (layout.spliceCompilerSiteBody normalized consistent admissible host
        hostKernel hostBlocks material materialKernel materialBlocks) := by
  let hostContext := host.siteContext ++ host.siteLocals
  let frameMap := layout.frameSiteIndexMap consistent hostContext
  let materialMap := layout.patternContextIndexMap consistent admissible
    material hostContext host.local.completeContext_exact
  let relationMap : RelationRenaming material.siteRels host.siteRels :=
    fun relation => material.spliceRelationMap normalized.toInput admissible
      host.siteBinders host.binder_covers relation
  let frameNodes := hostBlocks.nodeItems.renameWires frameMap
  let frameChildren := hostBlocks.childItems.renameWires frameMap
  let materialNodes := (materialBlocks.nodeItems.renameWires
    materialMap).renameRelations relationMap
  let materialChildren := (materialBlocks.childItems.renameWires
    materialMap).renameRelations relationMap
  let compilerItems := (frameNodes.append materialNodes).append
    (frameChildren.append materialChildren)
  let frameMaterialItems := (frameNodes.append frameChildren).append
    (materialNodes.append materialChildren)
  let outputLength := layout.patternSiteWires_split_length consistent
    host.siteContext host.siteLocals
  let sourceWireMap := Fin.cast List.length_append ∘
    material.spliceWireMap normalized.toInput layout admissible hostContext
      host.local.completeContext_exact
  let frameSourceItems :=
    (hostKernel.items.castWiresEq List.length_append).renameWires
      (Region.adjoinHostWire host.siteContext.length host.siteLocals.length
        material.siteLocals.length)
  let materialSourceItems :=
    (((materialKernel.items.castWiresEq List.length_append).renameWires
      (extendWireRenaming sourceWireMap material.siteLocals.length)
      ).renameRelations relationMap).renameWires
      (Region.adjoinMaterialWire host.siteContext.length
        host.siteLocals.length material.siteLocals.length)
  have frameIso := layout.frameItemsIso normalized consistent host hostKernel
    hostBlocks material
  have materialIso := layout.materialItemsIso normalized consistent admissible
    host material materialKernel materialBlocks
  have frameMaterialIso := frameIso.append materialIso
  have frameMaterialIso' :
      ItemSeqIso (layout.siteOutputWireEquiv normalized consistent host material)
        host.siteRels
        (frameSourceItems.append materialSourceItems)
        (frameMaterialItems.castWiresEq outputLength) := by
    have castAppendEq : frameMaterialItems.castWiresEq outputLength =
        ((frameNodes.append frameChildren).castWiresEq outputLength).append
          ((materialNodes.append materialChildren).castWiresEq
            outputLength) := by
      dsimp only [frameMaterialItems]
      exact ItemSeq.castWiresEq_append outputLength _ _
    rw [castAppendEq]
    simpa only [hostContext, frameMap, materialMap, relationMap,
      frameNodes, frameChildren, materialNodes, materialChildren,
      frameMaterialItems, sourceWireMap, frameSourceItems,
      materialSourceItems] using frameMaterialIso
  let blockPermutation := Splice.nodeChildBlocksToFrameMaterialBlocks
    frameNodes materialNodes frameChildren materialChildren
  let reordered := (castItemSeqIso blockPermutation outputLength).symm
  have finalItems := frameMaterialIso'.trans reordered
  have outputTrans :
      (layout.siteOutputWireEquiv normalized consistent host material).trans
          (FiniteEquiv.refl (Fin
            ((layout.mapFrameContext consistent host.siteContext).length +
              ((layout.mapFrameContext consistent host.siteLocals).length +
                layout.bodyLocalWires.length)))).symm =
        layout.siteOutputWireEquiv normalized consistent host material := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [outputTrans] at finalItems
  have normalized :
      ItemSeqIso (layout.siteOutputWireEquiv normalized consistent host material)
        host.siteRels
        (frameSourceItems.append materialSourceItems)
        (compilerItems.castWiresEq outputLength) := by
    simpa only [blockPermutation, compilerItems, frameMaterialItems,
      reordered] using finalItems
  let localWire := extendWireEquiv
    (layout.mapFrameContextEquiv consistent host.siteLocals)
    (layout.bodyLocalEquiv material)
  have regionIso : RegionIso
      (layout.mapFrameContextEquiv consistent host.siteContext)
      host.siteRels
      (.mk (host.siteLocals.length + material.siteLocals.length)
        (frameSourceItems.append materialSourceItems))
      (.mk ((layout.mapFrameContext consistent host.siteLocals).length +
          layout.bodyLocalWires.length)
        (compilerItems.castWiresEq outputLength)) := by
    exact RegionIso.mk localWire normalized
  rw [kernel_siteBody_itemsCast_eq hostKernel, materialKernel.body_eq]
  simpa only [hostContext, relationMap, compilerItems, frameNodes,
    materialNodes, frameChildren, materialChildren, sourceWireMap,
    frameSourceItems, materialSourceItems,
    spliceCompilerSiteBody, Region.spliceAt, Region.adjoinAt,
    Region.renameWires, Region.renameRelations] using regionIso

end Splice.Input.PlugLayout

end VisualProof.Concrete
