import VisualProof.Rule.Completeness.Comprehension
import VisualProof.Rule.Completeness.Erasure.Exposure

namespace VisualProof.Rule.Completeness.Erasure.TwoSite

open Diagram
open Theory
open WirePrimitive

def pattern
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    OpenDiagram description.materialWires :=
  Exposure.supportPattern description.material materialCanonical

def commonEquiv
    (description : Rule.Erasure.Description outer) :
    WireEquiv (outer ++ description.hostLocals)
      (outer ++ (description.hostLocals ++ [])) :=
  WireEquiv.ofEq (by simp)

/-- Eliminate the syntactic append-nil left by `before := hostLocals`. -/
noncomputable def appendNilAdjoinIso
    (hostLocals : List Sig) (body : Region (outer ++ hostLocals)) :
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt (hostLocals ++ []) .nil
        (body.renameWires
          (WireEquiv.ofEq (by simp) :
            WireEquiv (outer ++ hostLocals)
              (outer ++ (hostLocals ++ []))).toRenaming))
      (Region.adjoinAt hostLocals .nil body) := by
  cases body with
  | mk locals items =>
      let inheritedIso : WireEquiv (outer ++ hostLocals)
          (outer ++ (hostLocals ++ [])) := WireEquiv.ofEq (by simp)
      let localIso : WireEquiv ((hostLocals ++ []) ++ locals)
          (hostLocals ++ locals) := WireEquiv.ofEq (by simp)
      let ambient := (WireEquiv.refl outer).append localIso
      let sourceRename := WireRenaming.comp
        (Region.adjoinMaterialWire outer (hostLocals ++ []) locals)
        (inheritedIso.toRenaming.appendRight locals)
      let targetRename := Region.adjoinMaterialWire outer hostLocals locals
      have ambientIndex : ∀ {signature}
          (wire : Var (outer ++ ((hostLocals ++ []) ++ locals)) signature),
          (ambient wire).index.val = wire.index.val := by
        intro signature wire
        apply Var.appendCases (left := outer)
          (right := (hostLocals ++ []) ++ locals)
          (motive := fun wire => (ambient wire).index.val = wire.index.val)
        · intro outerSignature outerWire
          simp [ambient]
        · intro localSignature localWire
          simp [ambient, localIso, WireEquiv.ofEq_index_val]
      have sourceRenameIndex : ∀ {signature}
          (wire : Var ((outer ++ hostLocals) ++ locals) signature),
          (sourceRename wire).index.val = wire.index.val := by
        intro signature wire
        rw [show (sourceRename wire).index.val =
            ((inheritedIso.toRenaming.appendRight locals) wire).index.val by
          exact Region.adjoinMaterialWire_index_val _]
        apply Var.appendCases (left := outer ++ hostLocals) (right := locals)
          (motive := fun wire =>
            ((inheritedIso.toRenaming.appendRight locals) wire).index.val =
              wire.index.val)
        · intro inheritedSignature inherited
          simp [WireRenaming.appendRight, inheritedIso,
            WireEquiv.ofEq_index_val]
        · intro localSignature localWire
          simp [WireRenaming.appendRight]
      have commutes : ∀ {signature}
          (wire : Var ((outer ++ hostLocals) ++ locals) signature),
          ambient (sourceRename wire) = targetRename wire := by
        intro signature wire
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [ambientIndex, sourceRenameIndex,
          Region.adjoinMaterialWire_index_val]
      refine .mk localIso ?_
      simpa only [Region.adjoinAt, Region.renameWires, Region.locals,
        Region.items, ItemSeq.nil_append, ItemSeq.renameWires_comp,
        sourceRename, targetRename, ambient, inheritedIso] using
        (ItemSeqIso.renameWires items sourceRename targetRename ambient
          commutes)

/-- The support-completed material instantiated at the erased attachment. -/
def instanceRegion
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Region (outer ++ (description.hostLocals ++ [])) :=
  Comprehension.Instantiation.instantiate
    (pattern description materialCanonical)
    ((Exposure.applicationPorts description).map fun wire =>
      commonEquiv description wire)

def retainedHost
    (description : Rule.Erasure.Description outer) :
    Region (outer ++ (description.hostLocals ++ [])) :=
  Comprehension.retainedItemsPresentation
    (description.hostItems.renameWires (commonEquiv description).toRenaming)

/-- The exact two-site specialization produced by empty-fresh Iteration. -/
def specializedBody
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Region (outer ++ (description.hostLocals ++ [])) :=
  (instanceRegion description materialCanonical).conjoin
    ((instanceRegion description materialCanonical).conjoin
      (retainedHost description))

def specialized
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) : Region outer :=
  Region.adjoinAt (description.hostLocals ++ []) .nil
    (specializedBody description materialCanonical)

def baseInstance
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Region (outer ++ description.hostLocals) :=
  Comprehension.Instantiation.instantiate
    (pattern description materialCanonical)
    (Exposure.applicationPorts description)

def targetPresentation
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) : Region outer :=
  Region.adjoinAt description.hostLocals .nil
    ((baseInstance description materialCanonical).conjoin
      ((baseInstance description materialCanonical).conjoin
        (Comprehension.retainedItemsPresentation description.hostItems)))

noncomputable def specializedTargetIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      (specialized description materialCanonical)
      (targetPresentation description materialCanonical) := by
  simp only [specialized, specializedBody, instanceRegion, retainedHost,
    targetPresentation, baseInstance]
  rw [← Comprehension.EqualityNormalization.instantiate_renameWires,
    ← Comprehension.retainedItemsPresentation_renameWires,
    ← Region.renameWires_conjoin, ← Region.renameWires_conjoin]
  let body :=
    (Comprehension.Instantiation.instantiate
      (pattern description materialCanonical)
      (Exposure.applicationPorts description)).conjoin
        ((Comprehension.Instantiation.instantiate
          (pattern description materialCanonical)
          (Exposure.applicationPorts description)).conjoin
            (Comprehension.retainedItemsPresentation description.hostItems))
  change RegionIso (WireEquiv.refl outer)
    (Region.adjoinAt (description.hostLocals ++ []) .nil
      (body.renameWires (commonEquiv description).toRenaming))
    (Region.adjoinAt description.hostLocals .nil body)
  simpa only [commonEquiv] using
    (appendNilAdjoinIso description.hostLocals body)

def duplicatedMaterial
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Region (outer ++ description.hostLocals) :=
  (baseInstance description materialCanonical).conjoin
    (baseInstance description materialCanonical)

noncomputable def specializedHostedIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      (specialized description materialCanonical)
      (Region.adjoinAt description.hostLocals description.hostItems
        (duplicatedMaterial description materialCanonical)) := by
  let inst := baseInstance description materialCanonical
  let retained := Comprehension.retainedItemsPresentation description.hostItems
  let duplicated := inst.conjoin inst
  let reassociate := RegionIso.conjoinAssoc inst inst retained
  let presentRetained := RegionIso.conjoinCongr
    (RegionIso.refl duplicated)
    (Comprehension.retainedItemsPresentationIso description.hostItems)
  let swap := RegionIso.conjoinComm duplicated
    (Region.ofItems description.hostItems)
  let bodyPresentation := reassociate.symm.trans
    (presentRetained.trans swap)
  let lifted := RegionIso.adjoinAt description.hostLocals .nil
    bodyPresentation
  let hosted := RegionIso.ofEq
    (adjoinAt_hostedMaterial description.hostLocals description.hostItems
      duplicated).symm
  let chain := (specializedTargetIso description materialCanonical).trans
    (lifted.trans hosted)
  have ambientEq :
      (WireEquiv.refl outer).trans
          ((WireEquiv.refl outer).trans (WireEquiv.refl outer)) =
        WireEquiv.refl outer := by
    apply WireEquiv.ext
    intro signature wire
    rfl
  simpa only [duplicatedMaterial, duplicated, inst, retained] using
    chain.castAmbient ambientEq

theorem specialized_canonical
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical)
    (erasedCanonical : description.target.Canonical) :
    (specialized description materialCanonical).Canonical := by
  have instanceCanonical :
      (baseInstance description materialCanonical).Canonical :=
    Comprehension.Instantiation.instantiate_canonical
      (pattern description materialCanonical)
      (Exposure.applicationPorts description)
  have duplicatedCanonical :
      (duplicatedMaterial description materialCanonical).Canonical := by
    exact (Region.Canonical.conjoin_iff _ _).mpr
      ⟨instanceCanonical, instanceCanonical⟩
  have hostedCanonical :
      (Region.adjoinAt description.hostLocals description.hostItems
        (duplicatedMaterial description materialCanonical)).Canonical :=
    Region.Canonical.adjoinAt description.hostLocals description.hostItems
      (duplicatedMaterial description materialCanonical)
      erasedCanonical duplicatedCanonical
  exact (specializedHostedIso description materialCanonical).canonical_iff.mpr
    hostedCanonical

def frame
    (description : Rule.Erasure.Description outer) :=
  Content.Ends.rootFrame outer description.hostLocals []
    description.materialWires

def application
    (description : Rule.Erasure.Description outer) :
    Vars (outer ++ (description.hostLocals ++ []))
      description.materialWires :=
  (Exposure.applicationPorts description).map fun wire =>
    commonEquiv description wire

theorem frame_sourceKeep_index
    (description : Rule.Erasure.Description outer)
    (wire : Var (outer ++ (description.hostLocals ++ [])) signature) :
    ((frame description).sourceKeep wire).index.val = wire.index.val := by
  apply Var.appendCases (left := outer)
    (right := description.hostLocals ++ [])
    (motive := fun wire =>
      ((frame description).sourceKeep wire).index.val = wire.index.val)
  · intro inheritedSignature inherited
    simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
      Transform.Frame.keep]
  · intro localSignature localWire
    apply Var.appendCases (left := description.hostLocals) (right := [])
      (motive := fun localWire =>
        ((frame description).sourceKeep
          (Var.appendRight outer localWire)).index.val =
            (Var.appendRight outer localWire).index.val)
    · intro hostSignature hostWire
      simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep]
    · intro trailingSignature trailing
      exact nomatch trailing

theorem frame_targetKeep_eq_id
    (description : Rule.Erasure.Description outer) :
    (frame description).targetKeep = WireRenaming.id := by
  apply WireRenaming.ext
  intro signature wire
  apply Var.eq_of_index_eq
  apply Fin.ext
  apply Var.appendCases (left := outer)
    (right := description.hostLocals ++ [])
    (motive := fun wire =>
      ((frame description).targetKeep wire).index.val = wire.index.val)
  · intro inheritedSignature inherited
    simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
      Transform.Frame.keep]
  · intro localSignature localWire
    apply Var.appendCases (left := description.hostLocals) (right := [])
      (motive := fun localWire =>
        ((frame description).targetKeep
          (Var.appendRight outer localWire)).index.val =
            (Var.appendRight outer localWire).index.val)
    · intro hostSignature hostWire
      simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep]
    · intro trailingSignature trailing
      exact nomatch trailing

def selectedAtom
    (description : Rule.Erasure.Description outer) :
    Item (outer ++ (description.hostLocals ++
      .rel description.materialWires :: [])) :=
  .atom (frame description).selected
    ((application description).map fun wire => (frame description).sourceKeep wire)

def quantifiedItems
    (description : Rule.Erasure.Description outer) :
    ItemSeq (outer ++ (description.hostLocals ++
      .rel description.materialWires :: [])) :=
  .cons (selectedAtom description)
    (.cons (selectedAtom description)
      ((description.hostItems.renameWires
        (commonEquiv description).toRenaming).renameWires
          (frame description).sourceKeep))

def quantified
    (description : Rule.Erasure.Description outer) : Region outer :=
  .mk (description.hostLocals ++ [.rel description.materialWires])
    (quantifiedItems description)

def relationHead
    (description : Rule.Erasure.Description outer) :
    Var ((outer ++ description.hostLocals) ++
      [.rel description.materialWires]) (.rel description.materialWires) :=
  Var.appendRight (outer ++ description.hostLocals) .here

def relationPorts
    (description : Rule.Erasure.Description outer) :
    Vars ((outer ++ description.hostLocals) ++
      [.rel description.materialWires]) description.materialWires :=
  (Exposure.applicationPorts description).map fun wire =>
    wire.appendLeft [.rel description.materialWires]

def relationItems
    (description : Rule.Erasure.Description outer) :
    ItemSeq ((outer ++ description.hostLocals) ++
      [.rel description.materialWires]) :=
  .cons (.atom (relationHead description) (relationPorts description))
    (.cons (.atom (relationHead description) (relationPorts description)) .nil)

def relationMaterial
    (description : Rule.Erasure.Description outer) :
    Region (outer ++ description.hostLocals) :=
  .mk [.rel description.materialWires] (relationItems description)

theorem relationMaterial_canonical
    (description : Rule.Erasure.Description outer) :
    (relationMaterial description).Canonical := by
  constructor
  · intro localIndex
    have localIndexZero : localIndex.val = 0 := by
      have bound := localIndex.isLt
      change localIndex.val < 1 at bound
      omega
    have selectedIndex : (relationHead description).index.val =
        (outer ++ description.hostLocals).length := by
      simp [relationHead]
    rw [localIndexZero]
    simp only [relationItems,
      ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
      Nat.add_zero, selectedIndex, if_pos, List.length_append,
      List.length_replicate, RegionPath.RootedTwo]
    constructor
    · omega
    · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
      simp
  · exact ⟨True.intro, ⟨True.intro, True.intro⟩⟩

def hostFirst
    (description : Rule.Erasure.Description outer) : Region outer :=
  Region.adjoinAt description.hostLocals description.hostItems
    (relationMaterial description)

def atomFirst
    (description : Rule.Erasure.Description outer) : Region outer :=
  Region.appendAdjoinedHostSuffix description.hostLocals .nil
    description.hostItems (relationMaterial description)

theorem quantified_eq_atomFirst
    (description : Rule.Erasure.Description outer) :
    quantified description = atomFirst description := by
  have selectedEq : (frame description).selected =
      Region.adjoinMaterialWire outer description.hostLocals
        [.rel description.materialWires] (relationHead description) := by
    apply Var.eq_of_index_eq
    apply Fin.ext
    simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
      Transform.Frame.insertedHead, relationHead,
      Region.adjoinMaterialWire]
  have portEq :
      (application description).map
          (fun wire => (frame description).sourceKeep wire) =
        (relationPorts description).map
          (fun wire => Region.adjoinMaterialWire outer
            description.hostLocals [.rel description.materialWires] wire) := by
    unfold application relationPorts
    rw [Vars.map_map, Vars.map_map]
    apply Vars.map_congr
    intro signature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    rw [frame_sourceKeep_index]
    simp only [commonEquiv, WireEquiv.ofEq_index_val,
      Region.adjoinMaterialWire_index_val, Var.index_appendLeft]
  have hostMapEq : WireRenaming.comp (frame description).sourceKeep
      (commonEquiv description).toRenaming =
      Region.adjoinHostWire outer description.hostLocals
        [.rel description.materialWires] := by
    apply WireRenaming.ext
    intro signature wire
    apply Var.eq_of_index_eq
    apply Fin.ext
    change ((frame description).sourceKeep
      (commonEquiv description wire)).index.val = _
    rw [frame_sourceKeep_index]
    simp only [commonEquiv, WireEquiv.ofEq_index_val,
      Region.adjoinHostWire_index_val]
  unfold quantified quantifiedItems selectedAtom atomFirst
    Region.appendAdjoinedHostSuffix relationMaterial relationItems
  simp only [ItemSeq.renameWires, Item.renameWires, ItemSeq.nil_append,
    ItemSeq.renameWires_comp]
  rw [hostMapEq, selectedEq, portEq]
  rfl

noncomputable def quantifiedHostFirstIso
    (description : Rule.Erasure.Description outer) :
    RegionIso (WireEquiv.refl outer)
      (quantified description) (hostFirst description) :=
  (RegionIso.ofEq (quantified_eq_atomFirst description)).trans
    (RegionIso.adjoinAtMoveHostSuffix description.hostLocals .nil
      description.hostItems (relationMaterial description))

theorem hostFirst_canonical
    (description : Rule.Erasure.Description outer)
    (erasedCanonical : description.target.Canonical) :
    (hostFirst description).Canonical := by
  exact Region.Canonical.adjoinAt description.hostLocals
    description.hostItems (relationMaterial description)
    erasedCanonical (relationMaterial_canonical description)

theorem quantified_canonical
    (description : Rule.Erasure.Description outer)
    (erasedCanonical : description.target.Canonical) :
    (quantified description).Canonical :=
  (quantifiedHostFirstIso description).canonical_iff.mpr
    (hostFirst_canonical description erasedCanonical)

def retainedResult
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :=
  Comprehension.retainedItemsResult
    (pattern description materialCanonical) (frame description)
    (description.hostItems.renameWires (commonEquiv description).toRenaming)

def itemsResult
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Comprehension.Instantiation.ItemsResult
      (pattern description materialCanonical)
      (frame description).sourceKeep (frame description).selected
      (quantifiedItems description)
      (specializedBody description materialCanonical) :=
  .cons (.selectedAtom (application description))
    (.cons (.selectedAtom (application description))
      (retainedResult description materialCanonical))

/-- The declarative two-site comprehension witness. -/
theorem instantiates
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Rule.Comprehension.Instantiates
      (pattern description materialCanonical) description.hostLocals []
      (quantified description)
      (specialized description materialCanonical) := by
  exact .mk (itemsResult description materialCanonical)

def retainedSites
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :=
  Comprehension.retainedItemsSites
    (pattern description materialCanonical)
    (Content.Ends.operation description.materialWires)
    (frame description) PUnit.unit
    (description.hostItems.renameWires (commonEquiv description).toRenaming)

mutual
  def retainedRegionGuard
      (polarity : Polarity)
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (region : Region common) :
      Content.Ends.Absorb.RegionGuard polarity frame
        (Comprehension.regionEdit
          (operation := Content.Ends.operation arguments) PUnit.unit
          (Comprehension.retainedRegionResult pattern frame region)
          (Comprehension.retainedRegionSites pattern
            (Content.Ends.operation arguments) frame PUnit.unit region)).edit :=
    by
      cases region with
      | mk locals items =>
          simpa only [Comprehension.regionEdit,
            Comprehension.retainedRegionResult,
            Comprehension.retainedRegionSites] using
            Content.Ends.Absorb.RegionGuard.mk
              (retainedItemsGuard polarity pattern
                (frame.append locals) items)
  termination_by sizeOf region

  def retainedItemsGuard
      (polarity : Polarity)
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (items : ItemSeq common) :
      Content.Ends.Absorb.ItemsGuard polarity frame
        (Comprehension.itemsEdit
          (operation := Content.Ends.operation arguments) PUnit.unit
          (Comprehension.retainedItemsResult pattern frame items)
          (Comprehension.retainedItemsSites pattern
            (Content.Ends.operation arguments) frame PUnit.unit items)).edit :=
    by
      cases items with
      | nil =>
          simpa only [Comprehension.itemsEdit,
            Comprehension.retainedItemsResult,
            Comprehension.retainedItemsSites] using
            (Content.Ends.Absorb.ItemsGuard.nil (polarity := polarity)
              (frame := frame))
      | cons item tail =>
          simpa only [Comprehension.itemsEdit,
            Comprehension.retainedItemsResult,
            Comprehension.retainedItemsSites] using
            Content.Ends.Absorb.ItemsGuard.cons
              (retainedItemGuard polarity pattern frame item)
              (retainedItemsGuard polarity pattern frame tail)
  termination_by sizeOf items

  def retainedItemGuard
      (polarity : Polarity)
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (item : Item common) :
      Content.Ends.Absorb.ItemGuard polarity frame
        (Comprehension.itemEdit
          (operation := Content.Ends.operation arguments) PUnit.unit
          (Comprehension.retainedItemResult pattern frame item)
          (Comprehension.retainedItemSites pattern
            (Content.Ends.operation arguments) frame PUnit.unit item)).edit :=
    by
      cases item with
      | atom head ports =>
          simpa only [Comprehension.itemEdit,
            Comprehension.retainedItemResult,
            Comprehension.retainedItemSites] using
            Content.Ends.Absorb.ItemGuard.atom (polarity := polarity)
              (frame := frame) head ports
      | identity signature arity ports =>
          simpa only [Comprehension.itemEdit,
            Comprehension.retainedItemResult,
            Comprehension.retainedItemSites] using
            Content.Ends.Absorb.ItemGuard.identity (polarity := polarity)
              (frame := frame) signature arity ports
      | cut body =>
          simpa only [Comprehension.itemEdit,
            Comprehension.retainedItemResult,
            Comprehension.retainedItemSites] using
            Content.Ends.Absorb.ItemGuard.cut
              (Comprehension.regionEdit
                (operation := Content.Ends.operation arguments) PUnit.unit
                (Comprehension.retainedRegionResult pattern frame body)
                (Comprehension.retainedRegionSites pattern
                  (Content.Ends.operation arguments) frame PUnit.unit body)).edit
              (retainedRegionGuard (Content.Ends.Absorb.flip polarity)
                pattern frame body)
  termination_by sizeOf item
end

def itemsSites
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Comprehension.ItemsSites
      (Content.Ends.operation description.materialWires) PUnit.unit
      (itemsResult description materialCanonical) :=
  .cons (.selectedAtom (pattern := pattern description materialCanonical)
      (frame := frame description) (application description) PUnit.unit)
    (.cons (.selectedAtom (pattern := pattern description materialCanonical)
        (frame := frame description) (application description) PUnit.unit)
      (retainedSites description materialCanonical))

def editOutput
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :=
  Comprehension.itemsEdit
    (operation := Content.Ends.operation description.materialWires)
    PUnit.unit (itemsResult description materialCanonical)
    (itemsSites description materialCanonical)

def absorbedBody
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Region (outer ++ (description.hostLocals ++ [])) :=
  (editOutput description materialCanonical).endpoint

def absorbed
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) : Region outer :=
  Region.adjoinAt (description.hostLocals ++ []) .nil
    (absorbedBody description materialCanonical)

noncomputable def absorbedBodyRetainedIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl (outer ++ (description.hostLocals ++ [])))
      (absorbedBody description materialCanonical)
      (retainedHost description) := by
  let retained := retainedHost description
  let inner := RegionIso.blankConjoin retained
  let outerBlank := RegionIso.blankConjoin
    ((Region.blank (outer ++ (description.hostLocals ++ []))).conjoin retained)
  have retainedEndpoint := Comprehension.retainedItemsEditEndpoint
    (pattern description materialCanonical)
    (Content.Ends.operation description.materialWires)
    (frame description) PUnit.unit
    (description.hostItems.renameWires
      (commonEquiv description).toRenaming)
  have retainedEndpoint' :
      (Comprehension.itemsEdit
        (operation := Content.Ends.operation description.materialWires)
        PUnit.unit
        (Comprehension.retainedItemsResult
          (pattern description materialCanonical)
          (frame description)
          (description.hostItems.renameWires
            (commonEquiv description).toRenaming))
        (Comprehension.retainedItemsSites
          (pattern description materialCanonical)
          (Content.Ends.operation description.materialWires)
          (frame description) PUnit.unit
          (description.hostItems.renameWires
            (commonEquiv description).toRenaming))).endpoint =
        retainedHost description := by
    let base := Comprehension.retainedItemsPresentation
      (description.hostItems.renameWires
        (commonEquiv description).toRenaming)
    calc
      _ = base.renameWires WireRenaming.id := by
        simpa only [frame_targetKeep_eq_id] using retainedEndpoint
      _ = base := Region.renameWires_id base
      _ = retainedHost description := rfl
  change RegionIso (WireEquiv.refl (outer ++ (description.hostLocals ++ [])))
    ((Region.blank (outer ++ (description.hostLocals ++ []))).conjoin
      ((Region.blank (outer ++ (description.hostLocals ++ []))).conjoin
        (Comprehension.itemsEdit
          (operation := Content.Ends.operation description.materialWires)
          PUnit.unit
          (Comprehension.retainedItemsResult
            (pattern description materialCanonical)
            (frame description)
            (description.hostItems.renameWires
              (commonEquiv description).toRenaming))
          (Comprehension.retainedItemsSites
            (pattern description materialCanonical)
            (Content.Ends.operation description.materialWires)
            (frame description) PUnit.unit
            (description.hostItems.renameWires
              (commonEquiv description).toRenaming))).endpoint))
    (retainedHost description)
  rw [retainedEndpoint']
  exact outerBlank.trans inner

noncomputable def absorbedTargetIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      (absorbed description materialCanonical) description.target := by
  let removeBlanks := RegionIso.adjoinAt
    (description.hostLocals ++ []) .nil
    (absorbedBodyRetainedIso description materialCanonical)
  let retainedCommon :=
    Comprehension.retainedItemsPresentation
      (description.hostItems.renameWires (commonEquiv description).toRenaming)
  let retainedBase :=
    Comprehension.retainedItemsPresentation description.hostItems
  have retainedRename : retainedCommon =
      retainedBase.renameWires (commonEquiv description).toRenaming := by
    exact (Comprehension.retainedItemsPresentation_renameWires
      description.hostItems (commonEquiv description).toRenaming).symm
  let appendNil := appendNilAdjoinIso description.hostLocals retainedBase
  let presentation := RegionIso.adjoinAt description.hostLocals .nil
    (Comprehension.retainedItemsPresentationIso description.hostItems)
  let collapse := RegionIso.adjoinAtOfItems description.hostLocals
    description.hostItems
  have commonToPresented : RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt (description.hostLocals ++ []) .nil retainedCommon)
      (Region.adjoinAt description.hostLocals .nil retainedBase) := by
    rw [retainedRename]
    exact appendNil
  exact removeBlanks.trans
    (commonToPresented.trans (presentation.trans collapse))

def deletion
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Content.Ends.Delete.Description outer where
  arguments := description.materialWires
  before := description.hostLocals
  after := []
  items := quantifiedItems description
  itemsEdit := (editOutput description materialCanonical).edit

@[simp] theorem deletion_source
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    (deletion description materialCanonical).source = quantified description := by
  rfl

theorem deletion_target
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    (deletion description materialCanonical).target =
      absorbed description materialCanonical := by
  simp only [Content.Ends.Delete.Description.target, absorbed, absorbedBody,
    deletion]
  exact congrArg (Region.adjoinAt (description.hostLocals ++ []) .nil)
    (editOutput description materialCanonical).run_eq

def guard
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Content.Ends.Absorb.ItemsGuard .positive
      (frame description) (deletion description materialCanonical).itemsEdit :=
  .cons (.selectedAtom (application description))
    (.cons (.selectedAtom (application description))
      (retainedItemsGuard .positive
        (pattern description materialCanonical) (frame description)
        (description.hostItems.renameWires
          (commonEquiv description).toRenaming)))

def absorbDescription
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Content.Ends.Absorb.Description outer where
  deletion := deletion description materialCanonical
  guard := guard description materialCanonical

/-- Both selected sites occur at positive parity, so the guarded converse of
Ends absorbs the quantified two-site block. -/
theorem absorbEvidence
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    Content.Ends.Absorb
      (quantified description) (absorbed description materialCanonical) := by
  have evidence := Content.Ends.Absorb.mk
    (absorbDescription description materialCanonical)
  change Content.Ends.Absorb
    (deletion description materialCanonical).source
    (deletion description materialCanonical).target at evidence
  rw [deletion_source, deletion_target] at evidence
  exact evidence

theorem specializedFilledValidity
    {boundary outer : List Sig}
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source)
    (erasedCanonical :
      (occurrence.context.fill description.target).Canonical)
    (erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target)) :
    (occurrence.context.fill
        (specialized description materialCanonical)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (specialized description materialCanonical)) := by
  let hosted := Region.adjoinAt description.hostLocals description.hostItems
    (duplicatedMaterial description materialCanonical)
  have hostedCanonical : hosted.Canonical :=
    (specializedHostedIso description materialCanonical).canonical_iff.mp
      (specialized_canonical description materialCanonical
        (occurrence.context.holeCanonical description.target erasedCanonical))
  have extension := occurrence.context.extendCanonical description.target
    hosted erasedCanonical hostedCanonical (by
      intro signature wire
      simpa only [Rule.Erasure.Description.target, hosted] using
        Region.incidencePaths_adjoinAt_host_sublist
          description.hostLocals description.hostItems
          (duplicatedMaterial description materialCanonical) wire)
  have hostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill hosted) := by
    intro signature wire
    exact Nat.le_trans (erasedExternalTwoEnded wire)
      (Nat.add_le_add_left (extension.2 wire).length_le _)
  let filledIso := occurrence.context.fillIso
    (specializedHostedIso description materialCanonical)
  constructor
  · exact filledIso.canonical_iff.mpr extension.1
  · intro signature wire
    rw [filledIso.incidencePaths_length_eq wire]
    exact hostedExternalTwoEnded wire

theorem quantifiedFilledValidity
    {boundary outer : List Sig}
    (description : Rule.Erasure.Description outer)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source)
    (erasedCanonical :
      (occurrence.context.fill description.target).Canonical)
    (erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target)) :
    (occurrence.context.fill (quantified description)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill (quantified description)) := by
  have targetCanonical : description.target.Canonical :=
    occurrence.context.holeCanonical description.target erasedCanonical
  have extension := occurrence.context.extendCanonical description.target
    (hostFirst description) erasedCanonical
    (hostFirst_canonical description targetCanonical) (by
      intro signature wire
      simpa only [Rule.Erasure.Description.target, hostFirst] using
        Region.incidencePaths_adjoinAt_host_sublist
          description.hostLocals description.hostItems
          (relationMaterial description) wire)
  have hostFirstExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (hostFirst description)) := by
    intro signature wire
    exact Nat.le_trans (erasedExternalTwoEnded wire)
      (Nat.add_le_add_left (extension.2 wire).length_le _)
  let filledIso := occurrence.context.fillIso
    (quantifiedHostFirstIso description)
  constructor
  · exact filledIso.canonical_iff.mpr extension.1
  · intro signature wire
    rw [filledIso.incidencePaths_length_eq wire]
    exact hostFirstExternalTwoEnded wire

theorem absorbedFilledValidity
    {boundary outer : List Sig}
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source)
    (erasedCanonical :
      (occurrence.context.fill description.target).Canonical)
    (erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target)) :
    (occurrence.context.fill
        (absorbed description materialCanonical)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (absorbed description materialCanonical)) := by
  let filledIso := occurrence.context.fillIso
    (absorbedTargetIso description materialCanonical)
  constructor
  · exact filledIso.canonical_iff.mpr erasedCanonical
  · intro signature wire
    rw [filledIso.incidencePaths_length_eq wire]
    exact erasedExternalTwoEnded wire


end VisualProof.Rule.Completeness.Erasure.TwoSite
