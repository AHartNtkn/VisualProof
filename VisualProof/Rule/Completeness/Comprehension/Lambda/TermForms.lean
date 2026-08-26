import VisualProof.Rule.Completeness.Comprehension.Leaf.Forms
import VisualProof.Rule.Lambda.TermLeaf

namespace VisualProof.Rule.Completeness.Comprehension.LambdaTerm

open Diagram
open Theory
open WirePrimitive

/-- The literal Lambda term used by the direct Lambda TermLeaf client.
Its ordered formal ports make the operation's site datum canonical. -/
def positionalTermMaterial (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    Region (Lambda.TermLeaf.arguments freeArity) :=
  let application := EqualityNormalization.formalPorts
    (Lambda.TermLeaf.arguments freeArity)
  Region.singleton (.term (Lambda.TermLeaf.Vars.output application) freeArity
    (Lambda.TermLeaf.Vars.ports application) term)

theorem positionalTermMaterial_canonical
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    (positionalTermMaterial freeArity term).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

/-- The valid open pattern obtained by exposing the literal Lambda term.
This definition aligns exactly with the shared exposure theorem. -/
def positionalTermPattern (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    OpenDiagram (Lambda.TermLeaf.arguments freeArity) :=
  Erasure.Exposure.supportPattern
    (positionalTermMaterial freeArity term)
    (positionalTermMaterial_canonical freeArity term)

def positionalTermApplication
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (application : Vars wires (Lambda.TermLeaf.arguments freeArity)) :
    Region wires :=
  Region.singleton (.term (Lambda.TermLeaf.Vars.output application) freeArity
    (Lambda.TermLeaf.Vars.ports application) term)

theorem positionalTermMaterial_rename
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (application : Vars wires (Lambda.TermLeaf.arguments freeArity)) :
    (positionalTermMaterial freeArity term).renameWires
        (EqualityNormalization.formalSubstitution application) =
      positionalTermApplication freeArity term application := by
  unfold positionalTermMaterial positionalTermApplication
  rw [Region.singleton_renameWires]
  apply congrArg Region.singleton
  simp only [Item.renameWires]
  have mapped := EqualityNormalization.formalPorts_map_substitution application
  have outputEq := congrArg Lambda.TermLeaf.Vars.output mapped
  have portsEq := congrArg Lambda.TermLeaf.Vars.ports mapped
  have outputEq' :
      EqualityNormalization.formalSubstitution application
          (Lambda.TermLeaf.Vars.output
            (EqualityNormalization.formalPorts
              (Lambda.TermLeaf.arguments freeArity))) =
        Lambda.TermLeaf.Vars.output application := by
    simpa using outputEq
  have portsEq' :
      (fun slot => EqualityNormalization.formalSubstitution application
        (Lambda.TermLeaf.Vars.ports
          (EqualityNormalization.formalPorts
            (Lambda.TermLeaf.arguments freeArity)) slot)) =
        Lambda.TermLeaf.Vars.ports application := by
    simpa using portsEq
  rw [outputEq']
  congr 1

theorem termSiteNatural
    {freeArity : Nat} {term : VisualProof.Lambda.Term 0 (Fin freeArity)}
    {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
      siteTargetWires siteMappedTargetWires : List Sig}
    {siteFrame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      siteCommon siteSourceWires siteTargetWires}
    {siteMappedFrame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      siteMappedCommon siteMappedSourceWires siteMappedTargetWires}
    {siteData : (Lambda.TermLeaf.operation freeArity term).Data siteFrame}
    {siteMappedData :
      (Lambda.TermLeaf.operation freeArity term).Data siteMappedFrame}
    (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
    (siteTargetRename : WireRenaming siteTargetWires siteMappedTargetWires)
    (siteTargetKeepCommutes : ∀ {wireSignature}
      (wire : Var siteCommon wireSignature),
      siteTargetRename (siteFrame.targetKeep wire) =
        siteMappedFrame.targetKeep (siteCommonRename wire))
    (ports : Vars siteCommon (Lambda.TermLeaf.arguments freeArity))
    (site : (Lambda.TermLeaf.operation freeArity term).SiteData
      siteFrame siteData ports) :
    ∃ mappedSite :
        (Lambda.TermLeaf.operation freeArity term).SiteData
          siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire),
      Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
        (((Lambda.TermLeaf.operation freeArity term).site
          siteFrame siteData ports site).renameWires siteTargetRename)
        ((Lambda.TermLeaf.operation freeArity term).site
          siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire) mappedSite)) := by
  let mappedOutput := siteCommonRename site.val.1
  let mappedPorts := fun slot => siteCommonRename (site.val.2 slot)
  have mappedProperty :
      ports.map (fun wire => siteCommonRename wire) =
        Lambda.TermLeaf.Vars.fromTerm mappedOutput mappedPorts := by
    rw [← Lambda.TermLeaf.Vars.fromTerm_map, ← site.property]
  let mappedSite :
      (Lambda.TermLeaf.operation freeArity term).SiteData
        siteMappedFrame siteMappedData
        (ports.map fun wire => siteCommonRename wire) :=
    ⟨⟨mappedOutput, mappedPorts⟩, mappedProperty⟩
  refine ⟨mappedSite, ⟨RegionIso.ofEq ?_⟩⟩
  unfold Lambda.TermLeaf.operation
  rw [Region.singleton_renameWires]
  apply congrArg Region.singleton
  change Item.term
      (siteTargetRename (siteFrame.targetKeep site.val.1)) freeArity
        (fun slot => siteTargetRename
          (siteFrame.targetKeep (site.val.2 slot))) term = _
  rw [siteTargetKeepCommutes site.val.1]
  congr 1
  funext slot
  exact siteTargetKeepCommutes (site.val.2 slot)

def termDataNaturality (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    DataNaturality (Lambda.TermLeaf.operation freeArity term) where
  Coherent := fun _ _ _ _ _ _ => True
  append := by intros; trivial
  appendAssoc := by intros; trivial
  conjoinLeft := by intros; trivial
  conjoinRight := by intros; trivial
  appendNil := by intros; trivial
  site := by
    intro common mappedCommon sourceWires mappedSourceWires targetWires
      mappedTargetWires frame mappedFrame data mappedData commonRename
      targetRename _coherent targetKeepCommutes ports siteData
    exact termSiteNatural commonRename targetRename targetKeepCommutes
      ports siteData

theorem termRecordingSiteNatural
    {freeArity : Nat} {term : VisualProof.Lambda.Term 0 (Fin freeArity)} {patternArguments : List Sig}
    {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
      siteTargetWires siteMappedTargetWires : List Sig}
    {siteFrame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      siteCommon siteSourceWires siteTargetWires}
    {siteMappedFrame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      siteMappedCommon siteMappedSourceWires siteMappedTargetWires}
    {siteData : (Lambda.TermLeaf.operation freeArity term).Data siteFrame}
    {siteMappedData :
      (Lambda.TermLeaf.operation freeArity term).Data siteMappedFrame}
    (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
    (siteTargetRename : WireRenaming siteTargetWires siteMappedTargetWires)
    (siteTargetKeepCommutes : ∀ {wireSignature}
      (wire : Var siteCommon wireSignature),
      siteTargetRename (siteFrame.targetKeep wire) =
        siteMappedFrame.targetKeep (siteCommonRename wire))
    (ports : Vars siteCommon (Lambda.TermLeaf.arguments freeArity))
    (site : (recordingOperation (Lambda.TermLeaf.operation freeArity term)
      patternArguments).SiteData siteFrame siteData ports) :
    ∃ mappedSite :
        (recordingOperation (Lambda.TermLeaf.operation freeArity term)
          patternArguments).SiteData siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire),
      Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
        (((recordingOperation (Lambda.TermLeaf.operation freeArity term)
          patternArguments).site siteFrame siteData ports site).renameWires
            siteTargetRename)
        ((recordingOperation (Lambda.TermLeaf.operation freeArity term)
          patternArguments).site siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire) mappedSite)) := by
  obtain ⟨termSite, application⟩ := site
  obtain ⟨mappedTermSite, ⟨siteIso⟩⟩ :=
    termSiteNatural siteCommonRename siteTargetRename
      siteTargetKeepCommutes ports termSite
  exact ⟨⟨mappedTermSite,
      application.map fun wire => siteCommonRename wire⟩, ⟨siteIso⟩⟩

def termExposureDescriptionWithHost
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals)
      (Lambda.TermLeaf.arguments freeArity)) :
    Rule.UncappedErasure.Description outer where
  materialWires := Lambda.TermLeaf.arguments freeArity
  hostLocals := hostLocals
  hostItems := hostItems
  material := positionalTermMaterial freeArity term
  wireMap := EqualityNormalization.formalSubstitution application

theorem termExposureDescriptionWithHost_source
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals)
      (Lambda.TermLeaf.arguments freeArity)) :
    (termExposureDescriptionWithHost freeArity term hostLocals
      hostItems application).source =
      Region.adjoinAt hostLocals hostItems
        (positionalTermApplication freeArity term application) := by
  simp only [termExposureDescriptionWithHost,
    Rule.UncappedErasure.Description.source, Region.spliceAt]
  rw [positionalTermMaterial_rename]

theorem termExposureDescriptionWithHost_exposed
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals)
      (Lambda.TermLeaf.arguments freeArity))
    (materialCanonical :
      (termExposureDescriptionWithHost freeArity term hostLocals
        hostItems application).material.Canonical) :
    Erasure.Exposure.exposedRegion
        (termExposureDescriptionWithHost freeArity term hostLocals
          hostItems application) materialCanonical =
      Region.adjoinAt hostLocals hostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) application) := by
  unfold Erasure.Exposure.exposedRegion
  change Region.adjoinAt hostLocals hostItems
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (positionalTermMaterial freeArity term) materialCanonical)
        ((Erasure.Exposure.identityBoundary
          (Lambda.TermLeaf.arguments freeArity)).map
            (fun wire =>
              EqualityNormalization.formalSubstitution application wire))) = _
  have portsEq :
      (Erasure.Exposure.identityBoundary
        (Lambda.TermLeaf.arguments freeArity)).map
          (fun wire =>
            EqualityNormalization.formalSubstitution application wire) =
        application := by
    rw [← EqualityNormalization.formalPorts_eq_exposure,
      EqualityNormalization.formalPorts_map_substitution]
  rw [portsEq]
  have patternEq :
      Erasure.Exposure.supportPattern
          (positionalTermMaterial freeArity term) materialCanonical =
        positionalTermPattern freeArity term := by
    apply EqualityNormalization.OpenDiagram.eq_of_data
    · rfl
    · rfl
    · rfl
  rw [patternEq]

/-- Exposing literal term material is a nonempty symmetric phase from the
direct term to its positional-pattern instantiation. -/
theorem equatesPositionalTermApplication
    {boundary outer : List Sig}
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (application : Vars (outer ++ hostLocals)
      (Lambda.TermLeaf.arguments freeArity))
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (positionalTermApplication freeArity term application)) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalTermPattern freeArity term)
            application))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalTermPattern freeArity term) application)))) :
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) application))
      targetCanonical targetExternalTwoEnded := by
  by_cases nonempty : outer ++ hostLocals ≠ []
  · let pinnedItems := hostItems.append
      (EqualityNormalization.contextPins outer hostLocals)
    let description := termExposureDescriptionWithHost freeArity term
      hostLocals pinnedItems application
    apply EqualityNormalization.pinnedExposureStrict occurrence
      targetCanonical targetExternalTwoEnded nonempty description
    · simpa only [description] using
        termExposureDescriptionWithHost_source freeArity term hostLocals
          pinnedItems application
    · rfl
    · intro materialCanonical
      simpa only [description] using
        termExposureDescriptionWithHost_exposed freeArity term hostLocals
          pinnedItems application materialCanonical
  · have empty : outer ++ hostLocals = [] := Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] :=
      (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    let description := termExposureDescriptionWithHost freeArity term
      [] hostItems application
    have sourceEq : description.source =
        Region.adjoinAt [] hostItems
          (positionalTermApplication freeArity term application) := by
      simpa only [description] using
        termExposureDescriptionWithHost_source freeArity term []
          hostItems application
    let exposureOccurrence : Occurrence description.source source := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := by
        rw [sourceEq]
        exact occurrence.sourceCanonical
      sourceExternalTwoEnded := by
        intro wireSignature wire
        rw [sourceEq]
        exact occurrence.sourceExternalTwoEnded wire
      host_iso := by
        simpa only [sourceEq] using occurrence.host_iso
    }
    have directLocalCanonical :
        (Region.adjoinAt [] hostItems
          (positionalTermApplication freeArity term application)
        ).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have erasedLocalCanonical : description.target.Canonical := by
      have canonical := EqualityNormalization.pinnedHostCanonical
        ([] : List Sig) hostItems
        (positionalTermApplication freeArity term application)
        directLocalCanonical
      simpa only [description, termExposureDescriptionWithHost,
        Rule.UncappedErasure.Description.target,
        EqualityNormalization.contextPins,
        EqualityNormalization.allPins, List.nil_append,
        ItemSeq.pinWires, ItemSeq.nil_append, ItemSeq.append_nil] using canonical
    have erasedSameNonempty : ∀ {wireSignature}
        (wire : Var [] wireSignature),
        (Region.adjoinAt [] hostItems
          (positionalTermApplication freeArity term application)
        ).incidencePaths wire.index.val ≠ [] ↔
          description.target.incidencePaths wire.index.val ≠ [] := by
      intro wireSignature wire
      exact Fin.elim0 wire.index
    have erasedReplacement := occurrence.context.replaceCanonical
      (Region.adjoinAt [] hostItems
        (positionalTermApplication freeArity term application))
      description.target occurrence.sourceCanonical erasedLocalCanonical
        erasedSameNonempty
    let sourceEndpoint := occurrence.interface.withBody
      (occurrence.context.fill
        (Region.adjoinAt [] hostItems
          (positionalTermApplication freeArity term application)))
      occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
    have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill description.target) :=
      sourceEndpoint.externalTwoEnded_of_nonempty_iff _ erasedReplacement.2
    obtain ⟨materialCanonical, exposedCanonical,
        exposedExternalTwoEnded, exposedEquates⟩ :=
      Erasure.Exposure.equates description exposureOccurrence
        erasedReplacement.1 erasedExternalTwoEnded
    have exposedEq :
        Erasure.Exposure.exposedRegion description materialCanonical =
          Region.adjoinAt [] hostItems
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              (positionalTermPattern freeArity term) application) := by
      simpa only [description] using
        termExposureDescriptionWithHost_exposed freeArity term []
          hostItems application materialCanonical
    have equivalent : Equates occurrence
        (Region.adjoinAt [] hostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalTermPattern freeArity term) application))
        targetCanonical targetExternalTwoEnded := by
      simpa only [exposureOccurrence, sourceEq, exposedEq] using
        exposedEquates
    exact EqualityNormalization.strictEquates_of_equates occurrence equivalent

theorem positionalTermApplication_incidencePaths
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (application : Vars wires (Lambda.TermLeaf.arguments freeArity))
    (wire : Var wires wireSignature) :
    (positionalTermApplication freeArity term application).incidencePaths
        wire.index.val =
      List.replicate (application.countIndex wire.index.val) [] := by
  cases application with
  | cons output ports =>
      simp only [positionalTermApplication, Region.singleton, Region.ofItems,
        Region.incidencePaths, ItemSeq.renameWires, Item.renameWires,
        ItemSeq.incidencePaths, Item.incidencePaths, List.append_nil,
        Var.index_appendLeft, Lambda.TermLeaf.Vars.output,
        Lambda.TermLeaf.Vars.ports, Vars.countIndex]
      dsimp
      rw [← Leaf.Identity.Vars.countIndex_fromFn]
      change List.replicate
          ((if output.index.val = wire.index.val then 1 else 0) +
            (Leaf.Identity.Vars.fromFn
              (Leaf.Identity.Vars.toFn ports)).countIndex wire.index.val) [] = _
      rw [Leaf.Identity.Vars.fromFn_toFn]

theorem positionalTermApplication_incidencePaths_length
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (application : Vars wires (Lambda.TermLeaf.arguments freeArity))
    (wire : Var wires wireSignature) :
    ((positionalTermApplication freeArity term application).incidencePaths
        wire.index.val).length =
      application.countIndex wire.index.val := by
  rw [positionalTermApplication_incidencePaths, List.length_replicate]

theorem positionalTermInstantiation_scope
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (application : Vars wires (Lambda.TermLeaf.arguments freeArity)) :
    ScopePreservation
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalTermPattern freeArity term) application)
      (positionalTermApplication freeArity term application) := by
  constructor
  · intro _
    unfold positionalTermApplication
    change (forall _ : Fin 0, _) ∧ _
    exact ⟨fun localIndex => Fin.elim0 localIndex,
      ⟨True.intro, True.intro⟩⟩
  · intro wireSignature wire
    rw [← List.length_pos_iff, ← List.length_pos_iff,
      EqualityNormalization.instantiate_incidencePaths_length,
      positionalTermApplication_incidencePaths_length]
  · intro wireSignature wire sourceRoot
    have countBound : 2 ≤ application.countIndex wire.index.val := by
      rw [← EqualityNormalization.instantiate_rootedTwo_iff]
      exact sourceRoot
    constructor
    · rw [positionalTermApplication_incidencePaths_length]
      exact countBound
    · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
      rw [positionalTermApplication_incidencePaths,
        List.mem_replicate]
      exact ⟨by omega, rfl⟩

/-- Re-expanding a positional term application preserves the structural
scope facts needed to compose the leaf transformation inside a host. -/
theorem positionalTermApplication_scope
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (application : Vars wires (Lambda.TermLeaf.arguments freeArity)) :
    ScopePreservation
      (positionalTermApplication freeArity term application)
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalTermPattern freeArity term) application) := by
  let forward := positionalTermInstantiation_scope freeArity term
    application
  constructor
  · intro _
    exact VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
      (positionalTermPattern freeArity term) application
  · intro wireSignature wire
    exact (forward.incidenceNonempty wire).symm
  · intro wireSignature wire rooted
    rw [EqualityNormalization.instantiate_rootedTwo_iff]
    rw [← positionalTermApplication_incidencePaths_length]
    exact rooted.1

def termFormalPrefixSource
    (frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    ItemSeq sourceWires :=
  (hostItems.renameWires frame.sourceKeep).append
    (.cons (.atom frame.selected
      (application.map fun wire => frame.sourceKeep wire)) .nil)

def termFormalPrefixResult
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    Region common :=
  match hostItems with
  | .nil =>
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalTermPattern freeArity term) application).conjoin
        (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (termFormalPrefixResult freeArity term tail application)

theorem termFormalPrefixResult_renameWires
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostItems : ItemSeq sourceWires)
    (application : Vars sourceWires (Lambda.TermLeaf.arguments freeArity))
    (rename : WireRenaming sourceWires targetWires) :
    (termFormalPrefixResult freeArity term hostItems application).renameWires
        rename =
      termFormalPrefixResult freeArity term
        (hostItems.renameWires rename)
        (application.map fun wire => rename wire) := by
  cases hostItems with
  | nil =>
      unfold termFormalPrefixResult
      rw [Region.renameWires_conjoin,
        EqualityNormalization.instantiate_renameWires]
      rfl
  | cons item tail =>
      unfold termFormalPrefixResult
      rw [Region.renameWires_conjoin,
        retainedItemPresentation_renameWires item rename,
        termFormalPrefixResult_renameWires freeArity term tail
          application rename]
      rfl
termination_by sizeOf hostItems

def termFormalPrefixEvidence
    (frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      (positionalTermPattern freeArity term)
      frame.sourceKeep frame.selected
      (termFormalPrefixSource frame hostItems application)
      (termFormalPrefixResult freeArity term hostItems application) := by
  cases hostItems with
  | nil =>
      exact VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          application)
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
  | cons item tail =>
      simp only [termFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, termFormalPrefixResult]
      change VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (positionalTermPattern freeArity term) frame.sourceKeep
        frame.selected
        (.cons (item.renameWires frame.sourceKeep)
          (termFormalPrefixSource frame tail application))
        ((retainedItemPresentation item).conjoin
          (termFormalPrefixResult freeArity term tail application))
      exact VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (retainedItemResult (positionalTermPattern freeArity term)
          frame item)
        (termFormalPrefixEvidence (term := term) frame tail application)
termination_by sizeOf hostItems

def termFormalPrefixSites
    (frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    ItemsSites (Lambda.TermLeaf.operation freeArity term) PUnit.unit
      (termFormalPrefixEvidence (term := term) frame hostItems application) :=
  match hostItems with
  | .nil =>
      let termOutput := Lambda.TermLeaf.Vars.output application
      let termPorts := Lambda.TermLeaf.Vars.ports application
      let termPortsEq : application =
          Lambda.TermLeaf.Vars.fromTerm termOutput termPorts :=
        (Lambda.TermLeaf.Vars.fromTerm_output_ports application).symm
      let siteData :
          (Lambda.TermLeaf.operation freeArity term).SiteData
            frame PUnit.unit application :=
        ⟨⟨termOutput, termPorts⟩, termPortsEq⟩
      let tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (positionalTermPattern freeArity term) frame.sourceKeep
            frame.selected .nil (Region.blank common) :=
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom
          (pattern := positionalTermPattern freeArity term)
          (frame := frame) application siteData)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites (positionalTermPattern freeArity term)
          (Lambda.TermLeaf.operation freeArity term) frame PUnit.unit item)
        (termFormalPrefixSites (term := term) frame tail application)
termination_by sizeOf hostItems

def termFormalPrefixRecordingSites
    (frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (retained : Vars common (Lambda.TermLeaf.arguments freeArity))
    (application : Vars common patternArguments) :
    ItemsSites
      (recordingOperation (Lambda.TermLeaf.operation freeArity term)
        patternArguments)
      PUnit.unit
      (termFormalPrefixEvidence (term := term) frame hostItems retained) :=
  match hostItems with
  | .nil =>
      let termOutput := Lambda.TermLeaf.Vars.output retained
      let termPorts := Lambda.TermLeaf.Vars.ports retained
      let termPortsEq : retained =
          Lambda.TermLeaf.Vars.fromTerm termOutput termPorts :=
        (Lambda.TermLeaf.Vars.fromTerm_output_ports retained).symm
      let termSite :
          (Lambda.TermLeaf.operation freeArity term).SiteData
            frame PUnit.unit retained :=
        ⟨⟨termOutput, termPorts⟩, termPortsEq⟩
      let tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (positionalTermPattern freeArity term) frame.sourceKeep
            frame.selected .nil (Region.blank common) :=
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom
          (pattern := positionalTermPattern freeArity term)
          (frame := frame) retained ⟨termSite, application⟩)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites (positionalTermPattern freeArity term)
          (recordingOperation (Lambda.TermLeaf.operation freeArity term)
            patternArguments)
          frame PUnit.unit item)
        (termFormalPrefixRecordingSites (term := term) frame tail retained
          application)
termination_by sizeOf hostItems

theorem termFormalPrefixArgumentItemsEdit_source
    {term : VisualProof.Lambda.Term 0 (Fin freeArity)}
    (recordedFrame : Transform.Frame
      (Lambda.TermLeaf.arguments freeArity) common
      recordedSourceWires recordedTargetWires)
    (targetFrame : Transform.Frame arguments common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (retained : Vars common (Lambda.TermLeaf.arguments freeArity))
    (application : Vars common patternArguments)
    (current : Vars patternArguments arguments) :
    (argumentItemsEdit
      (termFormalPrefixRecordingSites (term := term) recordedFrame hostItems retained
        application)
      current (normalizationOperation arguments) targetFrame PUnit.unit
      (fun _ _ _ => PUnit.unit)).1 =
        (hostItems.renameWires targetFrame.sourceKeep).append
          (.cons (.atom targetFrame.selected
            (current.map fun wire =>
              targetFrame.sourceKeep
                (EqualityNormalization.formalSubstitution application wire)))
            .nil) := by
  cases hostItems with
  | nil =>
      simp only [termFormalPrefixRecordingSites, argumentItemsEdit,
        argumentItemEdit, ItemSeq.renameWires, ItemSeq.append, Vars.map_map]
  | cons item tail =>
      simp only [termFormalPrefixRecordingSites, argumentItemsEdit,
        ItemSeq.renameWires, ItemSeq.append]
      congr 1
      · exact retainedItemSites_argumentItemEdit_source
          (positionalTermPattern freeArity term)
          (Lambda.TermLeaf.operation freeArity term) recordedFrame PUnit.unit
          targetFrame item current
      · exact termFormalPrefixArgumentItemsEdit_source (term := term) recordedFrame
          targetFrame tail retained application current
termination_by sizeOf hostItems

theorem termFormalPrefixSource_eq_argumentItemsEdit
    {term : VisualProof.Lambda.Term 0 (Fin freeArity)}
    (frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (retained : Vars common (Lambda.TermLeaf.arguments freeArity))
    (application : Vars common patternArguments)
    (values : Vars patternArguments (Lambda.TermLeaf.arguments freeArity))
    (rename : WireRenaming patternArguments common)
    (applicationEq : application =
      (EqualityNormalization.formalPorts patternArguments).map
        fun wire => rename wire)
    (valuesEq : values.map (fun wire => rename wire) = retained) :
    termFormalPrefixSource frame hostItems retained =
      (argumentItemsEdit
        (termFormalPrefixRecordingSites (term := term) frame hostItems retained
          application)
        values
        (normalizationOperation (Lambda.TermLeaf.arguments freeArity))
        frame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
  cases hostItems with
  | nil =>
      simp only [termFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, termFormalPrefixRecordingSites,
        argumentItemsEdit, argumentItemEdit]
      rw [applicationEq]
      have substitutionEq : values.map (fun wire =>
            EqualityNormalization.formalSubstitution
              ((EqualityNormalization.formalPorts patternArguments).map
                fun formalWire => rename formalWire) wire) =
          values.map (fun wire => rename wire) := by
        apply Vars.map_congr
        intro wireSignature wire
        exact EqualityNormalization.formalSubstitution_formalPorts_map
          rename wire
      rw [substitutionEq, valuesEq]
  | cons item tail =>
      simp only [termFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, termFormalPrefixRecordingSites,
        argumentItemsEdit]
      congr 1
      · exact (retainedItemSites_argumentItemEdit_source
          (positionalTermPattern freeArity term)
          (Lambda.TermLeaf.operation freeArity term) frame PUnit.unit frame item
          values).symm
      · simpa only [termFormalPrefixSource] using
          termFormalPrefixSource_eq_argumentItemsEdit (term := term) frame tail retained
            application values rename applicationEq valuesEq

noncomputable def termFormalPrefixResultIso
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    RegionIso (WireEquiv.refl common)
      (termFormalPrefixResult freeArity term hostItems application)
      ((Region.ofItems hostItems).conjoin
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) application)) :=
  match hostItems with
  | .nil => by
      let inner :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) application
      exact (RegionIso.conjoinBlank inner).trans
        (RegionIso.blankConjoin inner).symm
  | .cons item tail => by
      let inner :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) application
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (termFormalPrefixResultIso freeArity term tail application)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) inner).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl inner)
      exact children.trans (associated.trans prefixIso)
termination_by sizeOf hostItems

def termFormalPrefixEndpoint
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    Region common :=
  match hostItems with
  | .nil =>
      (positionalTermApplication freeArity term application).conjoin
        (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (termFormalPrefixEndpoint freeArity term tail application)

theorem termFormalPrefixEndpoint_renameWires
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostItems : ItemSeq sourceWires)
    (application : Vars sourceWires (Lambda.TermLeaf.arguments freeArity))
    (rename : WireRenaming sourceWires targetWires) :
    (termFormalPrefixEndpoint freeArity term hostItems application).renameWires
        rename =
      termFormalPrefixEndpoint freeArity term
        (hostItems.renameWires rename)
        (application.map fun wire => rename wire) := by
  cases hostItems with
  | nil =>
      unfold termFormalPrefixEndpoint
      rw [Region.renameWires_conjoin]
      simp only [positionalTermApplication,
        Region.singleton_renameWires, Item.renameWires,
        Lambda.TermLeaf.Vars.output_map,
        Lambda.TermLeaf.Vars.ports_map, ItemSeq.renameWires]
      rfl
  | cons item tail =>
      unfold termFormalPrefixEndpoint
      rw [Region.renameWires_conjoin,
        retainedItemPresentation_renameWires item rename,
        termFormalPrefixEndpoint_renameWires freeArity term tail
          application rename]
      rfl

noncomputable def termFormalPrefixEndpointIso
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    RegionIso (WireEquiv.refl common)
      (termFormalPrefixEndpoint freeArity term hostItems application)
      ((Region.ofItems hostItems).conjoin
        (positionalTermApplication freeArity term application)) :=
  match hostItems with
  | .nil => by
      let direct := positionalTermApplication freeArity term application
      exact (RegionIso.conjoinBlank direct).trans
        (RegionIso.blankConjoin direct).symm
  | .cons item tail => by
      let direct := positionalTermApplication freeArity term application
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (termFormalPrefixEndpointIso freeArity term tail application)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) direct).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl direct)
      exact children.trans (associated.trans prefixIso)
termination_by sizeOf hostItems

theorem termFormalPrefixItemsEditEndpoint
    {common sourceWires targetWires : List Sig}
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity) common
      sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity)) :
    (itemsEdit (operation := Lambda.TermLeaf.operation freeArity term)
      PUnit.unit
      (termFormalPrefixEvidence frame hostItems application)
      (termFormalPrefixSites frame hostItems application)).endpoint =
      (termFormalPrefixEndpoint freeArity term hostItems application).renameWires
        frame.targetKeep := by
  cases hostItems with
  | nil =>
      unfold termFormalPrefixSites itemsEdit
      dsimp only
      simp only [itemEdit, ExactEdit.refl, termFormalPrefixEndpoint,
        Transform.ItemEdit.run]
      unfold itemsEdit ExactEdit.refl Transform.ItemsEdit.run
      rw [Region.renameWires_conjoin]
      simp [Region.renameWires, Region.blank, Lambda.TermLeaf.operation,
        Region.singleton_renameWires, Item.renameWires,
        ItemSeq.renameWires, positionalTermApplication]
  | cons item tail =>
      have tailEq := termFormalPrefixItemsEditEndpoint freeArity term
        frame tail application
      have headEq :
          (itemEdit (operation := Lambda.TermLeaf.operation freeArity term)
            PUnit.unit
            (retainedItemResult (positionalTermPattern freeArity term)
              frame item)
            (retainedItemSites (positionalTermPattern freeArity term)
              (Lambda.TermLeaf.operation freeArity term) frame PUnit.unit
              item)).endpoint =
            (retainedItemPresentation item).renameWires
              frame.targetKeep := by
        exact retainedItemEditEndpoint
          (positionalTermPattern freeArity term)
          (Lambda.TermLeaf.operation freeArity term) frame PUnit.unit item
      unfold termFormalPrefixSites itemsEdit
      dsimp only
      unfold termFormalPrefixEndpoint
      rw [Region.renameWires_conjoin, headEq]
      exact congrArg
        (fun material =>
          (retainedItemPresentation item).renameWires frame.targetKeep |>.conjoin
            material)
        tailEq
termination_by sizeOf hostItems

theorem termFormalPrefixRecordingItemsEditEndpoint
    {common sourceWires targetWires : List Sig}
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (patternArguments : List Sig)
    (frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity) common
      sourceWires targetWires)
    (hostItems : ItemSeq common)
    (retained : Vars common (Lambda.TermLeaf.arguments freeArity))
    (application : Vars common patternArguments) :
    (itemsEdit
      (operation := recordingOperation
        (Lambda.TermLeaf.operation freeArity term) patternArguments)
      PUnit.unit
      (termFormalPrefixEvidence frame hostItems retained)
      (termFormalPrefixRecordingSites frame hostItems retained
        application)).endpoint =
      (termFormalPrefixEndpoint freeArity term hostItems retained).renameWires
        frame.targetKeep := by
  cases hostItems with
  | nil =>
      unfold termFormalPrefixRecordingSites itemsEdit
      dsimp only
      simp only [itemEdit, ExactEdit.refl, termFormalPrefixEndpoint,
        Transform.ItemEdit.run, recordingOperation]
      unfold itemsEdit ExactEdit.refl Transform.ItemsEdit.run
      rw [Region.renameWires_conjoin]
      simp [Region.renameWires, Region.blank, Lambda.TermLeaf.operation,
        Region.singleton_renameWires, Item.renameWires,
        ItemSeq.renameWires, positionalTermApplication]
  | cons item tail =>
      have tailEq := termFormalPrefixRecordingItemsEditEndpoint
        freeArity term patternArguments frame tail retained
          application
      have headEq :
          (itemEdit
            (operation := recordingOperation
              (Lambda.TermLeaf.operation freeArity term) patternArguments)
            PUnit.unit
            (retainedItemResult (positionalTermPattern freeArity term)
              frame item)
            (retainedItemSites (positionalTermPattern freeArity term)
              (recordingOperation (Lambda.TermLeaf.operation freeArity term)
                patternArguments)
              frame PUnit.unit item)).endpoint =
            (retainedItemPresentation item).renameWires
              frame.targetKeep := by
        exact retainedItemEditEndpoint
          (positionalTermPattern freeArity term)
          (recordingOperation (Lambda.TermLeaf.operation freeArity term)
            patternArguments)
          frame PUnit.unit item
      unfold termFormalPrefixRecordingSites itemsEdit
      dsimp only
      unfold termFormalPrefixEndpoint
      rw [Region.renameWires_conjoin, headEq]
      exact congrArg
        (fun material =>
          (retainedItemPresentation item).renameWires frame.targetKeep |>.conjoin
            material)
        tailEq
termination_by sizeOf hostItems


end VisualProof.Rule.Completeness.Comprehension.LambdaTerm
