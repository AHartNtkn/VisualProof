import VisualProof.Rule.Completeness.Comprehension.Normalization.Arguments

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

def positionalAtomWires (arguments : List Sig) : List Sig :=
  .rel arguments :: arguments

def positionalAtomHead (arguments : List Sig) :
    Var (positionalAtomWires arguments) (.rel arguments) :=
  .here

def positionalAtomPorts (arguments : List Sig) :
    Vars (positionalAtomWires arguments) arguments :=
  (EqualityNormalization.formalPorts arguments).map fun wire => .there wire

def positionalAtomItem (arguments : List Sig) :
    Item (positionalAtomWires arguments) :=
  .atom (positionalAtomHead arguments) (positionalAtomPorts arguments)

theorem Vars.countIndex_map_of_sameIndex
    (variables : Vars source signatures)
    (rename : WireRenaming source target)
    (sameIndex : ∀ {signature} (wire : Var source signature),
      (rename wire).index.val = wire.index.val)
    (index : Nat) :
    (variables.map fun wire => rename wire).countIndex index =
      variables.countIndex index := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex, sameIndex head, induction]

theorem positionalAtomCanonical (arguments : List Sig) :
    (Region.singleton (positionalAtomItem arguments)).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

theorem positionalAtomExternalTwoEnded (arguments : List Sig) :
    OpenDiagram.ExternalTwoEnded
      (EqualityNormalization.formalPorts (positionalAtomWires arguments))
      (Region.singleton (positionalAtomItem arguments)) := by
  intro signature wire
  have boundaryPositive : 0 <
      (EqualityNormalization.formalPorts
        (positionalAtomWires arguments)).countIndex wire.index.val := by
    have positive :=
      (EqualityNormalization.formalPorts (positionalAtomWires arguments))
        |>.countIndex_get_positive wire.index
    rw [EqualityNormalization.formalPorts_get_index] at positive
    exact positive
  have bodyPositive : 0 <
      ((Region.singleton (positionalAtomItem arguments)).incidencePaths
        wire.index.val).length := by
    simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
      ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
      Item.incidencePaths, List.append_nil, List.length_replicate,
      Var.index_appendLeft, positionalAtomItem, positionalAtomHead]
    let appendNil : WireRenaming (positionalAtomWires arguments)
        (positionalAtomWires arguments ++ []) :=
      ⟨fun selected => selected.appendLeft []⟩
    have portCountEq :
        ((positionalAtomPorts arguments).map
          (fun selected => appendNil selected)).countIndex wire.index.val =
        (positionalAtomPorts arguments).countIndex wire.index.val :=
      Vars.countIndex_map_of_sameIndex (positionalAtomPorts arguments)
        appendNil (fun selected => Var.index_appendLeft selected [])
          wire.index.val
    rw [show ((positionalAtomPorts arguments).map
        (fun selected => selected.appendLeft [])).countIndex wire.index.val =
          (positionalAtomPorts arguments).countIndex wire.index.val by
      simpa only [appendNil] using portCountEq]
    change 0 <
      (EqualityNormalization.formalPorts
        (positionalAtomWires arguments)).countIndex wire.index.val
    exact boundaryPositive
  omega

def positionalAtomPattern (arguments : List Sig) :
    OpenDiagram (positionalAtomWires arguments) := {
  external := positionalAtomWires arguments
  boundaryWire := EqualityNormalization.formalPorts
    (positionalAtomWires arguments)
  boundarySurjective := EqualityNormalization.formalPorts_surjective
  body := Region.singleton (positionalAtomItem arguments)
  canonical := positionalAtomCanonical arguments
  externalTwoEnded := positionalAtomExternalTwoEnded arguments
}

/-- The literal homogeneous identity used by the direct IdentityLeaf client.
Its ordered formal ports make the operation's site datum canonical. -/
def positionalIdentityMaterial (signature : Sig) (arity : Nat) :
    Region (List.replicate arity signature) :=
  Region.singleton (.identity signature arity
    (Leaf.Identity.Vars.toFn
      (EqualityNormalization.formalPorts
        (List.replicate arity signature))))

theorem positionalIdentityMaterial_canonical
    (signature : Sig) (arity : Nat) :
    (positionalIdentityMaterial signature arity).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

/-- The valid open pattern obtained by exposing the literal homogeneous
identity.  This definition aligns exactly with the shared exposure theorem. -/
def positionalIdentityPattern (signature : Sig) (arity : Nat) :
    OpenDiagram (List.replicate arity signature) :=
  Erasure.Exposure.supportPattern
    (positionalIdentityMaterial signature arity)
    (positionalIdentityMaterial_canonical signature arity)

def positionalIdentityApplication
    (signature : Sig) (arity : Nat)
    (application : Vars wires (List.replicate arity signature)) :
    Region wires :=
  Region.singleton (.identity signature arity
    (Leaf.Identity.Vars.toFn application))

theorem positionalIdentityMaterial_rename
    (signature : Sig) (arity : Nat)
    (application : Vars wires (List.replicate arity signature)) :
    (positionalIdentityMaterial signature arity).renameWires
        (EqualityNormalization.formalSubstitution application) =
      positionalIdentityApplication signature arity application := by
  unfold positionalIdentityMaterial positionalIdentityApplication
  rw [Region.singleton_renameWires]
  apply congrArg Region.singleton
  apply congrArg (Item.identity signature arity)
  funext position
  change EqualityNormalization.formalSubstitution application
      (Leaf.Identity.Vars.toFn
        (EqualityNormalization.formalPorts
          (List.replicate arity signature)) position) =
    Leaf.Identity.Vars.toFn application position
  have mapped := congrArg Leaf.Identity.Vars.toFn
    (EqualityNormalization.formalPorts_map_substitution application)
  simpa only [Leaf.Identity.Vars.toFn_map] using congrFun mapped position

theorem identitySiteNatural
    {signature : Sig} {arity : Nat}
    {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
      siteTargetWires siteMappedTargetWires : List Sig}
    {siteFrame : Transform.Frame (List.replicate arity signature)
      siteCommon siteSourceWires siteTargetWires}
    {siteMappedFrame : Transform.Frame (List.replicate arity signature)
      siteMappedCommon siteMappedSourceWires siteMappedTargetWires}
    {siteData : (Leaf.Identity.operation signature arity).Data siteFrame}
    {siteMappedData :
      (Leaf.Identity.operation signature arity).Data siteMappedFrame}
    (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
    (siteTargetRename : WireRenaming siteTargetWires siteMappedTargetWires)
    (siteTargetKeepCommutes : ∀ {wireSignature}
      (wire : Var siteCommon wireSignature),
      siteTargetRename (siteFrame.targetKeep wire) =
        siteMappedFrame.targetKeep (siteCommonRename wire))
    (ports : Vars siteCommon (List.replicate arity signature))
    (site : (Leaf.Identity.operation signature arity).SiteData
      siteFrame siteData ports) :
    ∃ mappedSite :
        (Leaf.Identity.operation signature arity).SiteData
          siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire),
      Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
        (((Leaf.Identity.operation signature arity).site
          siteFrame siteData ports site).renameWires siteTargetRename)
        ((Leaf.Identity.operation signature arity).site
          siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire) mappedSite)) := by
  let mappedPorts := fun position =>
    siteCommonRename (site.val position)
  have mappedProperty :
      ports.map (fun wire => siteCommonRename wire) =
        Leaf.Identity.Vars.fromFn mappedPorts := by
    rw [← Leaf.Identity.Vars.fromFn_map, ← site.property]
  let mappedSite :
      (Leaf.Identity.operation signature arity).SiteData
        siteMappedFrame siteMappedData
        (ports.map fun wire => siteCommonRename wire) :=
    ⟨mappedPorts, mappedProperty⟩
  refine ⟨mappedSite, ⟨RegionIso.ofEq ?_⟩⟩
  unfold Leaf.Identity.operation
  rw [Region.singleton_renameWires]
  apply congrArg Region.singleton
  apply congrArg (Item.identity signature arity)
  funext position
  exact siteTargetKeepCommutes (site.val position)

theorem identityRecordingSiteNatural
    {signature : Sig} {arity : Nat} {patternArguments : List Sig}
    {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
      siteTargetWires siteMappedTargetWires : List Sig}
    {siteFrame : Transform.Frame (List.replicate arity signature)
      siteCommon siteSourceWires siteTargetWires}
    {siteMappedFrame : Transform.Frame (List.replicate arity signature)
      siteMappedCommon siteMappedSourceWires siteMappedTargetWires}
    {siteData : (Leaf.Identity.operation signature arity).Data siteFrame}
    {siteMappedData :
      (Leaf.Identity.operation signature arity).Data siteMappedFrame}
    (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
    (siteTargetRename : WireRenaming siteTargetWires siteMappedTargetWires)
    (siteTargetKeepCommutes : ∀ {wireSignature}
      (wire : Var siteCommon wireSignature),
      siteTargetRename (siteFrame.targetKeep wire) =
        siteMappedFrame.targetKeep (siteCommonRename wire))
    (ports : Vars siteCommon (List.replicate arity signature))
    (site : (recordingOperation (Leaf.Identity.operation signature arity)
      patternArguments).SiteData siteFrame siteData ports) :
    ∃ mappedSite :
        (recordingOperation (Leaf.Identity.operation signature arity)
          patternArguments).SiteData siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire),
      Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
        (((recordingOperation (Leaf.Identity.operation signature arity)
          patternArguments).site siteFrame siteData ports site).renameWires
            siteTargetRename)
        ((recordingOperation (Leaf.Identity.operation signature arity)
          patternArguments).site siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire) mappedSite)) := by
  obtain ⟨identitySite, application⟩ := site
  obtain ⟨mappedIdentitySite, ⟨siteIso⟩⟩ :=
    identitySiteNatural siteCommonRename siteTargetRename
      siteTargetKeepCommutes ports identitySite
  exact ⟨⟨mappedIdentitySite,
      application.map fun wire => siteCommonRename wire⟩, ⟨siteIso⟩⟩

def identityExposureDescriptionWithHost
    (signature : Sig) (arity : Nat)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals)
      (List.replicate arity signature)) :
    Rule.Erasure.Description outer where
  materialWires := List.replicate arity signature
  hostLocals := hostLocals
  hostItems := hostItems
  material := positionalIdentityMaterial signature arity
  wireMap := EqualityNormalization.formalSubstitution application

theorem identityExposureDescriptionWithHost_source
    (signature : Sig) (arity : Nat)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals)
      (List.replicate arity signature)) :
    (identityExposureDescriptionWithHost signature arity hostLocals
      hostItems application).source =
      Region.adjoinAt hostLocals hostItems
        (positionalIdentityApplication signature arity application) := by
  simp only [identityExposureDescriptionWithHost,
    Rule.Erasure.Description.source, Region.spliceAt]
  rw [positionalIdentityMaterial_rename]

theorem identityExposureDescriptionWithHost_exposed
    (signature : Sig) (arity : Nat)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals)
      (List.replicate arity signature))
    (materialCanonical :
      (identityExposureDescriptionWithHost signature arity hostLocals
        hostItems application).material.Canonical) :
    Erasure.Exposure.exposedRegion
        (identityExposureDescriptionWithHost signature arity hostLocals
          hostItems application) materialCanonical =
      Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application) := by
  unfold Erasure.Exposure.exposedRegion
  change Region.adjoinAt hostLocals hostItems
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (positionalIdentityMaterial signature arity) materialCanonical)
        ((Erasure.Exposure.identityBoundary
          (List.replicate arity signature)).map
            (fun wire =>
              EqualityNormalization.formalSubstitution application wire))) = _
  have portsEq :
      (Erasure.Exposure.identityBoundary
        (List.replicate arity signature)).map
          (fun wire =>
            EqualityNormalization.formalSubstitution application wire) =
        application := by
    rw [← EqualityNormalization.formalPorts_eq_exposure,
      EqualityNormalization.formalPorts_map_substitution]
  rw [portsEq]
  have patternEq :
      Erasure.Exposure.supportPattern
          (positionalIdentityMaterial signature arity) materialCanonical =
        positionalIdentityPattern signature arity := by
    apply EqualityNormalization.OpenDiagram.eq_of_data
    · rfl
    · rfl
    · rfl
  rw [patternEq]

/-- Exposing the literal identity material is a nonempty symmetric phase from
the direct identity to its positional-pattern instantiation. -/
theorem equatesPositionalIdentityApplication
    {boundary outer : List Sig}
    (signature : Sig) (arity : Nat)
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (application : Vars (outer ++ hostLocals)
      (List.replicate arity signature))
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (positionalIdentityApplication signature arity application)) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalIdentityPattern signature arity)
            application))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalIdentityPattern signature arity) application)))) :
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application))
      targetCanonical targetExternalTwoEnded := by
  by_cases nonempty : outer ++ hostLocals ≠ []
  · let pinnedItems := hostItems.append
      (EqualityNormalization.contextPins outer hostLocals)
    let description := identityExposureDescriptionWithHost signature arity
      hostLocals pinnedItems application
    apply EqualityNormalization.pinnedExposureStrict occurrence
      targetCanonical targetExternalTwoEnded nonempty description
    · simpa only [description] using
        identityExposureDescriptionWithHost_source signature arity hostLocals
          pinnedItems application
    · rfl
    · intro materialCanonical
      simpa only [description] using
        identityExposureDescriptionWithHost_exposed signature arity hostLocals
          pinnedItems application materialCanonical
  · have empty : outer ++ hostLocals = [] := Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] :=
      (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    let description := identityExposureDescriptionWithHost signature arity
      [] hostItems application
    have sourceEq : description.source =
        Region.adjoinAt [] hostItems
          (positionalIdentityApplication signature arity application) := by
      simpa only [description] using
        identityExposureDescriptionWithHost_source signature arity []
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
          (positionalIdentityApplication signature arity application)
        ).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have erasedLocalCanonical : description.target.Canonical := by
      have canonical := EqualityNormalization.pinnedHostCanonical
        ([] : List Sig) hostItems
        (positionalIdentityApplication signature arity application)
        directLocalCanonical
      simpa only [description, identityExposureDescriptionWithHost,
        Rule.Erasure.Description.target,
        EqualityNormalization.contextPins,
        EqualityNormalization.allPins, List.nil_append,
        ItemSeq.pinWires, ItemSeq.nil_append, ItemSeq.append_nil] using canonical
    have erasedSameNonempty : ∀ {wireSignature}
        (wire : Var [] wireSignature),
        (Region.adjoinAt [] hostItems
          (positionalIdentityApplication signature arity application)
        ).incidencePaths wire.index.val ≠ [] ↔
          description.target.incidencePaths wire.index.val ≠ [] := by
      intro wireSignature wire
      exact Fin.elim0 wire.index
    have erasedReplacement := occurrence.context.replaceCanonical
      (Region.adjoinAt [] hostItems
        (positionalIdentityApplication signature arity application))
      description.target occurrence.sourceCanonical erasedLocalCanonical
        erasedSameNonempty
    let sourceEndpoint := occurrence.interface.withBody
      (occurrence.context.fill
        (Region.adjoinAt [] hostItems
          (positionalIdentityApplication signature arity application)))
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
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (positionalIdentityPattern signature arity) application) := by
      simpa only [description] using
        identityExposureDescriptionWithHost_exposed signature arity []
          hostItems application materialCanonical
    have equivalent : Equates occurrence
        (Region.adjoinAt [] hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalIdentityPattern signature arity) application))
        targetCanonical targetExternalTwoEnded := by
      simpa only [exposureOccurrence, sourceEq, exposedEq] using
        exposedEquates
    exact EqualityNormalization.strictEquates_of_equates occurrence equivalent

theorem positionalIdentityApplication_incidencePaths
    (signature : Sig) (arity : Nat)
    (application : Vars wires (List.replicate arity signature))
    (wire : Var wires wireSignature) :
    (positionalIdentityApplication signature arity application).incidencePaths
        wire.index.val =
      List.replicate (application.countIndex wire.index.val) [] := by
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun selected => selected.appendLeft []⟩
  have countEq :
      (List.ofFn fun position : Fin arity =>
        (appendNil (Leaf.Identity.Vars.toFn application position)).index.val
      ).count wire.index.val = application.countIndex wire.index.val := by
    calc
      _ = (Leaf.Identity.Vars.fromFn (fun position =>
          appendNil (Leaf.Identity.Vars.toFn application position))).countIndex
            wire.index.val :=
        (Leaf.Identity.Vars.countIndex_fromFn _ _).symm
      _ = (application.map fun selected => appendNil selected).countIndex
            wire.index.val := by
        rw [← Leaf.Identity.Vars.fromFn_map,
          Leaf.Identity.Vars.fromFn_toFn]
      _ = application.countIndex wire.index.val :=
        Vars.countIndex_map_of_sameIndex application appendNil
          (fun selected => Var.index_appendLeft selected []) wire.index.val
  simpa only [positionalIdentityApplication, Region.singleton,
    Region.ofItems, Region.incidencePaths, ItemSeq.renameWires,
    Item.renameWires, ItemSeq.incidencePaths, Item.incidencePaths,
    List.append_nil, appendNil] using congrArg
      (fun count => List.replicate count []) countEq

theorem positionalIdentityApplication_incidencePaths_length
    (signature : Sig) (arity : Nat)
    (application : Vars wires (List.replicate arity signature))
    (wire : Var wires wireSignature) :
    ((positionalIdentityApplication signature arity application).incidencePaths
        wire.index.val).length =
      application.countIndex wire.index.val := by
  rw [positionalIdentityApplication_incidencePaths, List.length_replicate]

theorem positionalIdentityInstantiation_scope
    (signature : Sig) (arity : Nat)
    (application : Vars wires (List.replicate arity signature)) :
    ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) application)
      (positionalIdentityApplication signature arity application) := by
  constructor
  · intro _
    unfold positionalIdentityApplication
    change (forall _ : Fin 0, _) ∧ _
    exact ⟨fun localIndex => Fin.elim0 localIndex,
      ⟨True.intro, True.intro⟩⟩
  · intro wireSignature wire
    rw [← List.length_pos_iff, ← List.length_pos_iff,
      EqualityNormalization.instantiate_incidencePaths_length,
      positionalIdentityApplication_incidencePaths_length]
  · intro wireSignature wire sourceRoot
    have countBound : 2 ≤ application.countIndex wire.index.val := by
      rw [← EqualityNormalization.instantiate_rootedTwo_iff]
      exact sourceRoot
    constructor
    · rw [positionalIdentityApplication_incidencePaths_length]
      exact countBound
    · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
      rw [positionalIdentityApplication_incidencePaths,
        List.mem_replicate]
      exact ⟨by omega, rfl⟩

def positionalAtomSelection
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) :
    Vars wires (positionalAtomWires atomArguments) :=
  .cons head ports

theorem varsExtendHEqRight
    (initial : Vars context initialSignatures)
    {firstSignatures secondSignatures : List Sig}
    (first : Vars context firstSignatures)
    (second : Vars context secondSignatures)
    (signaturesEq : firstSignatures = secondSignatures)
    (equal : HEq first second) :
    HEq (Vars.extend initial first) (Vars.extend initial second) := by
  cases signaturesEq
  have valuesEq : first = second := eq_of_heq equal
  cases valuesEq
  rfl

theorem EqualityNormalization.formalPorts_cons_of_nonempty
    (nonempty : arguments ≠ []) :
    ∃ (signature : Sig) (rest : List Sig)
        (head : Var arguments signature) (tail : Vars arguments rest),
      arguments = signature :: rest ∧
        HEq (EqualityNormalization.formalPorts arguments)
          (Vars.cons head tail) := by
  cases arguments with
  | nil => exact (nonempty rfl).elim
  | cons signature rest =>
      refine ⟨signature, rest, .here,
        (EqualityNormalization.formalPorts rest).map fun wire => .there wire,
        rfl, ?_⟩
      simp only [EqualityNormalization.formalPorts,
        Erasure.Exposure.identityBoundary, Vars.map]
      exact HEq.rfl

def positionalAtomCollapse
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) :
    WireRenaming (positionalAtomWires atomArguments) wires :=
  EqualityNormalization.formalSubstitution
    (positionalAtomSelection head ports)

@[simp] theorem positionalAtomItem_rename
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) :
    (positionalAtomItem atomArguments).renameWires
        (positionalAtomCollapse head ports) =
      .atom head ports := by
  let tailRename : WireRenaming atomArguments
      (positionalAtomWires atomArguments) := ⟨fun wire => .there wire⟩
  let collapse := positionalAtomCollapse head ports
  have portsEq : (positionalAtomPorts atomArguments).map
      (fun wire => collapse wire) = ports := by
    calc
      (positionalAtomPorts atomArguments).map (fun wire => collapse wire) =
          (EqualityNormalization.formalPorts atomArguments).map
            (fun wire => collapse (tailRename wire)) := by
              simpa only [positionalAtomPorts, tailRename] using
                Diagram.vars_map_comp
                  (EqualityNormalization.formalPorts atomArguments)
                  tailRename collapse
      _ = ports := by
        change (EqualityNormalization.formalPorts atomArguments).map
            (fun wire =>
              EqualityNormalization.formalSubstitution ports wire) = ports
        exact EqualityNormalization.formalPorts_map_substitution ports
  change Item.atom (collapse (positionalAtomHead atomArguments))
      ((positionalAtomPorts atomArguments).map fun wire => collapse wire) =
    Item.atom head ports
  rw [show collapse (positionalAtomHead atomArguments) = head by rfl, portsEq]

theorem positionalAtomIncidenceNonempty
    (arguments : List Sig)
    (wire : Var (positionalAtomWires arguments) signature) :
    (Region.singleton (positionalAtomItem arguments)).incidencePaths
      wire.index.val ≠ [] := by
  have boundaryPositive : 0 <
      (EqualityNormalization.formalPorts
        (positionalAtomWires arguments)).countIndex wire.index.val := by
    have positive :=
      (EqualityNormalization.formalPorts (positionalAtomWires arguments))
        |>.countIndex_get_positive wire.index
    rw [EqualityNormalization.formalPorts_get_index] at positive
    exact positive
  rw [← List.length_pos_iff]
  simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
    Item.incidencePaths, List.append_nil, List.length_replicate,
    Var.index_appendLeft, positionalAtomItem, positionalAtomHead]
  let appendNil : WireRenaming (positionalAtomWires arguments)
      (positionalAtomWires arguments ++ []) :=
    ⟨fun selected => selected.appendLeft []⟩
  have portCountEq :
      ((positionalAtomPorts arguments).map
        (fun selected => appendNil selected)).countIndex wire.index.val =
      (positionalAtomPorts arguments).countIndex wire.index.val :=
    Vars.countIndex_map_of_sameIndex (positionalAtomPorts arguments) appendNil
      (fun selected => Var.index_appendLeft selected []) wire.index.val
  rw [show ((positionalAtomPorts arguments).map
      (fun selected => selected.appendLeft [])).countIndex wire.index.val =
        (positionalAtomPorts arguments).countIndex wire.index.val by
    simpa only [appendNil] using portCountEq]
  change 0 <
    (EqualityNormalization.formalPorts
      (positionalAtomWires arguments)).countIndex wire.index.val
  exact boundaryPositive

theorem positionalAtomSupportPins_eq_nil (arguments : List Sig) :
    Erasure.Exposure.supportPins
      (Region.singleton (positionalAtomItem arguments))
      (positionalAtomWires arguments)
      (Erasure.Exposure.identityBoundary (positionalAtomWires arguments)) =
        .nil := by
  apply EqualityNormalization.supportPins_eq_nil
  intro position
  exact positionalAtomIncidenceNonempty arguments
    ((Erasure.Exposure.identityBoundary
      (positionalAtomWires arguments)).get position)

theorem positionalAtomSupportPattern_eq (arguments : List Sig) :
    Erasure.Exposure.supportPattern
      (Region.singleton (positionalAtomItem arguments))
      (positionalAtomCanonical arguments) =
        positionalAtomPattern arguments := by
  apply EqualityNormalization.OpenDiagram.eq_of_data
  · rfl
  · rfl
  · exact heq_of_eq
      (EqualityNormalization.supportBody_eq_of_supportPins_nil _
        (positionalAtomSupportPins_eq_nil arguments))

theorem selectedAtomIncidencePaths_length
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments)
    (wire : Var wires signature) :
    ((Region.singleton (.atom head ports)).incidencePaths
      wire.index.val).length =
        (Vars.cons head ports).countIndex wire.index.val := by
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun selected => selected.appendLeft []⟩
  have portsCountEq :
      (ports.map (fun selected => appendNil selected)).countIndex
          wire.index.val =
        ports.countIndex wire.index.val :=
    Vars.countIndex_map_of_sameIndex ports appendNil
      (fun selected => Var.index_appendLeft selected []) wire.index.val
  simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
    ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
    Item.incidencePaths, List.append_nil, List.length_replicate,
    Var.index_appendLeft, Vars.countIndex]
  exact congrArg
    (fun count =>
      (if head.index.val = wire.index.val then 1 else 0) + count)
    portsCountEq

theorem positionalAtomInstantiation_scope
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) :
    ScopePreservation
      (Region.singleton (.atom head ports))
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons head ports)) := by
  constructor
  · intro _
    exact
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        (positionalAtomPattern atomArguments) (.cons head ports)
  · intro signature wire
    rw [← List.length_pos_iff, selectedAtomIncidencePaths_length]
    exact (EqualityNormalization.instantiate_incidence_nonempty_iff
      (positionalAtomPattern atomArguments) (.cons head ports) wire).symm
  · intro signature wire sourceRoot
    rw [EqualityNormalization.instantiate_rootedTwo_iff]
    have lengthBound := sourceRoot.1
    rw [selectedAtomIncidencePaths_length] at lengthBound
    exact lengthBound

def atomBodyWire
    (pattern : OpenDiagram patternArguments)
    (common : List Sig) :
    WireRenaming pattern.external
      (common ++ EqualityNormalization.locals pattern) :=
  let appendBody : WireRenaming pattern.external
      (pattern.external ++ pattern.body.locals) :=
    ⟨fun wire => wire.appendLeft pattern.body.locals⟩
  WireRenaming.comp
    (EqualityNormalization.bodyEmbedding pattern common) appendBody

theorem atomBodyWire_natural
    (pattern : OpenDiagram patternArguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp
        (rename.appendRight (EqualityNormalization.locals pattern))
        (atomBodyWire pattern sourceWires) =
      atomBodyWire pattern targetWires := by
  apply WireRenaming.ext
  intro signature wire
  let appendBody : WireRenaming pattern.external
      (pattern.external ++ pattern.body.locals) :=
    ⟨fun bodyWire => bodyWire.appendLeft pattern.body.locals⟩
  have natural := congrArg
    (fun embedding : WireRenaming
        (pattern.external ++ pattern.body.locals)
        (targetWires ++ EqualityNormalization.locals pattern) =>
      embedding (appendBody wire))
    (EqualityNormalization.bodyEmbedding_natural pattern rename)
  simpa only [atomBodyWire, appendBody, WireRenaming.comp] using natural

def atomSiteHostItems
    (pattern : OpenDiagram patternArguments)
    (tail : ItemSeq pattern.external)
    (application : Vars common patternArguments) :
    ItemSeq (common ++ EqualityNormalization.locals pattern) :=
  (tail.renameWires (atomBodyWire pattern common)).append
    (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      (application.map fun wire =>
        EqualityNormalization.actualEmbedding pattern common wire)
      (pattern.boundaryWire.map fun wire =>
        EqualityNormalization.patternEmbedding pattern common wire))

theorem atomSiteHostItems_renameWires
    (pattern : OpenDiagram patternArguments)
    (tail : ItemSeq pattern.external)
    (application : Vars sourceWires patternArguments)
    (rename : WireRenaming sourceWires targetWires) :
    (atomSiteHostItems pattern tail application).renameWires
        (rename.appendRight (EqualityNormalization.locals pattern)) =
      atomSiteHostItems pattern tail
        (application.map fun wire => rename wire) := by
  have actualMap :
      (application.map fun wire =>
          EqualityNormalization.actualEmbedding pattern sourceWires wire).map
            (fun wire =>
              rename.appendRight (EqualityNormalization.locals pattern) wire) =
        (application.map fun wire => rename wire).map
          (fun wire =>
            EqualityNormalization.actualEmbedding pattern targetWires wire) := by
    calc
      _ = application.map (fun wire =>
          rename.appendRight (EqualityNormalization.locals pattern)
            (EqualityNormalization.actualEmbedding pattern sourceWires
              wire)) :=
        Diagram.vars_map_comp application
          (EqualityNormalization.actualEmbedding pattern sourceWires)
          (rename.appendRight (EqualityNormalization.locals pattern))
      _ = application.map (fun wire =>
          EqualityNormalization.actualEmbedding pattern targetWires
            (rename wire)) := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming sourceWires
              (targetWires ++ EqualityNormalization.locals pattern) =>
            application.map fun wire => map wire)
          (EqualityNormalization.actualEmbedding_natural pattern rename)
      _ = _ := (Diagram.vars_map_comp application rename
        (EqualityNormalization.actualEmbedding pattern targetWires)).symm
  have patternMap :
      (pattern.boundaryWire.map fun wire =>
          EqualityNormalization.patternEmbedding pattern sourceWires wire).map
            (fun wire =>
              rename.appendRight (EqualityNormalization.locals pattern) wire) =
        pattern.boundaryWire.map (fun wire =>
          EqualityNormalization.patternEmbedding pattern targetWires wire) := by
    calc
      _ = pattern.boundaryWire.map (fun wire =>
          rename.appendRight (EqualityNormalization.locals pattern)
            (EqualityNormalization.patternEmbedding pattern sourceWires
              wire)) :=
        Diagram.vars_map_comp pattern.boundaryWire
          (EqualityNormalization.patternEmbedding pattern sourceWires)
          (rename.appendRight (EqualityNormalization.locals pattern))
      _ = _ := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming pattern.external
              (targetWires ++ EqualityNormalization.locals pattern) =>
            pattern.boundaryWire.map fun wire => map wire)
          (EqualityNormalization.patternEmbedding_natural pattern rename)
  unfold atomSiteHostItems
  rw [ItemSeq.renameWires_append, ItemSeq.renameWires_comp,
    atomBodyWire_natural pattern rename,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires,
    actualMap, patternMap]

theorem atomInstantiationItems_eq
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    (application : Vars common patternArguments) :
    EqualityNormalization.items pattern application =
      .cons
        (.atom (atomBodyWire pattern common head)
          (ports.map fun wire => atomBodyWire pattern common wire))
        (atomSiteHostItems pattern tail application) := by
  let appendBody : WireRenaming pattern.external
      (pattern.external ++ pattern.body.locals) :=
    ⟨fun wire => wire.appendLeft pattern.body.locals⟩
  let embedding := EqualityNormalization.bodyEmbedding pattern common
  have headEq : embedding (appendBody head) = atomBodyWire pattern common head :=
    rfl
  have portsEq :
      (ports.map fun wire => appendBody wire).map
          (fun wire => embedding wire) =
        ports.map (fun wire => atomBodyWire pattern common wire) := by
    simpa only [embedding, appendBody, atomBodyWire, WireRenaming.comp] using
      Diagram.vars_map_comp ports appendBody embedding
  have tailEq :
      (tail.renameWires appendBody).renameWires embedding =
        tail.renameWires (atomBodyWire pattern common) := by
    simpa only [embedding, appendBody, atomBodyWire] using
      ItemSeq.renameWires_comp tail appendBody embedding
  have bodyItems : pattern.body.items =
      (ItemSeq.cons (.atom head ports) tail).renameWires appendBody := by
    simp only [appendBody]
    rw [body_eq]
    rfl
  simp only [EqualityNormalization.items]
  rw [bodyItems]
  simp only [ItemSeq.renameWires, Item.renameWires]
  rw [headEq, portsEq, tailEq]
  rfl

theorem atomInstantiation_eq
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    (application : Vars common patternArguments) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application =
      Region.mk (EqualityNormalization.locals pattern)
        (.cons
          (.atom (atomBodyWire pattern common head)
            (ports.map fun wire => atomBodyWire pattern common wire))
          (atomSiteHostItems pattern tail application)) := by
  rw [EqualityNormalization.instantiate_eq_presentation,
    atomInstantiationItems_eq body_eq application]

theorem identityInstantiationItems_eq
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternArguments}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    (application : Vars common patternArguments) :
    EqualityNormalization.items pattern application =
      .cons
        (.identity signature arity
          (fun position => atomBodyWire pattern common (ports position)))
        (atomSiteHostItems pattern tail application) := by
  let appendBody : WireRenaming pattern.external
      (pattern.external ++ pattern.body.locals) :=
    ⟨fun wire => wire.appendLeft pattern.body.locals⟩
  let embedding := EqualityNormalization.bodyEmbedding pattern common
  have portsEq : (fun position => embedding (appendBody (ports position))) =
      fun position => atomBodyWire pattern common (ports position) := by
    funext position
    rfl
  have tailEq :
      (tail.renameWires appendBody).renameWires embedding =
        tail.renameWires (atomBodyWire pattern common) := by
    simpa only [embedding, appendBody, atomBodyWire] using
      ItemSeq.renameWires_comp tail appendBody embedding
  have bodyItems : pattern.body.items =
      (ItemSeq.cons (.identity signature arity ports) tail).renameWires
        appendBody := by
    simp only [appendBody]
    rw [body_eq]
    rfl
  simp only [EqualityNormalization.items]
  rw [bodyItems]
  simp only [ItemSeq.renameWires, Item.renameWires]
  rw [portsEq, tailEq]
  rfl

theorem identityInstantiation_eq
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternArguments}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    (application : Vars common patternArguments) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application =
      Region.mk (EqualityNormalization.locals pattern)
        (.cons
          (.identity signature arity
            (fun position => atomBodyWire pattern common (ports position)))
          (atomSiteHostItems pattern tail application)) := by
  rw [EqualityNormalization.instantiate_eq_presentation,
    identityInstantiationItems_eq body_eq application]

noncomputable def identitySelectedSourceIso
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternArguments}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    (application : Vars common patternArguments) :
    let retained : Vars
        (common ++ EqualityNormalization.locals pattern)
        (List.replicate arity signature) :=
      Leaf.Identity.Vars.fromFn
        (fun position => atomBodyWire pattern common (ports position))
    RegionIso (WireEquiv.refl common)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application)
      (Region.adjoinAt (EqualityNormalization.locals pattern)
        (atomSiteHostItems pattern tail application)
        (positionalIdentityApplication signature arity retained)) := by
  dsimp only
  let selected : Item
      (common ++ EqualityNormalization.locals pattern) :=
    .identity signature arity
      (fun position => atomBodyWire pattern common (ports position))
  let direct := positionalIdentityApplication signature arity
    (Leaf.Identity.Vars.fromFn
      (fun position => atomBodyWire pattern common (ports position)))
  have directEq : direct = Region.singleton selected := by
    unfold direct positionalIdentityApplication selected
    rw [Leaf.Identity.Vars.toFn_fromFn]
  let flattened := RegionIso.adjoinAtSingleton
    (EqualityNormalization.locals pattern)
    (atomSiteHostItems pattern tail application) selected
  let front := RegionIso.appendSingletonFront
    (EqualityNormalization.locals pattern)
    (atomSiteHostItems pattern tail application) selected
  rw [identityInstantiation_eq body_eq application]
  exact ((RegionIso.adjoinAt
    (EqualityNormalization.locals pattern)
    (atomSiteHostItems pattern tail application)
    (RegionIso.ofEq directEq)).trans (flattened.trans front)).symm

theorem atomExposureWires_nonempty
    {pattern : OpenDiagram patternArguments}
    (head : Var pattern.external (.rel atomArguments))
    (common : List Sig) :
    common ++ EqualityNormalization.locals pattern ≠ [] := by
  intro empty
  have localsEmpty : EqualityNormalization.locals pattern = [] :=
    (List.append_eq_nil_iff.mp empty).2
  have externalEmpty : pattern.external = [] := by
    have parts : pattern.external = [] ∧ pattern.body.locals = [] := by
      simpa only [EqualityNormalization.locals, List.append_nil,
        List.append_eq_nil_iff] using localsEmpty
    exact parts.1
  have impossible := head.index.isLt
  have externalLength : pattern.external.length = 0 := by
    exact congrArg List.length externalEmpty
  omega

def atomExposureDescription
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    (tail : ItemSeq pattern.external)
    (application : Vars common patternArguments) :
    Rule.Erasure.Description common where
  materialWires := positionalAtomWires atomArguments
  hostLocals := EqualityNormalization.locals pattern
  hostItems := atomSiteHostItems pattern tail application
  material := Region.singleton (positionalAtomItem atomArguments)
  wireMap := WireRenaming.comp (atomBodyWire pattern common)
    (positionalAtomCollapse head ports)

theorem atomExposureApplicationPorts
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    (tail : ItemSeq pattern.external)
    (application : Vars common patternArguments) :
    Erasure.Exposure.applicationPorts
        (atomExposureDescription (head := head) (ports := ports)
          tail application) =
      .cons (atomBodyWire pattern common head)
        (ports.map fun wire => atomBodyWire pattern common wire) := by
  change (Erasure.Exposure.identityBoundary
      (positionalAtomWires atomArguments)).map
        (fun wire =>
          atomBodyWire pattern common
            (positionalAtomCollapse head ports wire)) = _
  rw [← EqualityNormalization.formalPorts_eq_exposure]
  rw [← Diagram.vars_map_comp
    (EqualityNormalization.formalPorts (positionalAtomWires atomArguments))
    (positionalAtomCollapse head ports) (atomBodyWire pattern common)]
  rw [show (EqualityNormalization.formalPorts
      (positionalAtomWires atomArguments)).map
        (fun wire => positionalAtomCollapse head ports wire) =
      positionalAtomSelection head ports by
    exact EqualityNormalization.formalPorts_map_substitution
      (positionalAtomSelection head ports)]
  rfl

theorem singleton_conjoin_ofItems
    (item : Item wires) (tail : ItemSeq wires) :
    (Region.singleton item).conjoin (Region.ofItems tail) =
      Region.ofItems (.cons item tail) := by
  rw [show Region.singleton item = Region.ofItems (.cons item .nil) by rfl,
    Region.ofItems_conjoin]
  rfl

mutual
  theorem retainedRegionPresentation_renameWires
      (region : Region sourceWires)
      (rename : WireRenaming sourceWires targetWires) :
      (retainedRegionPresentation region).renameWires rename =
        retainedRegionPresentation (region.renameWires rename) := by
    cases region with
    | mk locals items =>
        unfold retainedRegionPresentation
        rw [Region.renameWires_adjoinAt_nil]
        exact congrArg (Region.adjoinAt locals .nil)
          (retainedItemsPresentation_renameWires items
            (rename.appendRight locals))
  termination_by sizeOf region

  theorem retainedItemsPresentation_renameWires
      (items : ItemSeq sourceWires)
      (rename : WireRenaming sourceWires targetWires) :
      (retainedItemsPresentation items).renameWires rename =
        retainedItemsPresentation (items.renameWires rename) := by
    cases items with
    | nil => rfl
    | cons item tail =>
        unfold retainedItemsPresentation
        rw [Region.renameWires_conjoin,
          retainedItemPresentation_renameWires item rename,
          retainedItemsPresentation_renameWires tail rename]
        rfl
  termination_by sizeOf items

  theorem retainedItemPresentation_renameWires
      (item : Item sourceWires)
      (rename : WireRenaming sourceWires targetWires) :
      (retainedItemPresentation item).renameWires rename =
        retainedItemPresentation (item.renameWires rename) := by
    cases item with
    | atom head ports =>
        unfold retainedItemPresentation
        rw [Region.singleton_renameWires]
        rfl
    | identity signature arity ports =>
        unfold retainedItemPresentation
        rw [Region.singleton_renameWires]
        rfl
    | cut body =>
        unfold retainedItemPresentation
        rw [Region.singleton_renameWires]
        exact congrArg (fun child => Region.singleton (.cut child))
          (retainedRegionPresentation_renameWires body rename)
  termination_by sizeOf item
end

mutual
  theorem retainedRegionResult
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (region : Region common) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult pattern
        frame.sourceKeep frame.selected
        (region.renameWires frame.sourceKeep)
        (retainedRegionPresentation region) := by
    cases region with
    | mk locals items =>
        simp only [Region.renameWires]
        have sourceKeepEq :
            (frame.append locals).sourceKeep =
              frame.sourceKeep.appendRight locals := by
          rfl
        rw [← sourceKeepEq]
        exact
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            (retainedItemsResult pattern (frame.append locals) items)
  termination_by sizeOf region

  theorem retainedItemsResult
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (items : ItemSeq common) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        frame.sourceKeep frame.selected
        (items.renameWires frame.sourceKeep)
        (retainedItemsPresentation items) := by
    cases items with
    | nil =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
    | cons item tail =>
        exact
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            (retainedItemResult pattern frame item)
            (retainedItemsResult pattern frame tail)
  termination_by sizeOf items

  theorem retainedItemResult
      (pattern : OpenDiagram arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (item : Item common) :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult pattern
        frame.sourceKeep frame.selected
        (item.renameWires frame.sourceKeep)
        (retainedItemPresentation item) := by
    cases item with
    | atom head ports =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
          head ports
    | identity signature arity ports =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
          signature arity ports
    | cut body =>
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
          (retainedRegionResult pattern frame body)
  termination_by sizeOf item
end

mutual
  def retainedRegionSites
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (region : Region common) :
      RegionSites operation data
        (retainedRegionResult pattern frame region) :=
    match region with
    | .mk locals items =>
        .mk (retainedItemsSites pattern operation (frame.append locals)
          (operation.appendData frame data locals) items)
  termination_by sizeOf region

  def retainedItemsSites
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (items : ItemSeq common) :
      ItemsSites operation data
        (retainedItemsResult pattern frame items) :=
    match items with
    | .nil => .nil _
    | .cons item tail =>
        .cons (retainedItemSites pattern operation frame data item)
          (retainedItemsSites pattern operation frame data tail)
  termination_by sizeOf items

  def retainedItemSites
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (item : Item common) :
      ItemSites operation data (retainedItemResult pattern frame item) :=
    match item with
    | .atom head ports =>
        ItemSites.atom (pattern := pattern) (frame := frame) head ports
    | .identity signature arity ports =>
        ItemSites.identity (pattern := pattern) (frame := frame)
          signature arity ports
    | .cut body =>
        ItemSites.cut (pattern := pattern) (frame := frame)
          (retainedRegionSites pattern operation frame data body)
  termination_by sizeOf item

end

mutual
  theorem retainedRegionSites_argumentRegionEdit_source
      (pattern : OpenDiagram arguments)
      (recordedOperation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : recordedOperation.Data frame)
      (region : Region common)
      (current : Vars external arguments) :
      (argumentRegionEdit
        (retainedRegionSites pattern
          (recordingOperation recordedOperation external) frame data region)
        current (normalizationOperation arguments) frame PUnit.unit
        (fun _ _ _ => PUnit.unit)).1 =
          region.renameWires frame.sourceKeep := by
    cases region with
    | mk locals items =>
        unfold retainedRegionSites argumentRegionEdit Region.renameWires
        exact congrArg (Region.mk locals)
          (retainedItemsSites_argumentItemsEdit_source pattern
            recordedOperation (frame.append locals)
            (recordedOperation.appendData frame data locals) items current)
  termination_by sizeOf region

  theorem retainedItemsSites_argumentItemsEdit_source
      (pattern : OpenDiagram arguments)
      (recordedOperation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : recordedOperation.Data frame)
      (items : ItemSeq common)
      (current : Vars external arguments) :
      (argumentItemsEdit
        (retainedItemsSites pattern
          (recordingOperation recordedOperation external) frame data items)
        current (normalizationOperation arguments) frame PUnit.unit
        (fun _ _ _ => PUnit.unit)).1 =
          items.renameWires frame.sourceKeep := by
    cases items with
    | nil =>
        unfold retainedItemsSites argumentItemsEdit ItemSeq.renameWires
        rfl
    | cons item tail =>
        unfold retainedItemsSites argumentItemsEdit ItemSeq.renameWires
        dsimp only
        rw [retainedItemSites_argumentItemEdit_source pattern
            recordedOperation frame data item current,
          retainedItemsSites_argumentItemsEdit_source pattern
            recordedOperation frame data tail current]
  termination_by sizeOf items

  theorem retainedItemSites_argumentItemEdit_source
      (pattern : OpenDiagram arguments)
      (recordedOperation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : recordedOperation.Data frame)
      (item : Item common)
      (current : Vars external arguments) :
      (argumentItemEdit
        (retainedItemSites pattern
          (recordingOperation recordedOperation external) frame data item)
        current (normalizationOperation arguments) frame PUnit.unit
        (fun _ _ _ => PUnit.unit)).1 =
          item.renameWires frame.sourceKeep := by
    cases item with
    | atom head ports =>
        unfold retainedItemSites argumentItemEdit Item.renameWires
        rfl
    | identity signature arity ports =>
        unfold retainedItemSites argumentItemEdit Item.renameWires
        rfl
    | cut body =>
        unfold retainedItemSites argumentItemEdit Item.renameWires
        exact congrArg Item.cut
          (retainedRegionSites_argumentRegionEdit_source pattern
            recordedOperation frame data body current)
  termination_by sizeOf item
end

def atomFormalPrefixSource
    (frame : Transform.Frame (positionalAtomWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) : ItemSeq sourceWires :=
  (hostItems.renameWires frame.sourceKeep).append
    (.cons (.atom frame.selected
      ((Vars.cons formal retained).map fun wire => frame.sourceKeep wire)) .nil)

def atomFormalPrefixResult
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) : Region common :=
  match hostItems with
  | .nil =>
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained)).conjoin
        (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (atomFormalPrefixResult tail formal retained)

theorem atomFormalPrefixResult_renameWires
    (hostItems : ItemSeq sourceWires)
    (formal : Var sourceWires (.rel atomArguments))
    (retained : Vars sourceWires atomArguments)
    (rename : WireRenaming sourceWires targetWires) :
    (atomFormalPrefixResult hostItems formal retained).renameWires rename =
      atomFormalPrefixResult (hostItems.renameWires rename) (rename formal)
        (retained.map fun wire => rename wire) := by
  cases hostItems with
  | nil =>
      unfold atomFormalPrefixResult
      rw [Region.renameWires_conjoin,
        EqualityNormalization.instantiate_renameWires]
      rfl
  | cons item tail =>
      unfold atomFormalPrefixResult
      rw [Region.renameWires_conjoin,
        retainedItemPresentation_renameWires item rename,
        atomFormalPrefixResult_renameWires tail formal retained rename]
      rfl
termination_by sizeOf hostItems

def atomFormalPrefixEvidence
    (frame : Transform.Frame (positionalAtomWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      (positionalAtomPattern atomArguments) frame.sourceKeep frame.selected
      (atomFormalPrefixSource frame hostItems formal retained)
      (atomFormalPrefixResult hostItems formal retained) := by
  cases hostItems with
  | nil =>
      exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (.cons formal retained))
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
  | cons item tail =>
      simp only [atomFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, atomFormalPrefixResult]
      change _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (positionalAtomPattern atomArguments) frame.sourceKeep frame.selected
        (.cons (item.renameWires frame.sourceKeep)
          (atomFormalPrefixSource frame tail formal retained))
        ((retainedItemPresentation item).conjoin
          (atomFormalPrefixResult tail formal retained))
      exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (retainedItemResult (positionalAtomPattern atomArguments) frame item)
        (atomFormalPrefixEvidence frame tail formal retained)
  termination_by sizeOf hostItems

def atomFormalPrefixSites
    (frame : Transform.Frame (positionalAtomWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    ItemsSites (Leaf.Formal.operation [] atomArguments) PUnit.unit
      (atomFormalPrefixEvidence frame hostItems formal retained) :=
  match hostItems with
  | .nil =>
      let siteData :
          (Leaf.Formal.operation [] atomArguments).SiteData frame PUnit.unit
            (.cons formal retained) :=
        ⟨formal, ⟨retained, rfl⟩⟩
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (positionalAtomPattern atomArguments) frame.sourceKeep
            frame.selected .nil (Region.blank common) :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom
          (pattern := positionalAtomPattern atomArguments)
          (frame := frame) (.cons formal retained) siteData)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites (positionalAtomPattern atomArguments)
          (Leaf.Formal.operation [] atomArguments) frame PUnit.unit item)
        (atomFormalPrefixSites frame tail formal retained)
  termination_by sizeOf hostItems

/-- The atom-formal prefix traversal with the authoritative comprehension
application recorded at its unique selected site. -/
def atomFormalPrefixRecordingSites
    (frame : Transform.Frame (positionalAtomWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments)
    (application : Vars common patternArguments) :
    ItemsSites
      (recordingOperation (Leaf.Formal.operation [] atomArguments)
        patternArguments)
      PUnit.unit
      (atomFormalPrefixEvidence frame hostItems formal retained) :=
  match hostItems with
  | .nil =>
      let formalSite :
          (Leaf.Formal.operation [] atomArguments).SiteData frame PUnit.unit
            (.cons formal retained) :=
        ⟨formal, ⟨retained, rfl⟩⟩
      let siteData := ⟨formalSite, application⟩
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (positionalAtomPattern atomArguments) frame.sourceKeep
            frame.selected .nil (Region.blank common) :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom
          (pattern := positionalAtomPattern atomArguments)
          (frame := frame) (.cons formal retained) siteData)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites (positionalAtomPattern atomArguments)
          (recordingOperation (Leaf.Formal.operation [] atomArguments)
            patternArguments)
          frame PUnit.unit item)
        (atomFormalPrefixRecordingSites frame tail formal retained application)
  termination_by sizeOf hostItems

theorem atomFormalPrefixSource_eq_argumentItemsEdit
    (frame : Transform.Frame (positionalAtomWires atomArguments)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments)
    (application : Vars common patternArguments)
    (values : Vars patternArguments (positionalAtomWires atomArguments))
    (rename : WireRenaming patternArguments common)
    (applicationEq : application =
      (EqualityNormalization.formalPorts patternArguments).map
        fun wire => rename wire)
    (valuesEq : values.map (fun wire => rename wire) =
      .cons formal retained) :
    atomFormalPrefixSource frame hostItems formal retained =
      (argumentItemsEdit
        (atomFormalPrefixRecordingSites frame hostItems formal retained
          application)
        values (normalizationOperation (positionalAtomWires atomArguments))
        frame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
  cases hostItems with
  | nil =>
      simp only [atomFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, atomFormalPrefixRecordingSites, argumentItemsEdit,
        argumentItemEdit]
      rw [applicationEq]
      have substitutionEq : values.map (fun wire =>
            EqualityNormalization.formalSubstitution
            ((EqualityNormalization.formalPorts patternArguments).map
              fun formalWire => rename formalWire) wire) =
          values.map (fun wire => rename wire) := by
        apply Vars.map_congr
        intro signature wire
        exact EqualityNormalization.formalSubstitution_formalPorts_map
          rename wire
      rw [substitutionEq, valuesEq]
  | cons item tail =>
      simp only [atomFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, atomFormalPrefixRecordingSites, argumentItemsEdit,
        argumentItemEdit]
      congr 1
      · exact (retainedItemSites_argumentItemEdit_source
          (positionalAtomPattern atomArguments)
          (Leaf.Formal.operation [] atomArguments) frame PUnit.unit item
          values).symm
      · simpa only [atomFormalPrefixSource] using
          atomFormalPrefixSource_eq_argumentItemsEdit frame tail formal retained
            application values rename applicationEq valuesEq
termination_by sizeOf hostItems

def identityFormalPrefixSource
    (frame : Transform.Frame (List.replicate arity signature)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    ItemSeq sourceWires :=
  (hostItems.renameWires frame.sourceKeep).append
    (.cons (.atom frame.selected
      (application.map fun wire => frame.sourceKeep wire)) .nil)

def identityFormalPrefixResult
    (signature : Sig) (arity : Nat)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    Region common :=
  match hostItems with
  | .nil =>
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) application).conjoin
        (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (identityFormalPrefixResult signature arity tail application)

theorem identityFormalPrefixResult_renameWires
    (signature : Sig) (arity : Nat)
    (hostItems : ItemSeq sourceWires)
    (application : Vars sourceWires (List.replicate arity signature))
    (rename : WireRenaming sourceWires targetWires) :
    (identityFormalPrefixResult signature arity hostItems application).renameWires
        rename =
      identityFormalPrefixResult signature arity
        (hostItems.renameWires rename)
        (application.map fun wire => rename wire) := by
  cases hostItems with
  | nil =>
      unfold identityFormalPrefixResult
      rw [Region.renameWires_conjoin,
        EqualityNormalization.instantiate_renameWires]
      rfl
  | cons item tail =>
      unfold identityFormalPrefixResult
      rw [Region.renameWires_conjoin,
        retainedItemPresentation_renameWires item rename,
        identityFormalPrefixResult_renameWires signature arity tail
          application rename]
      rfl
termination_by sizeOf hostItems

def identityFormalPrefixEvidence
    (frame : Transform.Frame (List.replicate arity signature)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
      (positionalIdentityPattern signature arity)
      frame.sourceKeep frame.selected
      (identityFormalPrefixSource frame hostItems application)
      (identityFormalPrefixResult signature arity hostItems application) := by
  cases hostItems with
  | nil =>
      exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          application)
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
  | cons item tail =>
      simp only [identityFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, identityFormalPrefixResult]
      change _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (positionalIdentityPattern signature arity) frame.sourceKeep
        frame.selected
        (.cons (item.renameWires frame.sourceKeep)
          (identityFormalPrefixSource frame tail application))
        ((retainedItemPresentation item).conjoin
          (identityFormalPrefixResult signature arity tail application))
      exact _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
        (retainedItemResult (positionalIdentityPattern signature arity)
          frame item)
        (identityFormalPrefixEvidence frame tail application)
termination_by sizeOf hostItems

def identityFormalPrefixSites
    (frame : Transform.Frame (List.replicate arity signature)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    ItemsSites (Leaf.Identity.operation signature arity) PUnit.unit
      (identityFormalPrefixEvidence frame hostItems application) :=
  match hostItems with
  | .nil =>
      let identityPorts := Leaf.Identity.Vars.toFn application
      let identityPortsEq : application =
          Leaf.Identity.Vars.fromFn identityPorts :=
        (Leaf.Identity.Vars.fromFn_toFn application).symm
      let siteData :
          (Leaf.Identity.operation signature arity).SiteData
            frame PUnit.unit application :=
        ⟨identityPorts, identityPortsEq⟩
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (positionalIdentityPattern signature arity) frame.sourceKeep
            frame.selected .nil (Region.blank common) :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom
          (pattern := positionalIdentityPattern signature arity)
          (frame := frame) application siteData)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites (positionalIdentityPattern signature arity)
          (Leaf.Identity.operation signature arity) frame PUnit.unit item)
        (identityFormalPrefixSites frame tail application)
termination_by sizeOf hostItems

def identityFormalPrefixRecordingSites
    (frame : Transform.Frame (List.replicate arity signature)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (retained : Vars common (List.replicate arity signature))
    (application : Vars common patternArguments) :
    ItemsSites
      (recordingOperation (Leaf.Identity.operation signature arity)
        patternArguments)
      PUnit.unit
      (identityFormalPrefixEvidence frame hostItems retained) :=
  match hostItems with
  | .nil =>
      let identityPorts := Leaf.Identity.Vars.toFn retained
      let identityPortsEq : retained =
          Leaf.Identity.Vars.fromFn identityPorts :=
        (Leaf.Identity.Vars.fromFn_toFn retained).symm
      let identitySite :
          (Leaf.Identity.operation signature arity).SiteData
            frame PUnit.unit retained :=
        ⟨identityPorts, identityPortsEq⟩
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (positionalIdentityPattern signature arity) frame.sourceKeep
            frame.selected .nil (Region.blank common) :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
      ItemsSites.cons
        (ItemSites.selectedAtom
          (pattern := positionalIdentityPattern signature arity)
          (frame := frame) retained ⟨identitySite, application⟩)
        (ItemsSites.nil tailEvidence)
  | .cons item tail =>
      ItemsSites.cons
        (retainedItemSites (positionalIdentityPattern signature arity)
          (recordingOperation (Leaf.Identity.operation signature arity)
            patternArguments)
          frame PUnit.unit item)
        (identityFormalPrefixRecordingSites frame tail retained application)
termination_by sizeOf hostItems

theorem identityFormalPrefixSource_eq_argumentItemsEdit
    (frame : Transform.Frame (List.replicate arity signature)
      common sourceWires targetWires)
    (hostItems : ItemSeq common)
    (retained : Vars common (List.replicate arity signature))
    (application : Vars common patternArguments)
    (values : Vars patternArguments (List.replicate arity signature))
    (rename : WireRenaming patternArguments common)
    (applicationEq : application =
      (EqualityNormalization.formalPorts patternArguments).map
        fun wire => rename wire)
    (valuesEq : values.map (fun wire => rename wire) = retained) :
    identityFormalPrefixSource frame hostItems retained =
      (argumentItemsEdit
        (identityFormalPrefixRecordingSites frame hostItems retained
          application)
        values
        (normalizationOperation (List.replicate arity signature))
        frame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
  cases hostItems with
  | nil =>
      simp only [identityFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, identityFormalPrefixRecordingSites,
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
      simp only [identityFormalPrefixSource, ItemSeq.renameWires,
        ItemSeq.append, identityFormalPrefixRecordingSites,
        argumentItemsEdit, argumentItemEdit]
      congr 1
      · exact (retainedItemSites_argumentItemEdit_source
          (positionalIdentityPattern signature arity)
          (Leaf.Identity.operation signature arity) frame PUnit.unit item
          values).symm
      · simpa only [identityFormalPrefixSource] using
          identityFormalPrefixSource_eq_argumentItemsEdit frame tail retained
            application values rename applicationEq valuesEq

theorem atomExposureMaterialRename
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    (tail : ItemSeq pattern.external)
    (application : Vars common patternArguments) :
    (Region.singleton (positionalAtomItem atomArguments)).renameWires
        (atomExposureDescription (head := head) (ports := ports)
          tail application).wireMap =
      Region.singleton
        (.atom (atomBodyWire pattern common head)
          (ports.map fun wire => atomBodyWire pattern common wire)) := by
  change (Region.singleton (positionalAtomItem atomArguments)).renameWires
      (WireRenaming.comp (atomBodyWire pattern common)
        (positionalAtomCollapse head ports)) = _
  rw [← Region.renameWires_comp]
  rw [Region.singleton_renameWires, positionalAtomItem_rename,
    Region.singleton_renameWires]
  rfl

noncomputable def atomExposureSourceIso
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    (application : Vars common patternArguments) :
    RegionIso (WireEquiv.refl common)
      (atomExposureDescription (head := head) (ports := ports)
        tail application).source
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) := by
  let selected : Item
      (common ++ EqualityNormalization.locals pattern) :=
    .atom (atomBodyWire pattern common head)
      (ports.map fun wire => atomBodyWire pattern common wire)
  let materialIso : RegionIso
      (WireEquiv.refl (common ++ EqualityNormalization.locals pattern))
      ((Region.singleton (positionalAtomItem atomArguments)).renameWires
        (atomExposureDescription (head := head) (ports := ports)
          tail application).wireMap)
      (Region.singleton selected) := by
    exact RegionIso.ofEq (atomExposureMaterialRename tail application)
  let adjoined := RegionIso.adjoinAt
    (EqualityNormalization.locals pattern)
    (atomSiteHostItems pattern tail application) materialIso
  let flattened := RegionIso.adjoinAtSingleton
    (EqualityNormalization.locals pattern)
    (atomSiteHostItems pattern tail application) selected
  let front := RegionIso.appendSingletonFront
    (EqualityNormalization.locals pattern)
    (atomSiteHostItems pattern tail application) selected
  rw [atomInstantiation_eq body_eq application]
  let combined := (adjoined.trans flattened).trans front
  simpa only [Rule.Erasure.Description.source, Region.spliceAt,
    atomExposureDescription, selected, WireEquiv.refl_trans] using combined

/-- Merge surrounding sibling syntax into the selected atom exposure host. -/
def atomExposureDescriptionWithHost
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    (tail : ItemSeq pattern.external)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternArguments) :
    Rule.Erasure.Description outer :=
  let inner := atomExposureDescription (head := head) (ports := ports)
    tail application
  let innerHost : Region (outer ++ hostLocals) :=
    .mk inner.hostLocals inner.hostItems
  {
    materialWires := inner.materialWires
    hostLocals := hostLocals ++ inner.hostLocals
    hostItems := Region.extendHostItems hostLocals hostItems innerHost
    material := inner.material
    wireMap := WireRenaming.comp
      (Region.adjoinMaterialWire outer hostLocals inner.hostLocals)
      inner.wireMap
  }

/-- Add the support pins required by the merged selected atom exposure. -/
def atomPinnedExposureDescriptionWithHost
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    (tail : ItemSeq pattern.external)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternArguments) :
    Rule.Erasure.Description outer :=
  let raw := atomExposureDescriptionWithHost
    (head := head) (ports := ports) tail hostLocals hostItems application
  {
    materialWires := raw.materialWires
    hostLocals := raw.hostLocals
    hostItems := raw.hostItems.append
      (EqualityNormalization.contextPins outer raw.hostLocals)
    material := raw.material
    wireMap := raw.wireMap
  }

/-- Flattening the surrounding host commutes with the selected exposure. -/
noncomputable def atomExposureDescriptionWithHostExposedIso
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    (tail : ItemSeq pattern.external)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternArguments) :
    RegionIso (WireEquiv.refl outer)
      (Erasure.Exposure.exposedRegion
        (atomExposureDescriptionWithHost
          (head := head) (ports := ports) tail hostLocals hostItems application)
        (positionalAtomCanonical atomArguments))
      (Region.adjoinAt hostLocals hostItems
        (Erasure.Exposure.exposedRegion
          (atomExposureDescription (head := head) (ports := ports)
            tail application)
          (positionalAtomCanonical atomArguments))) := by
  let inner := atomExposureDescription (head := head) (ports := ports)
    tail application
  let combined := atomExposureDescriptionWithHost
    (head := head) (ports := ports) tail hostLocals hostItems application
  let innerMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (Erasure.Exposure.supportPattern inner.material
        (positionalAtomCanonical atomArguments))
      (Erasure.Exposure.applicationPorts inner)
  let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
    inner.hostLocals
  have applicationPortsEq :
      Erasure.Exposure.applicationPorts combined =
        (Erasure.Exposure.applicationPorts inner).map
          (fun wire => assoc wire) := by
    simp only [combined, inner, assoc, Erasure.Exposure.applicationPorts,
      atomExposureDescriptionWithHost, atomExposureDescription]
    exact (Diagram.vars_map_comp
      (Erasure.Exposure.identityBoundary (positionalAtomWires atomArguments))
      ((atomBodyWire pattern (outer ++ hostLocals)).comp
        (positionalAtomCollapse head ports))
      (Region.adjoinMaterialWire outer hostLocals
        (EqualityNormalization.locals pattern))).symm
  have materialEq :
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern combined.material
            (positionalAtomCanonical atomArguments))
          (Erasure.Exposure.applicationPorts combined) =
        innerMaterial.renameWires assoc.toRenaming := by
    rw [EqualityNormalization.instantiate_renameWires, applicationPortsEq]
    rfl
  let flat := Region.adjoinAt (hostLocals ++ inner.hostLocals)
    (Region.extendHostItems hostLocals hostItems
      (.mk inner.hostLocals inner.hostItems))
    (innerMaterial.renameWires assoc.toRenaming)
  let nested := Region.adjoinAt hostLocals hostItems
    (Region.adjoinAt inner.hostLocals inner.hostItems innerMaterial)
  let associated := RegionIso.adjoinAtAssoc hostLocals hostItems
    inner.hostLocals inner.hostItems innerMaterial
  have combinedEq :
      Erasure.Exposure.exposedRegion combined
          (positionalAtomCanonical atomArguments) = flat := by
    change Region.adjoinAt combined.hostLocals combined.hostItems
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern combined.material
          (positionalAtomCanonical atomArguments))
        (Erasure.Exposure.applicationPorts combined)) = flat
    rw [materialEq]
    rfl
  have nestedEq : nested = Region.adjoinAt hostLocals hostItems
      (Erasure.Exposure.exposedRegion inner
        (positionalAtomCanonical atomArguments)) := by
    rfl
  exact (RegionIso.ofEq combinedEq).trans
    (associated.trans (RegionIso.ofEq nestedEq))

/-- The merged exposure source presents the exact hosted instantiation. -/
noncomputable def atomExposureDescriptionWithHostSourceIso
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternArguments) :
    RegionIso (WireEquiv.refl outer)
      (atomExposureDescriptionWithHost
        (head := head) (ports := ports) tail hostLocals hostItems application).source
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)) := by
  let inner := atomExposureDescription (head := head) (ports := ports)
    tail application
  let combined := atomExposureDescriptionWithHost
    (head := head) (ports := ports) tail hostLocals hostItems application
  let innerMaterial := inner.material.renameWires inner.wireMap
  let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals inner.hostLocals
  let materialPresentation :=
    (RegionIso.renameWiresComp inner.material inner.wireMap
      assoc.toRenaming).symm
  let flatPresentation := RegionIso.adjoinAt
    (hostLocals ++ inner.hostLocals)
    (Region.extendHostItems hostLocals hostItems
      (.mk inner.hostLocals inner.hostItems)) materialPresentation
  let associated := RegionIso.adjoinAtAssoc hostLocals hostItems
    inner.hostLocals inner.hostItems innerMaterial
  let sourcePresentation := (flatPresentation.trans associated).trans
    (RegionIso.adjoinAt hostLocals hostItems
      (atomExposureSourceIso body_eq application))
  simpa only [combined, inner, innerMaterial, assoc,
    atomExposureDescriptionWithHost, Rule.Erasure.Description.source,
    Region.spliceAt, WireEquiv.adjoinMaterialAssoc] using sourcePresentation

noncomputable def atomFormalPrefixResultIso
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    RegionIso (WireEquiv.refl common)
      (atomFormalPrefixResult hostItems formal retained)
      ((Region.ofItems hostItems).conjoin
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments)
          (.cons formal retained))) :=
  match hostItems with
  | .nil => by
      let inner :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retained)
      exact (RegionIso.conjoinBlank inner).trans
        (RegionIso.blankConjoin inner).symm
  | .cons item tail => by
      let inner :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retained)
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (atomFormalPrefixResultIso tail formal retained)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) inner).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl inner)
      exact children.trans (associated.trans prefixIso)
  termination_by sizeOf hostItems

noncomputable def atomFormalSelectedResultIso
    {atomArguments : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    (tail : ItemSeq pattern.external)
    (application : Vars common patternArguments) :
    let locals := EqualityNormalization.locals pattern
    let formal : Var (common ++ EqualityNormalization.locals pattern)
        (.rel atomArguments) := atomBodyWire pattern common head
    let retained : Vars
        (common ++ EqualityNormalization.locals pattern) atomArguments :=
      ports.map fun wire => atomBodyWire pattern common wire
    let hostItems : ItemSeq
        (common ++ EqualityNormalization.locals pattern) :=
      atomSiteHostItems pattern tail application
    RegionIso (WireEquiv.refl common)
      (Region.adjoinAt locals .nil
        (atomFormalPrefixResult hostItems formal retained))
      (Region.adjoinAt locals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments)
          (.cons formal retained))) := by
  dsimp only
  let hostItems := atomSiteHostItems pattern tail application
  let formal : Var (common ++ EqualityNormalization.locals pattern)
      (.rel atomArguments) := atomBodyWire pattern common head
  let retained : Vars
      (common ++ EqualityNormalization.locals pattern) atomArguments :=
    ports.map fun wire => atomBodyWire pattern common wire
  let inner :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalAtomPattern atomArguments) (.cons formal retained)
  let prefixIso := RegionIso.adjoinAt
    (EqualityNormalization.locals pattern) .nil
    (atomFormalPrefixResultIso hostItems formal retained)
  let hosted := adjoinAt_hostedMaterial
    (EqualityNormalization.locals pattern) hostItems inner
  exact prefixIso.trans (RegionIso.ofEq hosted.symm)

noncomputable def identityFormalPrefixResultIso
    (signature : Sig) (arity : Nat)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    RegionIso (WireEquiv.refl common)
      (identityFormalPrefixResult signature arity hostItems application)
      ((Region.ofItems hostItems).conjoin
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application)) :=
  match hostItems with
  | .nil => by
      let inner :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application
      exact (RegionIso.conjoinBlank inner).trans
        (RegionIso.blankConjoin inner).symm
  | .cons item tail => by
      let inner :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (identityFormalPrefixResultIso signature arity tail application)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) inner).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl inner)
      exact children.trans (associated.trans prefixIso)
termination_by sizeOf hostItems

noncomputable def identityFormalSelectedResultIso
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternArguments}
    {ports : Fin arity → Var pattern.external signature}
    (tail : ItemSeq pattern.external)
    (application : Vars common patternArguments) :
    let locals := EqualityNormalization.locals pattern
    let retained : Vars
        (common ++ EqualityNormalization.locals pattern)
        (List.replicate arity signature) :=
      Leaf.Identity.Vars.fromFn
        (fun position => atomBodyWire pattern common (ports position))
    let hostItems : ItemSeq
        (common ++ EqualityNormalization.locals pattern) :=
      atomSiteHostItems pattern tail application
    RegionIso (WireEquiv.refl common)
      (Region.adjoinAt locals .nil
        (identityFormalPrefixResult signature arity hostItems retained))
      (Region.adjoinAt locals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) retained)) := by
  dsimp only
  let hostItems := atomSiteHostItems pattern tail application
  let retained : Vars
      (common ++ EqualityNormalization.locals pattern)
      (List.replicate arity signature) :=
    Leaf.Identity.Vars.fromFn
      (fun position => atomBodyWire pattern common (ports position))
  let inner :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) retained
  let prefixIso := RegionIso.adjoinAt
    (EqualityNormalization.locals pattern) .nil
    (identityFormalPrefixResultIso signature arity hostItems retained)
  let hosted := adjoinAt_hostedMaterial
    (EqualityNormalization.locals pattern) hostItems inner
  exact prefixIso.trans (RegionIso.ofEq hosted.symm)

mutual
  theorem retainedRegionEditEndpoint
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (region : Region common) :
      (regionEdit data (retainedRegionResult pattern frame region)
        (retainedRegionSites pattern operation frame data region)).endpoint =
        (retainedRegionPresentation region).renameWires frame.targetKeep := by
    cases region with
    | mk locals items =>
        have childEq := retainedItemsEditEndpoint pattern operation
          (frame.append locals) (operation.appendData frame data locals) items
        unfold retainedRegionSites regionEdit retainedRegionPresentation
        dsimp only
        rw [Region.renameWires_adjoinAt_nil]
        apply congrArg (Region.adjoinAt locals .nil)
        simpa only [Transform.Frame.append] using childEq
  termination_by sizeOf region

  theorem retainedItemsEditEndpoint
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (items : ItemSeq common) :
      (itemsEdit data (retainedItemsResult pattern frame items)
        (retainedItemsSites pattern operation frame data items)).endpoint =
        (retainedItemsPresentation items).renameWires frame.targetKeep := by
    cases items with
    | nil =>
        unfold retainedItemsSites itemsEdit
        rw [← ExactEdit.run_eq]
        rfl
    | cons item tail =>
        have headEq := retainedItemEditEndpoint pattern operation frame data item
        have tailEq := retainedItemsEditEndpoint pattern operation frame data tail
        unfold retainedItemsSites itemsEdit retainedItemsPresentation
        dsimp only
        rw [headEq, tailEq, Region.renameWires_conjoin]
  termination_by sizeOf items

  theorem retainedItemEditEndpoint
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      (operation : Transform.Operation arguments)
      (frame : Transform.Frame arguments common sourceWires targetWires)
      (data : operation.Data frame)
      (item : Item common) :
      (itemEdit data (retainedItemResult pattern frame item)
        (retainedItemSites pattern operation frame data item)).endpoint =
        (retainedItemPresentation item).renameWires frame.targetKeep := by
    cases item with
    | atom head ports =>
        unfold retainedItemSites itemEdit retainedItemPresentation
        rw [← ExactEdit.run_eq]
        unfold ExactEdit.refl
        rw [Region.singleton_renameWires]
        rfl
    | identity signature arity ports =>
        unfold retainedItemSites itemEdit retainedItemPresentation
        rw [← ExactEdit.run_eq]
        unfold ExactEdit.refl
        rw [Region.singleton_renameWires]
        rfl
    | cut body =>
        have childEq := retainedRegionEditEndpoint pattern operation frame data body
        unfold retainedItemSites itemEdit retainedItemPresentation
        dsimp only
        rw [childEq]
        rw [Region.singleton_renameWires]
        rfl
  termination_by sizeOf item
end

theorem formalRootFrame_targetKeep
    (outer locals atomArguments : List Sig) :
    (Leaf.Formal.rootFrame outer [] locals [] atomArguments).targetKeep =
      WireRenaming.id := by
  apply WireRenaming.ext
  intro signature wire
  apply Var.appendCases (left := outer) (right := locals)
    (motive := fun wire =>
      (Leaf.Formal.rootFrame outer [] locals [] atomArguments).targetKeep
          wire =
        WireRenaming.id wire)
  · intro inheritedSignature inherited
    simp [Leaf.Formal.rootFrame, Transform.Frame.replace,
      Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
  · intro localSignature localWire
    simp [Leaf.Formal.rootFrame, Transform.Frame.replace,
      Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
      Var.appendMap, Var.appendRight]

def atomFormalPrefixEndpoint
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) : Region common :=
  match hostItems with
  | .nil =>
      (Region.singleton (.atom formal retained)).conjoin
        (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (atomFormalPrefixEndpoint tail formal retained)

theorem atomFormalPrefixEndpoint_renameWires
    (hostItems : ItemSeq sourceWires)
    (formal : Var sourceWires (.rel atomArguments))
    (retained : Vars sourceWires atomArguments)
    (rename : WireRenaming sourceWires targetWires) :
    (atomFormalPrefixEndpoint hostItems formal retained).renameWires rename =
      atomFormalPrefixEndpoint (hostItems.renameWires rename) (rename formal)
        (retained.map fun wire => rename wire) := by
  cases hostItems with
  | nil =>
      unfold atomFormalPrefixEndpoint
      rw [Region.renameWires_conjoin, Region.singleton_renameWires]
      rfl
  | cons item tail =>
      unfold atomFormalPrefixEndpoint
      rw [Region.renameWires_conjoin,
        retainedItemPresentation_renameWires item rename,
        atomFormalPrefixEndpoint_renameWires tail formal retained rename]
      rfl
termination_by sizeOf hostItems

noncomputable def atomFormalPrefixEndpointIso
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    RegionIso (WireEquiv.refl common)
      (atomFormalPrefixEndpoint hostItems formal retained)
      ((Region.ofItems hostItems).conjoin
        (Region.singleton (.atom formal retained))) :=
  match hostItems with
  | .nil => by
      let direct := Region.singleton (.atom formal retained)
      exact (RegionIso.conjoinBlank direct).trans
        (RegionIso.blankConjoin direct).symm
  | .cons item tail => by
      let direct := Region.singleton (.atom formal retained)
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (atomFormalPrefixEndpointIso tail formal retained)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) direct).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl direct)
      exact children.trans (associated.trans prefixIso)
  termination_by sizeOf hostItems

theorem atomFormalPrefixItemsEditEndpoint
    {common sourceWires targetWires : List Sig} (atomArguments : List Sig)
    (frame : Transform.Frame (positionalAtomWires atomArguments) common
      sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments) :
    (itemsEdit (operation := Leaf.Formal.operation [] atomArguments)
      PUnit.unit
      (atomFormalPrefixEvidence frame hostItems formal retained)
      (atomFormalPrefixSites frame hostItems formal retained)).endpoint =
      (atomFormalPrefixEndpoint hostItems formal retained).renameWires
        frame.targetKeep := by
  cases hostItems with
  | nil =>
      unfold atomFormalPrefixSites
      unfold itemsEdit
      dsimp only
      simp only [itemEdit, ExactEdit.refl, atomFormalPrefixEndpoint,
        Transform.ItemEdit.run, Leaf.Formal.operation]
      unfold itemsEdit ExactEdit.refl Transform.ItemsEdit.run
      rw [Region.renameWires_conjoin]
      simp [Region.renameWires, Region.blank, Region.singleton_renameWires,
        Item.renameWires, ItemSeq.renameWires]
  | cons item tail =>
      have tailEq := atomFormalPrefixItemsEditEndpoint atomArguments frame
        tail formal retained
      have headEq :
          (itemEdit (operation := Leaf.Formal.operation [] atomArguments)
            PUnit.unit
            (retainedItemResult (positionalAtomPattern atomArguments)
              frame item)
            (retainedItemSites (positionalAtomPattern atomArguments)
              (Leaf.Formal.operation [] atomArguments) frame PUnit.unit
              item)).endpoint =
            (retainedItemPresentation item).renameWires
              frame.targetKeep := by
        exact retainedItemEditEndpoint
          (positionalAtomPattern atomArguments)
          (Leaf.Formal.operation [] atomArguments) frame PUnit.unit item
      unfold atomFormalPrefixSites itemsEdit
      dsimp only
      unfold atomFormalPrefixEndpoint
      rw [Region.renameWires_conjoin, headEq]
      exact congrArg
        (fun material =>
          (retainedItemPresentation item).renameWires frame.targetKeep |>.conjoin
            material)
        tailEq
  termination_by sizeOf hostItems

theorem atomFormalPrefixRecordingItemsEditEndpoint
    {common sourceWires targetWires : List Sig}
    (atomArguments patternArguments : List Sig)
    (frame : Transform.Frame (positionalAtomWires atomArguments) common
      sourceWires targetWires)
    (hostItems : ItemSeq common)
    (formal : Var common (.rel atomArguments))
    (retained : Vars common atomArguments)
    (application : Vars common patternArguments) :
    (itemsEdit
      (operation := recordingOperation
        (Leaf.Formal.operation [] atomArguments) patternArguments)
      PUnit.unit
      (atomFormalPrefixEvidence frame hostItems formal retained)
      (atomFormalPrefixRecordingSites frame hostItems formal retained
        application)).endpoint =
      (atomFormalPrefixEndpoint hostItems formal retained).renameWires
        frame.targetKeep := by
  cases hostItems with
  | nil =>
      unfold atomFormalPrefixRecordingSites
      unfold itemsEdit
      dsimp only
      simp only [itemEdit, ExactEdit.refl, atomFormalPrefixEndpoint,
        Transform.ItemEdit.run, recordingOperation,
        Leaf.Formal.operation]
      unfold itemsEdit ExactEdit.refl Transform.ItemsEdit.run
      rw [Region.renameWires_conjoin]
      simp [Region.renameWires, Region.blank, Region.singleton_renameWires,
        Item.renameWires, ItemSeq.renameWires]
  | cons item tail =>
      have tailEq := atomFormalPrefixRecordingItemsEditEndpoint
        atomArguments patternArguments frame tail formal
          retained application
      have headEq :
          (itemEdit
            (operation := recordingOperation
              (Leaf.Formal.operation [] atomArguments) patternArguments)
            PUnit.unit
            (retainedItemResult (positionalAtomPattern atomArguments)
              frame item)
            (retainedItemSites (positionalAtomPattern atomArguments)
              (recordingOperation (Leaf.Formal.operation [] atomArguments)
                patternArguments)
              frame PUnit.unit item)).endpoint =
            (retainedItemPresentation item).renameWires
              frame.targetKeep := by
        exact retainedItemEditEndpoint
          (positionalAtomPattern atomArguments)
          (recordingOperation (Leaf.Formal.operation [] atomArguments)
            patternArguments)
          frame PUnit.unit item
      unfold atomFormalPrefixRecordingSites itemsEdit
      dsimp only
      unfold atomFormalPrefixEndpoint
      rw [Region.renameWires_conjoin, headEq]
      exact congrArg
        (fun material =>
          (retainedItemPresentation item).renameWires frame.targetKeep |>.conjoin
            material)
        tailEq
termination_by sizeOf hostItems

def identityFormalPrefixEndpoint
    (signature : Sig) (arity : Nat)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    Region common :=
  match hostItems with
  | .nil =>
      (positionalIdentityApplication signature arity application).conjoin
        (Region.blank common)
  | .cons item tail =>
      (retainedItemPresentation item).conjoin
        (identityFormalPrefixEndpoint signature arity tail application)

theorem identityFormalPrefixEndpoint_renameWires
    (signature : Sig) (arity : Nat)
    (hostItems : ItemSeq sourceWires)
    (application : Vars sourceWires (List.replicate arity signature))
    (rename : WireRenaming sourceWires targetWires) :
    (identityFormalPrefixEndpoint signature arity hostItems application).renameWires
        rename =
      identityFormalPrefixEndpoint signature arity
        (hostItems.renameWires rename)
        (application.map fun wire => rename wire) := by
  cases hostItems with
  | nil =>
      unfold identityFormalPrefixEndpoint
      rw [Region.renameWires_conjoin]
      simp only [positionalIdentityApplication,
        Region.singleton_renameWires, Item.renameWires,
        Leaf.Identity.Vars.toFn_map, ItemSeq.renameWires]
      rfl
  | cons item tail =>
      unfold identityFormalPrefixEndpoint
      rw [Region.renameWires_conjoin,
        retainedItemPresentation_renameWires item rename,
        identityFormalPrefixEndpoint_renameWires signature arity tail
          application rename]
      rfl

noncomputable def identityFormalPrefixEndpointIso
    (signature : Sig) (arity : Nat)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    RegionIso (WireEquiv.refl common)
      (identityFormalPrefixEndpoint signature arity hostItems application)
      ((Region.ofItems hostItems).conjoin
        (positionalIdentityApplication signature arity application)) :=
  match hostItems with
  | .nil => by
      let direct := positionalIdentityApplication signature arity application
      exact (RegionIso.conjoinBlank direct).trans
        (RegionIso.blankConjoin direct).symm
  | .cons item tail => by
      let direct := positionalIdentityApplication signature arity application
      let children := RegionIso.conjoinCongr
        (retainedItemPresentationIso item)
        (identityFormalPrefixEndpointIso signature arity tail application)
      let associated :=
        (RegionIso.conjoinAssoc (Region.singleton item)
          (Region.ofItems tail) direct).symm
      let prefixIso := RegionIso.conjoinCongr
        (RegionIso.ofEq (singleton_conjoin_ofItems item tail))
        (RegionIso.refl direct)
      exact children.trans (associated.trans prefixIso)
termination_by sizeOf hostItems

theorem identityFormalPrefixItemsEditEndpoint
    {common sourceWires targetWires : List Sig}
    (signature : Sig) (arity : Nat)
    (frame : Transform.Frame (List.replicate arity signature) common
      sourceWires targetWires)
    (hostItems : ItemSeq common)
    (application : Vars common (List.replicate arity signature)) :
    (itemsEdit (operation := Leaf.Identity.operation signature arity)
      PUnit.unit
      (identityFormalPrefixEvidence frame hostItems application)
      (identityFormalPrefixSites frame hostItems application)).endpoint =
      (identityFormalPrefixEndpoint signature arity hostItems application).renameWires
        frame.targetKeep := by
  cases hostItems with
  | nil =>
      unfold identityFormalPrefixSites itemsEdit
      dsimp only
      simp only [itemEdit, ExactEdit.refl, identityFormalPrefixEndpoint,
        Transform.ItemEdit.run, Leaf.Identity.operation]
      unfold itemsEdit ExactEdit.refl Transform.ItemsEdit.run
      rw [Region.renameWires_conjoin]
      simp [Region.renameWires, Region.blank,
        Region.singleton_renameWires, Item.renameWires,
        ItemSeq.renameWires, positionalIdentityApplication]
  | cons item tail =>
      have tailEq := identityFormalPrefixItemsEditEndpoint signature arity
        frame tail application
      have headEq :
          (itemEdit (operation := Leaf.Identity.operation signature arity)
            PUnit.unit
            (retainedItemResult (positionalIdentityPattern signature arity)
              frame item)
            (retainedItemSites (positionalIdentityPattern signature arity)
              (Leaf.Identity.operation signature arity) frame PUnit.unit
              item)).endpoint =
            (retainedItemPresentation item).renameWires
              frame.targetKeep := by
        exact retainedItemEditEndpoint
          (positionalIdentityPattern signature arity)
          (Leaf.Identity.operation signature arity) frame PUnit.unit item
      unfold identityFormalPrefixSites itemsEdit
      dsimp only
      unfold identityFormalPrefixEndpoint
      rw [Region.renameWires_conjoin, headEq]
      exact congrArg
        (fun material =>
          (retainedItemPresentation item).renameWires frame.targetKeep |>.conjoin
            material)
        tailEq
termination_by sizeOf hostItems

theorem identityFormalPrefixRecordingItemsEditEndpoint
    {common sourceWires targetWires : List Sig}
    (signature : Sig) (arity : Nat)
    (patternArguments : List Sig)
    (frame : Transform.Frame (List.replicate arity signature) common
      sourceWires targetWires)
    (hostItems : ItemSeq common)
    (retained : Vars common (List.replicate arity signature))
    (application : Vars common patternArguments) :
    (itemsEdit
      (operation := recordingOperation
        (Leaf.Identity.operation signature arity) patternArguments)
      PUnit.unit
      (identityFormalPrefixEvidence frame hostItems retained)
      (identityFormalPrefixRecordingSites frame hostItems retained
        application)).endpoint =
      (identityFormalPrefixEndpoint signature arity hostItems retained).renameWires
        frame.targetKeep := by
  cases hostItems with
  | nil =>
      unfold identityFormalPrefixRecordingSites itemsEdit
      dsimp only
      simp only [itemEdit, ExactEdit.refl, identityFormalPrefixEndpoint,
        Transform.ItemEdit.run, recordingOperation, Leaf.Identity.operation]
      unfold itemsEdit ExactEdit.refl Transform.ItemsEdit.run
      rw [Region.renameWires_conjoin]
      simp [Region.renameWires, Region.blank,
        Region.singleton_renameWires, Item.renameWires,
        ItemSeq.renameWires, positionalIdentityApplication]
  | cons item tail =>
      have tailEq := identityFormalPrefixRecordingItemsEditEndpoint
        signature arity patternArguments frame tail retained
          application
      have headEq :
          (itemEdit
            (operation := recordingOperation
              (Leaf.Identity.operation signature arity) patternArguments)
            PUnit.unit
            (retainedItemResult (positionalIdentityPattern signature arity)
              frame item)
            (retainedItemSites (positionalIdentityPattern signature arity)
              (recordingOperation (Leaf.Identity.operation signature arity)
                patternArguments)
              frame PUnit.unit item)).endpoint =
            (retainedItemPresentation item).renameWires
              frame.targetKeep := by
        exact retainedItemEditEndpoint
          (positionalIdentityPattern signature arity)
          (recordingOperation (Leaf.Identity.operation signature arity)
            patternArguments)
          frame PUnit.unit item
      unfold identityFormalPrefixRecordingSites itemsEdit
      dsimp only
      unfold identityFormalPrefixEndpoint
      rw [Region.renameWires_conjoin, headEq]
      exact congrArg
        (fun material =>
          (retainedItemPresentation item).renameWires frame.targetKeep |>.conjoin
            material)
        tailEq
termination_by sizeOf hostItems


end VisualProof.Rule.Completeness.Comprehension
