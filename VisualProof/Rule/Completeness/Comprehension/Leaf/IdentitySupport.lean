import VisualProof.Rule.Completeness.Comprehension.Leaf.Targets

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

def supportIdentityMaterial
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) : Region wires :=
  Region.singleton (.identity signature arity ports)

theorem supportIdentityMaterial_canonical
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    (supportIdentityMaterial signature arity ports).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

def supportIdentityPinsAppended
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) : ItemSeq (wires ++ []) :=
  Erasure.Exposure.supportPins
    (supportIdentityMaterial signature arity ports) wires
    (Erasure.Exposure.identityBoundary wires)

def supportIdentityTail
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) : ItemSeq wires :=
  (supportIdentityPinsAppended signature arity ports).renameWires
    (WireEquiv.appendNil wires).toRenaming

theorem supportIdentityTail_appendNil
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    (supportIdentityTail signature arity ports).renameWires
        (WireEquiv.appendNil wires).symm.toRenaming =
      supportIdentityPinsAppended signature arity ports := by
  unfold supportIdentityTail
  rw [ItemSeq.renameWires_comp]
  have renameEq : WireRenaming.comp
      (WireEquiv.appendNil wires).symm.toRenaming
      (WireEquiv.appendNil wires).toRenaming = WireRenaming.id := by
    apply WireRenaming.ext
    intro wireSignature wire
    exact (WireEquiv.appendNil wires).left_inv wire
  rw [renameEq]
  exact ItemSeq.renameWires_id _

theorem supportIdentityBody_eq
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    Erasure.Exposure.supportBody
        (supportIdentityMaterial signature arity ports) =
      Region.ofItems (.cons (.identity signature arity ports)
        (supportIdentityTail signature arity ports)) := by
  unfold Erasure.Exposure.supportBody supportIdentityMaterial
  simp only [Region.singleton, Region.ofItems, Region.locals, Region.items]
  have pinsEq :
      Erasure.Exposure.supportPins
          (Region.mk [] (ItemSeq.renameWires
            ⟨fun wire => wire.appendLeft []⟩
            (.cons (.identity signature arity ports) .nil))) wires
          (Erasure.Exposure.identityBoundary wires) =
        supportIdentityPinsAppended signature arity ports := by
    simp [supportIdentityPinsAppended, supportIdentityMaterial,
      Region.singleton, Region.ofItems, Region.locals]
  rw [pinsEq]
  rw [← supportIdentityTail_appendNil signature arity ports]
  have appendEq : (⟨fun wire => wire.appendLeft []⟩ :
      WireRenaming wires (wires ++ [])) =
      (WireEquiv.appendNil wires).symm.toRenaming := by
    apply WireRenaming.ext
    intro wireSignature wire
    exact (WireEquiv.appendNil_symm_apply wires wire).symm
  rw [appendEq]
  rfl

theorem positionalIdentityInstantiation_reverseHostedScope
    (signature : Sig) (arity : Nat)
    (application : Vars wires (List.replicate arity signature)) :
    HostedScope
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) application)
      (positionalIdentityApplication signature arity application) := by
  intro target rename
  have sourceEq :
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) application).renameWires
          rename =
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity)
          (application.map fun wire => rename wire) := by
    exact EqualityNormalization.instantiate_renameWires
      (positionalIdentityPattern signature arity) application rename
  have targetEq :
      (positionalIdentityApplication signature arity application).renameWires
          rename =
        positionalIdentityApplication signature arity
          (application.map fun wire => rename wire) := by
    simp [positionalIdentityApplication, Region.singleton_renameWires,
      Item.renameWires, Leaf.Identity.Vars.toFn_map]
  rw [sourceEq, targetEq]
  exact positionalIdentityInstantiation_scope signature arity
    (application.map fun wire => rename wire)

/-- A selected support-singleton identity is presented directly at its actual
application, without copied boundary locals. -/
theorem supportIdentitySelectedTargetItem
    {wires itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature)
    {itemFrame : Transform.Frame wires itemCommon itemSourceWires
      itemTargetWires}
    {itemOperation : Transform.Operation wires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon wires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame (List.replicate arity signature)
      itemCommon formalSourceWires formalTargetWires) :
    TargetItem
      (targetPattern := positionalIdentityPattern signature arity)
      (targetOperation := Leaf.Identity.operation signature arity)
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := Erasure.Exposure.supportPattern
          (supportIdentityMaterial signature arity ports)
          (supportIdentityMaterial_canonical signature arity ports))
        (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := Erasure.Exposure.supportPattern
          (supportIdentityMaterial signature arity ports)
          (supportIdentityMaterial_canonical signature arity ports))
        (frame := itemFrame) application siteData)
      (Leaf.Identity.Vars.fromFn ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult _formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (supportIdentityMaterial signature arity ports)
                  (supportIdentityMaterial_canonical signature arity ports))
                application)
              staged ∧
            ScopePreservation
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (supportIdentityMaterial signature arity ports)
                  (supportIdentityMaterial_canonical signature arity ports))
                application)
              staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult)) ∧
              retained = [] ∧
              let authoritativeFrame : Transform.Frame wires itemCommon
                  itemSourceWires itemSourceWires := {
                sourceKeep := itemFrame.sourceKeep
                targetKeep := itemFrame.sourceKeep
                selected := itemFrame.selected
              }
              let direct := Region.singleton (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire))
              let authoritative := Region.adjoinAt retained .nil
                (Region.ofItems
                  (argumentItemsEdit formalSites
                    (EqualityNormalization.formalPorts wires)
                    (normalizationOperation wires)
                    (authoritativeFrame.append retained)
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1)
              HostedStrict direct authoritative ∧
                HostedScope direct authoritative) := by
  unfold TargetItem
  let commonEquiv := WireEquiv.appendNil itemCommon
  let commonAppend := commonEquiv.symm.toRenaming
  let mappedApplication := application.map fun wire => commonAppend wire
  let substitution := EqualityNormalization.formalSubstitution mappedApplication
  let mappedPins := EqualityNormalization.allPins wires substitution
  let hostItems :=
    ((supportIdentityTail signature arity ports).renameWires substitution).append
      (mappedPins.append mappedPins)
  let retainedPorts := Leaf.Identity.Vars.fromFn
    (fun position => substitution (ports position))
  let childFrame := formalFrame.append []
  let formalSource := identityFormalPrefixSource childFrame hostItems retainedPorts
  let formalResult := identityFormalPrefixResult signature arity hostItems
    retainedPorts
  let formalEvidence := identityFormalPrefixEvidence childFrame hostItems
    retainedPorts
  let formalSites := identityFormalPrefixRecordingSites childFrame hostItems
    retainedPorts mappedApplication
  refine ⟨[], formalSource, formalResult, formalEvidence, formalSites, ?_, ?_⟩
  · apply identityFormalPrefixSource_eq_argumentItemsEdit childFrame hostItems
      retainedPorts mappedApplication (Leaf.Identity.Vars.fromFn ports)
      substitution
    · exact (EqualityNormalization.formalPorts_map_substitution
        mappedApplication).symm
    · rw [Leaf.Identity.Vars.fromFn_map]
  · let rawSubstitution := EqualityNormalization.formalSubstitution application
    let rawSupportItems :=
      (supportIdentityTail signature arity ports).renameWires rawSubstitution
    let rawPins := EqualityNormalization.allPins wires rawSubstitution
    let rawHostItems := rawSupportItems.append (rawPins.append rawPins)
    let rawRetainedPorts := Leaf.Identity.Vars.fromFn
      (fun position => rawSubstitution (ports position))
    let staged := identityFormalPrefixResult signature arity rawHostItems
      rawRetainedPorts
    refine ⟨staged, ?_, ?_, ?_, rfl, ?_⟩
    · let material := supportIdentityMaterial signature arity ports
      let materialCanonical := supportIdentityMaterial_canonical signature arity
        ports
      let supported := Erasure.Exposure.supportBody material
      let supportedCanonical := Erasure.Exposure.supportBody_canonical
        material materialCanonical
      have supportedPinsNil : Erasure.Exposure.supportPins supported wires
          (Erasure.Exposure.identityBoundary wires) = .nil := by
        apply EqualityNormalization.supportPins_eq_nil
        intro position
        exact Erasure.Exposure.supportBody_incidence_nonempty material
          ((Erasure.Exposure.identityBoundary wires).get position)
      have supportedFixed : Erasure.Exposure.supportBody supported =
          supported :=
        EqualityNormalization.supportBody_eq_of_supportPins_nil supported
          supportedPinsNil
      have patternEq : Erasure.Exposure.supportPattern supported
            supportedCanonical =
          Erasure.Exposure.supportPattern material materialCanonical := by
        apply EqualityNormalization.OpenDiagram.eq_of_data
        · rfl
        · rfl
        · exact heq_of_eq supportedFixed
      have sourceToSupported : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (supported.renameWires rawSubstitution) := by
        rw [← patternEq]
        exact supportInstantiationHosted supported supportedCanonical application
      let direct := positionalIdentityApplication signature arity
        rawRetainedPorts
      have directItemEq : direct = Region.singleton
          (.identity signature arity
            (fun position => rawSubstitution (ports position))) := by
        unfold direct positionalIdentityApplication rawRetainedPorts
        rw [Leaf.Identity.Vars.toFn_fromFn]
      have supportedTargetEq : supported.renameWires rawSubstitution =
          Region.ofItems (.cons
            (.identity signature arity
              (fun position => rawSubstitution (ports position)))
            rawSupportItems) := by
        change (Erasure.Exposure.supportBody
          (supportIdentityMaterial signature arity ports)).renameWires
            rawSubstitution = _
        rw [supportIdentityBody_eq signature arity ports]
        simp only [Region.renameWires, Region.ofItems, ItemSeq.renameWires,
          Item.renameWires, rawSupportItems]
        simp [WireRenaming.appendRight, ItemSeq.renameWires_comp]
        apply congrArg (fun rename =>
          (supportIdentityTail signature arity ports).renameWires rename)
        apply WireRenaming.ext
        intro wireSignature wire
        simp [WireRenaming.comp]
      let supportPins := Region.ofItems rawSupportItems
      let allPins := Region.ofItems (rawPins.append rawPins)
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) rawRetainedPorts
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (direct.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          ((RegionIso.ofEq (Region.singleton_conjoin_ofItems
            (.identity signature arity
              (fun position => rawSubstitution (ports position)))
            rawSupportItems).symm).trans
            (RegionIso.conjoinCongr (RegionIso.ofEq directItemEq.symm)
              (RegionIso.refl supportPins)))
      have sourceToDirectPins : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (direct.conjoin supportPins) :=
        HostedStrict.iso (RegionIso.refl _) supportedPresentation
          sourceToSupported
      have positionalToDirect : HostedStrict positional direct := by
        have exposed := supportInstantiationHosted
          (positionalIdentityMaterial signature arity)
          (positionalIdentityMaterial_canonical signature arity)
          rawRetainedPorts
        change HostedStrict positional
          ((positionalIdentityMaterial signature arity).renameWires
            (EqualityNormalization.formalSubstitution rawRetainedPorts)) at exposed
        rw [positionalIdentityMaterial_rename] at exposed
        exact exposed
      have directToPositionalPins : HostedStrict (direct.conjoin supportPins)
          (positional.conjoin supportPins) :=
        HostedStrict.conjoin direct supportPins positional supportPins
          positionalToDirect.symm (HostedStrict.refl supportPins)
      have positionalPinsReverse : HostedScope
          (positional.conjoin supportPins)
          (direct.conjoin supportPins) := by
        intro target rename
        simpa only [positional, direct, Region.renameWires_conjoin] using
          ScopePreservation.conjoin
            (positionalIdentityInstantiation_reverseHostedScope signature
              arity rawRetainedPorts rename)
            (ScopePreservation.refl (supportPins.renameWires rename))
      have sourceToPositionalPins : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (positional.conjoin supportPins) :=
        HostedStrict.trans sourceToDirectPins directToPositionalPins
          (fun outer hostLocals rename hostItems =>
            HostedScope.adjoinHost positionalPinsReverse outer hostLocals
              rename hostItems)
      let source :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern material materialCanonical)
          application
      let pinned := HostedStrict.conjoin source (Region.blank itemCommon)
        (positional.conjoin supportPins) allPins sourceToPositionalPins
        (HostedStrict.allPinsTwice wires rawSubstitution)
      let supportPinsPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supportPins.conjoin allPins) (Region.ofItems rawHostItems) :=
        RegionIso.ofEq (by rw [Region.ofItems_conjoin])
      let resultPresentation : RegionIso (WireEquiv.refl itemCommon)
          ((positional.conjoin supportPins).conjoin allPins) staged :=
        (RegionIso.conjoinAssoc positional supportPins allPins).trans
          ((RegionIso.conjoinCongr (RegionIso.refl positional)
            supportPinsPresentation).trans
            ((RegionIso.conjoinComm positional
              (Region.ofItems rawHostItems)).trans
              (identityFormalPrefixResultIso signature arity rawHostItems
                rawRetainedPorts).symm))
      exact HostedStrict.iso (RegionIso.conjoinBlank source).symm
        resultPresentation pinned
    · let material := supportIdentityMaterial signature arity ports
      let supported := Erasure.Exposure.supportBody material
      let pins := rawPins
      let pinRegion := Region.ofItems (pins.append pins)
      have ofItemsRenameEq : ∀ {sourceWires targetWires : List Sig}
          (items : ItemSeq sourceWires)
          (rename : WireRenaming sourceWires targetWires),
          (Region.ofItems items).renameWires rename =
            Region.ofItems (items.renameWires rename) := by
        intro sourceWires targetWires items rename
        unfold Region.ofItems Region.renameWires
        congr 1
        simp only [ItemSeq.renameWires_comp]
        apply congrArg (fun mapped => items.renameWires mapped)
        apply WireRenaming.ext
        intro wireSignature wire
        simp [WireRenaming.comp, WireRenaming.appendRight]
      have mappedFormalOfPositive : ∀ {wireSignature}
          (wire : Var itemCommon wireSignature),
          0 < application.countIndex wire.index.val →
          ∃ sourceSignature, ∃ sourceWire : Var wires sourceSignature,
            (rawSubstitution sourceWire).index.val = wire.index.val := by
        intro wireSignature wire positive
        obtain ⟨position, positionEq⟩ :=
          EqualityNormalization.Vars.exists_get_index_of_countIndex_pos
            application wire.index.val positive
        let sourceWire := (EqualityNormalization.formalPorts wires).get position
        have mappedAt : rawSubstitution sourceWire = application.get position := by
          have mappedTuple :=
            EqualityNormalization.formalPorts_map_substitution application
          have mappedGet := congrArg (fun variables => variables.get position)
            mappedTuple
          simpa only [EqualityNormalization.Vars.get_map, sourceWire,
            rawSubstitution] using mappedGet
        exact ⟨wires.get position, sourceWire, by rw [mappedAt, positionEq]⟩
      have noPreimageOfCountZero :
          ∀ {sourceSignatures : List Sig}
            (variables : Vars itemCommon sourceSignatures)
            {targetSignature} (targetWire : Var itemCommon targetSignature),
            variables.countIndex targetWire.index.val = 0 →
            ∀ {sourceSignature}
              (sourceWire : Var sourceSignatures sourceSignature),
              (EqualityNormalization.formalSubstitution variables
                sourceWire).index.val ≠ targetWire.index.val := by
        intro sourceSignatures variables
        induction variables with
        | nil =>
            intro targetSignature targetWire zero sourceSignature sourceWire
            exact nomatch sourceWire
        | cons applicationHead applicationTail induction =>
            intro targetSignature targetWire zero sourceSignature sourceWire
            cases sourceWire with
            | here =>
                intro mapped
                simp only [EqualityNormalization.formalSubstitution_here]
                  at mapped
                simp only [Vars.countIndex, mapped, if_true] at zero
                omega
            | there tailWire =>
                apply induction targetWire
                simp only [Vars.countIndex] at zero
                omega
      have supportedCanonical : supported.Canonical :=
        Erasure.Exposure.supportBody_canonical material
          (supportIdentityMaterial_canonical signature arity ports)
      have pinCanonical : pinRegion.Canonical := by
        change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
          ((pins.append pins).renameWires _).ChildrenCanonical
        exact ⟨fun localIndex => Fin.elim0 localIndex,
          (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
            (EqualityNormalization.allPins_twice_childrenCanonical
              wires rawSubstitution)⟩
      have sourceToSupportedPins : ScopePreservation
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material
              (supportIdentityMaterial_canonical signature arity ports))
            application)
          ((supported.renameWires rawSubstitution).conjoin pinRegion) := by
        constructor
        · intro _
          exact EqualityNormalization.canonical_conjoin
            ((Region.Canonical.renameWires_iff supported rawSubstitution).mpr
              supportedCanonical)
            pinCanonical
        · intro wireSignature wire
          rw [EqualityNormalization.instantiate_incidence_nonempty_iff]
          constructor
          · intro positive
            obtain ⟨sourceSignature, sourceWire, mappedIndex⟩ :=
              mappedFormalOfPositive wire positive
            have pinRoot := EqualityNormalization.allPins_twice_rooted
              wires rawSubstitution sourceWire 0
            rw [mappedIndex] at pinRoot
            have pinNonempty : pinRegion.incidencePaths wire.index.val ≠ [] := by
              rw [Region.incidencePaths_ofItems]
              exact pinRoot.nonempty
            rw [Region.incidencePaths_conjoin]
            intro empty
            have mappedEmpty := (List.append_eq_nil_iff.mp empty).2
            exact pinNonempty ((List.map_eq_nil_iff).mp mappedEmpty)
          · intro targetNonempty
            cases countEq : application.countIndex wire.index.val with
            | zero =>
                have noPreimage : ∀ {sourceSignature}
                    (sourceWire : Var wires sourceSignature),
                    (rawSubstitution sourceWire).index.val ≠
                      wire.index.val := by
                  exact noPreimageOfCountZero application wire countEq
                have supportedEmpty :
                    (supported.renameWires rawSubstitution).incidencePaths
                      wire.index.val = [] := by
                  change ((Erasure.Exposure.supportBody
                    (supportIdentityMaterial signature arity ports)
                    ).renameWires rawSubstitution).incidencePaths
                      wire.index.val = []
                  rw [supportIdentityBody_eq signature arity ports,
                    ofItemsRenameEq, Region.incidencePaths_ofItems]
                  apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
                  · exact wire.index.isLt
                  · exact noPreimage
                have firstPinsEmpty :
                    pins.incidencePaths wire.index.val 0 = [] := by
                  exact ItemSeq.pinWires_incidence_eq_nil_of wires
                    rawSubstitution (fun _ => true) wire.index.val 0
                    (fun sourceWire _ => noPreimage sourceWire)
                have secondPinsEmpty :
                    pins.incidencePaths wire.index.val pins.length = [] := by
                  exact ItemSeq.pinWires_incidence_eq_nil_of wires
                    rawSubstitution (fun _ => true) wire.index.val pins.length
                    (fun sourceWire _ => noPreimage sourceWire)
                have pinEmpty : pinRegion.incidencePaths wire.index.val = [] := by
                  rw [Region.incidencePaths_ofItems,
                    ItemSeq.incidencePaths_append, firstPinsEmpty]
                  simpa only [List.nil_append, Nat.zero_add] using
                    secondPinsEmpty
                rw [Region.incidencePaths_conjoin, supportedEmpty, pinEmpty]
                  at targetNonempty
                exact False.elim (targetNonempty (by simp))
            | succ count => omega
        · intro wireSignature wire sourceRoot
          have positive : 0 < application.countIndex wire.index.val := by
            have countBound :=
              (EqualityNormalization.instantiate_rootedTwo_iff
                (Erasure.Exposure.supportPattern material
                  (supportIdentityMaterial_canonical signature arity ports))
                application wire).mp sourceRoot
            omega
          obtain ⟨sourceSignature, sourceWire, mappedIndex⟩ :=
            mappedFormalOfPositive wire positive
          have pinRoot := EqualityNormalization.allPins_twice_rooted
            wires rawSubstitution sourceWire 0
          rw [mappedIndex] at pinRoot
          rw [Region.incidencePaths_conjoin]
          apply RegionPath.RootedTwo.of_sublist
            (List.sublist_append_right _ _)
          exact (RegionPath.RootedTwo.map_shiftHead_iff _ _).mpr (by
            rw [Region.incidencePaths_ofItems]
            exact pinRoot)
      let direct := positionalIdentityApplication signature arity
        rawRetainedPorts
      have directItemEq : direct = Region.singleton
          (.identity signature arity
            (fun position => rawSubstitution (ports position))) := by
        unfold direct positionalIdentityApplication rawRetainedPorts
        rw [Leaf.Identity.Vars.toFn_fromFn]
      have supportedTargetEq : supported.renameWires rawSubstitution =
          Region.ofItems (.cons
            (.identity signature arity
              (fun position => rawSubstitution (ports position)))
            rawSupportItems) := by
        change (Erasure.Exposure.supportBody
          (supportIdentityMaterial signature arity ports)).renameWires
            rawSubstitution = _
        rw [supportIdentityBody_eq signature arity ports]
        simp only [Region.renameWires, Region.ofItems, ItemSeq.renameWires,
          Item.renameWires, rawSupportItems]
        simp [WireRenaming.appendRight, ItemSeq.renameWires_comp]
        apply congrArg (fun rename =>
          (supportIdentityTail signature arity ports).renameWires rename)
        apply WireRenaming.ext
        intro wireSignature wire
        simp [WireRenaming.comp]
      let supportPins := Region.ofItems rawSupportItems
      let allPins := pinRegion
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) rawRetainedPorts
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (direct.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          ((RegionIso.ofEq (Region.singleton_conjoin_ofItems
            (.identity signature arity
              (fun position => rawSubstitution (ports position)))
            rawSupportItems).symm).trans
            (RegionIso.conjoinCongr (RegionIso.ofEq directItemEq.symm)
              (RegionIso.refl supportPins)))
      have supportedToDirectPins : ScopePreservation
          ((supported.renameWires rawSubstitution).conjoin allPins)
          ((direct.conjoin supportPins).conjoin allPins) :=
        ScopePreservation.ofIso
          (RegionIso.conjoinCongr supportedPresentation
            (RegionIso.refl allPins))
      have directToPositionalPins : ScopePreservation
          ((direct.conjoin supportPins).conjoin allPins)
          ((positional.conjoin supportPins).conjoin allPins) :=
        ScopePreservation.conjoin
          (ScopePreservation.conjoin
            (positionalIdentityApplication_scope signature arity
              rawRetainedPorts)
            (ScopePreservation.refl supportPins))
          (ScopePreservation.refl allPins)
      let supportPinsPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supportPins.conjoin allPins) (Region.ofItems rawHostItems) :=
        RegionIso.ofEq (by rw [Region.ofItems_conjoin])
      let resultPresentation : RegionIso (WireEquiv.refl itemCommon)
          ((positional.conjoin supportPins).conjoin allPins) staged :=
        (RegionIso.conjoinAssoc positional supportPins allPins).trans
          ((RegionIso.conjoinCongr (RegionIso.refl positional)
            supportPinsPresentation).trans
            ((RegionIso.conjoinComm positional
              (Region.ofItems rawHostItems)).trans
              (identityFormalPrefixResultIso signature arity rawHostItems
                rawRetainedPorts).symm))
      exact sourceToSupportedPins.trans
        (supportedToDirectPins.trans
          (directToPositionalPins.trans
            (ScopePreservation.ofIso resultPresentation)))
    · have mappedResultEq : staged.renameWires commonAppend = formalResult := by
        rw [identityFormalPrefixResult_renameWires]
        have hostItemsEq : rawHostItems.renameWires commonAppend = hostItems := by
          have substitutionEq :
              WireRenaming.comp commonAppend rawSubstitution = substitution := by
            apply WireRenaming.ext
            intro wireSignature wire
            exact (EqualityNormalization.formalSubstitution_map
              application commonAppend wire).symm
          have supportItemsEq : rawSupportItems.renameWires commonAppend =
              (supportIdentityTail signature arity ports).renameWires
                substitution := by
            unfold rawSupportItems rawSubstitution
            rw [ItemSeq.renameWires_comp, substitutionEq]
          have pinsEq : rawPins.renameWires commonAppend = mappedPins := by
            unfold rawPins mappedPins rawSubstitution
            rw [EqualityNormalization.allPins_renameWires, substitutionEq]
          unfold rawHostItems hostItems
          simp only [ItemSeq.renameWires_append, supportItemsEq, pinsEq]
        have portsEq : rawRetainedPorts.map (fun wire => commonAppend wire) =
            retainedPorts := by
          unfold rawRetainedPorts retainedPorts
          rw [Leaf.Identity.Vars.fromFn_map]
          apply congrArg Leaf.Identity.Vars.fromFn
          funext position
          exact (EqualityNormalization.formalSubstitution_map
            application commonAppend (ports position)).symm
        rw [hostItemsEq, portsEq]
      let intoMapped : RegionIso commonEquiv.symm staged formalResult := by
        let renamed := RegionIso.renameWires staged WireRenaming.id
          commonAppend commonEquiv.symm (by intro wireSignature wire; rfl)
        rw [Region.renameWires_id, mappedResultEq] at renamed
        exact renamed
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv
            (by intro wireSignature wire; rfl)
      let chained := (intoMapped.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq : (commonEquiv.symm.trans commonEquiv).trans
          (WireEquiv.refl itemCommon) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro wireSignature wire
        exact commonEquiv.right_inv wire
      exact ⟨chained.castAmbient ambientEq⟩
    · dsimp only
      simp only [formalSites]
      let authoritativeFrame : Transform.Frame wires itemCommon
          itemSourceWires itemSourceWires := {
        sourceKeep := itemFrame.sourceKeep
        targetKeep := itemFrame.sourceKeep
        selected := itemFrame.selected
      }
      have editedEq :=
        identityFormalPrefixArgumentItemsEdit_source childFrame
          (authoritativeFrame.append []) hostItems retainedPorts
          mappedApplication (EqualityNormalization.formalPorts wires)
      change
        let direct := Region.singleton (.atom itemFrame.selected
          (application.map fun wire => itemFrame.sourceKeep wire))
        let authoritative := Region.adjoinAt [] .nil
          (Region.ofItems
            (argumentItemsEdit
              (identityFormalPrefixRecordingSites childFrame hostItems
                retainedPorts mappedApplication)
              (EqualityNormalization.formalPorts wires)
              (normalizationOperation wires)
              (authoritativeFrame.append []) PUnit.unit
              (fun _ _ _ => PUnit.unit)).1)
        HostedStrict direct authoritative ∧
          HostedScope direct authoritative
      rw [editedEq]
      let rawSubstitution :=
        EqualityNormalization.formalSubstitution application
      let targetSubstitution : WireRenaming wires itemSourceWires :=
        WireRenaming.comp itemFrame.sourceKeep rawSubstitution
      let direct := Region.singleton (.atom itemFrame.selected
        (application.map fun wire => itemFrame.sourceKeep wire))
      let supportPins := Region.ofItems
        ((supportIdentityTail signature arity ports).renameWires
          targetSubstitution)
      let pins := EqualityNormalization.allPins wires targetSubstitution
      let allPins := Region.ofItems (pins.append pins)
      let material := supportIdentityMaterial signature arity ports
      have supportStep : HostedStrict (Region.blank itemSourceWires)
          supportPins := by
        have base : HostedStrict (Region.blank wires)
            (Region.ofItems (supportIdentityTail signature arity ports)) := by
          apply HostedStrict.specialize
            (HostedStrict.supportPins material
              (Erasure.Exposure.identityBoundary wires))
            (WireEquiv.appendNil wires).toRenaming
          · change (Region.blank (wires ++ [])).renameWires
                (WireEquiv.appendNil wires).toRenaming =
              Region.blank wires
            rfl
          · unfold material supportIdentityMaterial
            rw [Region.ofItems_renameWires]
            simp [supportIdentityTail, supportIdentityPinsAppended,
              supportIdentityMaterial] <;> rfl
        apply HostedStrict.specialize base targetSubstitution
        · rfl
        · unfold supportPins
          exact Region.ofItems_renameWires
            (supportIdentityTail signature arity ports) targetSubstitution
      have allPinsStep : HostedStrict (Region.blank itemSourceWires)
          allPins :=
        HostedStrict.allPinsTwice wires targetSubstitution
      let hostStep := HostedStrict.conjoin
        (Region.blank itemSourceWires) (Region.blank itemSourceWires)
        supportPins allPins supportStep allPinsStep
      let host := supportPins.conjoin allPins
      let hostFromBlank : HostedStrict (Region.blank itemSourceWires) host :=
        HostedStrict.iso (RegionIso.blankConjoin _).symm
          (RegionIso.refl host) hostStep
      let directHost := HostedStrict.conjoin direct
        (Region.blank itemSourceWires) direct host
        (HostedStrict.refl direct) hostFromBlank
      let directToHostDirect : HostedStrict direct (host.conjoin direct) :=
        HostedStrict.iso (RegionIso.conjoinBlank direct).symm
          (RegionIso.conjoinComm direct host) directHost
      let authoritativeSource :=
        (hostItems.renameWires
            (authoritativeFrame.append []).sourceKeep).append
          (.cons (.atom (authoritativeFrame.append []).selected
            ((EqualityNormalization.formalPorts wires).map fun wire =>
              (authoritativeFrame.append []).sourceKeep
                (EqualityNormalization.formalSubstitution mappedApplication
                  wire))) .nil)
      let child := Region.ofItems authoritativeSource
      have childDownEq :
          child.renameWires (WireEquiv.appendNil itemSourceWires).toRenaming =
            host.conjoin direct := by
        let down := (WireEquiv.appendNil itemSourceWires).toRenaming
        let downFrame : WireRenaming (itemCommon ++ []) itemSourceWires :=
          WireRenaming.comp down
            (authoritativeFrame.append []).sourceKeep
        have downFrameCommonEq : ∀ {wireSignature}
            (wire : Var itemCommon wireSignature),
            downFrame (commonAppend wire) = itemFrame.sourceKeep wire := by
          intro wireSignature wire
          unfold downFrame down commonAppend authoritativeFrame
          rw [show commonEquiv.symm.toRenaming wire =
              wire.appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon wire]
          simp [WireRenaming.comp, Transform.Frame.append,
            WireRenaming.appendRight, Var.appendMap_left,
            WireEquiv.appendNil_apply]
        have combinedSubstitutionEq :
            WireRenaming.comp downFrame substitution =
              targetSubstitution := by
          apply WireRenaming.ext
          intro wireSignature wire
          change downFrame
              (EqualityNormalization.formalSubstitution mappedApplication
                wire) =
            itemFrame.sourceKeep
              (EqualityNormalization.formalSubstitution application wire)
          rw [EqualityNormalization.formalSubstitution_map
            application commonAppend wire]
          exact downFrameCommonEq _
        have selectedPortsEq :
            (EqualityNormalization.formalPorts wires).map (fun wire =>
              downFrame
                (EqualityNormalization.formalSubstitution mappedApplication
                  wire)) =
              application.map fun wire => itemFrame.sourceKeep wire := by
          calc
            _ = ((EqualityNormalization.formalPorts wires).map
                (fun wire =>
                  EqualityNormalization.formalSubstitution mappedApplication
                    wire)).map (fun wire => downFrame wire) := by
              rw [Vars.map_map]
            _ = mappedApplication.map (fun wire => downFrame wire) := by
              rw [EqualityNormalization.formalPorts_map_substitution]
            _ = application.map (fun wire => itemFrame.sourceKeep wire) := by
              unfold mappedApplication
              rw [Vars.map_map]
              apply Vars.map_congr
              intro wireSignature wire
              exact downFrameCommonEq wire
        have selectedHeadEq :
            down ((authoritativeFrame.append []).selected) =
              itemFrame.selected := by
          unfold down authoritativeFrame
          simp [Transform.Frame.append, WireEquiv.appendNil_apply]
        have hostItemsDownEq :
            hostItems.renameWires downFrame =
              ((supportIdentityTail signature arity ports).renameWires
                  targetSubstitution).append
                (pins.append pins) := by
          unfold hostItems mappedPins pins
          simp only [ItemSeq.renameWires_append,
            ItemSeq.renameWires_comp,
            EqualityNormalization.allPins_renameWires]
          rw [combinedSubstitutionEq]
        unfold host supportPins allPins direct
        unfold child authoritativeSource pins
        rw [Region.ofItems_renameWires]
        rw [show Region.singleton
              (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire)) =
            Region.ofItems
              (.cons (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire))
                .nil) by rfl]
        rw [Region.ofItems_conjoin]
        rw [Region.ofItems_conjoin]
        apply congrArg Region.ofItems
        simp only [ItemSeq.renameWires_append, ItemSeq.renameWires,
          Item.renameWires, ItemSeq.renameWires_comp, Vars.map_map]
        change
          (hostItems.renameWires downFrame).append
              (.cons (.atom
                (down ((authoritativeFrame.append []).selected))
                ((EqualityNormalization.formalPorts wires).map fun wire =>
                  downFrame
                    (EqualityNormalization.formalSubstitution
                      mappedApplication wire))) .nil) =
            (((supportIdentityTail signature arity ports).renameWires
                targetSubstitution).append
              ((EqualityNormalization.allPins wires
                  targetSubstitution).append
                (EqualityNormalization.allPins wires
                  targetSubstitution))).append
              (.cons (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire)) .nil)
        rw [hostItemsDownEq, selectedHeadEq, selectedPortsEq]
      have supportPinsCanonical : supportPins.Canonical := by
        have baseCanonical :
            (Region.ofItems
              (supportIdentityTail signature arity ports)).Canonical := by
          constructor
          · intro localIndex
            exact Fin.elim0 localIndex
          · unfold supportIdentityTail supportIdentityPinsAppended
            exact (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
              ((ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
                (Erasure.Exposure.supportPins_childrenCanonical
                  (supportIdentityMaterial signature arity ports)
                  (Erasure.Exposure.identityBoundary wires)))
        simpa only [supportPins, Region.ofItems_renameWires] using
          (Region.Canonical.renameWires_iff
            (Region.ofItems (supportIdentityTail signature arity ports))
            targetSubstitution).mpr baseCanonical
      have allPinsCanonical : allPins.Canonical := by
        constructor
        · intro localIndex
          exact Fin.elim0 localIndex
        · exact (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
            (EqualityNormalization.allPins_twice_childrenCanonical
              wires targetSubstitution)
      have hostCanonical : host.Canonical := by
        exact EqualityNormalization.canonical_conjoin supportPinsCanonical
          allPinsCanonical
      have directToHostDirectScope : HostedScope direct
          (host.conjoin direct) := by
        intro target rename
        let mappedApplication :=
          (application.map fun wire => itemFrame.sourceKeep wire).map
            (fun wire => rename wire)
        let mappedSubstitution : WireRenaming wires target :=
          EqualityNormalization.formalSubstitution mappedApplication
        have mappedSubstitutionEq : mappedSubstitution =
            WireRenaming.comp rename targetSubstitution := by
          apply WireRenaming.ext
          intro wireSignature wire
          unfold mappedSubstitution mappedApplication targetSubstitution
            rawSubstitution
          calc
            _ = rename
                (EqualityNormalization.formalSubstitution
                  (application.map fun wire => itemFrame.sourceKeep wire)
                  wire) :=
              EqualityNormalization.formalSubstitution_map
                (application.map fun wire => itemFrame.sourceKeep wire)
                rename wire
            _ = rename
                (itemFrame.sourceKeep
                  (EqualityNormalization.formalSubstitution application
                    wire)) := by
              rw [EqualityNormalization.formalSubstitution_map]
            _ = _ := rfl
        have directRenameEq : direct.renameWires rename =
            Region.singleton (.atom (rename itemFrame.selected)
              mappedApplication) := by
          unfold direct mappedApplication
          simp only [Region.singleton_renameWires, Item.renameWires,
            Vars.map_map]
        have hostRenameCanonical : (host.renameWires rename).Canonical :=
          (Region.Canonical.renameWires_iff host rename).mpr hostCanonical
        have scopeProof : ScopePreservation
            (direct.renameWires rename)
            ((host.renameWires rename).conjoin
              (direct.renameWires rename)) :=
          ScopePreservation.hostLeft
            (direct.renameWires rename) (host.renameWires rename)
            hostRenameCanonical (by
              intro wireSignature wire hostNonempty
              rw [directRenameEq]
              intro directEmpty
              let appendNil : WireRenaming target (target ++ []) :=
                ⟨fun selected => selected.appendLeft []⟩
              have mappedCountEq :
                  (mappedApplication.map fun selected =>
                    appendNil selected).countIndex wire.index.val =
                    mappedApplication.countIndex wire.index.val :=
                Vars.countIndex_map_of_sameIndex mappedApplication appendNil
                  (fun selected => Var.index_appendLeft selected [])
                  wire.index.val
              simp only [Region.singleton, Region.ofItems,
                Region.incidencePaths, ItemSeq.renameWires,
                Item.renameWires, ItemSeq.incidencePaths,
                Item.incidencePaths, List.append_nil,
                Var.index_appendLeft] at directEmpty
              rw [mappedCountEq] at directEmpty
              have countZero : mappedApplication.countIndex
                  wire.index.val = 0 := by
                have totalZero :
                    (if (rename itemFrame.selected).index.val =
                        wire.index.val then 1 else 0) +
                      mappedApplication.countIndex wire.index.val = 0 := by
                  simpa only [List.replicate_eq_nil_iff] using directEmpty
                omega
              have noPreimage : ∀ {sourceSignature}
                  (sourceWire : Var wires sourceSignature),
                  ((WireRenaming.comp rename targetSubstitution)
                      sourceWire).index.val ≠ wire.index.val := by
                intro sourceSignature sourceWire
                rw [← mappedSubstitutionEq]
                exact EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                  mappedApplication wire countZero sourceWire
              have supportEmpty :
                  (supportPins.renameWires rename).incidencePaths
                    wire.index.val = [] := by
                unfold supportPins
                rw [Region.ofItems_renameWires,
                  ItemSeq.renameWires_comp, Region.incidencePaths_ofItems]
                exact ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
                  (supportIdentityTail signature arity ports)
                  (WireRenaming.comp rename targetSubstitution)
                  wire.index.val 0 wire.index.isLt noPreimage
              have firstPinsEmpty :
                  (EqualityNormalization.allPins wires mappedSubstitution
                    ).incidencePaths wire.index.val 0 = [] := by
                exact ItemSeq.pinWires_incidence_eq_nil_of wires
                  mappedSubstitution (fun _ => true) wire.index.val 0
                  (fun sourceWire _ =>
                    EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                      mappedApplication wire countZero sourceWire)
              have secondPinsEmpty :
                  (EqualityNormalization.allPins wires mappedSubstitution
                    ).incidencePaths wire.index.val
                      (EqualityNormalization.allPins wires
                        mappedSubstitution).length = [] := by
                exact ItemSeq.pinWires_incidence_eq_nil_of wires
                  mappedSubstitution (fun _ => true) wire.index.val
                  (EqualityNormalization.allPins wires
                    mappedSubstitution).length
                  (fun sourceWire _ =>
                    EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                      mappedApplication wire countZero sourceWire)
              have allPinsEmpty :
                  (allPins.renameWires rename).incidencePaths
                    wire.index.val = [] := by
                rw [mappedSubstitutionEq] at firstPinsEmpty secondPinsEmpty
                unfold allPins pins
                rw [Region.ofItems_renameWires,
                  ItemSeq.renameWires_append,
                  EqualityNormalization.allPins_renameWires,
                  Region.incidencePaths_ofItems,
                  ItemSeq.incidencePaths_append, firstPinsEmpty]
                simpa only [List.nil_append, Nat.zero_add] using
                  secondPinsEmpty
              unfold host at hostNonempty
              rw [Region.renameWires_conjoin,
                Region.incidencePaths_conjoin, supportEmpty, allPinsEmpty]
                at hostNonempty
              exact hostNonempty (by simp))
        simpa only [Region.renameWires_conjoin] using scopeProof
      let targetPresentation :=
        (RegionIso.ofEq childDownEq).symm.trans
          (RegionIso.adjoinAtNil child)
      exact ⟨HostedStrict.iso (RegionIso.refl direct)
          targetPresentation directToHostDirect, by
        intro target rename
        exact (directToHostDirectScope rename).trans
          ((HostedScope.ofIso targetPresentation) rename)⟩

/-- The positional identity operation target can always be re-expanded to its
pattern instantiation when the operation retains the common wires literally. -/
theorem positionalIdentityLeafEndpoint_reverseHostedScope
    (signature : Sig) (arity : Nat)
    {originalArguments common sourceWires : List Sig}
    {frame : Transform.Frame (List.replicate arity signature) common
      sourceWires common}
    (targetKeepEq : frame.targetKeep = WireRenaming.id)
    (application : Vars common (List.replicate arity signature))
    (site : (recordingOperation
      (Leaf.Identity.operation signature arity) originalArguments).SiteData
        frame PUnit.unit application) :
    HostedScope
      ((recordingOperation
        (Leaf.Identity.operation signature arity) originalArguments).site
          frame PUnit.unit application site)
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) application) := by
  rcases site with ⟨⟨identityPorts, applicationEq⟩, recordedApplication⟩
  subst application
  have targetEq :
      (recordingOperation
        (Leaf.Identity.operation signature arity) originalArguments).site
          frame PUnit.unit (Leaf.Identity.Vars.fromFn identityPorts)
          ⟨⟨identityPorts, rfl⟩, recordedApplication⟩ =
        positionalIdentityApplication signature arity
          (Leaf.Identity.Vars.fromFn identityPorts) := by
    change Region.singleton (.identity signature arity
      (fun position => frame.targetKeep (identityPorts position))) = _
    rw [targetKeepEq]
    simp [positionalIdentityApplication, WireRenaming.id,
      Leaf.Identity.Vars.toFn_fromFn]
  rw [targetEq]
  intro target rename
  let retained := Leaf.Identity.Vars.fromFn identityPorts
  let mapped := retained.map fun wire => rename wire
  have sourceEq :
      (positionalIdentityApplication signature arity retained).renameWires
          rename =
        positionalIdentityApplication signature arity mapped := by
    simp [retained, mapped, positionalIdentityApplication,
      Region.singleton_renameWires, Item.renameWires]
  have targetEq :
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) retained).renameWires
          rename =
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) mapped := by
    exact EqualityNormalization.instantiate_renameWires
      (positionalIdentityPattern signature arity) retained rename
  rw [sourceEq, targetEq]
  exact positionalIdentityApplication_scope signature arity mapped

end VisualProof.Rule.Completeness.Comprehension
