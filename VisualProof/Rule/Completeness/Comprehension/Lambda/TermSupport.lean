import VisualProof.Rule.Completeness.Comprehension.Lambda.TermForms
import VisualProof.Rule.Completeness.Comprehension.Leaf.Targets
import VisualProof.Rule.Lambda.TermLeaf

namespace VisualProof.Rule.Completeness.Comprehension.LambdaTerm

open Diagram
open Theory
open WirePrimitive

def supportTermMaterial
    {wires : List Sig} (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota) : Region wires :=
  Region.singleton (.term output freeArity ports term)

theorem supportTermMaterial_canonical
    {wires : List Sig} (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota) :
    (supportTermMaterial freeArity term output ports).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

def supportTermPinsAppended
    {wires : List Sig} (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota) : ItemSeq (wires ++ []) :=
  Erasure.Exposure.supportPins
    (supportTermMaterial freeArity term output ports) wires
    (Erasure.Exposure.identityBoundary wires)

def supportTermTail
    {wires : List Sig} (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota) : ItemSeq wires :=
  (supportTermPinsAppended freeArity term output ports).renameWires
    (WireEquiv.appendNil wires).toRenaming

theorem supportTermTail_appendNil
    {wires : List Sig} (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota) :
    (supportTermTail freeArity term output ports).renameWires
        (WireEquiv.appendNil wires).symm.toRenaming =
      supportTermPinsAppended freeArity term output ports := by
  unfold supportTermTail
  rw [ItemSeq.renameWires_comp]
  have renameEq : WireRenaming.comp
      (WireEquiv.appendNil wires).symm.toRenaming
      (WireEquiv.appendNil wires).toRenaming = WireRenaming.id := by
    apply WireRenaming.ext
    intro wireSignature wire
    exact (WireEquiv.appendNil wires).left_inv wire
  rw [renameEq]
  exact ItemSeq.renameWires_id _

theorem supportTermBody_eq
    {wires : List Sig} (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota) :
    Erasure.Exposure.supportBody
        (supportTermMaterial freeArity term output ports) =
      Region.ofItems (.cons (.term output freeArity ports term)
        (supportTermTail freeArity term output ports)) := by
  unfold Erasure.Exposure.supportBody supportTermMaterial
  simp only [Region.singleton, Region.ofItems, Region.locals, Region.items]
  have pinsEq :
      Erasure.Exposure.supportPins
          (Region.mk [] (ItemSeq.renameWires
            ⟨fun wire => wire.appendLeft []⟩
            (.cons (.term output freeArity ports term) .nil))) wires
          (Erasure.Exposure.identityBoundary wires) =
        supportTermPinsAppended freeArity term output ports := by
    simp [supportTermPinsAppended, supportTermMaterial,
      Region.singleton, Region.ofItems, Region.locals]
  rw [pinsEq]
  rw [← supportTermTail_appendNil freeArity term output ports]
  have appendEq : (⟨fun wire => wire.appendLeft []⟩ :
      WireRenaming wires (wires ++ [])) =
      (WireEquiv.appendNil wires).symm.toRenaming := by
    apply WireRenaming.ext
    intro wireSignature wire
    exact (WireEquiv.appendNil_symm_apply wires wire).symm
  rw [appendEq]
  rfl

theorem positionalTermInstantiation_reverseHostedScope
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (application : Vars wires (Lambda.TermLeaf.arguments freeArity)) :
    HostedScope
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalTermPattern freeArity term) application)
      (positionalTermApplication freeArity term application) := by
  intro target rename
  have sourceEq :
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalTermPattern freeArity term) application).renameWires
          rename =
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term)
          (application.map fun wire => rename wire) := by
    exact EqualityNormalization.instantiate_renameWires
      (positionalTermPattern freeArity term) application rename
  have targetEq :
      (positionalTermApplication freeArity term application).renameWires
          rename =
        positionalTermApplication freeArity term
          (application.map fun wire => rename wire) := by
    simp [positionalTermApplication, Region.singleton_renameWires,
      Item.renameWires, Lambda.TermLeaf.Vars.output_map,
      Lambda.TermLeaf.Vars.ports_map]
  rw [sourceEq, targetEq]
  exact positionalTermInstantiation_scope freeArity term
    (application.map fun wire => rename wire)

/-- A selected support-singleton term is presented directly at its actual
application, without copied boundary locals. -/
theorem supportTermSelectedTargetItem
    {wires itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota)
    {itemFrame : Transform.Frame wires itemCommon itemSourceWires
      itemTargetWires}
    {itemOperation : Transform.Operation wires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon wires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame (Lambda.TermLeaf.arguments freeArity)
      itemCommon formalSourceWires formalTargetWires) :
    TargetItem
      (targetPattern := positionalTermPattern freeArity term)
      (targetOperation := Lambda.TermLeaf.operation freeArity term)
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := Erasure.Exposure.supportPattern
          (supportTermMaterial freeArity term output ports)
          (supportTermMaterial_canonical freeArity term output ports))
        (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := Erasure.Exposure.supportPattern
          (supportTermMaterial freeArity term output ports)
          (supportTermMaterial_canonical freeArity term output ports))
        (frame := itemFrame) application siteData)
      (Lambda.TermLeaf.Vars.fromTerm output ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult _formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (supportTermMaterial freeArity term output ports)
                  (supportTermMaterial_canonical freeArity term output ports))
                application)
              staged ∧
            ScopePreservation
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (supportTermMaterial freeArity term output ports)
                  (supportTermMaterial_canonical freeArity term output ports))
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
    ((supportTermTail freeArity term output ports).renameWires substitution).append
      (mappedPins.append mappedPins)
  let retainedPorts := Lambda.TermLeaf.Vars.fromTerm (substitution output)
    (fun slot => substitution (ports slot))
  let childFrame := formalFrame.append []
  let formalSource := termFormalPrefixSource childFrame hostItems retainedPorts
  let formalResult := termFormalPrefixResult freeArity term hostItems
    retainedPorts
  let formalEvidence := termFormalPrefixEvidence (term := term) childFrame hostItems
    retainedPorts
  let formalSites := termFormalPrefixRecordingSites (term := term) childFrame hostItems
    retainedPorts mappedApplication
  refine ⟨[], formalSource, formalResult, formalEvidence, formalSites, ?_, ?_⟩
  · apply termFormalPrefixSource_eq_argumentItemsEdit (term := term)
      childFrame hostItems retainedPorts mappedApplication
      (Lambda.TermLeaf.Vars.fromTerm output ports)
      substitution
    · exact (EqualityNormalization.formalPorts_map_substitution
        mappedApplication).symm
    · rw [Lambda.TermLeaf.Vars.fromTerm_map]
  · let rawSubstitution := EqualityNormalization.formalSubstitution application
    let rawSupportItems :=
      (supportTermTail freeArity term output ports).renameWires rawSubstitution
    let rawPins := EqualityNormalization.allPins wires rawSubstitution
    let rawHostItems := rawSupportItems.append (rawPins.append rawPins)
    let rawRetainedPorts := Lambda.TermLeaf.Vars.fromTerm
      (rawSubstitution output) (fun slot => rawSubstitution (ports slot))
    let staged := termFormalPrefixResult freeArity term rawHostItems
      rawRetainedPorts
    refine ⟨staged, ?_, ?_, ?_, rfl, ?_⟩
    · let material := supportTermMaterial freeArity term output ports
      let materialCanonical := supportTermMaterial_canonical freeArity term
        output ports
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
      let direct := positionalTermApplication freeArity term
        rawRetainedPorts
      have directItemEq : direct = Region.singleton
          (.term (rawSubstitution output) freeArity
            (fun slot => rawSubstitution (ports slot)) term) := by
        unfold direct positionalTermApplication rawRetainedPorts
        simp
      have supportedTargetEq : supported.renameWires rawSubstitution =
          Region.ofItems (.cons
            (.term (rawSubstitution output) freeArity
              (fun slot => rawSubstitution (ports slot)) term)
            rawSupportItems) := by
        change (Erasure.Exposure.supportBody
          (supportTermMaterial freeArity term output ports)).renameWires
            rawSubstitution = _
        rw [supportTermBody_eq freeArity term output ports]
        simp only [Region.renameWires, Region.ofItems, ItemSeq.renameWires,
          Item.renameWires, rawSupportItems]
        simp [WireRenaming.appendRight, ItemSeq.renameWires_comp]
        apply congrArg (fun rename =>
          (supportTermTail freeArity term output ports).renameWires rename)
        apply WireRenaming.ext
        intro wireSignature wire
        simp [WireRenaming.comp]
      let supportPins := Region.ofItems rawSupportItems
      let allPins := Region.ofItems (rawPins.append rawPins)
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) rawRetainedPorts
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (direct.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          ((RegionIso.ofEq (Region.singleton_conjoin_ofItems
            (.term (rawSubstitution output) freeArity
              (fun slot => rawSubstitution (ports slot)) term)
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
          (positionalTermMaterial freeArity term)
          (positionalTermMaterial_canonical freeArity term)
          rawRetainedPorts
        change HostedStrict positional
          ((positionalTermMaterial freeArity term).renameWires
            (EqualityNormalization.formalSubstitution rawRetainedPorts)) at exposed
        rw [positionalTermMaterial_rename] at exposed
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
            (positionalTermInstantiation_reverseHostedScope freeArity term
              rawRetainedPorts rename)
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
              (termFormalPrefixResultIso freeArity term rawHostItems
                rawRetainedPorts).symm))
      exact HostedStrict.iso (RegionIso.conjoinBlank source).symm
        resultPresentation pinned
    · let material := supportTermMaterial freeArity term output ports
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
          (supportTermMaterial_canonical freeArity term output ports)
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
              (supportTermMaterial_canonical freeArity term output ports))
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
                    (supportTermMaterial freeArity term output ports)
                    ).renameWires rawSubstitution).incidencePaths
                      wire.index.val = []
                  rw [supportTermBody_eq freeArity term output ports,
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
                  (supportTermMaterial_canonical freeArity term output ports))
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
      let direct := positionalTermApplication freeArity term
        rawRetainedPorts
      have directItemEq : direct = Region.singleton
          (.term (rawSubstitution output) freeArity
            (fun slot => rawSubstitution (ports slot)) term) := by
        unfold direct positionalTermApplication rawRetainedPorts
        simp
      have supportedTargetEq : supported.renameWires rawSubstitution =
          Region.ofItems (.cons
            (.term (rawSubstitution output) freeArity
              (fun slot => rawSubstitution (ports slot)) term)
            rawSupportItems) := by
        change (Erasure.Exposure.supportBody
          (supportTermMaterial freeArity term output ports)).renameWires
            rawSubstitution = _
        rw [supportTermBody_eq freeArity term output ports]
        simp only [Region.renameWires, Region.ofItems, ItemSeq.renameWires,
          Item.renameWires, rawSupportItems]
        simp [WireRenaming.appendRight, ItemSeq.renameWires_comp]
        apply congrArg (fun rename =>
          (supportTermTail freeArity term output ports).renameWires rename)
        apply WireRenaming.ext
        intro wireSignature wire
        simp [WireRenaming.comp]
      let supportPins := Region.ofItems rawSupportItems
      let allPins := pinRegion
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) rawRetainedPorts
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (direct.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          ((RegionIso.ofEq (Region.singleton_conjoin_ofItems
            (.term (rawSubstitution output) freeArity
              (fun slot => rawSubstitution (ports slot)) term)
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
            (positionalTermApplication_scope freeArity term
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
              (termFormalPrefixResultIso freeArity term rawHostItems
                rawRetainedPorts).symm))
      exact sourceToSupportedPins.trans
        (supportedToDirectPins.trans
          (directToPositionalPins.trans
            (ScopePreservation.ofIso resultPresentation)))
    · have mappedResultEq : staged.renameWires commonAppend = formalResult := by
        rw [termFormalPrefixResult_renameWires]
        have hostItemsEq : rawHostItems.renameWires commonAppend = hostItems := by
          have substitutionEq :
              WireRenaming.comp commonAppend rawSubstitution = substitution := by
            apply WireRenaming.ext
            intro wireSignature wire
            exact (EqualityNormalization.formalSubstitution_map
              application commonAppend wire).symm
          have supportItemsEq : rawSupportItems.renameWires commonAppend =
              (supportTermTail freeArity term output ports).renameWires
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
          rw [Lambda.TermLeaf.Vars.fromTerm_map]
          congr 1
          · exact (EqualityNormalization.formalSubstitution_map
              application commonAppend output).symm
          · funext slot
            exact (EqualityNormalization.formalSubstitution_map
              application commonAppend (ports slot)).symm
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
        termFormalPrefixArgumentItemsEdit_source (term := term) childFrame
          (authoritativeFrame.append []) hostItems retainedPorts
          mappedApplication (EqualityNormalization.formalPorts wires)
      change
        let direct := Region.singleton (.atom itemFrame.selected
          (application.map fun wire => itemFrame.sourceKeep wire))
        let authoritative := Region.adjoinAt [] .nil
          (Region.ofItems
            (argumentItemsEdit
              (termFormalPrefixRecordingSites childFrame hostItems
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
        ((supportTermTail freeArity term output ports).renameWires
          targetSubstitution)
      let pins := EqualityNormalization.allPins wires targetSubstitution
      let allPins := Region.ofItems (pins.append pins)
      let material := supportTermMaterial freeArity term output ports
      have supportStep : HostedStrict (Region.blank itemSourceWires)
          supportPins := by
        have base : HostedStrict (Region.blank wires)
            (Region.ofItems (supportTermTail freeArity term output ports)) := by
          apply HostedStrict.specialize
            (HostedStrict.supportPins material
              (Erasure.Exposure.identityBoundary wires))
            (WireEquiv.appendNil wires).toRenaming
          · change (Region.blank (wires ++ [])).renameWires
                (WireEquiv.appendNil wires).toRenaming =
              Region.blank wires
            rfl
          · unfold material supportTermMaterial
            rw [Region.ofItems_renameWires]
            simp [supportTermTail, supportTermPinsAppended,
              supportTermMaterial] <;> rfl
        apply HostedStrict.specialize base targetSubstitution
        · rfl
        · unfold supportPins
          exact Region.ofItems_renameWires
            (supportTermTail freeArity term output ports) targetSubstitution
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
              ((supportTermTail freeArity term output ports).renameWires
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
            (((supportTermTail freeArity term output ports).renameWires
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
              (supportTermTail freeArity term output ports)).Canonical := by
          constructor
          · intro localIndex
            exact Fin.elim0 localIndex
          · unfold supportTermTail supportTermPinsAppended
            exact (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
              ((ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
                (Erasure.Exposure.supportPins_childrenCanonical
                  (supportTermMaterial freeArity term output ports)
                  (Erasure.Exposure.identityBoundary wires)))
        simpa only [supportPins, Region.ofItems_renameWires] using
          (Region.Canonical.renameWires_iff
            (Region.ofItems (supportTermTail freeArity term output ports))
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
                  (supportTermTail freeArity term output ports)
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

/-- The positional term operation target can always be re-expanded to its
pattern instantiation when the operation retains the common wires literally. -/
theorem positionalTermLeafEndpoint_reverseHostedScope
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    {originalArguments common sourceWires : List Sig}
    {frame : Transform.Frame (Lambda.TermLeaf.arguments freeArity) common
      sourceWires common}
    (targetKeepEq : frame.targetKeep = WireRenaming.id)
    (application : Vars common (Lambda.TermLeaf.arguments freeArity))
    (site : (recordingOperation
      (Lambda.TermLeaf.operation freeArity term) originalArguments).SiteData
        frame PUnit.unit application) :
    HostedScope
      ((recordingOperation
        (Lambda.TermLeaf.operation freeArity term) originalArguments).site
          frame PUnit.unit application site)
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalTermPattern freeArity term) application) := by
  rcases site with ⟨⟨⟨termOutput, termPorts⟩, applicationEq⟩,
    recordedApplication⟩
  subst application
  have targetEq :
      (recordingOperation
        (Lambda.TermLeaf.operation freeArity term) originalArguments).site
          frame PUnit.unit (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts)
          ⟨⟨⟨termOutput, termPorts⟩, rfl⟩, recordedApplication⟩ =
        positionalTermApplication freeArity term
          (Lambda.TermLeaf.Vars.fromTerm termOutput termPorts) := by
    change Region.singleton (.term (frame.targetKeep termOutput) freeArity
      (fun slot => frame.targetKeep (termPorts slot)) term) = _
    rw [targetKeepEq]
    simp [positionalTermApplication, WireRenaming.id,
      Lambda.TermLeaf.Vars.output_fromTerm,
      Lambda.TermLeaf.Vars.ports_fromTerm]
  rw [targetEq]
  intro target rename
  let retained := Lambda.TermLeaf.Vars.fromTerm termOutput termPorts
  let mapped := retained.map fun wire => rename wire
  have sourceEq :
      (positionalTermApplication freeArity term retained).renameWires
          rename =
        positionalTermApplication freeArity term mapped := by
    simp [retained, mapped, positionalTermApplication,
      Region.singleton_renameWires, Item.renameWires]
  have targetEq :
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalTermPattern freeArity term) retained).renameWires
          rename =
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalTermPattern freeArity term) mapped := by
    exact EqualityNormalization.instantiate_renameWires
      (positionalTermPattern freeArity term) retained rename
  rw [sourceEq, targetEq]
  exact positionalTermApplication_scope freeArity term mapped

end VisualProof.Rule.Completeness.Comprehension.LambdaTerm
