import VisualProof.Rule.Completeness.Comprehension.Leaf.Forms

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- Present one selected application of an authoritative identity-headed
pattern as the literal positional IdentityLeaf edit, retaining every sibling
and equality item in the same site. -/
theorem accumulateSelectedIdentity
    {patternArguments outer hostLocals : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternArguments}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    (outerHostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternArguments)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals outerHostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)) host) :
    let common := outer ++ hostLocals
    let retainedLocals := EqualityNormalization.locals pattern
    let frame := Leaf.Identity.rootFrame common [] retainedLocals signature arity
    let hostItems := atomSiteHostItems pattern tail application
    let retained : Vars (common ++ retainedLocals)
        (List.replicate arity signature) :=
      Leaf.Identity.Vars.fromFn
        (fun position => atomBodyWire pattern common (ports position))
    let formalResult := identityFormalPrefixResult signature arity hostItems
      retained
    let formalEvidence := identityFormalPrefixEvidence frame hostItems retained
    let formalSites := identityFormalPrefixSites frame hostItems retained
    let output := itemsEdit
      (operation := Leaf.Identity.operation signature arity)
      PUnit.unit formalEvidence formalSites
    ∃ stagedCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals outerHostItems
            (Region.adjoinAt retainedLocals .nil formalResult))).Canonical,
      ∃ stagedExternalTwoEnded :
          OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
            (occurrence.context.fill
              (Region.adjoinAt hostLocals outerHostItems
                (Region.adjoinAt retainedLocals .nil formalResult))),
        EqualityNormalization.StrictEquates occurrence
            (Region.adjoinAt hostLocals outerHostItems
              (Region.adjoinAt retainedLocals .nil formalResult))
            stagedCanonical stagedExternalTwoEnded ∧
          ∃ outputCanonical :
              (occurrence.context.fill
                (Region.adjoinAt hostLocals outerHostItems
                  (Region.adjoinAt retainedLocals .nil output.endpoint))).Canonical,
            ∃ outputExternalTwoEnded :
                OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
                  (occurrence.context.fill
                    (Region.adjoinAt hostLocals outerHostItems
                      (Region.adjoinAt retainedLocals .nil output.endpoint))),
              EqualityNormalization.StrictEquates
                (exactOccurrence occurrence.interface occurrence.context
                  (Region.adjoinAt hostLocals outerHostItems
                    (Region.adjoinAt retainedLocals .nil formalResult))
                  stagedCanonical stagedExternalTwoEnded)
                (Region.adjoinAt hostLocals outerHostItems
                  (Region.adjoinAt retainedLocals .nil output.endpoint))
                outputCanonical outputExternalTwoEnded := by
  let common := outer ++ hostLocals
  let retainedLocals := EqualityNormalization.locals pattern
  let frame := Leaf.Identity.rootFrame common [] retainedLocals signature arity
  let hostItems := atomSiteHostItems pattern tail application
  let retained : Vars (common ++ retainedLocals)
      (List.replicate arity signature) :=
    Leaf.Identity.Vars.fromFn
      (fun position => atomBodyWire pattern common (ports position))
  let direct := positionalIdentityApplication signature arity retained
  let positional :=
    VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) retained
  let formalResult := identityFormalPrefixResult signature arity hostItems
    retained
  let formalEvidence := identityFormalPrefixEvidence frame hostItems retained
  let formalSites := identityFormalPrefixSites frame hostItems retained
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit formalEvidence formalSites
  let sourceIso := identitySelectedSourceIso body_eq application
  let hostedSourceIso := RegionIso.adjoinAt hostLocals outerHostItems sourceIso
  let nestedDirect := Region.adjoinAt hostLocals outerHostItems
    (Region.adjoinAt retainedLocals hostItems direct)
  let nestedPositional := Region.adjoinAt hostLocals outerHostItems
    (Region.adjoinAt retainedLocals hostItems positional)
  have originalLocalCanonical := occurrence.context.holeCanonical _
    occurrence.sourceCanonical
  have nestedDirectCanonical := hostedSourceIso.canonical_iff.mp
    originalLocalCanonical
  have materialScopeForward := positionalIdentityInstantiation_scope
    signature arity retained
  have materialScope : ScopePreservation direct positional := {
    canonical := fun _ =>
      VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        (positionalIdentityPattern signature arity) retained
    incidenceNonempty := fun wire =>
      (materialScopeForward.incidenceNonempty wire).symm
    rootedTwo := fun wire sourceRoot => by
      rw [EqualityNormalization.instantiate_rootedTwo_iff]
      rw [← positionalIdentityApplication_incidencePaths_length]
      exact sourceRoot.1
  }
  have innerScope := adjoinAt_preserves_scope retainedLocals hostItems direct
    positional materialScope
  have nestedScope := adjoinAt_preserves_scope hostLocals outerHostItems
    (Region.adjoinAt retainedLocals hostItems direct)
    (Region.adjoinAt retainedLocals hostItems positional) innerScope
  have nestedPositionalCanonical := nestedScope.canonical nestedDirectCanonical
  have originalNestedScope : ScopePreservation
      (Region.adjoinAt hostLocals outerHostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)) nestedPositional :=
    {
      canonical := fun canonical =>
        nestedScope.canonical (hostedSourceIso.canonical_iff.mp canonical)
      incidenceNonempty := fun wire => by
        have sourceIsoNonempty :
            (Region.adjoinAt hostLocals outerHostItems
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern application)).incidencePaths wire.index.val ≠ [] ↔
              nestedDirect.incidencePaths wire.index.val ≠ [] := by
          have lengthEq := hostedSourceIso.incidencePaths_length_eq wire
          rw [← List.length_pos_iff, ← List.length_pos_iff, lengthEq]
        exact sourceIsoNonempty.trans (nestedScope.incidenceNonempty wire)
      rootedTwo := fun wire rooted =>
        nestedScope.rootedTwo wire
          ((hostedSourceIso.rootedTwo_incidencePaths_iff wire).mp rooted)
    }
  have nestedReplacement := occurrence.context.replaceCanonical _ _
    occurrence.sourceCanonical nestedPositionalCanonical
    (fun wire => originalNestedScope.incidenceNonempty wire)
  let originalEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (Region.adjoinAt hostLocals outerHostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application))) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have nestedPositionalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill nestedPositional) :=
    originalEndpoint.externalTwoEnded_of_nonempty_iff _ nestedReplacement.2
  let leading : Region (outer ++ hostLocals) :=
    .mk retainedLocals hostItems
  let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals retainedLocals
  let flatHostItems := Region.extendHostItems hostLocals outerHostItems leading
  let flatRetained := retained.map fun wire => assoc wire
  let flatDirect := Region.adjoinAt (hostLocals ++ retainedLocals)
    flatHostItems
    (positionalIdentityApplication signature arity flatRetained)
  let flatPositional := Region.adjoinAt (hostLocals ++ retainedLocals)
    flatHostItems
    (VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) flatRetained)
  let directAssoc : RegionIso (WireEquiv.refl outer) flatDirect nestedDirect := by
    let associated := RegionIso.adjoinAtAssoc hostLocals outerHostItems
      retainedLocals hostItems direct
    have renamedEq : direct.renameWires assoc.toRenaming =
        positionalIdentityApplication signature arity flatRetained := by
      simp only [direct, flatRetained, positionalIdentityApplication,
        Region.singleton_renameWires, Item.renameWires,
        Leaf.Identity.Vars.toFn_map]
    exact (RegionIso.ofEq (congrArg
      (fun material => Region.adjoinAt (hostLocals ++ retainedLocals)
        flatHostItems material) renamedEq.symm)).trans associated
  let positionalAssoc : RegionIso (WireEquiv.refl outer)
      flatPositional nestedPositional := by
    let associated := RegionIso.adjoinAtAssoc hostLocals outerHostItems
      retainedLocals hostItems positional
    have renamedEq : positional.renameWires assoc.toRenaming =
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) flatRetained := by
      simpa only [positional, flatRetained] using
        EqualityNormalization.instantiate_renameWires
          (positionalIdentityPattern signature arity) retained
            assoc.toRenaming
    exact (RegionIso.ofEq (congrArg
      (fun material => Region.adjoinAt (hostLocals ++ retainedLocals)
        flatHostItems material) renamedEq.symm)).trans associated
  let originalToFlatDirect := hostedSourceIso.trans directAssoc.symm
  have flatDirectCanonical := originalToFlatDirect.canonical_iff.mp
    originalLocalCanonical
  have flatDirectNonempty : ∀ {wireSignature}
      (wire : Var outer wireSignature),
      (Region.adjoinAt hostLocals outerHostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application)).incidencePaths wire.index.val ≠ [] ↔
        flatDirect.incidencePaths wire.index.val ≠ [] := by
    intro wireSignature wire
    have lengthEq := originalToFlatDirect.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let flatOccurrence := EqualityNormalization.presentationOccurrence occurrence
    flatDirectCanonical flatDirectNonempty originalToFlatDirect
  have flatPositionalCanonical := positionalAssoc.canonical_iff.mpr
    nestedPositionalCanonical
  have flatPositionalReplacement := flatOccurrence.context.replaceCanonical
    flatDirect flatPositional flatOccurrence.sourceCanonical
      flatPositionalCanonical (fun wire => by
        have directToNested := directAssoc.incidencePaths_length_eq wire
        have positionalToNested := positionalAssoc.incidencePaths_length_eq wire
        exact ⟨fun nonempty => by
          have nestedNonempty : nestedDirect.incidencePaths wire.index.val ≠ [] := by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← directToNested]
          have targetNonempty := (nestedScope.incidenceNonempty wire).mp
            nestedNonempty
          rw [← List.length_pos_iff] at targetNonempty ⊢
          rwa [positionalToNested], fun nonempty => by
          have nestedNonempty : nestedPositional.incidencePaths wire.index.val ≠ [] := by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← positionalToNested]
          have sourceNonempty := (nestedScope.incidenceNonempty wire).mpr
            nestedNonempty
          rw [← List.length_pos_iff] at sourceNonempty ⊢
          rwa [directToNested]⟩)
  have flatPositionalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      flatOccurrence.interface.boundaryWire
      (flatOccurrence.context.fill flatPositional) := by
    let flatSourceEndpoint := flatOccurrence.interface.withBody
      (flatOccurrence.context.fill flatDirect) flatOccurrence.sourceCanonical
        flatOccurrence.sourceExternalTwoEnded
    intro signature wire
    exact flatSourceEndpoint.externalTwoEnded_of_nonempty_iff _
      flatPositionalReplacement.2 wire
  have core := equatesPositionalIdentityApplication signature arity
    flatRetained flatOccurrence flatPositionalReplacement.1
      flatPositionalExternalTwoEnded
  let formalIso := identityFormalSelectedResultIso
    (pattern := pattern) (ports := ports) tail application
  let hostedFormalIso := RegionIso.adjoinAt hostLocals outerHostItems formalIso
  let flatToStaged := positionalAssoc.trans hostedFormalIso.symm
  have stagedCanonical := flatToStaged.canonical_iff.mp
    flatPositionalCanonical
  have stagedReplacement := flatOccurrence.context.replaceCanonical
    flatPositional
    (Region.adjoinAt hostLocals outerHostItems
      (Region.adjoinAt retainedLocals .nil formalResult))
    flatPositionalReplacement.1 stagedCanonical (fun wire => by
      have lengthEq := flatToStaged.incidencePaths_length_eq wire
      exact ⟨fun nonempty => by
        rw [← List.length_pos_iff] at nonempty ⊢
        rwa [← lengthEq], fun nonempty => by
        rw [← List.length_pos_iff] at nonempty ⊢
        rwa [lengthEq]⟩)
  have stagedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      flatOccurrence.interface.boundaryWire
      (flatOccurrence.context.fill
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil formalResult))) := by
    let flatPositionalEndpoint := flatOccurrence.interface.withBody
      (flatOccurrence.context.fill flatPositional)
      flatPositionalReplacement.1 flatPositionalExternalTwoEnded
    intro signature wire
    exact flatPositionalEndpoint.externalTwoEnded_of_nonempty_iff _
      stagedReplacement.2 wire
  let stagedOpenIso := OpenDiagram.withBody_iso
    flatPositionalReplacement.1 stagedReplacement.1
    flatPositionalExternalTwoEnded stagedExternalTwoEnded
    (DiagramContext.fillIso flatOccurrence.context flatToStaged)
  have stagedStrictDirect := EqualityNormalization.StrictEquates.targetIso
    core stagedOpenIso
  have stagedStrict : EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil formalResult))
      stagedReplacement.1 stagedExternalTwoEnded := by
    simpa only [EqualityNormalization.StrictEquates, flatOccurrence,
      EqualityNormalization.presentationOccurrence] using stagedStrictDirect
  have outputEq : output.endpoint =
      identityFormalPrefixEndpoint signature arity hostItems retained := by
    have identity : frame.targetKeep = WireRenaming.id := by
        apply WireRenaming.ext
        intro wireSignature wire
        apply Var.appendCases (left := common) (right := retainedLocals)
          (motive := fun wire => frame.targetKeep wire = WireRenaming.id wire)
        · intro inheritedSignature inherited
          simp [frame, Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
        · intro localSignature localWire
          simp [frame, Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
            Var.appendMap, Var.appendRight]
    have endpoint := identityFormalPrefixItemsEditEndpoint signature arity frame
      hostItems retained
    rw [identity] at endpoint
    exact endpoint.trans (Region.renameWires_id _)
  let outputEndpointIso : RegionIso
      (WireEquiv.refl (common ++ retainedLocals)) output.endpoint
      ((Region.ofItems hostItems).conjoin direct) :=
    (RegionIso.ofEq outputEq).trans
      (identityFormalPrefixEndpointIso signature arity hostItems retained)
  let outputLocalIso : RegionIso (WireEquiv.refl common)
      (Region.adjoinAt retainedLocals .nil output.endpoint)
      (Region.adjoinAt retainedLocals hostItems direct) :=
    (RegionIso.adjoinAt retainedLocals .nil outputEndpointIso).trans
      (RegionIso.ofEq
        (adjoinAt_hostedMaterial retainedLocals hostItems direct).symm)
  let hostedOutputIso := RegionIso.adjoinAt hostLocals outerHostItems
    outputLocalIso
  let originalOutputIso : RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt hostLocals outerHostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application))
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil output.endpoint)) :=
    hostedSourceIso.trans hostedOutputIso.symm
  have outputCanonical := originalOutputIso.canonical_iff.mp
    originalLocalCanonical
  have outputReplacement := occurrence.context.replaceCanonical _ _
    occurrence.sourceCanonical outputCanonical (fun wire => by
      have lengthEq := originalOutputIso.incidencePaths_length_eq wire
      exact ⟨fun nonempty => by
        rw [← List.length_pos_iff] at nonempty ⊢
        rwa [← lengthEq], fun nonempty => by
        rw [← List.length_pos_iff] at nonempty ⊢
        rwa [lengthEq]⟩)
  have outputExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil output.endpoint))) :=
    originalEndpoint.externalTwoEnded_of_nonempty_iff _ outputReplacement.2
  let exactOutputOpenIso : OpenDiagramIso
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals outerHostItems
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              pattern application)))
        occurrence.sourceCanonical occurrence.sourceExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals outerHostItems
            (Region.adjoinAt retainedLocals .nil output.endpoint)))
        outputReplacement.1 outputExternalTwoEnded) :=
    OpenDiagram.withBody_iso occurrence.sourceCanonical outputReplacement.1
      occurrence.sourceExternalTwoEnded outputExternalTwoEnded
      (DiagramContext.fillIso occurrence.context originalOutputIso)
  let originalOutputOpenIso : OpenDiagramIso host
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals outerHostItems
            (Region.adjoinAt retainedLocals .nil output.endpoint)))
        outputReplacement.1 outputExternalTwoEnded) :=
    occurrence.host_iso.trans exactOutputOpenIso
  let stagedEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil formalResult)))
    stagedReplacement.1 stagedExternalTwoEnded
  have outputStrict : EqualityNormalization.StrictEquates
      (exactOccurrence occurrence.interface occurrence.context
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil formalResult))
        stagedReplacement.1 stagedExternalTwoEnded)
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil output.endpoint))
      outputReplacement.1 outputExternalTwoEnded := by
    exact ⟨transGen_iso (OpenDiagramIso.refl stagedEndpoint)
        stagedStrict.2 originalOutputOpenIso,
      transGen_iso originalOutputOpenIso stagedStrict.1
        (OpenDiagramIso.refl stagedEndpoint)⟩
  exact ⟨stagedReplacement.1, stagedExternalTwoEnded, stagedStrict,
    outputReplacement.1, outputExternalTwoEnded, outputStrict⟩

/-- One selected application whose pattern begins with an atom is presented
as literal positional-Formal evidence.  The exact derivation-owned edit
endpoint is retained alongside the strict exposure segment. -/
theorem accumulateSelectedAtomFormal
    {patternArguments atomArguments outer hostLocals : List Sig}
    {pattern : OpenDiagram patternArguments}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    (outerHostItems : ItemSeq (outer ++ hostLocals))
    (application : Vars (outer ++ hostLocals) patternArguments)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals outerHostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)) host) :
    let common := outer ++ hostLocals
    let retainedLocals := EqualityNormalization.locals pattern
    let frame := Leaf.Formal.rootFrame common [] retainedLocals []
      atomArguments
    let hostItems := atomSiteHostItems pattern tail application
    let formal : Var (common ++ retainedLocals) (.rel atomArguments) :=
      atomBodyWire pattern common head
    let retainedPorts : Vars (common ++ retainedLocals) atomArguments :=
      ports.map fun wire => atomBodyWire pattern common wire
    let formalSource := atomFormalPrefixSource frame hostItems formal
      retainedPorts
    let formalResult := atomFormalPrefixResult hostItems formal retainedPorts
    let formalEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (positionalAtomPattern atomArguments) frame.sourceKeep frame.selected
          formalSource formalResult :=
      atomFormalPrefixEvidence frame hostItems formal retainedPorts
    let formalSites := atomFormalPrefixSites frame hostItems formal retainedPorts
    let output := itemsEdit
      (operation := Leaf.Formal.operation [] atomArguments)
      PUnit.unit formalEvidence formalSites
    ∃ stagedCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals outerHostItems
            (Region.adjoinAt retainedLocals .nil formalResult))).Canonical,
      ∃ stagedExternalTwoEnded :
          OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (Region.adjoinAt hostLocals outerHostItems
                (Region.adjoinAt retainedLocals .nil formalResult))),
        EqualityNormalization.StrictEquates occurrence
            (Region.adjoinAt hostLocals outerHostItems
              (Region.adjoinAt retainedLocals .nil formalResult))
            stagedCanonical stagedExternalTwoEnded ∧
          ∃ outputCanonical :
              (occurrence.context.fill
                (Region.adjoinAt hostLocals outerHostItems
                  (Region.adjoinAt retainedLocals .nil
                    output.endpoint))).Canonical,
            ∃ outputExternalTwoEnded :
                OpenDiagram.ExternalTwoEnded
                  occurrence.interface.boundaryWire
                  (occurrence.context.fill
                    (Region.adjoinAt hostLocals outerHostItems
                      (Region.adjoinAt retainedLocals .nil
                        output.endpoint))),
              EqualityNormalization.StrictEquates
                (exactOccurrence occurrence.interface
                  occurrence.context
                  (Region.adjoinAt hostLocals outerHostItems
                    (Region.adjoinAt retainedLocals .nil formalResult))
                  stagedCanonical stagedExternalTwoEnded)
                (Region.adjoinAt hostLocals outerHostItems
                  (Region.adjoinAt retainedLocals .nil output.endpoint))
                outputCanonical outputExternalTwoEnded := by
  let common := outer ++ hostLocals
  let retainedLocals := EqualityNormalization.locals pattern
  let frame := Leaf.Formal.rootFrame common [] retainedLocals [] atomArguments
  let hostItems := atomSiteHostItems pattern tail application
  let formal : Var (common ++ retainedLocals) (.rel atomArguments) :=
    atomBodyWire pattern common head
  let retainedPorts : Vars (common ++ retainedLocals) atomArguments :=
    ports.map fun wire => atomBodyWire pattern common wire
  let direct : Region (common ++ retainedLocals) :=
    Region.singleton (.atom formal retainedPorts)
  let positional : Region (common ++ retainedLocals) :=
    VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalAtomPattern atomArguments) (.cons formal retainedPorts)
  let formalSource := atomFormalPrefixSource frame hostItems formal
    retainedPorts
  let formalResult := atomFormalPrefixResult hostItems formal retainedPorts
  let formalEvidence := atomFormalPrefixEvidence frame hostItems formal
    retainedPorts
  let formalSites := atomFormalPrefixSites frame hostItems formal retainedPorts
  let output := itemsEdit
    (operation := Leaf.Formal.operation [] atomArguments)
    PUnit.unit formalEvidence formalSites
  let raw := atomExposureDescription (head := head) (ports := ports)
    tail application
  let combinedRaw := atomExposureDescriptionWithHost
    (head := head) (ports := ports) tail hostLocals outerHostItems application
  let description := atomPinnedExposureDescriptionWithHost
    (head := head) (ports := ports) tail hostLocals outerHostItems application
  have rawSourceEq : raw.source =
      Region.adjoinAt retainedLocals hostItems direct := by
    simp only [raw, Rule.UncappedErasure.Description.source, Region.spliceAt,
      atomExposureDescription, retainedLocals, hostItems, direct]
    exact congrArg
      (fun material => Region.adjoinAt
        (EqualityNormalization.locals pattern)
        (atomSiteHostItems pattern tail application) material)
      (by
        simpa only [atomExposureDescription, formal, retainedPorts] using
          atomExposureMaterialRename tail application)
  let rawSourceIso := atomExposureSourceIso body_eq application
  let directSourceIso : RegionIso (WireEquiv.refl common)
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application)
      (Region.adjoinAt retainedLocals hostItems direct) :=
    rawSourceIso.symm.trans (RegionIso.ofEq rawSourceEq)
  have originalHostedCanonical :
      (Region.adjoinAt hostLocals outerHostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)).Canonical :=
    occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have originalLocalCanonical :
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application).Canonical :=
    Region.Canonical.material_of_adjoinAt hostLocals outerHostItems _
      originalHostedCanonical
  have directLocalCanonical :
      (Region.adjoinAt retainedLocals hostItems direct).Canonical :=
    directSourceIso.canonical_iff.mp originalLocalCanonical
  let hostedDirectIso := RegionIso.adjoinAt hostLocals outerHostItems
    directSourceIso
  have directHostedCanonical :
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals hostItems direct)).Canonical :=
    hostedDirectIso.canonical_iff.mp originalHostedCanonical
  have directSameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals outerHostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application)).incidencePaths wire.index.val ≠ [] ↔
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals hostItems direct)).incidencePaths
            wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := hostedDirectIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have materialScope := positionalAtomInstantiation_scope formal retainedPorts
  have exposureScope := adjoinAt_preserves_scope retainedLocals hostItems
    direct positional materialScope
  have hostedExposureScope := adjoinAt_preserves_scope hostLocals
    outerHostItems
    (Region.adjoinAt retainedLocals hostItems direct)
    (Region.adjoinAt retainedLocals hostItems positional) exposureScope
  let combinedSourceIso := atomExposureDescriptionWithHostSourceIso
    body_eq hostLocals outerHostItems application
  have combinedSourceLocalCanonical : combinedRaw.source.Canonical :=
    combinedSourceIso.canonical_iff.mpr originalHostedCanonical
  have combinedSourceSameNonempty : ∀ {signature}
      (wire : Var outer signature),
      (Region.adjoinAt hostLocals outerHostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application)).incidencePaths wire.index.val ≠ [] ↔
        combinedRaw.source.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := combinedSourceIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq]⟩
  let combinedOccurrence := EqualityNormalization.presentationOccurrence
    occurrence combinedSourceLocalCanonical combinedSourceSameNonempty
      combinedSourceIso.symm
  let combinedExposed := Erasure.Exposure.exposedRegion combinedRaw
    (positionalAtomCanonical atomArguments)
  let combinedExposedIso := atomExposureDescriptionWithHostExposedIso
    (head := head) (ports := ports) tail hostLocals outerHostItems application
  have rawExposedEq :
      Erasure.Exposure.exposedRegion raw
          (positionalAtomCanonical atomArguments) =
        Region.adjoinAt retainedLocals hostItems positional := by
    unfold Erasure.Exposure.exposedRegion
    change Region.adjoinAt retainedLocals hostItems
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.singleton (positionalAtomItem atomArguments))
          (positionalAtomCanonical atomArguments))
        (Erasure.Exposure.applicationPorts raw)) =
      Region.adjoinAt retainedLocals hostItems positional
    rw [positionalAtomSupportPattern_eq]
    have portsEq : Erasure.Exposure.applicationPorts raw =
        .cons formal retainedPorts := by
      simpa only [raw, formal, retainedPorts, common] using
        atomExposureApplicationPorts tail application
    rw [portsEq]
    rfl
  let combinedPositionalIso : RegionIso (WireEquiv.refl outer)
      combinedExposed
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals hostItems positional)) :=
    combinedExposedIso.trans
      (RegionIso.adjoinAt hostLocals outerHostItems
        (RegionIso.ofEq rawExposedEq))
  have hostedExposedLocalCanonical :
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals hostItems positional)).Canonical :=
    hostedExposureScope.canonical directHostedCanonical
  have combinedExposedLocalCanonical : combinedExposed.Canonical :=
    combinedPositionalIso.canonical_iff.mpr hostedExposedLocalCanonical
  have combinedTargetSameNonempty : ∀ {signature}
      (wire : Var outer signature),
      combinedRaw.source.incidencePaths wire.index.val ≠ [] ↔
        combinedExposed.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have sourceLength := combinedSourceIso.incidencePaths_length_eq wire
    have directLength := hostedDirectIso.incidencePaths_length_eq wire
    have exposedLength := combinedPositionalIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      have originalNonempty :
          (Region.adjoinAt hostLocals outerHostItems
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              pattern application)).incidencePaths wire.index.val ≠ [] := by
        rw [← List.length_pos_iff] at nonempty ⊢
        rwa [← sourceLength]
      have directNonempty :
          (Region.adjoinAt hostLocals outerHostItems
            (Region.adjoinAt retainedLocals hostItems direct)).incidencePaths
              wire.index.val ≠ [] := (directSameNonempty wire).mp originalNonempty
      have hostedExposedNonempty :=
        (hostedExposureScope.incidenceNonempty wire).mp directNonempty
      rw [← List.length_pos_iff] at hostedExposedNonempty ⊢
      rwa [exposedLength], fun nonempty => by
      have hostedExposedNonempty :
          (Region.adjoinAt hostLocals outerHostItems
            (Region.adjoinAt retainedLocals hostItems positional)).incidencePaths
              wire.index.val ≠ [] := by
        rw [← List.length_pos_iff] at nonempty ⊢
        rwa [← exposedLength]
      have directNonempty :=
        (hostedExposureScope.incidenceNonempty wire).mpr
          hostedExposedNonempty
      have originalNonempty := (directSameNonempty wire).mpr directNonempty
      rw [← List.length_pos_iff] at originalNonempty ⊢
      rwa [sourceLength]⟩
  have combinedReplacement := combinedOccurrence.context.replaceCanonical
    combinedRaw.source combinedExposed combinedOccurrence.sourceCanonical
    combinedExposedLocalCanonical combinedTargetSameNonempty
  have combinedExposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      combinedOccurrence.interface.boundaryWire
      (combinedOccurrence.context.fill combinedExposed) := by
    let combinedSourceEndpoint := combinedOccurrence.interface.withBody
      (combinedOccurrence.context.fill combinedRaw.source)
      combinedOccurrence.sourceCanonical
      combinedOccurrence.sourceExternalTwoEnded
    intro signature wire
    exact combinedSourceEndpoint.externalTwoEnded_of_nonempty_iff _
      combinedReplacement.2 wire
  have descriptionSourceEq : description.source =
      Region.adjoinAt combinedRaw.hostLocals
        (combinedRaw.hostItems.append
          (EqualityNormalization.contextPins outer combinedRaw.hostLocals))
        (combinedRaw.material.renameWires combinedRaw.wireMap) := by
    rfl
  have descriptionTargetEq : description.target =
      Region.mk combinedRaw.hostLocals
        (combinedRaw.hostItems.append
          (EqualityNormalization.contextPins outer combinedRaw.hostLocals)) := by
    rfl
  have descriptionExposedEq :
      ∀ materialCanonical : description.material.Canonical,
        Erasure.Exposure.exposedRegion description materialCanonical =
          Region.adjoinAt combinedRaw.hostLocals
            (combinedRaw.hostItems.append
              (EqualityNormalization.contextPins outer
                combinedRaw.hostLocals))
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              (Erasure.Exposure.supportPattern combinedRaw.material
                (positionalAtomCanonical atomArguments))
              (Erasure.Exposure.applicationPorts combinedRaw)) := by
    intro materialCanonical
    have materialProof : materialCanonical =
        positionalAtomCanonical atomArguments := Subsingleton.elim _ _
    subst materialCanonical
    rfl
  have combinedWiresNonempty : outer ++ combinedRaw.hostLocals ≠ [] := by
    simpa only [combinedRaw, atomExposureDescriptionWithHost,
      List.append_assoc] using
      atomExposureWires_nonempty head (outer ++ hostLocals)
  change Occurrence
    (Region.adjoinAt combinedRaw.hostLocals combinedRaw.hostItems
      (combinedRaw.material.renameWires combinedRaw.wireMap)) host
    at combinedOccurrence
  have combinedStrict := EqualityNormalization.pinnedExposureStrict
    (hostLocals := combinedRaw.hostLocals)
    (hostItems := combinedRaw.hostItems)
    (before := combinedRaw.material.renameWires combinedRaw.wireMap)
    (after :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern combinedRaw.material
          (positionalAtomCanonical atomArguments))
        (Erasure.Exposure.applicationPorts combinedRaw))
    combinedOccurrence combinedReplacement.1
    combinedExposedExternalTwoEnded combinedWiresNonempty description
    descriptionSourceEq descriptionTargetEq descriptionExposedEq
  let formalIso := atomFormalSelectedResultIso
    (pattern := pattern) (head := head) (ports := ports) tail application
  let hostedFormalIso := RegionIso.adjoinAt hostLocals outerHostItems
    formalIso
  let combinedToStagedIso : RegionIso (WireEquiv.refl outer)
      combinedExposed
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil formalResult)) :=
    combinedPositionalIso.trans hostedFormalIso.symm
  have stagedLocalCanonical :
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil formalResult)).Canonical :=
    combinedToStagedIso.canonical_iff.mp combinedExposedLocalCanonical
  have formalSameNonempty : ∀ {signature} (wire : Var outer signature),
      combinedExposed.incidencePaths wire.index.val ≠ [] ↔
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil formalResult)).incidencePaths
            wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := combinedToStagedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have stagedReplacement := combinedOccurrence.context.replaceCanonical
    combinedExposed
    (Region.adjoinAt hostLocals outerHostItems
      (Region.adjoinAt retainedLocals .nil formalResult))
    combinedReplacement.1 stagedLocalCanonical formalSameNonempty
  have stagedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      combinedOccurrence.interface.boundaryWire
      (combinedOccurrence.context.fill
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil formalResult))) := by
    let exposedEndpoint := combinedOccurrence.interface.withBody
      (combinedOccurrence.context.fill combinedExposed)
      combinedReplacement.1 combinedExposedExternalTwoEnded
    intro signature wire
    exact exposedEndpoint.externalTwoEnded_of_nonempty_iff _
      stagedReplacement.2 wire
  let formalOpenIso := OpenDiagram.withBody_iso
    combinedReplacement.1 stagedReplacement.1
    combinedExposedExternalTwoEnded stagedExternalTwoEnded
    (DiagramContext.fillIso combinedOccurrence.context combinedToStagedIso)
  have stagedStrictDirect := EqualityNormalization.StrictEquates.targetIso
    combinedStrict formalOpenIso
  have stagedStrict : EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil formalResult))
      stagedReplacement.1 stagedExternalTwoEnded := by
    simpa only [EqualityNormalization.StrictEquates] using
      stagedStrictDirect
  have outputEndpointEq : output.endpoint =
      atomFormalPrefixEndpoint hostItems formal retainedPorts := by
    have identity : frame.targetKeep = WireRenaming.id := by
      simpa only [frame] using
        formalRootFrame_targetKeep common retainedLocals atomArguments
    have endpoint := atomFormalPrefixItemsEditEndpoint atomArguments frame
      hostItems formal retainedPorts
    rw [identity] at endpoint
    exact endpoint.trans (Region.renameWires_id _)
  let outputEndpointIso : RegionIso
      (WireEquiv.refl (common ++ retainedLocals)) output.endpoint
      ((Region.ofItems hostItems).conjoin direct) :=
    (RegionIso.ofEq outputEndpointEq).trans
      (atomFormalPrefixEndpointIso hostItems formal retainedPorts)
  let outputLocalIso : RegionIso (WireEquiv.refl common)
      (Region.adjoinAt retainedLocals .nil output.endpoint)
      (Region.adjoinAt retainedLocals hostItems direct) :=
    (RegionIso.adjoinAt retainedLocals .nil outputEndpointIso).trans
      (RegionIso.ofEq
        (adjoinAt_hostedMaterial retainedLocals hostItems direct).symm)
  let hostedOutputLocalIso := RegionIso.adjoinAt hostLocals outerHostItems
    outputLocalIso
  let originalOutputIso : RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt hostLocals outerHostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application))
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil output.endpoint)) :=
    hostedDirectIso.trans hostedOutputLocalIso.symm
  have outputLocalCanonical :
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil output.endpoint)).Canonical :=
    originalOutputIso.canonical_iff.mp originalHostedCanonical
  have outputSameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals outerHostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application)).incidencePaths wire.index.val ≠ [] ↔
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil output.endpoint)).incidencePaths
            wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := originalOutputIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have outputReplacement := occurrence.context.replaceCanonical
    (Region.adjoinAt hostLocals outerHostItems
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application))
    (Region.adjoinAt hostLocals outerHostItems
      (Region.adjoinAt retainedLocals .nil output.endpoint))
    occurrence.sourceCanonical outputLocalCanonical outputSameNonempty
  have outputExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil output.endpoint))) := by
    let originalEndpoint := occurrence.interface.withBody
      (occurrence.context.fill
        (Region.adjoinAt hostLocals outerHostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application)))
      occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
    intro signature wire
    exact originalEndpoint.externalTwoEnded_of_nonempty_iff _
      outputReplacement.2 wire
  let outputOpenIso := OpenDiagram.withBody_iso
    occurrence.sourceCanonical outputReplacement.1
    occurrence.sourceExternalTwoEnded outputExternalTwoEnded
    (DiagramContext.fillIso occurrence.context originalOutputIso)
  have outputStrict := EqualityNormalization.StrictEquates.targetIso
    (EqualityNormalization.StrictEquates.refl occurrence) outputOpenIso
  have midpointOutputStrict : EqualityNormalization.StrictEquates
      (exactOccurrence occurrence.interface occurrence.context
        (Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil formalResult))
        stagedReplacement.1 stagedExternalTwoEnded)
      (Region.adjoinAt hostLocals outerHostItems
        (Region.adjoinAt retainedLocals .nil output.endpoint))
      outputReplacement.1 outputExternalTwoEnded := by
    exact ⟨stagedStrict.2.trans outputStrict.1,
      outputStrict.2.trans stagedStrict.1⟩
  exact ⟨stagedReplacement.1, stagedExternalTwoEnded, stagedStrict,
    outputReplacement.1, outputExternalTwoEnded, midpointOutputStrict⟩

/-! Literal Formal evidence is reindexed only along the explicit source and
retained-wire embeddings used when recursive and sibling accumulators are
combined. -/

theorem formalSiteNatural
    {atomArguments common mappedCommon sourceWires mappedSourceWires
      targetWires mappedTargetWires : List Sig}
    {frame : Transform.Frame (positionalAtomWires atomArguments) common
      sourceWires targetWires}
    {mappedFrame : Transform.Frame (positionalAtomWires atomArguments)
      mappedCommon mappedSourceWires mappedTargetWires}
    (commonRename : WireRenaming common mappedCommon)
    (targetRename : WireRenaming targetWires mappedTargetWires)
    (targetKeepCommutes : ∀ {wireSignature}
      (wire : Var common wireSignature),
      targetRename (frame.targetKeep wire) =
        mappedFrame.targetKeep (commonRename wire))
    (ports : Vars common (positionalAtomWires atomArguments))
    (site : (Leaf.Formal.operation [] atomArguments).SiteData frame
      PUnit.unit ports) :
    ∃ mappedSite :
        (Leaf.Formal.operation [] atomArguments).SiteData mappedFrame
          PUnit.unit (ports.map fun wire => commonRename wire),
      Nonempty (RegionIso (WireEquiv.refl mappedTargetWires)
        (((Leaf.Formal.operation [] atomArguments).site frame PUnit.unit
          ports site).renameWires targetRename)
        ((Leaf.Formal.operation [] atomArguments).site mappedFrame PUnit.unit
          (ports.map fun wire => commonRename wire) mappedSite)) := by
  obtain ⟨formal, retained, portsEq⟩ := site
  let mappedFormal := commonRename formal
  let mappedRetained := retained.map fun wire => commonRename wire
  have mappedPortsEq : ports.map (fun wire => commonRename wire) =
      Argument.Projection.Vars.insertAt [] mappedFormal mappedRetained := by
    dsimp only [mappedFormal, mappedRetained]
    rw [portsEq]
    exact Argument.Projection.Vars.insertAt_map [] formal retained commonRename
  let mappedSite :
      (Leaf.Formal.operation [] atomArguments).SiteData mappedFrame
        PUnit.unit (ports.map fun wire => commonRename wire) :=
    ⟨mappedFormal, ⟨mappedRetained, mappedPortsEq⟩⟩
  refine ⟨mappedSite, ⟨?_⟩⟩
  apply RegionIso.ofEq
  simp only [Leaf.Formal.operation, Region.singleton_renameWires,
    Item.renameWires]
  dsimp only [mappedSite, mappedFormal, mappedRetained]
  rw [targetKeepCommutes formal]
  apply congrArg Region.singleton
  apply congrArg (Item.atom (mappedFrame.targetKeep (commonRename formal)))
  calc
    _ = retained.map (fun wire =>
        WireRenaming.comp targetRename frame.targetKeep wire) :=
      Diagram.vars_map_comp retained frame.targetKeep targetRename
    _ = retained.map (fun wire =>
        WireRenaming.comp mappedFrame.targetKeep commonRename wire) := by
      apply congrArg (fun rename : WireRenaming common mappedTargetWires =>
        retained.map fun wire => rename wire)
      apply WireRenaming.ext
      intro signature wire
      exact targetKeepCommutes wire
    _ = _ := (Diagram.vars_map_comp retained commonRename
      mappedFrame.targetKeep).symm

def formalDataNaturality (atomArguments : List Sig) :
    DataNaturality (Leaf.Formal.operation [] atomArguments) where
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
    cases data
    cases mappedData
    exact formalSiteNatural commonRename targetRename targetKeepCommutes
      ports siteData

theorem formalRecordingSiteNatural
    {atomArguments patternArguments common mappedCommon sourceWires
      mappedSourceWires targetWires mappedTargetWires : List Sig}
    {frame : Transform.Frame (positionalAtomWires atomArguments) common
      sourceWires targetWires}
    {mappedFrame : Transform.Frame (positionalAtomWires atomArguments)
      mappedCommon mappedSourceWires mappedTargetWires}
    (commonRename : WireRenaming common mappedCommon)
    (targetRename : WireRenaming targetWires mappedTargetWires)
    (targetKeepCommutes : ∀ {wireSignature}
      (wire : Var common wireSignature),
      targetRename (frame.targetKeep wire) =
        mappedFrame.targetKeep (commonRename wire))
    (ports : Vars common (positionalAtomWires atomArguments))
    (site : (recordingOperation (Leaf.Formal.operation [] atomArguments)
      patternArguments).SiteData frame PUnit.unit ports) :
    ∃ mappedSite :
        (recordingOperation (Leaf.Formal.operation [] atomArguments)
          patternArguments).SiteData mappedFrame PUnit.unit
          (ports.map fun wire => commonRename wire),
      Nonempty (RegionIso (WireEquiv.refl mappedTargetWires)
        (((recordingOperation (Leaf.Formal.operation [] atomArguments)
          patternArguments).site frame PUnit.unit ports site).renameWires
            targetRename)
        ((recordingOperation (Leaf.Formal.operation [] atomArguments)
          patternArguments).site mappedFrame PUnit.unit
            (ports.map fun wire => commonRename wire) mappedSite)) := by
  obtain ⟨formalSite, application⟩ := site
  obtain ⟨mappedFormalSite, ⟨siteIso⟩⟩ :=
    formalSiteNatural commonRename targetRename targetKeepCommutes ports
      formalSite
  exact ⟨⟨mappedFormalSite, application.map fun wire => commonRename wire⟩,
    ⟨siteIso⟩⟩

mutual
  theorem targetRegionReindex
      {arguments external argumentArguments common mappedCommon sourceWires
        mappedSourceWires targetWires mappedTargetWires argumentSourceWires
        mappedArgumentSourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {baseOperation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common
        sourceWires targetWires}
      {mappedFrame : Transform.Frame arguments
        mappedCommon mappedSourceWires mappedTargetWires}
      {data : baseOperation.Data frame}
      {mappedData : baseOperation.Data mappedFrame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep
          frame.selected source result)
      (sites : RegionSites (recordingOperation baseOperation external)
        data evidence)
      (current : Vars external arguments)
      (argumentCurrent : Vars external argumentArguments)
      (argumentFrame : Transform.Frame argumentArguments common
        argumentSourceWires argumentSourceWires)
      (mappedArgumentFrame : Transform.Frame argumentArguments mappedCommon
        mappedArgumentSourceWires mappedArgumentSourceWires)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (targetRename : WireRenaming targetWires mappedTargetWires)
      (argumentSourceRename : WireRenaming argumentSourceWires
        mappedArgumentSourceWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (targetKeepCommutes : ∀ {signature} (wire : Var common signature),
        targetRename (frame.targetKeep wire) =
          mappedFrame.targetKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected)
      (argumentKeepCommutes : ∀ {signature} (wire : Var common signature),
        argumentSourceRename (argumentFrame.sourceKeep wire) =
          mappedArgumentFrame.sourceKeep (commonRename wire))
      (argumentSelectedCommutes : argumentSourceRename argumentFrame.selected =
        mappedArgumentFrame.selected)
      (naturality : DataNaturality baseOperation)
      (dataCoherent : naturality.Coherent frame mappedFrame data mappedData
        commonRename targetRename) :
      ∃ mappedSource : Region mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              VisualProof.Rule.Comprehension.Instantiation.RegionResult
                pattern
                mappedFrame.sourceKeep mappedFrame.selected
                mappedSource mappedResult,
            ∃ mappedSites : RegionSites
                (recordingOperation baseOperation external) mappedData
                mappedEvidence,
              source.renameWires sourceRename = mappedSource ∧
                (argumentRegionEdit sites current
                    (normalizationOperation arguments) frame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename =
                (argumentRegionEdit mappedSites current
                    (normalizationOperation arguments) mappedFrame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1 ∧
                (argumentRegionEdit sites argumentCurrent
                    (normalizationOperation argumentArguments) argumentFrame
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1.renameWires
                    argumentSourceRename =
                  (argumentRegionEdit mappedSites argumentCurrent
                    (normalizationOperation argumentArguments)
                    mappedArgumentFrame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1 ∧
                Nonempty (RegionIso (WireEquiv.refl mappedCommon)
                  (result.renameWires commonRename) mappedResult) ∧
                Nonempty (RegionIso (WireEquiv.refl mappedTargetWires)
                  ((regionEdit
                    (operation := recordingOperation baseOperation external)
                    data evidence sites).endpoint.renameWires targetRename)
                  (regionEdit
                    (operation := recordingOperation baseOperation external)
                    mappedData mappedEvidence mappedSites).endpoint) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult
        childEvidence childSites => by
        have keepMaps : WireRenaming.comp sourceRename frame.sourceKeep =
            WireRenaming.comp mappedFrame.sourceKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact keepCommutes wire
        have targetMaps : WireRenaming.comp targetRename frame.targetKeep =
            WireRenaming.comp mappedFrame.targetKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact targetKeepCommutes wire
        have argumentKeepMaps : WireRenaming.comp argumentSourceRename
              argumentFrame.sourceKeep =
            WireRenaming.comp mappedArgumentFrame.sourceKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact argumentKeepCommutes wire
        have appendedKeep : ∀ {signature}
            (wire : Var (common ++ locals) signature),
            sourceRename.appendRight locals
                ((frame.append locals).sourceKeep wire) =
              (mappedFrame.append locals).sourceKeep
                (commonRename.appendRight locals wire) := by
          intro signature wire
          change sourceRename.appendRight locals
              (frame.sourceKeep.appendRight locals wire) =
            mappedFrame.sourceKeep.appendRight locals
              (commonRename.appendRight locals wire)
          rw [WireRenaming.appendRight_comp_apply,
            WireRenaming.appendRight_comp_apply, keepMaps]
        have appendedSelected :
            sourceRename.appendRight locals
                (frame.append locals).selected =
              (mappedFrame.append locals).selected := by
          simpa only [Transform.Frame.append, WireRenaming.appendRight,
            Var.appendMap_left] using
              congrArg (fun wire => wire.appendLeft locals) selectedCommutes
        have appendedArgumentKeep : ∀ {signature}
            (wire : Var (common ++ locals) signature),
            argumentSourceRename.appendRight locals
                ((argumentFrame.append locals).sourceKeep wire) =
              (mappedArgumentFrame.append locals).sourceKeep
                (commonRename.appendRight locals wire) := by
          intro signature wire
          change argumentSourceRename.appendRight locals
              (argumentFrame.sourceKeep.appendRight locals wire) =
            mappedArgumentFrame.sourceKeep.appendRight locals
              (commonRename.appendRight locals wire)
          rw [WireRenaming.appendRight_comp_apply,
            WireRenaming.appendRight_comp_apply, argumentKeepMaps]
        have appendedArgumentSelected :
            argumentSourceRename.appendRight locals
                (argumentFrame.append locals).selected =
              (mappedArgumentFrame.append locals).selected := by
          simpa only [Transform.Frame.append, WireRenaming.appendRight,
            Var.appendMap_left] using congrArg
              (fun wire => wire.appendLeft locals) argumentSelectedCommutes
        obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
            mappedChildSites, mappedChildSourceEq,
            mappedChildArgumentEq,
            mappedChildSourceArgumentEq,
            ⟨mappedChildIso⟩, ⟨mappedChildEndpointIso⟩⟩ :=
          targetItemsReindex childEvidence childSites current argumentCurrent
            (argumentFrame.append locals) (mappedArgumentFrame.append locals)
            (commonRename.appendRight locals)
            (sourceRename.appendRight locals) (targetRename.appendRight locals)
            (argumentSourceRename.appendRight locals)
            appendedKeep (by
              intro signature wire
              change targetRename.appendRight locals
                  (frame.targetKeep.appendRight locals wire) =
                mappedFrame.targetKeep.appendRight locals
                  (commonRename.appendRight locals wire)
              rw [WireRenaming.appendRight_comp_apply,
                WireRenaming.appendRight_comp_apply, targetMaps])
            appendedSelected appendedArgumentKeep appendedArgumentSelected
            naturality (naturality.append dataCoherent locals)
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            mappedChildEvidence
        let mappedSites : RegionSites
            (recordingOperation baseOperation external) mappedData
            mappedEvidence :=
          RegionSites.mk
            (operation := recordingOperation baseOperation external)
            (data := mappedData) mappedChildSites
        have mappedSourceEq :
            (Region.mk locals items).renameWires sourceRename =
              Region.mk locals mappedChildSource := by
          simpa only [Region.renameWires] using
            congrArg (Region.mk locals) mappedChildSourceEq
        have mappedArgumentEq :
            (Region.mk locals
                (argumentItemsEdit childSites current
                  (normalizationOperation arguments) (frame.append locals)
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1).renameWires
                sourceRename =
              Region.mk locals
                (argumentItemsEdit mappedChildSites current
                  (normalizationOperation arguments)
                  (mappedFrame.append locals) PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1 := by
          simpa only [Region.renameWires] using
            congrArg (Region.mk locals) mappedChildArgumentEq
        have mappedSourceArgumentEq :
            (Region.mk locals
                (argumentItemsEdit childSites argumentCurrent
                  (normalizationOperation argumentArguments)
                  (argumentFrame.append locals) PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1).renameWires
                argumentSourceRename =
              Region.mk locals
                (argumentItemsEdit mappedChildSites argumentCurrent
                  (normalizationOperation argumentArguments)
                  (mappedArgumentFrame.append locals) PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1 := by
          simpa only [Region.renameWires] using
            congrArg (Region.mk locals) mappedChildSourceArgumentEq
        let exposed := RegionIso.renameWiresAdjoinAtNil childResult
          commonRename
        let child := RegionIso.adjoinAt locals .nil mappedChildIso
        let exposedEndpoint := RegionIso.renameWiresAdjoinAtNil
          (itemsEdit
            (operation := recordingOperation baseOperation external)
            (baseOperation.appendData frame data locals)
            childEvidence childSites).endpoint targetRename
        let childEndpoint := RegionIso.adjoinAt locals .nil
          mappedChildEndpointIso
        exact ⟨Region.mk locals mappedChildSource,
          Region.adjoinAt locals .nil mappedChildResult, mappedEvidence,
          mappedSites, mappedSourceEq, mappedArgumentEq,
          mappedSourceArgumentEq,
          ⟨exposed.trans child⟩,
          ⟨exposedEndpoint.trans childEndpoint⟩⟩
  termination_by sizeOf source

  theorem targetItemsReindex
      {arguments external argumentArguments common mappedCommon sourceWires
        mappedSourceWires targetWires mappedTargetWires argumentSourceWires
        mappedArgumentSourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {baseOperation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common
        sourceWires targetWires}
      {mappedFrame : Transform.Frame arguments
        mappedCommon mappedSourceWires mappedTargetWires}
      {data : baseOperation.Data frame}
      {mappedData : baseOperation.Data mappedFrame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep
          frame.selected source result)
      (sites : ItemsSites (recordingOperation baseOperation external)
        data evidence)
      (current : Vars external arguments)
      (argumentCurrent : Vars external argumentArguments)
      (argumentFrame : Transform.Frame argumentArguments common
        argumentSourceWires argumentSourceWires)
      (mappedArgumentFrame : Transform.Frame argumentArguments mappedCommon
        mappedArgumentSourceWires mappedArgumentSourceWires)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (targetRename : WireRenaming targetWires mappedTargetWires)
      (argumentSourceRename : WireRenaming argumentSourceWires
        mappedArgumentSourceWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (targetKeepCommutes : ∀ {signature} (wire : Var common signature),
        targetRename (frame.targetKeep wire) =
          mappedFrame.targetKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected)
      (argumentKeepCommutes : ∀ {signature} (wire : Var common signature),
        argumentSourceRename (argumentFrame.sourceKeep wire) =
          mappedArgumentFrame.sourceKeep (commonRename wire))
      (argumentSelectedCommutes : argumentSourceRename argumentFrame.selected =
        mappedArgumentFrame.selected)
      (naturality : DataNaturality baseOperation)
      (dataCoherent : naturality.Coherent frame mappedFrame data mappedData
        commonRename targetRename) :
      ∃ mappedSource : ItemSeq mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                pattern
                mappedFrame.sourceKeep mappedFrame.selected
                mappedSource mappedResult,
            ∃ mappedSites : ItemsSites
                (recordingOperation baseOperation external) mappedData
                mappedEvidence,
              source.renameWires sourceRename = mappedSource ∧
                (argumentItemsEdit sites current
                    (normalizationOperation arguments) frame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename =
                (argumentItemsEdit mappedSites current
                    (normalizationOperation arguments) mappedFrame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1 ∧
                (argumentItemsEdit sites argumentCurrent
                    (normalizationOperation argumentArguments) argumentFrame
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1.renameWires
                    argumentSourceRename =
                  (argumentItemsEdit mappedSites argumentCurrent
                    (normalizationOperation argumentArguments)
                    mappedArgumentFrame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1 ∧
                Nonempty (RegionIso (WireEquiv.refl mappedCommon)
                  (result.renameWires commonRename) mappedResult) ∧
                Nonempty (RegionIso (WireEquiv.refl mappedTargetWires)
                  ((itemsEdit
                    (operation := recordingOperation baseOperation external)
                    data evidence sites).endpoint.renameWires targetRename)
                  (itemsEdit
                    (operation := recordingOperation baseOperation external)
                    mappedData mappedEvidence mappedSites).endpoint) :=
    match sites with
    | .nil _ => by
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected)
        exact ⟨.nil, Region.blank mappedCommon, mappedEvidence,
          .nil mappedEvidence, rfl, rfl, rfl, ⟨RegionIso.refl _⟩,
          ⟨by
            unfold itemsEdit ExactEdit.refl
            exact RegionIso.refl _⟩⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        obtain ⟨mappedItemSource, mappedItemResult, mappedItemEvidence,
            mappedItemSites, mappedItemSourceEq,
            mappedItemArgumentEq,
            mappedItemSourceArgumentEq,
            ⟨mappedItemIso⟩,
            ⟨mappedItemEndpointIso⟩⟩ :=
          targetItemReindex itemEvidence itemSites current argumentCurrent
            argumentFrame mappedArgumentFrame commonRename sourceRename
            targetRename argumentSourceRename keepCommutes targetKeepCommutes
            selectedCommutes argumentKeepCommutes argumentSelectedCommutes
            naturality dataCoherent
        obtain ⟨mappedTailSource, mappedTailResult, mappedTailEvidence,
            mappedTailSites, mappedTailSourceEq,
            mappedTailArgumentEq,
            mappedTailSourceArgumentEq,
            ⟨mappedTailIso⟩,
            ⟨mappedTailEndpointIso⟩⟩ :=
          targetItemsReindex tailEvidence tailSites current argumentCurrent
            argumentFrame mappedArgumentFrame commonRename sourceRename
            targetRename argumentSourceRename keepCommutes targetKeepCommutes
            selectedCommutes argumentKeepCommutes argumentSelectedCommutes
            naturality dataCoherent
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            mappedItemEvidence mappedTailEvidence
        let mappedSites : ItemsSites
            (recordingOperation baseOperation external) mappedData
            mappedEvidence :=
          .cons mappedItemSites mappedTailSites
        have mappedSourceEq :
            (ItemSeq.cons item tail).renameWires sourceRename =
              .cons mappedItemSource mappedTailSource := by
          simp only [ItemSeq.renameWires, mappedItemSourceEq,
            mappedTailSourceEq]
        have mappedArgumentEq :
            (ItemSeq.cons
                (argumentItemEdit itemSites current
                  (normalizationOperation arguments) frame PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1
                (argumentItemsEdit tailSites current
                  (normalizationOperation arguments) frame PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1).renameWires sourceRename =
              ItemSeq.cons
                (argumentItemEdit mappedItemSites current
                  (normalizationOperation arguments) mappedFrame PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1
                (argumentItemsEdit mappedTailSites current
                  (normalizationOperation arguments) mappedFrame PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1 := by
          simp only [ItemSeq.renameWires, mappedItemArgumentEq,
            mappedTailArgumentEq]
        have mappedSourceArgumentEq :
            (ItemSeq.cons
                (argumentItemEdit itemSites argumentCurrent
                  (normalizationOperation argumentArguments) argumentFrame
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1
                (argumentItemsEdit tailSites argumentCurrent
                  (normalizationOperation argumentArguments) argumentFrame
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1).renameWires
                argumentSourceRename =
              ItemSeq.cons
                (argumentItemEdit mappedItemSites argumentCurrent
                  (normalizationOperation argumentArguments)
                  mappedArgumentFrame PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1
                (argumentItemsEdit mappedTailSites argumentCurrent
                  (normalizationOperation argumentArguments)
                  mappedArgumentFrame PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1 := by
          simp only [ItemSeq.renameWires, mappedItemSourceArgumentEq,
            mappedTailSourceArgumentEq]
        let exposed := RegionIso.renameWiresConjoin itemResult tailResult
          commonRename
        let children := RegionIso.conjoinCongr mappedItemIso mappedTailIso
        let exposedEndpoint := RegionIso.renameWiresConjoin
          (itemEdit
            (operation := recordingOperation baseOperation external)
            data itemEvidence itemSites).endpoint
          (itemsEdit
            (operation := recordingOperation baseOperation external)
            data tailEvidence tailSites).endpoint targetRename
        let endpointChildren := RegionIso.conjoinCongr mappedItemEndpointIso
          mappedTailEndpointIso
        exact ⟨.cons mappedItemSource mappedTailSource,
          mappedItemResult.conjoin mappedTailResult, mappedEvidence,
          mappedSites, mappedSourceEq, mappedArgumentEq,
          mappedSourceArgumentEq,
          ⟨exposed.trans children⟩,
          ⟨exposedEndpoint.trans endpointChildren⟩⟩
  termination_by sizeOf source

  theorem targetItemReindex
      {arguments external argumentArguments common mappedCommon sourceWires
        mappedSourceWires targetWires mappedTargetWires argumentSourceWires
        mappedArgumentSourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {baseOperation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common
        sourceWires targetWires}
      {mappedFrame : Transform.Frame arguments
        mappedCommon mappedSourceWires mappedTargetWires}
      {data : baseOperation.Data frame}
      {mappedData : baseOperation.Data mappedFrame}
      {source : Item sourceWires} {result : Region common}
      (originalEvidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep
          frame.selected source result)
      (sites : ItemSites (recordingOperation baseOperation external)
        data originalEvidence)
      (current : Vars external arguments)
      (argumentCurrent : Vars external argumentArguments)
      (argumentFrame : Transform.Frame argumentArguments common
        argumentSourceWires argumentSourceWires)
      (mappedArgumentFrame : Transform.Frame argumentArguments mappedCommon
        mappedArgumentSourceWires mappedArgumentSourceWires)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (targetRename : WireRenaming targetWires mappedTargetWires)
      (argumentSourceRename : WireRenaming argumentSourceWires
        mappedArgumentSourceWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (targetKeepCommutes : ∀ {signature} (wire : Var common signature),
        targetRename (frame.targetKeep wire) =
          mappedFrame.targetKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected)
      (argumentKeepCommutes : ∀ {signature} (wire : Var common signature),
        argumentSourceRename (argumentFrame.sourceKeep wire) =
          mappedArgumentFrame.sourceKeep (commonRename wire))
      (argumentSelectedCommutes : argumentSourceRename argumentFrame.selected =
        mappedArgumentFrame.selected)
      (naturality : DataNaturality baseOperation)
      (dataCoherent : naturality.Coherent frame mappedFrame data mappedData
        commonRename targetRename) :
      ∃ mappedSource : Item mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              VisualProof.Rule.Comprehension.Instantiation.ItemResult
                pattern
                mappedFrame.sourceKeep mappedFrame.selected
                mappedSource mappedResult,
            ∃ mappedSites : ItemSites
                (recordingOperation baseOperation external) mappedData
                mappedEvidence,
              source.renameWires sourceRename = mappedSource ∧
                (argumentItemEdit sites current
                    (normalizationOperation arguments) frame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename =
                (argumentItemEdit mappedSites current
                    (normalizationOperation arguments) mappedFrame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1 ∧
                (argumentItemEdit sites argumentCurrent
                    (normalizationOperation argumentArguments) argumentFrame
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1.renameWires
                    argumentSourceRename =
                  (argumentItemEdit mappedSites argumentCurrent
                    (normalizationOperation argumentArguments)
                    mappedArgumentFrame PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1 ∧
                Nonempty (RegionIso (WireEquiv.refl mappedCommon)
                  (result.renameWires commonRename) mappedResult) ∧
                Nonempty (RegionIso (WireEquiv.refl mappedTargetWires)
                  ((itemEdit
                    (operation := recordingOperation baseOperation external)
                    data originalEvidence sites).endpoint.renameWires
                      targetRename)
                  (itemEdit
                    (operation := recordingOperation baseOperation external)
                    mappedData mappedEvidence mappedSites).endpoint) :=
    match sites with
    | .atom itemHead itemPorts => by
        let mappedPorts := itemPorts.map fun wire => commonRename wire
        have keepMaps : WireRenaming.comp sourceRename frame.sourceKeep =
            WireRenaming.comp mappedFrame.sourceKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact keepCommutes wire
        have mappedPortWires :
            (itemPorts.map fun wire => frame.sourceKeep wire).map
                (fun wire => sourceRename wire) =
              mappedPorts.map fun wire => mappedFrame.sourceKeep wire := by
          calc
            _ = itemPorts.map (fun wire =>
                WireRenaming.comp sourceRename frame.sourceKeep wire) :=
              Diagram.vars_map_comp itemPorts frame.sourceKeep sourceRename
            _ = itemPorts.map (fun wire =>
                WireRenaming.comp mappedFrame.sourceKeep commonRename wire) :=
              congrArg (fun rename : WireRenaming common mappedSourceWires =>
                itemPorts.map fun wire => rename wire) keepMaps
            _ = _ := (Diagram.vars_map_comp itemPorts commonRename
              mappedFrame.sourceKeep).symm
        have mappedSource :
            (Item.atom (frame.sourceKeep itemHead)
              (itemPorts.map fun wire => frame.sourceKeep wire)).renameWires
                sourceRename =
              Item.atom (mappedFrame.sourceKeep (commonRename itemHead))
                (mappedPorts.map fun wire => mappedFrame.sourceKeep wire) := by
          simp only [Item.renameWires]
          rw [keepCommutes itemHead]
          exact congrArg
            (Item.atom (mappedFrame.sourceKeep (commonRename itemHead)))
            mappedPortWires
        have mappedArgumentPortWires :
            (itemPorts.map fun wire => argumentFrame.sourceKeep wire).map
                (fun wire => argumentSourceRename wire) =
              mappedPorts.map fun wire =>
                mappedArgumentFrame.sourceKeep wire := by
          calc
            _ = itemPorts.map (fun wire =>
                argumentSourceRename (argumentFrame.sourceKeep wire)) :=
              Diagram.vars_map_comp itemPorts argumentFrame.sourceKeep
                argumentSourceRename
            _ = itemPorts.map (fun wire =>
                mappedArgumentFrame.sourceKeep (commonRename wire)) := by
              apply Vars.map_congr
              intro signature wire
              exact argumentKeepCommutes wire
            _ = _ := (Diagram.vars_map_comp itemPorts commonRename
              mappedArgumentFrame.sourceKeep).symm
        have mappedSourceArgument :
            (Item.atom (argumentFrame.sourceKeep itemHead)
              (itemPorts.map fun wire =>
                argumentFrame.sourceKeep wire)).renameWires
                argumentSourceRename =
              Item.atom
                (mappedArgumentFrame.sourceKeep (commonRename itemHead))
                (mappedPorts.map fun wire =>
                  mappedArgumentFrame.sourceKeep wire) := by
          simp only [Item.renameWires]
          rw [argumentKeepCommutes itemHead]
          exact congrArg
            (Item.atom (mappedArgumentFrame.sourceKeep
              (commonRename itemHead))) mappedArgumentPortWires
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            (pattern := pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected)
            (commonRename itemHead) mappedPorts
        let mappedSites : ItemSites
            (recordingOperation baseOperation external) mappedData
            mappedEvidence :=
          ItemSites.atom
              (pattern := pattern)
              (frame := mappedFrame) (commonRename itemHead) mappedPorts
        have mappedResult :
            (Region.singleton (.atom itemHead itemPorts)).renameWires
                commonRename =
              Region.singleton (.atom (commonRename itemHead) mappedPorts) := by
          rw [Region.singleton_renameWires]
          rfl
        have mappedTargetPorts :
            (itemPorts.map fun wire => frame.targetKeep wire).map
                (fun wire => targetRename wire) =
              mappedPorts.map fun wire => mappedFrame.targetKeep wire := by
          calc
            _ = itemPorts.map (fun wire =>
                WireRenaming.comp targetRename frame.targetKeep wire) :=
              Diagram.vars_map_comp itemPorts frame.targetKeep targetRename
            _ = itemPorts.map (fun wire =>
                WireRenaming.comp mappedFrame.targetKeep commonRename wire) := by
              apply congrArg (fun rename : WireRenaming common mappedTargetWires =>
                itemPorts.map fun wire => rename wire)
              apply WireRenaming.ext
              intro signature wire
              exact targetKeepCommutes wire
            _ = _ := (Diagram.vars_map_comp itemPorts commonRename
              mappedFrame.targetKeep).symm
        have mappedEndpoint :
            (itemEdit
              (operation := recordingOperation baseOperation external)
              data originalEvidence
              (ItemSites.atom
                (pattern := pattern)
                (frame := frame) itemHead itemPorts)).endpoint.renameWires
                targetRename =
              (itemEdit
                (operation := recordingOperation baseOperation external)
                mappedData mappedEvidence mappedSites).endpoint := by
          unfold itemEdit ExactEdit.refl
          simp only [Transform.ItemEdit.run, Region.singleton_renameWires,
            Item.renameWires]
          rw [targetKeepCommutes itemHead]
          exact congrArg Region.singleton (congrArg
            (Item.atom (mappedFrame.targetKeep (commonRename itemHead)))
            mappedTargetPorts)
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          mappedSource, mappedSourceArgument,
          ⟨RegionIso.ofEq mappedResult⟩,
          ⟨RegionIso.ofEq mappedEndpoint⟩⟩
    | .selectedAtom application siteData => by
        let mappedApplication := application.map fun wire => commonRename wire
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            (pattern := pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected) mappedApplication
        have keepMaps : WireRenaming.comp sourceRename frame.sourceKeep =
            WireRenaming.comp mappedFrame.sourceKeep commonRename := by
          apply WireRenaming.ext
          intro signature wire
          exact keepCommutes wire
        have mappedPortWires :
            (application.map fun wire => frame.sourceKeep wire).map
                (fun wire => sourceRename wire) =
              mappedApplication.map
                (fun wire => mappedFrame.sourceKeep wire) := by
          calc
            _ = application.map (fun wire =>
                WireRenaming.comp sourceRename frame.sourceKeep wire) :=
              Diagram.vars_map_comp application frame.sourceKeep sourceRename
            _ = application.map (fun wire =>
                WireRenaming.comp mappedFrame.sourceKeep commonRename wire) :=
              congrArg (fun rename : WireRenaming common mappedSourceWires =>
                application.map fun wire => rename wire) keepMaps
            _ = _ := (Diagram.vars_map_comp application commonRename
              mappedFrame.sourceKeep).symm
        have mappedSource :
            (Item.atom frame.selected
              (application.map fun wire => frame.sourceKeep wire)).renameWires
                sourceRename =
              Item.atom mappedFrame.selected
                (mappedApplication.map
                  fun wire => mappedFrame.sourceKeep wire) := by
          simp only [Item.renameWires, selectedCommutes]
          exact congrArg (Item.atom mappedFrame.selected) mappedPortWires
        have mappedResult :
            (VisualProof.Rule.Comprehension.Instantiation.instantiate
              pattern application).renameWires
                commonRename =
              VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern mappedApplication := by
          exact EqualityNormalization.instantiate_renameWires
            pattern application commonRename
        obtain ⟨mappedSite, ⟨mappedEndpointIso⟩⟩ :=
          naturality.site dataCoherent targetKeepCommutes application siteData.1
        let coherentMappedSite :
            (recordingOperation baseOperation external).SiteData
              mappedFrame mappedData mappedApplication :=
          ⟨mappedSite, siteData.2.map fun wire => commonRename wire⟩
        let mappedSites : ItemSites
            (recordingOperation baseOperation external) mappedData
            mappedEvidence :=
          ItemSites.selectedAtom (pattern := pattern) (frame := mappedFrame)
            mappedApplication coherentMappedSite
        have mappedArgumentEq :
            (Item.atom frame.selected
                (current.map fun wire => frame.sourceKeep
                  (EqualityNormalization.formalSubstitution siteData.2
                    wire))).renameWires sourceRename =
              Item.atom mappedFrame.selected
                (current.map fun wire => mappedFrame.sourceKeep
                  (EqualityNormalization.formalSubstitution
                    coherentMappedSite.2 wire)) := by
          simp only [Item.renameWires, selectedCommutes]
          apply congrArg (Item.atom mappedFrame.selected)
          calc
            _ = current.map (fun wire => sourceRename
                  (frame.sourceKeep
                    (EqualityNormalization.formalSubstitution siteData.2
                      wire))) := Vars.map_map _ _ _
            _ = _ := by
              apply Vars.map_congr
              intro wireSignature wire
              rw [EqualityNormalization.formalSubstitution_map]
              exact keepCommutes
                (EqualityNormalization.formalSubstitution siteData.2 wire)
        have mappedSourceArgumentEq :
            (Item.atom argumentFrame.selected
                (argumentCurrent.map fun wire => argumentFrame.sourceKeep
                  (EqualityNormalization.formalSubstitution siteData.2
                    wire))).renameWires argumentSourceRename =
              Item.atom mappedArgumentFrame.selected
                (argumentCurrent.map fun wire =>
                  mappedArgumentFrame.sourceKeep
                    (EqualityNormalization.formalSubstitution
                      coherentMappedSite.2 wire)) := by
          simp only [Item.renameWires, argumentSelectedCommutes]
          apply congrArg (Item.atom mappedArgumentFrame.selected)
          calc
            _ = argumentCurrent.map (fun wire => argumentSourceRename
                  (argumentFrame.sourceKeep
                    (EqualityNormalization.formalSubstitution siteData.2
                      wire))) := Vars.map_map _ _ _
            _ = _ := by
              apply Vars.map_congr
              intro wireSignature wire
              rw [EqualityNormalization.formalSubstitution_map]
              exact argumentKeepCommutes
                (EqualityNormalization.formalSubstitution siteData.2 wire)
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          by
            simpa only [argumentItemEdit, Vars.map_map, mappedSites,
              coherentMappedSite] using mappedArgumentEq,
          by
            simpa only [argumentItemEdit, Vars.map_map, mappedSites,
              coherentMappedSite] using mappedSourceArgumentEq,
          ⟨RegionIso.ofEq mappedResult⟩,
          ⟨by
            simpa only [itemEdit, ExactEdit.refl,
              Transform.ItemEdit.run] using mappedEndpointIso⟩⟩
    | .identity signature arity identityPorts => by
        let mappedPorts := fun position => commonRename (identityPorts position)
        have mappedSource :
            (Item.identity signature arity
              (fun position => frame.sourceKeep
                (identityPorts position))).renameWires sourceRename =
              Item.identity signature arity
                (fun position => mappedFrame.sourceKeep
                  (mappedPorts position)) := by
          simp only [Item.renameWires, mappedPorts]
          apply congrArg (Item.identity signature arity)
          funext position
          exact keepCommutes (identityPorts position)
        have mappedSourceArgument :
            (Item.identity signature arity
              (fun position => argumentFrame.sourceKeep
                (identityPorts position))).renameWires argumentSourceRename =
              Item.identity signature arity
                (fun position => mappedArgumentFrame.sourceKeep
                  (mappedPorts position)) := by
          simp only [Item.renameWires, mappedPorts]
          apply congrArg (Item.identity signature arity)
          funext position
          exact argumentKeepCommutes (identityPorts position)
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            (pattern := pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected) signature arity mappedPorts
        let mappedSites : ItemSites
            (recordingOperation baseOperation external) mappedData
            mappedEvidence :=
          ItemSites.identity
              (pattern := pattern)
              (frame := mappedFrame) signature arity mappedPorts
        have mappedResult :
            (Region.singleton
              (.identity signature arity identityPorts)).renameWires
                commonRename =
              Region.singleton (.identity signature arity mappedPorts) := by
          rw [Region.singleton_renameWires]
          rfl
        have mappedEndpoint :
            (itemEdit
              (operation := recordingOperation baseOperation external)
              data originalEvidence
              (ItemSites.identity
                (pattern := pattern)
                (frame := frame) signature arity identityPorts)).endpoint.renameWires
                targetRename =
              (itemEdit
                (operation := recordingOperation baseOperation external)
                mappedData mappedEvidence mappedSites).endpoint := by
          unfold itemEdit ExactEdit.refl
          simp only [Transform.ItemEdit.run, Region.singleton_renameWires,
            Item.renameWires]
          apply congrArg Region.singleton
          apply congrArg (Item.identity signature arity)
          funext position
          exact targetKeepCommutes (identityPorts position)
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          mappedSource, mappedSourceArgument, ⟨RegionIso.ofEq mappedResult⟩,
          ⟨RegionIso.ofEq mappedEndpoint⟩⟩
    | .term output freeArity ports term => by
        let mappedOutput := commonRename output
        let mappedPorts := fun position => commonRename (ports position)
        have mappedSource :
            (Item.term (frame.sourceKeep output) freeArity
              (fun position => frame.sourceKeep (ports position)) term).renameWires
                sourceRename =
              Item.term (mappedFrame.sourceKeep mappedOutput) freeArity
                (fun position => mappedFrame.sourceKeep
                  (mappedPorts position)) term := by
          simp only [Item.renameWires, mappedOutput, mappedPorts]
          rw [keepCommutes output]
          apply congrArg
            (Item.term (mappedFrame.sourceKeep (commonRename output))
              freeArity · term)
          funext position
          exact keepCommutes (ports position)
        have mappedSourceArgument :
            (Item.term (argumentFrame.sourceKeep output) freeArity
              (fun position => argumentFrame.sourceKeep (ports position))
                term).renameWires argumentSourceRename =
              Item.term (mappedArgumentFrame.sourceKeep mappedOutput) freeArity
                (fun position => mappedArgumentFrame.sourceKeep
                  (mappedPorts position)) term := by
          simp only [Item.renameWires, mappedOutput, mappedPorts]
          rw [argumentKeepCommutes output]
          apply congrArg
            (Item.term
              (mappedArgumentFrame.sourceKeep (commonRename output))
              freeArity · term)
          funext position
          exact argumentKeepCommutes (ports position)
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.term
            (pattern := pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected)
            mappedOutput freeArity mappedPorts term
        let mappedSites : ItemSites
            (recordingOperation baseOperation external) mappedData
            mappedEvidence :=
          ItemSites.term (pattern := pattern) (frame := mappedFrame)
            mappedOutput freeArity mappedPorts term
        have mappedResult :
            (Region.singleton (.term output freeArity ports term)).renameWires
                commonRename =
              Region.singleton
                (.term mappedOutput freeArity mappedPorts term) := by
          rw [Region.singleton_renameWires]
          rfl
        have mappedEndpoint :
            (itemEdit
              (operation := recordingOperation baseOperation external)
              data originalEvidence
              (ItemSites.term
                (pattern := pattern) (frame := frame)
                output freeArity ports term)).endpoint.renameWires
                targetRename =
              (itemEdit
                (operation := recordingOperation baseOperation external)
                mappedData mappedEvidence mappedSites).endpoint := by
          unfold itemEdit ExactEdit.refl
          simp only [Transform.ItemEdit.run, Region.singleton_renameWires,
            Item.renameWires, mappedOutput, mappedPorts]
          rw [targetKeepCommutes output]
          apply congrArg Region.singleton
          apply congrArg
            (Item.term (mappedFrame.targetKeep (commonRename output))
              freeArity · term)
          funext position
          exact targetKeepCommutes (ports position)
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          mappedSource, mappedSourceArgument, ⟨RegionIso.ofEq mappedResult⟩,
          ⟨RegionIso.ofEq mappedEndpoint⟩⟩
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
            mappedChildSites, mappedChildSourceEq,
            mappedChildArgumentEq,
            mappedChildSourceArgumentEq,
            ⟨mappedChildIso⟩, ⟨mappedChildEndpointIso⟩⟩ :=
          targetRegionReindex childEvidence childSites current argumentCurrent
            argumentFrame mappedArgumentFrame commonRename sourceRename
            targetRename argumentSourceRename keepCommutes targetKeepCommutes
            selectedCommutes argumentKeepCommutes argumentSelectedCommutes
            naturality dataCoherent
        let mappedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            mappedChildEvidence
        let mappedSites : ItemSites
            (recordingOperation baseOperation external) mappedData
            mappedEvidence :=
          .cut mappedChildSites
        have mappedSourceEq :
            (Item.cut body).renameWires sourceRename =
              Item.cut mappedChildSource := by
          simpa only [Item.renameWires] using
            congrArg Item.cut mappedChildSourceEq
        let exposed : RegionIso (WireEquiv.refl mappedCommon)
            ((Region.singleton (.cut childResult)).renameWires commonRename)
            (Region.singleton
              (.cut (childResult.renameWires commonRename))) := by
          rw [Region.singleton_renameWires]
          exact RegionIso.refl _
        let child := RegionIso.singletonCutCongr mappedChildIso
        let exposedEndpoint : RegionIso (WireEquiv.refl mappedTargetWires)
            ((Region.singleton
              (.cut (regionEdit
                (operation := recordingOperation baseOperation external)
                data childEvidence childSites).endpoint))
                |>.renameWires targetRename)
            (Region.singleton (.cut
              ((regionEdit
                (operation := recordingOperation baseOperation external)
                data childEvidence childSites).endpoint
                |>.renameWires targetRename))) := by
          rw [Region.singleton_renameWires]
          exact RegionIso.refl _
        let endpointChild := RegionIso.singletonCutCongr
          mappedChildEndpointIso
        exact ⟨.cut mappedChildSource,
          Region.singleton (.cut mappedChildResult), mappedEvidence,
          mappedSites, mappedSourceEq, by
            unfold argumentItemEdit
            exact congrArg Item.cut mappedChildArgumentEq,
          by
            unfold argumentItemEdit
            exact congrArg Item.cut mappedChildSourceArgumentEq,
          ⟨exposed.trans child⟩,
          ⟨exposedEndpoint.trans endpointChild⟩⟩
  termination_by sizeOf source
end

/-! Concatenating two reindexed literal Formal segments preserves their
authoritative evidence and sites; conjunction reassociation is presentation
only. -/
theorem targetItemsAppend
    {arguments external argumentArguments common sourceWires targetWires
      argumentSourceWires : List Sig}
    {pattern : OpenDiagram arguments}
    {baseOperation : Transform.Operation arguments}
    {frame : Transform.Frame arguments common
      sourceWires targetWires}
    {data : baseOperation.Data frame}
    {firstSource secondSource : ItemSeq sourceWires}
    {firstResult secondResult : Region common}
    (firstEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected
        firstSource firstResult)
    (firstSites : ItemsSites
      (recordingOperation baseOperation external) data firstEvidence)
    (secondEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected
        secondSource secondResult)
    (secondSites : ItemsSites
      (recordingOperation baseOperation external) data secondEvidence)
    (current : Vars external arguments)
    (argumentCurrent : Vars external argumentArguments)
    (argumentFrame : Transform.Frame argumentArguments common
      argumentSourceWires argumentSourceWires) :
    ∃ combinedResult : Region common,
      ∃ combinedEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            pattern frame.sourceKeep
            frame.selected (firstSource.append secondSource) combinedResult,
        ∃ combinedSites : ItemsSites
            (recordingOperation baseOperation external) data combinedEvidence,
          (argumentItemsEdit combinedSites current
              (normalizationOperation arguments) frame PUnit.unit
              (fun _ _ _ => PUnit.unit)).1 =
            (argumentItemsEdit firstSites current
                (normalizationOperation arguments) frame PUnit.unit
                (fun _ _ _ => PUnit.unit)).1.append
              (argumentItemsEdit secondSites current
                (normalizationOperation arguments) frame PUnit.unit
                (fun _ _ _ => PUnit.unit)).1 ∧
          (argumentItemsEdit combinedSites argumentCurrent
              (normalizationOperation argumentArguments) argumentFrame
              PUnit.unit (fun _ _ _ => PUnit.unit)).1 =
            (argumentItemsEdit firstSites argumentCurrent
                (normalizationOperation argumentArguments) argumentFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1.append
              (argumentItemsEdit secondSites argumentCurrent
                (normalizationOperation argumentArguments) argumentFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1 ∧
          Nonempty (RegionIso (WireEquiv.refl common)
            (firstResult.conjoin secondResult) combinedResult) ∧
            Nonempty (RegionIso (WireEquiv.refl targetWires)
              ((itemsEdit
                (operation := recordingOperation baseOperation external)
                data firstEvidence firstSites).endpoint.conjoin
                (itemsEdit
                  (operation := recordingOperation baseOperation external)
                  data secondEvidence secondSites).endpoint)
              (itemsEdit
                (operation := recordingOperation baseOperation external)
                data combinedEvidence combinedSites).endpoint) :=
  match firstSites with
  | .nil _ => by
      exact ⟨secondResult, secondEvidence, secondSites, rfl, rfl,
        ⟨RegionIso.blankConjoin secondResult⟩,
        ⟨by
          unfold itemsEdit ExactEdit.refl
          simp only [Transform.ItemsEdit.run]
          exact RegionIso.blankConjoin _⟩⟩
  | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
      itemEvidence tailEvidence itemSites tailSites => by
      obtain ⟨combinedTailResult, combinedTailEvidence,
          combinedTailSites, combinedTailArgumentEq,
          combinedTailSourceArgumentEq, ⟨combinedTailIso⟩,
          ⟨combinedTailEndpointIso⟩⟩ :=
        targetItemsAppend tailEvidence tailSites secondEvidence secondSites
          current argumentCurrent argumentFrame
      let combinedEvidence :=
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
          itemEvidence combinedTailEvidence
      let combinedSites : ItemsSites
          (recordingOperation baseOperation external) data combinedEvidence :=
        .cons itemSites combinedTailSites
      let associated := RegionIso.conjoinAssoc itemResult tailResult
        secondResult
      let tailPresented := RegionIso.conjoinCongr
        (RegionIso.refl itemResult) combinedTailIso
      let itemOutput := itemEdit
        (operation := recordingOperation baseOperation external)
          data itemEvidence itemSites
      let tailOutput := itemsEdit
        (operation := recordingOperation baseOperation external)
          data tailEvidence tailSites
      let secondOutput := itemsEdit
        (operation := recordingOperation baseOperation external)
          data secondEvidence secondSites
      let endpointAssociated := RegionIso.conjoinAssoc itemOutput.endpoint
        tailOutput.endpoint secondOutput.endpoint
      let endpointTailPresented := RegionIso.conjoinCongr
        (RegionIso.refl itemOutput.endpoint) combinedTailEndpointIso
      exact ⟨itemResult.conjoin combinedTailResult, combinedEvidence,
          combinedSites, by
          simpa only [combinedSites, argumentItemsEdit,
            ItemSeq.append] using congrArg
              (fun tail => ItemSeq.cons
                (argumentItemEdit itemSites current
                  (normalizationOperation arguments) frame PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1 tail)
              combinedTailArgumentEq,
        by
          simpa only [combinedSites, argumentItemsEdit,
            ItemSeq.append] using congrArg
              (fun tail => ItemSeq.cons
                (argumentItemEdit itemSites argumentCurrent
                  (normalizationOperation argumentArguments) argumentFrame
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1 tail)
              combinedTailSourceArgumentEq,
        ⟨associated.trans tailPresented⟩,
        ⟨by
          simpa only [itemsEdit, itemOutput, tailOutput, secondOutput,
            combinedSites] using
            endpointAssociated.trans endpointTailPresented⟩⟩
  termination_by sizeOf firstSource


end VisualProof.Rule.Completeness.Comprehension
