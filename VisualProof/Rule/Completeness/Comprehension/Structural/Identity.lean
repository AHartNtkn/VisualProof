import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

theorem identityZeroItemsSites_nonempty
    {signature : Sig}
    {common sourceWires targetWires : List Sig}
    {frame : Transform.Frame [] common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (positionalIdentityPattern signature 0)
        frame.sourceKeep frame.selected source result) :
    Nonempty (ItemsSites (Leaf.Identity.operation signature 0)
      PUnit.unit evidence) := by
  cases evidence with
  | nil => exact ⟨.nil _⟩
  | cons itemEvidence tailEvidence =>
      obtain ⟨itemSites⟩ := itemSites
        (signature := signature) (frame := frame) itemEvidence
      obtain ⟨tailSites⟩ := identityZeroItemsSites_nonempty
        (signature := signature) (frame := frame) tailEvidence
      exact ⟨.cons itemSites tailSites⟩
termination_by sizeOf source
where
  regionSites
      {signature : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (positionalIdentityPattern signature 0)
          frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (Leaf.Identity.operation signature 0)
        PUnit.unit evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := identityZeroItemsSites_nonempty
          (signature := signature) (frame := frame.append _) childEvidence
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  itemSites
      {signature : Sig}
      {common sourceWires targetWires : List Sig}
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          (positionalIdentityPattern signature 0)
          frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (Leaf.Identity.operation signature 0)
        PUnit.unit evidence) := by
    cases evidence with
    | atom head ports =>
        exact ⟨.atom (pattern := positionalIdentityPattern signature 0)
          head ports⟩
    | selectedAtom application =>
        let identityPorts : Fin 0 → Var common signature :=
          fun position => Fin.elim0 position
        have applicationEq : application =
            Leaf.Identity.Vars.fromFn identityPorts := by
          cases application
          rfl
        exact ⟨ItemSites.selectedAtom
          (operation := Leaf.Identity.operation signature 0)
          (pattern := positionalIdentityPattern signature 0)
          (frame := frame) application ⟨identityPorts, applicationEq⟩⟩
    | identity itemSignature itemArity ports =>
        exact ⟨ItemSites.identity
          (operation := Leaf.Identity.operation signature 0)
          (pattern := positionalIdentityPattern signature 0)
          (frame := frame) itemSignature itemArity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := regionSites
          (signature := signature) (frame := frame) childEvidence
        exact ⟨.cut childSites⟩
  termination_by sizeOf source

/-- The nullary identity constructor is derivable by IdentityLeaf. -/
theorem supportIdentityDerives
    {wires : List Sig} (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) (wiresEq : wires = []) :
    SupportDerives (Region.singleton (.identity signature arity ports)) := by
subst wires
have arityEq : arity = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro positive
  exact nomatch ports ⟨0, positive⟩
subst arity
intro materialCanonical structuralOuter structuralBefore structuralAfter
  items result evidence structuralRequest
have materialEq :
    Region.singleton (.identity signature 0 ports) =
      positionalIdentityMaterial signature 0 := by
  apply congrArg Region.singleton
  apply congrArg (Item.identity signature 0)
  funext position
  exact Fin.elim0 position
have patternEq :
    Erasure.Exposure.supportPattern
        (Region.singleton (.identity signature 0 ports))
        materialCanonical =
      positionalIdentityPattern signature 0 := by
  unfold positionalIdentityPattern
  apply EqualityNormalization.OpenDiagram.eq_of_data
  · rfl
  · rfl
  · exact heq_of_eq (congrArg Erasure.Exposure.supportBody materialEq)
rw [patternEq] at evidence
obtain ⟨identitySites⟩ := identityZeroItemsSites_nonempty
  (signature := signature)
  (frame := Leaf.Identity.rootFrame structuralOuter structuralBefore
    structuralAfter signature 0) evidence
let output := itemsEdit
  (operation := Leaf.Identity.operation signature 0)
  PUnit.unit evidence identitySites
have targetKeepEq :
    (Leaf.Identity.rootFrame structuralOuter structuralBefore
      structuralAfter signature 0).targetKeep = WireRenaming.id := by
  apply WireRenaming.ext
  intro wireSignature wire
  apply Var.appendCases (left := structuralOuter)
    (right := structuralBefore ++ structuralAfter)
    (motive := fun wire =>
      (Leaf.Identity.rootFrame structuralOuter structuralBefore
        structuralAfter signature 0).targetKeep wire =
          WireRenaming.id wire)
  · intro inheritedSignature inherited
    simp [Leaf.Identity.rootFrame, Transform.Frame.replace,
      Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
  · intro localSignature localWire
    apply Var.appendCases (left := structuralBefore)
      (right := structuralAfter)
      (motive := fun localWire =>
        (Leaf.Identity.rootFrame structuralOuter structuralBefore
          structuralAfter signature 0).targetKeep
            (Var.appendRight structuralOuter localWire) =
          WireRenaming.id (Var.appendRight structuralOuter localWire))
    · intro beforeSignature beforeWire
      simp [Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
    · intro afterSignature afterWire
      apply Var.eq_of_index_eq
      apply Fin.ext
      simp [Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
        Var.index_appendRight, Var.appendRight]
obtain ⟨preparationHosted, preparationScope⟩ :=
  leafItemsEndpoint evidence identitySites targetKeepEq
    (fun siteTargetKeepEq application site => by
      let recordedSite :
          (recordingOperation
            (Leaf.Identity.operation signature 0) []).SiteData
              _ PUnit.unit application :=
        (site, Vars.nil)
      simpa only [recordingOperation] using
        (positionalIdentityLeafEndpoint signature 0
          siteTargetKeepEq application recordedSite))
let instantiated := Region.adjoinAt
  (structuralBefore ++ structuralAfter) .nil result
let rawPrepared := Region.adjoinAt
  (structuralBefore ++ structuralAfter) .nil output.endpoint
have rawPreparedScope : ScopePreservation instantiated rawPrepared := by
  exact adjoinAt_preserves_scope
    (structuralBefore ++ structuralAfter) .nil result output.endpoint
    preparationScope
have rawPreparedValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context instantiated rawPrepared
  structuralRequest.instantiatedCanonical
  structuralRequest.instantiatedExternalTwoEnded rawPreparedScope
have polarityEq : structuralRequest.occurrence.context.polarity =
    structuralRequest.polarity := structuralRequest.continuation.1
have renamedInstantiatedCanonical :
    (structuralRequest.occurrence.context.fill
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
        (result.renameWires WireRenaming.id))).Canonical := by
  simpa only [Region.renameWires_id] using
    structuralRequest.instantiatedCanonical
have renamedInstantiatedExternal : OpenDiagram.ExternalTwoEnded
    structuralRequest.occurrence.interface.boundaryWire
    (structuralRequest.occurrence.context.fill
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
        (result.renameWires WireRenaming.id))) := by
  intro wireSignature wire
  simpa only [Region.renameWires_id] using
    structuralRequest.instantiatedExternalTwoEnded wire
have renamedPreparedCanonical :
    (structuralRequest.occurrence.context.fill
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
        (output.endpoint.renameWires WireRenaming.id))).Canonical := by
  simpa only [Region.renameWires_id] using rawPreparedValidity.1
have renamedPreparedExternal : OpenDiagram.ExternalTwoEnded
    structuralRequest.occurrence.interface.boundaryWire
    (structuralRequest.occurrence.context.fill
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
        (output.endpoint.renameWires WireRenaming.id))) := by
  intro wireSignature wire
  simpa only [Region.renameWires_id] using rawPreparedValidity.2 wire
have preparationTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context instantiated rawPrepared
    structuralRequest.instantiatedCanonical
    structuralRequest.instantiatedExternalTwoEnded
    rawPreparedValidity.1 rawPreparedValidity.2 := by
  simpa only [instantiated, rawPrepared, Region.renameWires_id] using
    telescopeOfHosted preparationHosted WireRenaming.id .nil
      structuralRequest.polarity
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context
      renamedInstantiatedCanonical renamedInstantiatedExternal
      renamedPreparedCanonical renamedPreparedExternal polarityEq
let preparation : structuralRequest.Preparation rawPrepared := {
  prepared := rawPrepared
  preparedCanonical := rawPreparedValidity.1
  preparedExternalTwoEnded := rawPreparedValidity.2
  rawPreparedCanonical := rawPreparedValidity.1
  rawPreparedExternalTwoEnded := rawPreparedValidity.2
  preparedIso := RegionIso.refl rawPrepared
  telescope := by
    simpa only [instantiated] using preparationTelescope
}
exact itemsIdentity (signature := signature) (arity := 0)
  (localBefore := structuralBefore) (localAfter := structuralAfter)
  evidence identitySites structuralRequest (by
    simpa only [rawPrepared, output, List.nil_append] using preparation)

end Structural

end VisualProof.Rule.Completeness.Comprehension
