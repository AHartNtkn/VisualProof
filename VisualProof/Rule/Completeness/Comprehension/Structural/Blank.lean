import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural.Blank

def blankPattern : OpenDiagram [] where
  external := []
  boundaryWire := .nil
  boundarySurjective := fun wire => Fin.elim0 wire
  body := Region.blank []
  canonical := by
    simp [Region.blank, Region.Canonical, ItemSeq.ChildrenCanonical]
  externalTwoEnded := by
    intro signature wire
    cases wire

/-- Instantiating the literal blank pattern is a presentation of the blank
region. -/
noncomputable def blankPatternInstantiationIso
    (application : Vars wires []) :
    RegionIso (WireEquiv.refl wires)
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        blankPattern application) (Region.blank wires) := by
  cases application
  let inner := RegionIso.blankConjoin (Region.blank (wires ++ []))
  let hosted := RegionIso.adjoinAt [] .nil inner
  let collapsed := hosted.trans
    (RegionIso.adjoinAtNil (Region.blank (wires ++ []))).symm
  simpa [
    VisualProof.Rule.Comprehension.Instantiation.instantiate,
    blankPattern, Region.blank, Region.renameWires] using collapsed

mutual
  /-- The Ends operation has unit site data at every selected blank-pattern
  application, so authoritative region evidence admits exact sites. -/
  theorem endsRegionSites_nonempty
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          blankPattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (Content.Ends.operation []) PUnit.unit evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := endsItemsSites_nonempty
          (frame := frame.append _) childEvidence
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem endsItemsSites_nonempty
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          blankPattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (Content.Ends.operation []) PUnit.unit evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := endsItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := endsItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem endsItemSites_nonempty
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          blankPattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (Content.Ends.operation []) PUnit.unit evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := blankPattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := blankPattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := blankPattern) signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := endsRegionSites_nonempty childEvidence
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

noncomputable def endsItemsSites
    {frame : Transform.Frame [] common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        blankPattern frame.sourceKeep frame.selected source result) :
    ItemsSites (Content.Ends.operation []) PUnit.unit evidence :=
  Classical.choice (endsItemsSites_nonempty evidence)

mutual
  /-- Ends removes precisely the selected blank applications; its recursive
  edit endpoint is therefore a presentation of the authoritative result. -/
  theorem endsRegionEndpointIso_nonempty
      {frame : Transform.Frame [] common sourceWires common}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          blankPattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites (Content.Ends.operation []) PUnit.unit evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id) :
      Nonempty (RegionIso (WireEquiv.refl common)
        (regionEdit (operation := Content.Ends.operation []) PUnit.unit
          evidence sites).endpoint result) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites =>
        by
          have childIdentity :
              (frame.append locals).targetKeep = WireRenaming.id := by
            apply WireRenaming.ext
            intro signature wire
            change frame.targetKeep.appendRight locals wire = wire
            rw [targetKeepEq]
            exact WireRenaming.appendRight_id_apply locals wire
          obtain ⟨childIso⟩ :=
            endsItemsEndpointIso_nonempty childSites childIdentity
          exact ⟨RegionIso.adjoinAt locals .nil childIso⟩
  termination_by sizeOf source

  theorem endsItemsEndpointIso_nonempty
      {frame : Transform.Frame [] common sourceWires common}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          blankPattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites (Content.Ends.operation []) PUnit.unit evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id) :
      Nonempty (RegionIso (WireEquiv.refl common)
        (itemsEdit (operation := Content.Ends.operation []) PUnit.unit
          evidence sites).endpoint result) :=
    match sites with
    | .nil _ => ⟨RegionIso.refl _⟩
    | .cons itemSites tailSites => by
          obtain ⟨itemIso⟩ :=
            endsItemEndpointIso_nonempty itemSites targetKeepEq
          obtain ⟨tailIso⟩ :=
            endsItemsEndpointIso_nonempty tailSites targetKeepEq
          exact ⟨RegionIso.conjoinCongr itemIso tailIso⟩
  termination_by sizeOf source

  theorem endsItemEndpointIso_nonempty
      {frame : Transform.Frame [] common sourceWires common}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          blankPattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites (Content.Ends.operation []) PUnit.unit evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id) :
      Nonempty (RegionIso (WireEquiv.refl common)
        (itemEdit (operation := Content.Ends.operation []) PUnit.unit
          evidence sites).endpoint result) :=
    match sites with
    | .atom head ports => by
        have portsEq :
            ports.map (fun wire => frame.targetKeep wire) = ports := by
          rw [targetKeepEq]
          exact Diagram.vars_map_id ports
        have headEq : frame.targetKeep head = head := by
          rw [targetKeepEq]
          rfl
        exact ⟨RegionIso.ofEq (by
          simp only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
            headEq, portsEq])⟩
    | .selectedAtom application siteData => by
        exact ⟨(blankPatternInstantiationIso application).symm⟩
    | .identity signature arity ports => by
        have portsEq :
            (fun position => frame.targetKeep (ports position)) = ports := by
          funext position
          rw [targetKeepEq]
          rfl
        exact ⟨RegionIso.ofEq (by
          simp only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
            portsEq])⟩
    | .cut childSites => by
        obtain ⟨childIso⟩ :=
          endsRegionEndpointIso_nonempty childSites targetKeepEq
        exact ⟨RegionIso.singletonCutCongr childIso⟩
  termination_by sizeOf source
end

/-- Derive every authoritative blank-pattern site through one Ends spawn at
the binder home. Sites, the deterministic edit, and its presentation of the
authoritative result are all derived internally from the evidence. -/
theorem itemsEnds
    {outer before after : List Sig}
    {source : ItemSeq (outer ++ (before ++ .rel [] :: after))}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        blankPattern
        (Content.Ends.rootFrame outer before after []).sourceKeep
        (Content.Ends.rootFrame outer before after []).selected source result)
    (request : Telescope.Request
      (Region.adjoinAt (before ++ after) .nil result)
      (.mk (before ++ .rel [] :: after) source)) :
    request.Result := by
  let frame := Content.Ends.rootFrame outer before after []
  let sites := endsItemsSites evidence
  let output := itemsEdit (operation := Content.Ends.operation []) PUnit.unit
    evidence sites
  have targetKeepEq : frame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    apply Var.appendCases (left := outer) (right := before ++ after)
      (motive := fun wire => frame.targetKeep wire = WireRenaming.id wire)
    · intro inheritedSignature inherited
      simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, WireRenaming.id]
    · intro localSignature localWire
      apply Var.appendCases (left := before) (right := after)
        (motive := fun localWire =>
          frame.targetKeep (Var.appendRight outer localWire) =
            WireRenaming.id (Var.appendRight outer localWire))
      · intro beforeSignature beforeWire
        simp [frame, Content.Ends.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
      · intro afterSignature afterWire
        simp only [frame, Content.Ends.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
          Var.appendMap_right]
        apply Var.eq_of_index_eq
        apply Fin.ext
        simp [Var.index_appendRight, Var.appendRight]
  obtain ⟨endpointIso⟩ :=
    endsItemsEndpointIso_nonempty sites targetKeepEq
  let description : Content.Ends.Delete.Description outer := {
    arguments := []
    before := before
    after := after
    items := source
    itemsEdit := output.edit
  }
  let instantiated := Region.adjoinAt (before ++ after) .nil result
  have rawPreparedEq :
      Region.adjoinAt (before ++ after) .nil output.endpoint =
        description.target := by
    change Region.adjoinAt (before ++ after) .nil output.endpoint =
      Region.adjoinAt (before ++ after) .nil output.edit.run
    rw [output.run_eq]
  let rawPreparedIso : RegionIso (WireEquiv.refl outer)
      instantiated description.target :=
    (RegionIso.adjoinAt (before ++ after) .nil endpointIso.symm).trans
      (RegionIso.ofEq rawPreparedEq)
  let basePreparation : request.Preparation instantiated := {
    prepared := instantiated
    preparedCanonical := request.instantiatedCanonical
    preparedExternalTwoEnded := request.instantiatedExternalTwoEnded
    rawPreparedCanonical := request.instantiatedCanonical
    rawPreparedExternalTwoEnded := request.instantiatedExternalTwoEnded
    preparedIso := RegionIso.refl instantiated
    telescope := Telescope.refl request.polarity request.occurrence.interface
      request.occurrence.context request.instantiatedCanonical
      request.instantiatedExternalTwoEnded request.continuation.1
  }
  let preparation : request.Preparation description.target :=
    basePreparation.rawIso rawPreparedIso
  have pendingEq :
      (.mk (before ++ .rel [] :: after) source : Region outer) =
        description.source := by
    rfl
  have rawPendingCanonical :
      (request.occurrence.context.fill description.source).Canonical := by
    rw [← pendingEq]
    exact request.pendingCanonical
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    intro signature wire
    rw [← pendingEq]
    exact request.pendingExternalTwoEnded wire
  let branch : request.Branch preparation.prepared := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := Content.Ends.Local
    inject := fun step => Step.ends step
    preparedCanonical := preparation.preparedCanonical
    preparedExternalTwoEnded := preparation.preparedExternalTwoEnded
    rawPreparedCanonical := preparation.rawPreparedCanonical
    rawPreparedExternalTwoEnded := preparation.rawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := preparation.preparedIso
    pendingIso := RegionIso.ofEq pendingEq
    localStep := .spawn (.mk description)
    preparation := preparation.telescope
  }
  exact branch.derive

end Structural.Blank

namespace Structural

/-- The empty item-sequence constructor is derivable by Ends. -/
theorem supportBlankDerives
    {wires : List Sig} (wiresEq : wires = []) :
    SupportDerives (Region.ofItems (ItemSeq.nil : ItemSeq wires)) := by
  subst wires
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence structuralRequest
  have patternEq :
      Erasure.Exposure.supportPattern (Region.ofItems ItemSeq.nil)
          materialCanonical = Structural.Blank.blankPattern := by
    apply EqualityNormalization.OpenDiagram.eq_of_data <;> rfl
  rw [patternEq] at evidence
  exact Structural.Blank.itemsEnds evidence structuralRequest

end Structural

end VisualProof.Rule.Completeness.Comprehension
