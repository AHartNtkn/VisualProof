import VisualProof.Rule.Completeness.Comprehension.Telescope
import VisualProof.Rule.Completeness.Erasure.Exposure
import VisualProof.Diagram.Scope.Isomorphism
import VisualProof.Diagram.Isomorphism.Algebra

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Compiler

/-- One transform traversal carrying both the primitive's actual site data and
the authoritative full comprehension application used by later argument
normalization. Its site and pin outputs are definitionally those of the
underlying primitive operation. -/
def recordingOperation (targetOperation : Transform.Operation targetArguments)
    (originalArguments : List Sig) : Transform.Operation targetArguments where
  Data := targetOperation.Data
  appendData := targetOperation.appendData
  SiteData := fun {_common _sourceWires _targetWires} frame data ports =>
    targetOperation.SiteData frame data ports × Vars _common originalArguments
  site := fun frame data ports site =>
    targetOperation.site frame data ports site.1
  pin := targetOperation.pin

mutual
  def recordingRegionSitesTarget
      {targetOperation : Transform.Operation targetArguments}
      {frame : Transform.Frame targetArguments common sourceWires targetWires}
      {data : targetOperation.Data frame}
      {pattern : OpenDiagram targetArguments}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites
        (recordingOperation targetOperation originalArguments) data evidence) :
      RegionSites targetOperation data evidence :=
    match sites with
    | .mk childSites => .mk (recordingItemsSitesTarget childSites)
  termination_by structural sites

  def recordingItemsSitesTarget
      {targetOperation : Transform.Operation targetArguments}
      {frame : Transform.Frame targetArguments common sourceWires targetWires}
      {data : targetOperation.Data frame}
      {pattern : OpenDiagram targetArguments}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites
        (recordingOperation targetOperation originalArguments) data evidence) :
      ItemsSites targetOperation data evidence :=
    match sites with
    | .nil evidence => .nil evidence
    | .cons itemSites tailSites =>
        .cons (recordingItemSitesTarget itemSites)
          (recordingItemsSitesTarget tailSites)
  termination_by structural sites

  def recordingItemSitesTarget
      {targetOperation : Transform.Operation targetArguments}
      {frame : Transform.Frame targetArguments common sourceWires targetWires}
      {data : targetOperation.Data frame}
      {pattern : OpenDiagram targetArguments}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites
        (recordingOperation targetOperation originalArguments) data evidence) :
      ItemSites targetOperation data evidence :=
    match sites with
    | .atom head ports => .atom (pattern := pattern) head ports
    | .selectedAtom ports siteData =>
        .selectedAtom (pattern := pattern) ports siteData.1
    | .identity signature arity ports =>
        .identity (pattern := pattern) signature arity ports
    | .cut childSites => .cut (recordingRegionSitesTarget childSites)
  termination_by structural sites

end

/-- Instantiating the literal blank pattern is a presentation of the blank
region. -/
noncomputable def blankPatternInstantiationIso
    (application : Vars wires []) :
    RegionIso (WireEquiv.refl wires)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        blankPattern application) (Region.blank wires) := by
  cases application
  let inner := RegionIso.blankConjoin (Region.blank (wires ++ []))
  let hosted := RegionIso.adjoinAt [] .nil inner
  let collapsed := hosted.trans
    (RegionIso.adjoinAtNil (Region.blank (wires ++ []))).symm
  simpa [
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate,
    blankPattern, Region.blank, Region.renameWires] using collapsed

mutual
  /-- The Ends operation has unit site data at every selected blank-pattern
  application, so authoritative region evidence admits exact sites. -/
  theorem endsRegionSites_nonempty
      {frame : Transform.Frame [] common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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

/-- Compile every authoritative blank-pattern site through one Ends spawn at
the binder home. Sites, the deterministic edit, and its presentation of the
authoritative result are all derived internally from the evidence. -/
theorem itemsEnds
    {outer before after : List Sig}
    {source : ItemSeq (outer ++ (before ++ .rel [] :: after))}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
  exact branch.compile

mutual
  theorem regionEdit_noSelectedPin
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence) :
      (regionEdit data evidence sites).edit.NoSelectedPin :=
    match sites with
    | .mk childSites => itemsEdit_noSelectedPin childSites
  termination_by structural sites

  theorem itemsEdit_noSelectedPin
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites operation data evidence) :
      (itemsEdit data evidence sites).edit.NoSelectedPin :=
    match sites with
    | .nil _ => True.intro
    | .cons itemSites tailSites =>
        ⟨itemEdit_noSelectedPin itemSites,
          itemsEdit_noSelectedPin tailSites⟩
  termination_by structural sites

  theorem itemEdit_noSelectedPin
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites operation data evidence) :
      (itemEdit data evidence sites).edit.NoSelectedPin :=
    match sites with
    | .atom _ _ => True.intro
    | .selectedAtom _ _ => True.intro
    | .identity _ _ _ => True.intro
    | .cut childSites => regionEdit_noSelectedPin childSites
  termination_by structural sites
end

mutual
  def RegionSites.selectedPaths
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence) : List RegionPath :=
    match sites with
    | .mk childSites => childSites.selectedPaths 0
  termination_by structural sites

  def ItemsSites.selectedPaths
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites operation data evidence) (itemIndex : Nat) :
      List RegionPath :=
    match sites with
    | .nil _ => []
    | .cons itemSites tailSites =>
        itemSites.selectedPaths itemIndex ++
          tailSites.selectedPaths (itemIndex + 1)
  termination_by structural sites

  def ItemSites.selectedPaths
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites operation data evidence) (itemIndex : Nat) :
      List RegionPath :=
    match sites with
    | .atom _ _ => []
    | .selectedAtom _ _ => [[]]
    | .identity _ _ _ => []
    | .cut childSites =>
        childSites.selectedPaths.map (fun path => itemIndex :: path)
  termination_by structural sites
end

mutual
  theorem RegionSites.source_selectedPaths
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence)
      (invariant : Transform.RetainedIndexInvariant frame) :
      source.incidencePaths frame.selected.index.val = sites.selectedPaths :=
    match sites with
    | .mk childSites => by
        simpa [Region.incidencePaths, RegionSites.selectedPaths,
          Transform.Frame.append] using
          childSites.source_selectedPaths (invariant.append _) 0
  termination_by structural sites

  theorem ItemsSites.source_selectedPaths
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites operation data evidence)
      (invariant : Transform.RetainedIndexInvariant frame) (itemIndex : Nat) :
      source.incidencePaths frame.selected.index.val itemIndex =
        sites.selectedPaths itemIndex :=
    match sites with
    | .nil _ => rfl
    | .cons itemSites tailSites => by
        simp only [ItemSeq.incidencePaths, ItemsSites.selectedPaths]
        rw [itemSites.source_selectedPaths invariant itemIndex,
          tailSites.source_selectedPaths invariant (itemIndex + 1)]
  termination_by structural sites

  theorem ItemSites.source_selectedPaths
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites operation data evidence)
      (invariant : Transform.RetainedIndexInvariant frame) (itemIndex : Nat) :
      source.incidencePaths frame.selected.index.val itemIndex =
        sites.selectedPaths itemIndex :=
    match sites with
    | .atom head ports => by
        have headNe := Ne.symm (invariant.selectedFresh head)
        have portsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
          frame.sourceKeep frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh wire))
        simp [ItemSites.selectedPaths, Item.incidencePaths, headNe, portsZero]
    | .selectedAtom ports siteData => by
        have portsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
          frame.sourceKeep frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh wire))
        simp [ItemSites.selectedPaths, Item.incidencePaths, portsZero]
    | .identity signature arity ports => by
        have portsZero := countPorts_map_eq_zero_of_no_preimage arity ports
          frame.sourceKeep frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh wire))
        simp [ItemSites.selectedPaths, Item.incidencePaths, portsZero]
    | .cut childSites => by
        simp only [Item.incidencePaths, ItemSites.selectedPaths]
        rw [childSites.source_selectedPaths invariant]
  termination_by structural sites
end

/-- A proof-irrelevant traversal operation used to recover the exact selected
site layout from authoritative instantiation evidence. -/
def normalizationOperation (arguments : List Sig) :
    Transform.Operation arguments where
  Data := fun _ => PUnit
  appendData := fun _ _ _ => PUnit.unit
  SiteData := fun _ _ _ => PUnit
  site := fun {_ _ targetWires} _ _ _ _ => Region.blank targetWires
  pin := fun {_ _ targetWires} _ _ => Region.blank targetWires

mutual
  def retainedRegionPresentation : Region wires → Region wires
    | .mk locals items =>
        Region.adjoinAt locals .nil (retainedItemsPresentation items)

  def retainedItemsPresentation : ItemSeq wires → Region wires
    | .nil => Region.blank wires
    | .cons item tail =>
        (retainedItemPresentation item).conjoin
          (retainedItemsPresentation tail)

  def retainedItemPresentation : Item wires → Region wires
    | .atom head ports => Region.singleton (.atom head ports)
    | .identity signature arity ports =>
        Region.singleton (.identity signature arity ports)
    | .cut body =>
        Region.singleton (.cut (retainedRegionPresentation body))
end


mutual
  noncomputable def retainedRegionPresentationIso
      (region : Region wires) :
      RegionIso (WireEquiv.refl wires)
        (retainedRegionPresentation region) region :=
    match region with
    | .mk locals items => by
        let child := RegionIso.adjoinAt locals .nil
          (retainedItemsPresentationIso items)
        exact child.trans (RegionIso.adjoinAtOfItems locals items)
  termination_by sizeOf region

  noncomputable def retainedItemsPresentationIso
      (items : ItemSeq wires) :
      RegionIso (WireEquiv.refl wires)
        (retainedItemsPresentation items) (Region.ofItems items) :=
    match items with
    | .nil => RegionIso.refl _
    | .cons item tail => by
        let children := RegionIso.conjoinCongr
          (retainedItemPresentationIso item)
          (retainedItemsPresentationIso tail)
        let presented := RegionIso.ofEq
          (Region.singleton_conjoin_ofItems item tail)
        exact children.trans presented
  termination_by sizeOf items

  noncomputable def retainedItemPresentationIso
      (item : Item wires) :
      RegionIso (WireEquiv.refl wires)
        (retainedItemPresentation item) (Region.singleton item) :=
    match item with
    | .atom _ _ => RegionIso.refl _
    | .identity _ _ _ => RegionIso.refl _
    | .cut body =>
        RegionIso.singletonCutCongr (retainedRegionPresentationIso body)
  termination_by sizeOf item
end

mutual
  theorem recordingRegionEditEndpoint_eq
      {targetOperation : Transform.Operation targetArguments}
      {frame : Transform.Frame targetArguments common sourceWires targetWires}
      {data : targetOperation.Data frame}
      {pattern : OpenDiagram targetArguments}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites
        (recordingOperation targetOperation originalArguments) data evidence) :
      (regionEdit
          (operation := recordingOperation targetOperation originalArguments)
          data evidence sites).endpoint =
        (regionEdit (operation := targetOperation) data evidence
          (recordingRegionSitesTarget sites)).endpoint :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals _ _ _ childSites =>
        congrArg (Region.adjoinAt _ .nil)
          (recordingItemsEditEndpoint_eq childSites)
  termination_by structural sites

  theorem recordingItemsEditEndpoint_eq
      {targetOperation : Transform.Operation targetArguments}
      {frame : Transform.Frame targetArguments common sourceWires targetWires}
      {data : targetOperation.Data frame}
      {pattern : OpenDiagram targetArguments}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites
        (recordingOperation targetOperation originalArguments) data evidence) :
      (itemsEdit
          (operation := recordingOperation targetOperation originalArguments)
          data evidence sites).endpoint =
        (itemsEdit (operation := targetOperation) data evidence
          (recordingItemsSitesTarget sites)).endpoint :=
    match sites with
    | .nil evidence => rfl
    | .cons itemSites tailSites => by
        unfold recordingItemsSitesTarget
        unfold itemsEdit
        dsimp only
        rw [recordingItemEditEndpoint_eq itemSites,
          recordingItemsEditEndpoint_eq tailSites]
  termination_by structural sites

  theorem recordingItemEditEndpoint_eq
      {targetOperation : Transform.Operation targetArguments}
      {frame : Transform.Frame targetArguments common sourceWires targetWires}
      {data : targetOperation.Data frame}
      {pattern : OpenDiagram targetArguments}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites
        (recordingOperation targetOperation originalArguments) data evidence) :
      (itemEdit
          (operation := recordingOperation targetOperation originalArguments)
          data evidence sites).endpoint =
        (itemEdit (operation := targetOperation) data evidence
          (recordingItemSitesTarget sites)).endpoint :=
    match sites with
    | .atom head ports => rfl
    | .selectedAtom ports siteData => rfl
    | .identity signature arity ports => rfl
    | .cut childSites =>
        congrArg (fun child => Region.singleton (.cut child))
          (recordingRegionEditEndpoint_eq childSites)
  termination_by structural sites
end

/-- Compile one authoritative cut-pattern layer through the single CutShape
primitive at the binder home. The recursive child supplies only the exact
telescope ending at the deterministic all-sites edit endpoint. -/
theorem itemsCut
    {arguments outer before after : List Sig}
    {pattern : OpenDiagram arguments}
    {source : ItemSeq
      (outer ++ (before ++ .rel arguments :: after))}
    {result : Region (outer ++ (before ++ after))}
    {instantiated : Region outer}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Content.Cut.rootFrame outer before after arguments).sourceKeep
        (Content.Cut.rootFrame outer before after arguments).selected
        source result)
    (sites : ItemsSites (Content.Cut.operation arguments)
      (Content.Cut.targetHead outer before after arguments) evidence)
    (request : Telescope.Request instantiated
      (.mk (before ++ .rel arguments :: after) source))
    (prepare : request.Preparation
      (Region.adjoinAt (before ++ .rel arguments :: after) .nil
        (itemsEdit
          (operation := Content.Cut.operation arguments)
          (Content.Cut.targetHead outer before after arguments)
          evidence sites).endpoint)) :
    request.Result := by
  generalize outputEq :
    itemsEdit (operation := Content.Cut.operation arguments)
      (Content.Cut.targetHead outer before after arguments)
      evidence sites = output at prepare
  cases output with
  | mk edit staged runEq =>
      let description : Content.Cut.Wrap.Description outer := {
        arguments := arguments
        before := before
        after := after
        items := source
        itemsEdit := edit
      }
      let prepared := Region.adjoinAt
        (before ++ .rel arguments :: after) .nil staged
      have preparedEq : prepared = description.target := by
        change Region.adjoinAt (before ++ .rel arguments :: after) .nil
            staged =
          Region.adjoinAt (before ++ .rel arguments :: after) .nil edit.run
        rw [runEq]
      let preparation : request.Preparation description.target :=
        preparedEq ▸ prepare
      have pendingEq :
          (.mk (before ++ .rel arguments :: after) source : Region outer) =
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
        localRule := symmetric Content.Cut.Local
        inject := fun step => Step.cutShape step
        preparedCanonical := preparation.preparedCanonical
        preparedExternalTwoEnded := preparation.preparedExternalTwoEnded
        rawPreparedCanonical := preparation.rawPreparedCanonical
        rawPreparedExternalTwoEnded := preparation.rawPreparedExternalTwoEnded
        rawPendingCanonical := rawPendingCanonical
        rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
        preparedIso := preparation.preparedIso
        pendingIso := RegionIso.ofEq pendingEq
        localStep := Or.inr (.wrap (.mk description))
        preparation := preparation.telescope
      }
      exact branch.compile

/-- Compile one authoritative pattern-local wire through the single Arity
primitive at the binder home. The preparation is indexed by the deterministic
all-sites edit endpoint. -/
theorem itemsArity
    {arguments outer before after : List Sig}
    {added : Sig}
    {pattern : OpenDiagram arguments}
    {source : ItemSeq
      (outer ++ (before ++ .rel arguments :: after))}
    {result : Region (outer ++ (before ++ after))}
    {instantiated : Region outer}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Arity.rootFrame outer before after arguments added).sourceKeep
        (Arity.rootFrame outer before after arguments added).selected
        source result)
    (sites : ItemsSites (Arity.operation arguments added)
      (Arity.targetHead outer before after arguments added) evidence)
    (request : Telescope.Request instantiated
      (.mk (before ++ .rel arguments :: after) source))
    (prepare : request.Preparation
      (Region.adjoinAt
        (before ++ .rel (arguments ++ [added]) :: after) .nil
        (itemsEdit (operation := Arity.operation arguments added)
          (Arity.targetHead outer before after arguments added)
          evidence sites).endpoint)) :
    request.Result := by
  generalize outputEq :
    itemsEdit (operation := Arity.operation arguments added)
      (Arity.targetHead outer before after arguments added)
      evidence sites = output at prepare
  cases output with
  | mk edit staged runEq =>
      let description : Arity.Shift.Description outer := {
        arguments := arguments
        before := before
        after := after
        added := added
        items := source
        itemsEdit := edit
      }
      let prepared := Region.adjoinAt
        (before ++ .rel (arguments ++ [added]) :: after) .nil staged
      have preparedEq : prepared = description.target := by
        change Region.adjoinAt
            (before ++ .rel (arguments ++ [added]) :: after) .nil staged =
          Region.adjoinAt
            (before ++ .rel (arguments ++ [added]) :: after) .nil edit.run
        rw [runEq]
      let preparation : request.Preparation description.target :=
        preparedEq ▸ prepare
      have pendingEq :
          (.mk (before ++ .rel arguments :: after) source : Region outer) =
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
        localRule := symmetric Arity.Local
        inject := fun step => Step.arity step
        preparedCanonical := preparation.preparedCanonical
        preparedExternalTwoEnded := preparation.preparedExternalTwoEnded
        rawPreparedCanonical := preparation.rawPreparedCanonical
        rawPreparedExternalTwoEnded := preparation.rawPreparedExternalTwoEnded
        rawPendingCanonical := rawPendingCanonical
        rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
        preparedIso := preparation.preparedIso
        pendingIso := RegionIso.ofEq pendingEq
        localStep := Or.inr (.shift (.mk description))
        preparation := preparation.telescope
      }
      exact branch.compile

/-- Compile one authoritative conjunction layer through the single
ParallelShape primitive at the binder home. Recursive child compilation has
already supplied the one combined preparation ending at the deterministic
all-sites edit endpoint. -/
theorem itemsParallel
    {arguments outer before after : List Sig}
    {pattern : OpenDiagram arguments}
    {source : ItemSeq
      (outer ++ (before ++ .rel arguments :: after))}
    {result : Region (outer ++ (before ++ after))}
    {instantiated : Region outer}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Content.Parallel.rootFrame outer before after arguments).sourceKeep
        (Content.Parallel.rootFrame outer before after arguments).selected
        source result)
    (sites : ItemsSites (Content.Parallel.operation arguments)
      (Content.Parallel.firstHead outer before after arguments,
        Content.Parallel.secondHead outer before after arguments)
      evidence)
    (request : Telescope.Request instantiated
      (.mk (before ++ .rel arguments :: after) source))
    (prepare : request.Preparation
      (Region.adjoinAt
        (before ++ .rel arguments :: .rel arguments :: after) .nil
        (itemsEdit (operation := Content.Parallel.operation arguments)
          (Content.Parallel.firstHead outer before after arguments,
            Content.Parallel.secondHead outer before after arguments)
          evidence sites).endpoint)) :
    request.Result := by
  generalize outputEq :
    itemsEdit (operation := Content.Parallel.operation arguments)
      (Content.Parallel.firstHead outer before after arguments,
        Content.Parallel.secondHead outer before after arguments)
      evidence sites = output at prepare
  cases output with
  | mk edit staged runEq =>
      let description : Content.Parallel.Split.Description outer := {
        arguments := arguments
        before := before
        after := after
        items := source
        itemsEdit := edit
      }
      let prepared := Region.adjoinAt
        (before ++ .rel arguments :: .rel arguments :: after) .nil staged
      have preparedEq : prepared = description.target := by
        change Region.adjoinAt
            (before ++ .rel arguments :: .rel arguments :: after) .nil
              staged =
          Region.adjoinAt
            (before ++ .rel arguments :: .rel arguments :: after) .nil
              edit.run
        rw [runEq]
      let preparation : request.Preparation description.target :=
        preparedEq ▸ prepare
      have pendingEq :
          (.mk (before ++ .rel arguments :: after) source : Region outer) =
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
        localRule := symmetric Content.Parallel.Local
        inject := fun step => Step.parallelShape step
        preparedCanonical := preparation.preparedCanonical
        preparedExternalTwoEnded := preparation.preparedExternalTwoEnded
        rawPreparedCanonical := preparation.rawPreparedCanonical
        rawPreparedExternalTwoEnded := preparation.rawPreparedExternalTwoEnded
        rawPendingCanonical := rawPendingCanonical
        rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
        preparedIso := preparation.preparedIso
        pendingIso := RegionIso.ofEq pendingEq
        localStep := Or.inr (.split (.mk description))
        preparation := preparation.telescope
      }
      exact branch.compile


/-- Compile one complete selected-application layer through formal
application. Boundary and equality compilation prepare the authoritative
instantiation endpoint to the exact all-sites transform endpoint; this theorem
owns the mandatory primitive at the comprehension binder's home occurrence. -/
theorem itemsFormal
    {outer localBefore localAfter before after : List Sig}
    {pattern : OpenDiagram
      (before ++ .rel (before ++ after) :: after)}
    {source : ItemSeq
      (outer ++ (localBefore ++
        .rel (before ++ .rel (before ++ after) :: after) :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    {instantiated : Region outer}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Leaf.Formal.rootFrame outer localBefore localAfter before after).sourceKeep
        (Leaf.Formal.rootFrame outer localBefore localAfter before after).selected
        source result)
    (sites : ItemsSites (Leaf.Formal.operation before after) PUnit.unit
      evidence)
    (request : Telescope.Request instantiated
      (.mk
        (localBefore ++
          .rel (before ++ .rel (before ++ after) :: after) :: localAfter)
        source))
    (prepare : request.Preparation
      (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
        (itemsEdit (operation := Leaf.Formal.operation before after)
          PUnit.unit evidence sites).endpoint)) :
    request.Result := by
  generalize outputEq :
    itemsEdit (operation := Leaf.Formal.operation before after)
      PUnit.unit evidence sites = output at prepare
  cases output with
  | mk edit staged runEq =>
          let description : Leaf.Formal.Applies.Description outer := {
            before := before
            after := after
            localBefore := localBefore
            localAfter := localAfter
            items := source
            itemsEdit := edit
          }
          have stagedEq :
              Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
                description.target := by
            change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
              Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
            rw [runEq]
          let preparation : request.Preparation description.target :=
            stagedEq ▸ prepare
          have pendingEq :
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                source : Region outer) = description.source := by
            rfl
          have rawPendingCanonical :
              (request.occurrence.context.fill
                description.source).Canonical := by
            rw [← pendingEq]
            exact request.pendingCanonical
          have rawPendingExternalTwoEnded :
              OpenDiagram.ExternalTwoEnded
                request.occurrence.interface.boundaryWire
                (request.occurrence.context.fill description.source) := by
            rw [← pendingEq]
            exact request.pendingExternalTwoEnded
          have pendingIso : RegionIso (WireEquiv.refl outer)
              (.mk
                (localBefore ++
                  .rel (before ++ .rel (before ++ after) :: after) ::
                    localAfter)
                source)
              description.source := by
            rw [← pendingEq]
            exact RegionIso.refl _
          let branch : request.Branch preparation.prepared := {
            rawPrepared := description.target
            rawPending := description.source
            localRule := Leaf.Formal.Local
            inject := fun step => Step.formalApplication step
            preparedCanonical := preparation.preparedCanonical
            preparedExternalTwoEnded :=
              preparation.preparedExternalTwoEnded
            rawPreparedCanonical := preparation.rawPreparedCanonical
            rawPreparedExternalTwoEnded :=
              preparation.rawPreparedExternalTwoEnded
            rawPendingCanonical := rawPendingCanonical
            rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
            preparedIso := preparation.preparedIso
            pendingIso := pendingIso
            localStep := .abstractFormal (.mk description)
            preparation := preparation.telescope
          }
          have stagedIso : RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              branch.rawPrepared := by
            change RegionIso (WireEquiv.refl outer)
              (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
              description.target
            rw [stagedEq]
            exact RegionIso.refl _
          exact (Telescope.Request.Discharge.primitive branch stagedIso).compile

/-- Compile one complete selected-application layer through identity leaf.
The preparation is indexed by the deterministic all-sites edit endpoint, and
this theorem owns the single directed primitive at the binder home. -/
theorem itemsIdentity
    {outer localBefore localAfter : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram (List.replicate arity signature)}
    {source : ItemSeq
      (outer ++ (localBefore ++
        .rel (List.replicate arity signature) :: localAfter))}
    {result : Region (outer ++ (localBefore ++ localAfter))}
    {instantiated : Region outer}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        (Leaf.Identity.rootFrame outer localBefore localAfter signature
          arity).sourceKeep
        (Leaf.Identity.rootFrame outer localBefore localAfter signature
          arity).selected
        source result)
    (sites : ItemsSites (Leaf.Identity.operation signature arity) PUnit.unit
      evidence)
    (request : Telescope.Request instantiated
      (.mk
        (localBefore ++ .rel (List.replicate arity signature) :: localAfter)
        source))
    (prepare : request.Preparation
      (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil
        (itemsEdit (operation := Leaf.Identity.operation signature arity)
          PUnit.unit evidence sites).endpoint)) :
    request.Result := by
  generalize outputEq :
    itemsEdit (operation := Leaf.Identity.operation signature arity)
      PUnit.unit evidence sites = output at prepare
  cases output with
  | mk edit staged runEq =>
      let description : Leaf.Identity.Leaves.Description outer := {
        signature := signature
        arity := arity
        localBefore := localBefore
        localAfter := localAfter
        items := source
        itemsEdit := edit
      }
      have stagedEq :
          Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged =
            description.target := by
        change Region.adjoinAt (localBefore ++ localAfter) .nil staged =
          Region.adjoinAt (localBefore ++ localAfter) .nil edit.run
        rw [runEq]
      let preparation : request.Preparation description.target :=
        stagedEq ▸ prepare
      have pendingEq :
          (.mk
            (localBefore ++
              .rel (List.replicate arity signature) :: localAfter)
            source : Region outer) = description.source := by
        rfl
      have rawPendingCanonical :
          (request.occurrence.context.fill description.source).Canonical := by
        rw [← pendingEq]
        exact request.pendingCanonical
      have rawPendingExternalTwoEnded :
          OpenDiagram.ExternalTwoEnded
            request.occurrence.interface.boundaryWire
            (request.occurrence.context.fill description.source) := by
        rw [← pendingEq]
        exact request.pendingExternalTwoEnded
      have pendingIso : RegionIso (WireEquiv.refl outer)
          (.mk
            (localBefore ++
              .rel (List.replicate arity signature) :: localAfter)
            source)
          description.source := by
        rw [← pendingEq]
        exact RegionIso.refl _
      let branch : request.Branch preparation.prepared := {
        rawPrepared := description.target
        rawPending := description.source
        localRule := Leaf.Identity.Local
        inject := fun step => Step.identityLeaf step
        preparedCanonical := preparation.preparedCanonical
        preparedExternalTwoEnded := preparation.preparedExternalTwoEnded
        rawPreparedCanonical := preparation.rawPreparedCanonical
        rawPreparedExternalTwoEnded :=
          preparation.rawPreparedExternalTwoEnded
        rawPendingCanonical := rawPendingCanonical
        rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
        preparedIso := preparation.preparedIso
        pendingIso := pendingIso
        localStep := .abstractIdentity (.mk description)
        preparation := preparation.telescope
      }
      have stagedIso : RegionIso (WireEquiv.refl outer)
          (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
          branch.rawPrepared := by
        change RegionIso (WireEquiv.refl outer)
          (Region.adjoinAt (localBefore ++ ([] ++ localAfter)) .nil staged)
          description.target
        rw [stagedEq]
        exact RegionIso.refl _
      exact (Telescope.Request.Discharge.primitive branch stagedIso).compile

namespace PatternCompiler

namespace EqualityNormalization

def formalPorts (arguments : List Sig) : Vars arguments arguments :=
  Erasure.Exposure.identityBoundary arguments

theorem formalPorts_append (left right : List Sig) :
    formalPorts (left ++ right) =
      Vars.extend
        ((formalPorts left).map fun wire => wire.appendLeft right)
        ((formalPorts right).map fun wire => Var.appendRight left wire) := by
  induction left with
  | nil =>
      simp [formalPorts, Erasure.Exposure.identityBoundary, Vars.map,
        Vars.extend, Var.appendRight]
  | cons head tail induction =>
      change Vars.cons .here
          ((formalPorts (tail ++ right)).map fun wire => .there wire) = _
      rw [induction, Vars.map_extend, Vars.map_map, Vars.map_map]
      apply congrArg (Vars.cons .here)
      congr 1
      · rw [Vars.map_map]
        apply Vars.map_congr
        intro signature wire
        rfl

private theorem Vars.get_map
    (variables : Vars source signatures)
    (rename : ∀ {signature}, Var source signature → Var target signature)
    (position : Fin signatures.length) :
    (variables.map rename).get position = rename (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun rest => induction rest) position

private theorem formalPorts_get_index (position : Fin arguments.length) :
    ((formalPorts arguments).get position).index = position := by
  exact Erasure.Exposure.identityBoundary_get_index position

private theorem formalPorts_surjective (wire : Fin arguments.length) :
    ∃ position : Fin arguments.length,
      ((formalPorts arguments).get position).index = wire :=
  ⟨wire, formalPorts_get_index wire⟩

private theorem equalityItems_left_mem_nil
    (left right : Vars wires signatures)
    (position : Fin signatures.length) (itemIndex : Nat) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      left right).incidencePaths (left.get position).index.val itemIndex := by
  induction left generalizing itemIndex with
  | nil => cases right; exact Fin.elim0 position
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          revert itemIndex
          refine Fin.cases (fun itemIndex => ?_)
            (fun rest itemIndex => ?_) position
          · change [] ∈
              (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
                (.cons leftHead leftTail)
                (.cons rightHead rightTail)).incidencePaths
                  leftHead.index.val itemIndex
            simp only [
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems,
              ItemSeq.incidencePaths, Item.incidencePaths,
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityPorts,
              List.mem_append, List.mem_replicate]
            apply Or.inl
            constructor
            · intro countZero
              have absent := List.count_eq_zero.mp countZero
              exact absent (by simp)
            · trivial
          · simp only [
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems,
              ItemSeq.incidencePaths, List.mem_append]
            exact Or.inr (induction rightTail rest (itemIndex + 1))

/-- Exact local list produced by the defining instantiation operations. -/
private def locals (pattern : OpenDiagram arguments) : List Sig :=
  pattern.external ++ (pattern.body.locals ++ [])

private def bodyEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming (pattern.external ++ pattern.body.locals)
      (targetWires ++ locals pattern) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire targetWires pattern.external
      (pattern.body.locals ++ []))
    (WireRenaming.comp
      (Region.conjoinLeftWire (targetWires ++ pattern.external)
        pattern.body.locals [])
      ((⟨fun wire => Var.appendRight targetWires wire⟩ :
        WireRenaming pattern.external
          (targetWires ++ pattern.external)).appendRight pattern.body.locals))

private def equalityEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming ((targetWires ++ pattern.external) ++ [])
      (targetWires ++ locals pattern) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire targetWires pattern.external
      (pattern.body.locals ++ []))
    (Region.conjoinRightWire (targetWires ++ pattern.external)
      pattern.body.locals [])

private def actualEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming targetWires (targetWires ++ locals pattern) :=
  ⟨fun wire => equalityEmbedding pattern targetWires
    ((wire.appendLeft pattern.external).appendLeft [])⟩

private def patternEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming pattern.external (targetWires ++ locals pattern) :=
  ⟨fun wire => equalityEmbedding pattern targetWires
    ((Var.appendRight targetWires wire).appendLeft [])⟩

private def items (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    ItemSeq (targetWires ++ locals pattern) :=
  (pattern.body.items.renameWires (bodyEmbedding pattern targetWires)).append
    (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      (ports.map fun wire => actualEmbedding pattern targetWires wire)
      (pattern.boundaryWire.map
        fun wire => patternEmbedding pattern targetWires wire))

private theorem bodyEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (bodyEmbedding pattern sourceWires) =
      bodyEmbedding pattern targetWires := by
  apply WireRenaming.ext
  intro signature wire
  apply Var.appendCases (left := pattern.external)
    (right := pattern.body.locals)
    (motive := fun wire =>
      WireRenaming.comp (rename.appendRight (locals pattern))
          (bodyEmbedding pattern sourceWires) wire =
        bodyEmbedding pattern targetWires wire)
  · intro externalSignature external
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]

private theorem actualEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (actualEmbedding pattern sourceWires) =
      WireRenaming.comp (actualEmbedding pattern targetWires) rename := by
  apply WireRenaming.ext
  intro signature wire
  simp [actualEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    WireRenaming.appendRight, Region.adjoinMaterialWire,
    Region.conjoinRightWire]

private theorem patternEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (patternEmbedding pattern sourceWires) =
      patternEmbedding pattern targetWires := by
  apply WireRenaming.ext
  intro signature wire
  simp [patternEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    WireRenaming.appendRight, Region.adjoinMaterialWire,
    Region.conjoinRightWire]

@[simp] private theorem actualEmbedding_index_val
    (pattern : OpenDiagram arguments)
    (wire : Var targetWires signature) :
    (actualEmbedding pattern targetWires wire).index.val = wire.index.val := by
  simp [actualEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    Region.adjoinMaterialWire, Region.conjoinRightWire]

private theorem bodyEmbedding_index_lower
    (pattern : OpenDiagram arguments)
    (wire : Var (pattern.external ++ pattern.body.locals) signature) :
    targetWires.length ≤
      (bodyEmbedding pattern targetWires wire).index.val := by
  apply Var.appendCases (left := pattern.external)
    (right := pattern.body.locals)
    (motive := fun wire => targetWires.length ≤
      (bodyEmbedding pattern targetWires wire).index.val)
  · intro externalSignature external
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]

private theorem patternEmbedding_index_lower
    (pattern : OpenDiagram arguments)
    (wire : Var pattern.external signature) :
    targetWires.length ≤
      (patternEmbedding pattern targetWires wire).index.val := by
  simp [patternEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    Region.adjoinMaterialWire, Region.conjoinRightWire]

private theorem Vars.map_comp4
    (variables : Vars first signatures)
    (firstMap : ∀ {signature}, Var first signature → Var second signature)
    (secondMap : ∀ {signature}, Var second signature → Var third signature)
    (thirdMap : ∀ {signature}, Var third signature → Var fourth signature)
    (fourthMap : ∀ {signature}, Var fourth signature → Var fifth signature) :
    (((variables.map fun wire => firstMap wire).map
      fun wire => secondMap wire).map fun wire => thirdMap wire).map
        (fun wire => fourthMap wire) =
      variables.map fun wire =>
        fourthMap (thirdMap (secondMap (firstMap wire))) := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons
        (fourthMap (thirdMap (secondMap (firstMap head))))) induction

private theorem instantiate_eq_presentation
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports = .mk (locals pattern) (items pattern ports) := by
  cases pattern with
  | mk external boundaryWire boundarySurjective body canonical
      externalTwoEnded =>
    cases body with
    | mk bodyLocals bodyItems =>
      simp only [
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate,
        _root_.VisualProof.Rule.Comprehension.Instantiation.Equalities_eq_ofItems,
        items, bodyEmbedding, actualEmbedding, patternEmbedding,
        equalityEmbedding, locals,
        Region.locals, Region.items, Region.renameWires, Region.conjoin,
        Region.adjoinAt, Region.ofItems, ItemSeq.renameWires_append,
        ItemSeq.renameWires_comp,
        _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires]
      simp only [ItemSeq.renameWires, ItemSeq.nil_append,
        Vars.map_comp4, WireRenaming.comp]

private theorem instantiate_renameWires
    (pattern : OpenDiagram arguments)
    (ports : Vars sourceWires arguments)
    (rename : WireRenaming sourceWires targetWires) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).renameWires rename =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate pattern
        (ports.map fun wire => rename wire) := by
  have actualMap :
      (ports.map fun wire => actualEmbedding pattern sourceWires wire).map
          (fun wire => rename.appendRight (locals pattern) wire) =
        (ports.map fun wire => rename wire).map
          (fun wire => actualEmbedding pattern targetWires wire) := by
    calc
      _ = ports.map (fun wire =>
          rename.appendRight (locals pattern)
            (actualEmbedding pattern sourceWires wire)) :=
        Diagram.vars_map_comp ports (actualEmbedding pattern sourceWires)
          (rename.appendRight (locals pattern))
      _ = ports.map (fun wire =>
          actualEmbedding pattern targetWires (rename wire)) := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming sourceWires
              (targetWires ++ locals pattern) =>
            ports.map fun wire => map wire)
          (actualEmbedding_natural pattern rename)
      _ = _ := (Diagram.vars_map_comp ports rename
        (actualEmbedding pattern targetWires)).symm
  have patternMap :
      (pattern.boundaryWire.map
          fun wire => patternEmbedding pattern sourceWires wire).map
            (fun wire => rename.appendRight (locals pattern) wire) =
        pattern.boundaryWire.map
          (fun wire => patternEmbedding pattern targetWires wire) := by
    calc
      _ = pattern.boundaryWire.map (fun wire =>
          rename.appendRight (locals pattern)
            (patternEmbedding pattern sourceWires wire)) :=
        Diagram.vars_map_comp pattern.boundaryWire
          (patternEmbedding pattern sourceWires)
          (rename.appendRight (locals pattern))
      _ = _ := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming pattern.external
              (targetWires ++ locals pattern) =>
            pattern.boundaryWire.map fun wire => map wire)
          (patternEmbedding_natural pattern rename)
  rw [instantiate_eq_presentation, instantiate_eq_presentation]
  simp only [Region.renameWires, items, ItemSeq.renameWires_append,
    ItemSeq.renameWires_comp,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires]
  rw [bodyEmbedding_natural, actualMap, patternMap]

/-- Every actual port of an instantiation has a root-level equality
incidence. -/
private theorem instantiate_port_incidence_mem_nil
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (position : Fin arguments.length) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths (ports.get position).index.val := by
  rw [instantiate_eq_presentation]
  simp only [Region.incidencePaths, items, ItemSeq.incidencePaths_append]
  have selected := equalityItems_left_mem_nil
    (ports.map fun wire => actualEmbedding pattern targetWires wire)
    (pattern.boundaryWire.map
      fun wire => patternEmbedding pattern targetWires wire)
    position (pattern.body.items.renameWires
      (bodyEmbedding pattern targetWires)).length
  have selectedIndex :
      ((ports.map fun wire => actualEmbedding pattern targetWires wire).get
        position).index.val = (ports.get position).index.val := by
    rw [Vars.get_map]
    simp [actualEmbedding, equalityEmbedding, WireRenaming.comp,
      Region.conjoinRightWire, Region.adjoinMaterialWire, locals]
  rw [selectedIndex] at selected
  exact List.mem_append_right _ (by
    simpa only [Nat.zero_add] using selected)

/-- Every actual port of an instantiation has an equality incidence. -/
private theorem instantiate_port_incidence_nonempty
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (position : Fin arguments.length) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths (ports.get position).index.val ≠ [] :=
  List.ne_nil_of_mem (instantiate_port_incidence_mem_nil pattern ports position)

private theorem Vars.countIndex_map_zero_of_lower
    (variables : Vars source signatures)
    (rename : WireRenaming source target)
    (floor wireIndex : Nat)
    (lower : ∀ {signature} (wire : Var source signature),
      floor ≤ (rename wire).index.val)
    (below : wireIndex < floor) :
    (variables.map fun wire => rename wire).countIndex wireIndex = 0 := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex]
      have different : (rename head).index.val ≠ wireIndex := by
        intro equality
        have := lower head
        omega
      simp only [different, if_false, Nat.zero_add]
      exact induction

private theorem Vars.countIndex_map_actual
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires signatures)
    (wireIndex : Nat) :
    (ports.map fun wire => actualEmbedding pattern targetWires wire).countIndex
        wireIndex = ports.countIndex wireIndex := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex, actualEmbedding_index_val,
        induction]

private theorem instantiate_incidencePaths_length
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val).length =
      ports.countIndex wire.index.val := by
  have bodyEmpty :
      (pattern.body.items.renameWires
        (bodyEmbedding pattern targetWires)).incidencePaths
          wire.index.val 0 = [] := by
    apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
    · have bound := wire.index.isLt
      simp only [List.length_append]
      omega
    · intro bodySignature bodyWire equality
      have lower := bodyEmbedding_index_lower
        (targetWires := targetWires) pattern bodyWire
      have bound := wire.index.isLt
      omega
  have rightZero :
      (pattern.boundaryWire.map
        fun boundaryWire => patternEmbedding pattern targetWires
          boundaryWire).countIndex wire.index.val = 0 := by
    apply Vars.countIndex_map_zero_of_lower pattern.boundaryWire
      (patternEmbedding pattern targetWires) targetWires.length
        wire.index.val
    · exact patternEmbedding_index_lower
        (targetWires := targetWires) pattern
    · exact wire.index.isLt
  rw [instantiate_eq_presentation]
  simp only [Region.incidencePaths, items, ItemSeq.incidencePaths_append,
    List.length_append,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_incidencePaths_length,
    bodyEmpty,
    List.length_nil, Nat.zero_add, Vars.countIndex_map_actual, rightZero,
    Nat.add_zero]

private theorem instantiate_incidence_nonempty_iff
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val ≠ [] ↔
      0 < ports.countIndex wire.index.val := by
  rw [← List.length_pos_iff, instantiate_incidencePaths_length]

/-- Replace an arbitrary valid pattern boundary by the ordered identity
boundary over its argument context. Its body is the exact existing-syntax
instantiation of the original pattern on those formal variables. -/
def identityBoundary (pattern : OpenDiagram arguments) :
    OpenDiagram arguments where
  external := arguments
  boundaryWire := formalPorts arguments
  boundarySurjective := formalPorts_surjective
  body := _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
    pattern (formalPorts arguments)
  canonical :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
      pattern (formalPorts arguments)
  externalTwoEnded := by
    intro signature wire
    have boundaryPositive :
        0 < (formalPorts arguments).countIndex wire.index.val := by
      obtain ⟨position, maps⟩ := formalPorts_surjective wire.index
      have positive := (formalPorts arguments).countIndex_get_positive position
      rw [maps] at positive
      exact positive
    have bodyPositive : 0 <
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (formalPorts arguments)).incidencePaths
            wire.index.val).length := by
      have nonempty := instantiate_port_incidence_nonempty pattern
        (formalPorts arguments) wire.index
      rw [formalPorts_get_index] at nonempty
      exact List.length_pos_iff.mpr nonempty
    omega

def formalSubstitution : {arguments : List Sig} →
    Vars targetWires arguments → WireRenaming arguments targetWires
  | [], .nil => ⟨fun wire => nomatch wire⟩
  | _ :: _, .cons head tail => ⟨fun wire =>
      match wire with
      | .here => head
      | .there rest => formalSubstitution tail rest⟩

@[simp] theorem formalSubstitution_here
    (head : Var targetWires signature)
    (tail : Vars targetWires arguments) :
    formalSubstitution (.cons head tail) (.here : Var (signature :: arguments)
      signature) = head := rfl

theorem formalPorts_map_substitution
    (ports : Vars targetWires arguments) :
    (formalPorts arguments).map
      (fun wire => formalSubstitution ports wire) = ports := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [formalPorts, Erasure.Exposure.identityBoundary, Vars.map,
        formalSubstitution_here]
      congr 1
      rw [Diagram.vars_map_comp
        (Erasure.Exposure.identityBoundary _) ⟨fun wire => .there wire⟩
          (formalSubstitution (.cons head tail))]
      change (formalPorts _).map
        (fun wire => formalSubstitution tail wire) = tail
      exact induction

theorem formalSubstitution_formalPorts_map
    (rename : WireRenaming arguments targetWires)
    {signature : Sig} (wire : Var arguments signature) :
    formalSubstitution
        ((formalPorts arguments).map fun formalWire => rename formalWire) wire =
      rename wire := by
  induction arguments with
  | nil => exact nomatch wire
  | cons head rest induction =>
      cases wire with
      | here => rfl
      | there wire =>
          simp only [formalPorts, Erasure.Exposure.identityBoundary, Vars.map]
          let restRename : WireRenaming rest targetWires :=
            ⟨fun restWire => rename (.there restWire)⟩
          have tailEq :
              ((Erasure.Exposure.identityBoundary rest).map
                  fun restWire => (.there restWire : Var (head :: rest) _)).map
                    (fun restWire => rename restWire) =
                (formalPorts rest).map fun restWire => restRename restWire := by
            exact Diagram.vars_map_comp
              (Erasure.Exposure.identityBoundary rest)
              ⟨fun restWire => .there restWire⟩ rename
          simp only [formalSubstitution]
          rw [tailEq]
          exact induction restRename wire

theorem formalSubstitution_map
    (application : Vars source arguments)
    (rename : WireRenaming source target)
    {signature : Sig} (wire : Var arguments signature) :
    formalSubstitution (application.map fun applicationWire =>
        rename applicationWire) wire =
      rename (formalSubstitution application wire) := by
  induction application with
  | nil => exact nomatch wire
  | cons head tail induction =>
      cases wire with
      | here => rfl
      | there wire => exact induction wire

private theorem formalPorts_eq_exposure :
    formalPorts arguments = Erasure.Exposure.identityBoundary arguments := by
  rfl

private theorem supportPins_eq_nil
    (material : Region materialWires)
    (variables : Vars materialWires signatures)
    (supported : ∀ position : Fin signatures.length,
      material.incidencePaths (variables.get position).index.val ≠ []) :
    Erasure.Exposure.supportPins material signatures variables = .nil := by
  induction variables with
  | nil => rfl
  | @cons signature rest head tail induction =>
      have headSupported : material.incidencePaths head.index.val ≠ [] := by
        simpa only [Vars.get] using supported 0
      have tailSupported : ∀ position : Fin rest.length,
          material.incidencePaths (tail.get position).index.val ≠ [] := by
        intro position
        simpa only [Vars.get] using supported position.succ
      simp only [Erasure.Exposure.supportPins, headSupported, ↓reduceIte]
      exact induction tailSupported

theorem normalized_supportPins_eq_nil
    (pattern : OpenDiagram arguments) :
    Erasure.Exposure.supportPins
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments))
      arguments (Erasure.Exposure.identityBoundary arguments) = .nil := by
  apply supportPins_eq_nil
  intro position
  simpa only [← formalPorts_eq_exposure] using
    instantiate_port_incidence_nonempty pattern
      (formalPorts arguments) position

private theorem supportBody_eq_of_supportPins_nil
    (material : Region materialWires)
    (empty : Erasure.Exposure.supportPins material materialWires
      (Erasure.Exposure.identityBoundary materialWires) = .nil) :
    Erasure.Exposure.supportBody material = material := by
  unfold Erasure.Exposure.supportBody
  rw [empty]
  cases material with
  | mk locals materialItems =>
      change Region.mk locals (materialItems.append .nil) =
        Region.mk locals materialItems
      rw [ItemSeq.append_nil]

private theorem OpenDiagram.eq_of_data
    (left right : OpenDiagram boundary)
    (externalEq : left.external = right.external)
    (boundaryEq : HEq left.boundaryWire right.boundaryWire)
    (bodyEq : HEq left.body right.body) : left = right := by
  cases left with
  | mk leftExternal leftBoundary leftSurjective leftBody leftCanonical
      leftTwoEnded =>
    cases right with
    | mk rightExternal rightBoundary rightSurjective rightBody rightCanonical
        rightTwoEnded =>
      simp only at externalEq boundaryEq bodyEq
      cases externalEq
      cases boundaryEq
      cases bodyEq
      rfl

theorem normalized_supportBody_eq
    (pattern : OpenDiagram arguments) :
    Erasure.Exposure.supportBody
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments)) =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments) := by
  apply supportBody_eq_of_supportPins_nil
  exact normalized_supportPins_eq_nil pattern

theorem supportPattern_eq_identityBoundary
    (pattern : OpenDiagram arguments)
    (materialCanonical :
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments)).Canonical) :
    Erasure.Exposure.supportPattern
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (formalPorts arguments)) materialCanonical =
      identityBoundary pattern := by
  apply OpenDiagram.eq_of_data
  · rfl
  · rfl
  · exact heq_of_eq (normalized_supportBody_eq pattern)

private def exposureDescriptionWithHost
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    Rule.Erasure.Description outer where
  materialWires := arguments
  hostLocals := hostLocals
  hostItems := hostItems
  material := _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
    pattern (formalPorts arguments)
  wireMap := formalSubstitution ports

private theorem exposureDescriptionWithHost_source
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    (exposureDescriptionWithHost pattern hostLocals hostItems ports).source =
      Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports) := by
  simp only [Rule.Erasure.Description.source,
    exposureDescriptionWithHost, Region.spliceAt]
  rw [instantiate_renameWires, formalPorts_map_substitution]

private theorem exposureDescriptionWithHost_applicationPorts
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    Erasure.Exposure.applicationPorts
      (exposureDescriptionWithHost pattern hostLocals hostItems ports) =
      ports := by
  simp only [Erasure.Exposure.applicationPorts,
    exposureDescriptionWithHost]
  rw [← formalPorts_eq_exposure, formalPorts_map_substitution]

private theorem exposureDescriptionWithHost_exposedRegion
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments)
    (materialCanonical :
      (exposureDescriptionWithHost pattern hostLocals hostItems ports).material.Canonical) :
    Erasure.Exposure.exposedRegion
        (exposureDescriptionWithHost pattern hostLocals hostItems ports)
        materialCanonical =
      Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (identityBoundary pattern) ports) := by
  simp only [Erasure.Exposure.exposedRegion]
  change Region.adjoinAt hostLocals hostItems
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern (formalPorts arguments)) materialCanonical)
        (Erasure.Exposure.applicationPorts
          (exposureDescriptionWithHost pattern hostLocals hostItems ports))) =
    _
  rw [supportPattern_eq_identityBoundary pattern materialCanonical,
    exposureDescriptionWithHost_applicationPorts]

private theorem Vars.exists_get_index_of_countIndex_pos
    (variables : Vars context signatures) (wireIndex : Nat)
    (positive : 0 < variables.countIndex wireIndex) :
    ∃ position : Fin signatures.length,
      (variables.get position).index.val = wireIndex := by
  induction variables with
  | nil => simp [Vars.countIndex] at positive
  | @cons signature rest head tail induction =>
      by_cases headEq : head.index.val = wireIndex
      · exact ⟨0, headEq⟩
      · have tailPositive : 0 < tail.countIndex wireIndex := by
          simpa [Vars.countIndex, headEq] using positive
        obtain ⟨position, positionEq⟩ := induction tailPositive
        exact ⟨position.succ, by
          simpa only [Vars.get] using positionEq⟩

private theorem instantiate_incidence_mem_nil_of_nonempty
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature)
    (nonempty :
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports).incidencePaths wire.index.val ≠ []) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val := by
  have positive := (instantiate_incidence_nonempty_iff pattern ports wire).mp
    nonempty
  obtain ⟨position, positionEq⟩ :=
    Vars.exists_get_index_of_countIndex_pos ports wire.index.val positive
  have rootIncidence := instantiate_port_incidence_mem_nil pattern ports position
  rw [positionEq] at rootIncidence
  exact rootIncidence

private theorem instantiate_rootedTwo_iff
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    RegionPath.RootedTwo
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports).incidencePaths wire.index.val) ↔
      2 ≤ ports.countIndex wire.index.val := by
  constructor
  · intro rooted
    have lengthBound := rooted.1
    rw [instantiate_incidencePaths_length] at lengthBound
    exact lengthBound
  · intro countBound
    have nonempty :
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports).incidencePaths wire.index.val ≠ [] :=
      (instantiate_incidence_nonempty_iff pattern ports wire).mpr (by omega)
    constructor
    · rw [instantiate_incidencePaths_length]
      exact countBound
    · exact RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _
        (instantiate_incidence_mem_nil_of_nonempty pattern ports wire nonempty)

mutual
  private def normalizedRegion
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .mk childSites =>
        let childOutput := normalizedItems pattern _ childSites
        ⟨Region.adjoinAt _ .nil childOutput.1,
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            childOutput.2⟩
  termination_by structural sites

  private def normalizedItems
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .nil _ =>
        ⟨Region.blank common,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil⟩
    | .cons itemSites tailSites =>
        let itemOutput := normalizedItem pattern _ itemSites
        let tailOutput := normalizedItems pattern _ tailSites
        ⟨itemOutput.1.conjoin tailOutput.1,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemOutput.2 tailOutput.2⟩
  termination_by structural sites

  private def normalizedItem
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .atom head ports =>
        ⟨Region.singleton (.atom head ports),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            head ports⟩
    | .selectedAtom ports _ =>
        ⟨_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            ports⟩
    | .identity signature arity ports =>
        ⟨Region.singleton (.identity signature arity ports),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            signature arity ports⟩
    | .cut childSites =>
        let childOutput := normalizedRegion pattern _ childSites
        ⟨Region.singleton (.cut childOutput.1),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            childOutput.2⟩
  termination_by structural sites
end

mutual
  /-- Whether the exact site annotation contains any selected application. -/
  private def regionHasSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence) : Bool :=
    match sites with
    | .mk childSites => itemsHaveSelection childSites
  termination_by structural sites

  private def itemsHaveSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites operation data evidence) : Bool :=
    match sites with
    | .nil _ => false
    | .cons itemSites tailSites =>
        itemHasSelection itemSites || itemsHaveSelection tailSites
  termination_by structural sites

  private def itemHasSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites operation data evidence) : Bool :=
    match sites with
    | .atom _ _ => false
    | .selectedAtom _ _ => true
    | .identity _ _ _ => false
    | .cut childSites => regionHasSelection childSites
  termination_by structural sites
end

mutual
  private theorem normalizedRegion_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (none : regionHasSelection sites = false) :
      (normalizedRegion pattern evidence sites).1 = result :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        change Region.adjoinAt locals .nil
            (normalizedItems pattern childEvidence childSites).1 =
          Region.adjoinAt locals .nil childResult
        rw [normalizedItems_eq_of_noSelection pattern childEvidence
          childSites (by simpa only [regionHasSelection] using none)]
  termination_by structural sites

  private theorem normalizedItems_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (none : itemsHaveSelection sites = false) :
      (normalizedItems pattern evidence sites).1 = result :=
    match sites with
    | .nil _ => rfl
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemEndpoint tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        have itemNone : itemHasSelection itemSites = false := by
          cases selected : itemHasSelection itemSites with
          | false => rfl
          | true => simp_all only [itemsHaveSelection, Bool.true_or,
              Bool.true_eq_false]
        have tailNone : itemsHaveSelection tailSites = false := by
          cases selected : itemsHaveSelection tailSites with
          | false => rfl
          | true => simp_all only [itemsHaveSelection, Bool.or_true,
              Bool.true_eq_false]
        change
          (normalizedItem pattern itemEvidence itemSites).1.conjoin
              (normalizedItems pattern tailEvidence tailSites).1 =
            itemEndpoint.conjoin tailResult
        rw [normalizedItem_eq_of_noSelection pattern itemEvidence itemSites
          itemNone]
        rw [normalizedItems_eq_of_noSelection pattern tailEvidence tailSites
          tailNone]
  termination_by structural sites

  private theorem normalizedItem_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (none : itemHasSelection sites = false) :
      (normalizedItem pattern evidence sites).1 = result :=
    match sites with
    | .atom _ _ => rfl
    | .selectedAtom _ _ => by
        simp only [itemHasSelection, Bool.true_eq_false] at none
    | .identity _ _ _ => rfl
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        change Region.singleton
            (.cut (normalizedRegion pattern childEvidence childSites).1) =
          Region.singleton (.cut childResult)
        rw [normalizedRegion_eq_of_noSelection pattern childEvidence
          childSites (by simpa only [itemHasSelection] using none)]
  termination_by structural sites
end

mutual
  private theorem normalizedRegion_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      ScopePreservation result (normalizedRegion pattern evidence sites).1 :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        let childOutput := normalizedItems pattern childEvidence childSites
        let childPreservation :=
          normalizedItems_scope pattern childEvidence childSites
        change ScopePreservation
          (Region.adjoinAt locals .nil childResult)
          (Region.adjoinAt locals .nil childOutput.1)
        constructor
        · intro sourceCanonical
          have sourceChildCanonical : childResult.Canonical :=
            Region.Canonical.material_of_adjoinAt locals .nil childResult
              sourceCanonical
          have targetChildCanonical : childOutput.1.Canonical :=
            childPreservation.canonical sourceChildCanonical
          apply Region.Canonical.adjoinAt_of_material_roots locals .nil
            childOutput.1 True.intro targetChildCanonical
          intro localIndex
          let localWire := Var.appendRight common (Var.ofIndex localIndex)
          have sourceRoot : RegionPath.RootedTwo
              (childResult.incidencePaths localWire.index.val) := by
            simpa [localWire] using
              Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
                childResult sourceCanonical localIndex
          have targetRoot := childPreservation.rootedTwo localWire sourceRoot
          simpa [localWire] using targetRoot
        · intro signature wire
          let childWire := wire.appendLeft locals
          have sourcePaths := Region.incidencePaths_adjoinAt_nil childResult
            childWire
          have targetPaths := Region.incidencePaths_adjoinAt_nil childOutput.1
            childWire
          have childIndex : childWire.index.val = wire.index.val := by
            simp [childWire]
          rw [childIndex] at sourcePaths targetPaths
          rw [sourcePaths, targetPaths]
          simpa only [childWire, Var.index_appendLeft] using
            childPreservation.incidenceNonempty childWire
        · intro signature wire sourceRoot
          let childWire := wire.appendLeft locals
          have sourcePaths := Region.incidencePaths_adjoinAt_nil childResult
            childWire
          have targetPaths := Region.incidencePaths_adjoinAt_nil childOutput.1
            childWire
          have childIndex : childWire.index.val = wire.index.val := by
            simp [childWire]
          rw [childIndex] at sourcePaths targetPaths
          rw [sourcePaths] at sourceRoot
          rw [targetPaths]
          simpa only [childWire, Var.index_appendLeft] using
            childPreservation.rootedTwo childWire (by
              simpa only [childWire, Var.index_appendLeft] using sourceRoot)
  termination_by structural sites

  private theorem normalizedItems_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      ScopePreservation result (normalizedItems pattern evidence sites).1 :=
    match sites with
    | .nil _ => by
        change ScopePreservation (Region.blank common) (Region.blank common)
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemEndpoint tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        let itemOutput := normalizedItem pattern itemEvidence itemSites
        let tailOutput := normalizedItems pattern tailEvidence tailSites
        let itemPreservation := normalizedItem_scope pattern itemEvidence
          itemSites
        let tailPreservation := normalizedItems_scope pattern tailEvidence
          tailSites
        change ScopePreservation (itemEndpoint.conjoin tailResult)
          (itemOutput.1.conjoin tailOutput.1)
        have combined := Region.conjoin_preserves_scope itemEndpoint tailResult
          itemOutput.1 tailOutput.1 itemPreservation.canonical
            tailPreservation.canonical itemPreservation.incidenceNonempty
              tailPreservation.incidenceNonempty itemPreservation.rootedTwo
                tailPreservation.rootedTwo
        exact {
          canonical := combined.1
          incidenceNonempty := fun wire => (combined.2 wire).1
          rootedTwo := fun wire => (combined.2 wire).2
        }
  termination_by structural sites

  private theorem normalizedItem_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      ScopePreservation result (normalizedItem pattern evidence sites).1 :=
    match sites with
    | .atom head ports => by
        change ScopePreservation (Region.singleton (.atom head ports))
          (Region.singleton (.atom head ports))
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | .selectedAtom ports _ => by
        change ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports)
        constructor
        · intro _
          exact
            _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
              (identityBoundary pattern) ports
        · intro signature wire
          rw [instantiate_incidence_nonempty_iff,
            instantiate_incidence_nonempty_iff]
        · intro signature wire sourceRoot
          rw [instantiate_rootedTwo_iff] at sourceRoot ⊢
          exact sourceRoot
    | .identity signature arity ports => by
        change ScopePreservation
          (Region.singleton (.identity signature arity ports))
          (Region.singleton (.identity signature arity ports))
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        let childOutput := normalizedRegion pattern childEvidence childSites
        let childPreservation := normalizedRegion_scope pattern childEvidence
          childSites
        change ScopePreservation (Region.singleton (.cut childResult))
          (Region.singleton (.cut childOutput.1))
        constructor
        · intro sourceCanonical
          apply (Region.singleton_cut_canonical_iff childOutput.1).mpr
          exact childPreservation.canonical
            ((Region.singleton_cut_canonical_iff childResult).mp
              sourceCanonical)
        · intro signature wire
          rw [Region.incidencePaths_singleton_cut,
            Region.incidencePaths_singleton_cut]
          constructor
          · intro sourceNonempty
            have childSourceNonempty :
                childResult.incidencePaths wire.index.val ≠ [] := by
              intro sourceEmpty
              exact sourceNonempty
                ((List.map_eq_nil_iff).mpr sourceEmpty)
            have childTargetNonempty :=
              (childPreservation.incidenceNonempty wire).mp
                childSourceNonempty
            intro targetEmpty
            exact childTargetNonempty
              ((List.map_eq_nil_iff).mp targetEmpty)
          · intro targetNonempty
            have childTargetNonempty :
                childOutput.1.incidencePaths wire.index.val ≠ [] := by
              intro targetEmpty
              exact targetNonempty
                ((List.map_eq_nil_iff).mpr targetEmpty)
            have childSourceNonempty :=
              (childPreservation.incidenceNonempty wire).mpr
                childTargetNonempty
            intro sourceEmpty
            exact childSourceNonempty
              ((List.map_eq_nil_iff).mp sourceEmpty)
        · intro signature wire sourceRoot
          have sameEmpty :
              childResult.incidencePaths wire.index.val = [] ↔
                childOutput.1.incidencePaths wire.index.val = [] := by
            constructor
            · intro sourceEmpty
              by_cases targetEmpty :
                  childOutput.1.incidencePaths wire.index.val = []
              · exact targetEmpty
              · exact False.elim
                  (((childPreservation.incidenceNonempty wire).mpr
                    targetEmpty) sourceEmpty)
            · intro targetEmpty
              by_cases sourceEmpty :
                  childResult.incidencePaths wire.index.val = []
              · exact sourceEmpty
              · exact False.elim
                  (((childPreservation.incidenceNonempty wire).mp
                    sourceEmpty) targetEmpty)
          rw [Region.incidencePaths_singleton_cut] at sourceRoot ⊢
          have replaced := RegionPath.rootedTwo_replace []
            (childResult.incidencePaths wire.index.val)
            (childOutput.1.incidencePaths wire.index.val) [] 0 sameEmpty
          simpa only [List.nil_append, List.append_nil] using
            replaced.mp (by simpa using sourceRoot)
  termination_by structural sites
end

/-- Normalize every selected application in one exact authoritative item
sequence and preserve the canonical, externally two-ended scope of its actual
occurrence. The normalized endpoint and its instantiation evidence are
generated solely from the supplied evidence-indexed sites. -/
theorem normalizeItemsScope
    {arguments common sourceWires targetWires : List Sig}
    (pattern : OpenDiagram arguments)
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ normalized : Region common,
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized ∧
        (occurrence.context.fill normalized).Canonical ∧
        OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill normalized) := by
  let output := normalizedItems pattern evidence sites
  let preservation := normalizedItems_scope pattern evidence sites
  have resultCanonical : result.Canonical :=
    occurrence.context.holeCanonical result occurrence.sourceCanonical
  have normalizedCanonical : output.1.Canonical :=
    preservation.canonical resultCanonical
  have replacement := occurrence.context.replaceCanonical result output.1
    occurrence.sourceCanonical normalizedCanonical
      preservation.incidenceNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill result) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have normalizedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill output.1) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill output.1) replacement.2
  exact ⟨output.1, output.2, replacement.1, normalizedExternalTwoEnded⟩

private def appendHostWire (outer hostLocals : List Sig) :
    WireRenaming outer (outer ++ hostLocals) :=
  ⟨fun wire => wire.appendLeft hostLocals⟩

private theorem conjoin_eq_adjoinRename
    (host material : Region outer) :
    host.conjoin material =
      Region.adjoinAt host.locals host.items
        (material.renameWires (appendHostWire outer host.locals)) := by
  cases host with
  | mk hostLocals hostItems =>
      cases material with
      | mk materialLocals materialItems =>
          have materialMap : WireRenaming.comp
              (Region.adjoinMaterialWire outer hostLocals materialLocals)
              ((appendHostWire outer hostLocals).appendRight materialLocals) =
            Region.conjoinRightWire outer hostLocals materialLocals := by
            apply WireRenaming.ext
            intro signature wire
            apply Var.appendCases (left := outer)
              (right := materialLocals)
              (motive := fun wire =>
                WireRenaming.comp
                    (Region.adjoinMaterialWire outer hostLocals materialLocals)
                    ((appendHostWire outer hostLocals).appendRight
                      materialLocals) wire =
                  Region.conjoinRightWire outer hostLocals materialLocals
                    wire)
            · intro inheritedSignature inherited
              simp [WireRenaming.comp, WireRenaming.appendRight,
                appendHostWire, Region.adjoinMaterialWire,
                Region.conjoinRightWire]
            · intro localSignature localWire
              simp [WireRenaming.comp, WireRenaming.appendRight,
                appendHostWire, Region.adjoinMaterialWire,
                Region.conjoinRightWire]
          simp only [Region.conjoin, Region.adjoinAt, Region.renameWires,
            Region.locals, Region.items, ItemSeq.renameWires_comp,
            Region.adjoinHostWire]
          rw [materialMap]

private noncomputable def instantiateRenameIso
    (pattern : OpenDiagram arguments)
    (ports : Vars sourceWires arguments)
    (rename : WireRenaming sourceWires targetWires) :
    RegionIso (WireEquiv.refl targetWires)
      ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports).renameWires rename)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate pattern
        (ports.map fun wire => rename wire)) := by
  rw [instantiate_renameWires]
  exact RegionIso.refl _

theorem canonical_conjoin
    {outer : List Sig} {first second : Region outer}
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical) :
    (first.conjoin second).Canonical := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          rw [conjoin_eq_adjoinRename]
          exact Region.Canonical.adjoinAt firstLocals firstItems
            ((Region.mk secondLocals secondItems).renameWires
              (appendHostWire _ firstLocals)) firstCanonical
            ((Region.Canonical.renameWires_iff
              (Region.mk secondLocals secondItems)
              (appendHostWire _ firstLocals)).mpr secondCanonical)

theorem canonical_right_of_conjoin
    {outer : List Sig} {first second : Region outer}
    (canonical : (first.conjoin second).Canonical) : second.Canonical := by
  rw [conjoin_eq_adjoinRename] at canonical
  have renamed := Region.Canonical.material_of_adjoinAt first.locals
    first.items (second.renameWires (appendHostWire _ first.locals)) canonical
  exact (Region.Canonical.renameWires_iff second
    (appendHostWire _ first.locals)).mp renamed

theorem canonical_left_of_conjoin
    {outer : List Sig} {first second : Region outer}
    (canonical : (first.conjoin second).Canonical) : first.Canonical := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          simp only [Region.conjoin, Region.Canonical] at canonical ⊢
          constructor
          · intro localIndex
            let hostWire := Var.appendRight outer (Var.ofIndex localIndex)
            let combinedIndex : Fin (firstLocals ++ secondLocals).length :=
              ⟨localIndex.val, by
                simp only [List.length_append]
                exact Nat.lt_add_right _ localIndex.isLt⟩
            have combinedRoot := canonical.1 combinedIndex
            have combinedWireIndex :
                outer.length + combinedIndex.val = hostWire.index.val := by
              simp [combinedIndex, hostWire]
            rw [combinedWireIndex, ItemSeq.incidencePaths_append]
              at combinedRoot
            have hostMap :
                Region.conjoinLeftWire outer firstLocals secondLocals =
                  Region.adjoinHostWire outer firstLocals secondLocals := rfl
            rw [hostMap,
              ItemSeq.incidencePaths_renameWires_adjoinHost
              firstItems hostWire 0] at combinedRoot
            have secondEmpty :
                (secondItems.renameWires
                  (Region.conjoinRightWire outer firstLocals
                    secondLocals)).incidencePaths hostWire.index.val
                      (0 + (firstItems.renameWires
                        (Region.conjoinLeftWire outer firstLocals
                          secondLocals)).length) = [] := by
              apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
              · have hostBound := localIndex.isLt
                simp [hostWire, List.length_append]
                omega
              · intro signature wire
                apply Var.appendCases (left := outer)
                  (right := secondLocals)
                  (motive := fun wire =>
                    (Region.conjoinRightWire outer firstLocals secondLocals
                      wire).index.val ≠ hostWire.index.val)
                · intro inheritedSignature inherited
                  have bound := inherited.index.isLt
                  simp [Region.conjoinRightWire, hostWire]
                  omega
                · intro localSignature localWire
                  have hostBound := localIndex.isLt
                  simp [Region.conjoinRightWire, hostWire]
                  omega
            have secondEmpty' :
                (secondItems.renameWires
                  (Region.conjoinRightWire outer firstLocals
                    secondLocals)).incidencePaths hostWire.index.val
                      (0 + (firstItems.renameWires
                        (Region.adjoinHostWire outer firstLocals
                          secondLocals)).length) = [] := by
              simpa only [← hostMap] using secondEmpty
            rw [secondEmpty', List.append_nil] at combinedRoot
            simpa [hostWire, combinedIndex] using combinedRoot
          · have children :=
              (ItemSeq.childrenCanonical_append _ _).mp canonical.2 |>.1
            exact (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
              firstItems).mp children
/-- Refine an actual occurrence through one further exact recursive context.
The composed context is the only occurrence path; `fill_comp` identifies its
source with the caller's actual filled endpoint. -/
noncomputable def Occurrence.nest
    {boundary middle holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    {inner : DiagramContext middle holeWires}
    (occurrence : Occurrence (inner.fill before) source) :
    Occurrence before source where
  interface := occurrence.interface
  context := occurrence.context.comp inner
  sourceCanonical := by
    simpa only [DiagramContext.fill_comp] using occurrence.sourceCanonical
  sourceExternalTwoEnded := by
    intro signature wire
    simpa only [DiagramContext.fill_comp] using
      occurrence.sourceExternalTwoEnded wire
  host_iso := by
    simpa only [DiagramContext.fill_comp] using occurrence.host_iso

/-- Bidirectional nonempty reachability between exact occurrence endpoints.
This stronger internal form permits endpoint presentation transport while
the public equality phase remains optional when no selected site exists. -/
def StrictEquates
    {boundary holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (after : Region holeWires)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)) : Prop :=
  let target := occurrence.interface.withBody
    (occurrence.context.fill after) targetCanonical targetExternalTwoEnded
  Relation.TransGen Step source target ∧
    Relation.TransGen Step target source

private theorem StrictEquates.toEquates
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)}
    (strict : StrictEquates occurrence after targetCanonical
      targetExternalTwoEnded) :
    Equates occurrence after targetCanonical targetExternalTwoEnded := by
  have optional : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last →
        Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail steps step induction => exact .tail induction step
  exact ⟨optional strict.1, optional strict.2⟩

/-- A nonempty symmetric loop at an exact occurrence. The two Vacuity steps
insert and immediately remove one structurally fixed point, so presentation
transport never relies on a zero-length derivation. -/
private theorem StrictEquates.refl
    {boundary holeWires : List Sig}
    {before : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source) :
    StrictEquates occurrence before occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded := by
  have regionEta :
      Vacuity.Point.plain before.locals before.items = before := by
    cases before
    rfl
  let pointOccurrence : Occurrence
      (Vacuity.Point.plain before.locals before.items) source := by
    rw [regionEta]
    exact occurrence
  have pointValidity :=
    Vacuity.Point.introduceValidity pointOccurrence Sig.iota
  let pointEndpoint := pointOccurrence.interface.withBody
    (pointOccurrence.context.fill
      (Vacuity.Point.present before.locals before.items Sig.iota))
    pointValidity.1 pointValidity.2
  have introduction : Vacuity source pointEndpoint := by
    exact ⟨holeWires,
      Vacuity.Point.plain before.locals before.items,
      Vacuity.Point.present before.locals before.items Sig.iota,
      pointOccurrence, pointValidity.1, pointValidity.2,
      OpenDiagramIso.refl _,
      atPolarity_symmetric_of pointOccurrence.context.polarity
        (.mk (.point before.locals before.items Sig.iota))⟩
  let exact := occurrence.interface.withBody
    (occurrence.context.fill before) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have exactIntroduction : Vacuity exact pointEndpoint := by
    exact Vacuity.iso occurrence.host_iso introduction
      (OpenDiagramIso.refl pointEndpoint)
  exact ⟨(Relation.TransGen.single (Step.vacuity introduction)).tail
      (Step.vacuity exactIntroduction.symm),
    (Relation.TransGen.single (Step.vacuity exactIntroduction)).tail
      (Step.vacuity introduction.symm)⟩

/-- Transport the exact target presentation of a nonempty symmetric phase. -/
theorem StrictEquates.targetIso
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (strict : StrictEquates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (targetIso : OpenDiagramIso
      (occurrence.interface.withBody (occurrence.context.fill middle)
        middleCanonical middleExternalTwoEnded)
      (occurrence.interface.withBody (occurrence.context.fill after)
        targetCanonical targetExternalTwoEnded)) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨transGen_iso (OpenDiagramIso.refl source) strict.1 targetIso,
    transGen_iso targetIso strict.2 (OpenDiagramIso.refl source)⟩

/-- Consecutive nonempty symmetric phases compose at their exact midpoint. -/
theorem StrictEquates.trans
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (first : StrictEquates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (second : StrictEquates
      (exactOccurrence occurrence.interface occurrence.context middle
        middleCanonical middleExternalTwoEnded)
      after targetCanonical targetExternalTwoEnded) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨first.1.trans second.1, second.2.trans first.2⟩

/-- Consecutive bidirectional phases at the same actual occurrence compose. -/
private theorem Equates.trans
    {boundary holeWires : List Sig}
    {before middle after : Region holeWires}
    {source : OpenDiagram boundary}
    {occurrence : Occurrence before source}
    {middleCanonical : (occurrence.context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill middle)}
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after)}
    (first : Equates occurrence middle middleCanonical
      middleExternalTwoEnded)
    (second : Equates
      (exactOccurrence occurrence.interface occurrence.context middle
        middleCanonical middleExternalTwoEnded)
      after targetCanonical targetExternalTwoEnded) :
    Equates occurrence after targetCanonical targetExternalTwoEnded := by
  exact ⟨first.1.trans second.1, second.2.trans first.2⟩


noncomputable def presentationOccurrence
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (afterCanonical : after.Canonical)
    (sameNonempty : ∀ {signature} (wire : Var holeWires signature),
      before.incidencePaths wire.index.val ≠ [] ↔
        after.incidencePaths wire.index.val ≠ [])
    (presentation : RegionIso (WireEquiv.refl holeWires) before after) :
    Occurrence after source := by
  have replacement := occurrence.context.replaceCanonical before after
    occurrence.sourceCanonical afterCanonical sameNonempty
  let beforeEndpoint := occurrence.interface.withBody
    (occurrence.context.fill before) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill after) :=
    beforeEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill after) replacement.2
  exact {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := replacement.1
    sourceExternalTwoEnded := afterExternalTwoEnded
    host_iso := occurrence.host_iso.trans
      (OpenDiagram.withBody_iso occurrence.sourceCanonical replacement.1
        occurrence.sourceExternalTwoEnded afterExternalTwoEnded
        (DiagramContext.fillIso occurrence.context presentation))
  }

/-- One unary identity for every wire in a typed source context. -/
private def allPins (source : List Sig)
    (rename : WireRenaming source target) : ItemSeq target :=
  ItemSeq.pinWires source rename (fun _ => true)

/-- Add one pin for every selected source wire at an exact occurrence. -/
private theorem pinAllExact
    {boundary holeWires locals pinWires : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (items : ItemSeq (holeWires ++ locals))
    (rename : WireRenaming pinWires (holeWires ++ locals))
    (sourceCanonical :
      (context.fill (.mk locals items)).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (.mk locals items))) :
    ∃ targetCanonical :
        (context.fill
          (.mk locals (items.append (allPins pinWires rename)))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          interface.boundaryWire
          (context.fill
            (.mk locals (items.append (allPins pinWires rename)))),
        Equates
          (exactOccurrence interface context (.mk locals items)
            sourceCanonical sourceExternalTwoEnded)
          (.mk locals (items.append (allPins pinWires rename)))
          targetCanonical targetExternalTwoEnded := by
  induction pinWires generalizing items with
  | nil =>
      refine ⟨by simpa [allPins, ItemSeq.pinWires, ItemSeq.append_nil] using
          sourceCanonical,
        by
          intro wireSignature wire
          simpa [allPins, ItemSeq.pinWires, ItemSeq.append_nil] using
            sourceExternalTwoEnded wire,
        ?_⟩
      simpa [allPins, ItemSeq.pinWires, ItemSeq.append_nil] using
        (show Equates
          (exactOccurrence interface context (.mk locals items)
            sourceCanonical sourceExternalTwoEnded)
          (.mk locals items) sourceCanonical sourceExternalTwoEnded from
          ⟨.refl, .refl⟩)
  | cons signature tail induction =>
      let tailRename : WireRenaming tail (holeWires ++ locals) :=
        ⟨fun wire => rename (.there wire)⟩
      let pin := Item.identity signature 1 (fun _ => rename .here)
      let occurrence := exactOccurrence interface context (.mk locals items)
        sourceCanonical sourceExternalTwoEnded
      obtain ⟨firstCanonical, firstExternalTwoEnded, firstSteps⟩ :=
        pinStep occurrence signature (rename .here)
      let firstItems := items.append (.cons pin .nil)
      have firstCanonical' :
          (context.fill (.mk locals firstItems)).Canonical := by
        simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
          Vacuity.Pin.plain] using firstCanonical
      have firstExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          interface.boundaryWire (context.fill (.mk locals firstItems)) := by
        intro wireSignature wire
        simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
          Vacuity.Pin.plain] using firstExternalTwoEnded wire
      obtain ⟨targetCanonical, targetExternalTwoEnded, rest⟩ :=
        induction firstItems tailRename firstCanonical'
          firstExternalTwoEnded'
      refine ⟨?_, ?_, ?_⟩
      · simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
          ItemSeq.append_assoc] using targetCanonical
      · intro wireSignature wire
        simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
          ItemSeq.append_assoc] using targetExternalTwoEnded wire
      · have firstEquates : Equates occurrence
            (.mk locals firstItems) firstCanonical' firstExternalTwoEnded' := by
          exact ⟨.tail .refl (by
              simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
                Vacuity.Pin.plain] using firstSteps.1),
            .tail .refl (by
              simpa only [occurrence, pin, firstItems, Vacuity.Pin.present,
                Vacuity.Pin.plain] using firstSteps.2)⟩
        have combined := Equates.trans firstEquates rest
        simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
          ItemSeq.append_assoc] using combined

/-- A nonempty all-wire pin batch has a genuine Vacuity step in each
direction, even when the supplied occurrence uses a nontrivial source
presentation. -/
private theorem pinAllNonempty
    {boundary holeWires locals : List Sig}
    {signature : Sig} {tail : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (Vacuity.Pin.plain locals items) source)
    (rename : WireRenaming (signature :: tail) (holeWires ++ locals)) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (.mk locals
            (items.append (allPins (signature :: tail) rename)))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk locals
              (items.append (allPins (signature :: tail) rename)))),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals
                  (items.append (allPins (signature :: tail) rename))))
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals
                  (items.append (allPins (signature :: tail) rename))))
              targetCanonical targetExternalTwoEnded)
            source := by
  let tailRename : WireRenaming tail (holeWires ++ locals) :=
    ⟨fun wire => rename (.there wire)⟩
  let pin := Item.identity signature 1 (fun _ => rename .here)
  obtain ⟨firstCanonical, firstExternalTwoEnded, firstSteps⟩ :=
    pinStep occurrence signature (rename .here)
  let firstItems := items.append (.cons pin .nil)
  have firstCanonical' :
      (occurrence.context.fill (.mk locals firstItems)).Canonical := by
    simpa only [pin, firstItems, Vacuity.Pin.present,
      Vacuity.Pin.plain] using firstCanonical
  have firstExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (.mk locals firstItems)) := by
    intro wireSignature wire
    simpa only [pin, firstItems, Vacuity.Pin.present,
      Vacuity.Pin.plain] using firstExternalTwoEnded wire
  obtain ⟨targetCanonical, targetExternalTwoEnded, rest⟩ :=
    pinAllExact occurrence.interface occurrence.context firstItems tailRename
      firstCanonical' firstExternalTwoEnded'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using targetCanonical
  · intro wireSignature wire
    simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using targetExternalTwoEnded wire
  · have first : Step source
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') := by
      simpa only [pin, firstItems, Vacuity.Pin.present,
        Vacuity.Pin.plain] using firstSteps.1
    have combined := (Relation.TransGen.single first).reflTransGen rest.1
    simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using combined
  · have first : Step
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') source := by
      simpa only [pin, firstItems, Vacuity.Pin.present,
        Vacuity.Pin.plain] using firstSteps.2
    have combined := rest.2.transGen (Relation.TransGen.single first)
    simpa only [allPins, ItemSeq.pinWires, if_true, firstItems, pin,
      ItemSeq.append_assoc] using combined

/-- Two complete pin batches provide two root incidences for every selected
wire and remain a nonempty symmetric Vacuity derivation. -/
private theorem pinAllTwiceNonempty
    {boundary holeWires locals : List Sig}
    {signature : Sig} {tail : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (.mk locals items) source)
    (rename : WireRenaming (signature :: tail) (holeWires ++ locals)) :
    let pins := allPins (signature :: tail) rename
    ∃ targetCanonical :
        (occurrence.context.fill
          (.mk locals ((items.append pins).append pins))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk locals ((items.append pins).append pins))),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded)
            source := by
  dsimp only
  obtain ⟨firstCanonical, firstExternalTwoEnded, first⟩ :=
    pinAllNonempty occurrence rename
  let pins := allPins (signature :: tail) rename
  let firstItems := items.append pins
  have firstCanonical' :
      (occurrence.context.fill (.mk locals firstItems)).Canonical := by
    simpa only [pins, firstItems] using firstCanonical
  have firstExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (.mk locals firstItems)) := by
    intro wireSignature wire
    simpa only [pins, firstItems] using firstExternalTwoEnded wire
  obtain ⟨targetCanonical, targetExternalTwoEnded, second⟩ :=
    pinAllExact occurrence.interface occurrence.context firstItems rename
      firstCanonical' firstExternalTwoEnded'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [pins, firstItems] using targetCanonical
  · intro wireSignature wire
    simpa only [pins, firstItems] using targetExternalTwoEnded wire
  · have first' : Relation.TransGen Step source
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') := by
      simpa only [pins, firstItems] using first.1
    exact first'.reflTransGen (by
      simpa only [pins, firstItems] using second.1)
  · have first' : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') source := by
      simpa only [pins, firstItems] using first.2
    have secondReverse : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (.mk locals ((items.append pins).append pins)))
          targetCanonical targetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill (.mk locals firstItems))
          firstCanonical' firstExternalTwoEnded') := by
      simpa only [pins, firstItems] using second.2
    exact secondReverse.transGen first'

private theorem pinAllTwiceOfNonempty
    {boundary holeWires locals pinWires : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (.mk locals items) source)
    (rename : WireRenaming pinWires (holeWires ++ locals))
    (nonempty : pinWires ≠ []) :
    let pins := allPins pinWires rename
    ∃ targetCanonical :
        (occurrence.context.fill
          (.mk locals ((items.append pins).append pins))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk locals ((items.append pins).append pins))),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill
                (.mk locals ((items.append pins).append pins)))
              targetCanonical targetExternalTwoEnded)
            source := by
  cases pinWires with
  | nil => exact False.elim (nonempty rfl)
  | cons signature tail => exact pinAllTwiceNonempty occurrence rename

private theorem allPins_renameWires
    (source : List Sig) (rename : WireRenaming source middle)
    (next : WireRenaming middle target) :
    (allPins source rename).renameWires next =
      allPins source (WireRenaming.comp next rename) := by
  induction source with
  | nil => rfl
  | cons signature tail induction =>
      simp only [allPins, ItemSeq.pinWires, if_true,
        ItemSeq.renameWires, Item.renameWires]
      exact congrArg (ItemSeq.cons
        (.identity signature 1
          (fun _ => next (rename (.here : Var (signature :: tail)
            signature)))))
        (induction ⟨fun wire => rename (.there wire)⟩)

private theorem allPins_mem_nil
    (source : List Sig) (rename : WireRenaming source target)
    (wire : Var source signature) (itemIndex : Nat) :
    [] ∈ (allPins source rename).incidencePaths
      (rename wire).index.val itemIndex := by
  exact ItemSeq.pinWires_mem_nil source rename (fun _ => true) wire
    itemIndex rfl

/-- Two complete pin batches root every selected wire at the current region. -/
private theorem allPins_twice_rooted
    (source : List Sig) (rename : WireRenaming source target)
    (wire : Var source signature) (itemIndex : Nat) :
    RegionPath.RootedTwo
      (((allPins source rename).append (allPins source rename)).incidencePaths
        (rename wire).index.val itemIndex) := by
  rw [ItemSeq.incidencePaths_append]
  have firstMem : [] ∈ (allPins source rename).incidencePaths
      (rename wire).index.val itemIndex :=
    allPins_mem_nil source rename wire itemIndex
  have secondMem : [] ∈ (allPins source rename).incidencePaths
      (rename wire).index.val
        (itemIndex + (allPins source rename).length) :=
    allPins_mem_nil source rename wire
      (itemIndex + (allPins source rename).length)
  constructor
  · have firstPositive := List.length_pos_iff.mpr
      (List.ne_nil_of_mem firstMem)
    have secondPositive := List.length_pos_iff.mpr
      (List.ne_nil_of_mem secondMem)
    simp only [List.length_append]
    omega
  · exact RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _
      (List.mem_append.mpr (Or.inl firstMem))

private theorem allPins_twice_childrenCanonical
    (source : List Sig) (rename : WireRenaming source target) :
    ((allPins source rename).append
      (allPins source rename)).ChildrenCanonical := by
  exact (ItemSeq.childrenCanonical_append _ _).mpr
    ⟨ItemSeq.pinWires_childrenCanonical source rename (fun _ => true),
      ItemSeq.pinWires_childrenCanonical source rename (fun _ => true)⟩
private def appendAdjoinedPins
    (hostLocals : List Sig) (hostItems pins : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) : Region outer :=
  match material with
  | .mk materialLocals materialItems =>
      let hostRename := Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      .mk (hostLocals ++ materialLocals)
        (((hostItems.renameWires hostRename).append
          (materialItems.renameWires materialRename)).append
            (pins.renameWires hostRename))

/-- Moving a pin block from after adjoined material into the host item block
is a presentation isomorphism and changes no rewrite authority. -/
private noncomputable def adjoinPinsIso
    (hostLocals : List Sig) (hostItems pins : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals)) :
    RegionIso (WireEquiv.refl outer)
      (appendAdjoinedPins hostLocals hostItems pins material)
      (Region.adjoinAt hostLocals (hostItems.append pins) material) := by
  cases material with
  | mk materialLocals materialItems =>
      let hostRename := Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      let host := hostItems.renameWires hostRename
      let material := materialItems.renameWires materialRename
      let pinItems := pins.renameWires hostRename
      let reordered : ItemSeqIso
          (WireEquiv.refl (outer ++ (hostLocals ++ materialLocals)))
          ((host.append material).append pinItems)
          ((host.append pinItems).append material) := by
        let moved := ItemSeqIso.append (ItemSeqIso.refl host)
          (ItemSeqIso.swapAppend material pinItems)
        simpa only [ItemSeq.append_assoc] using moved
      refine .mk (WireEquiv.refl (hostLocals ++ materialLocals)) ?_
      simpa only [Region.adjoinAt, Region.locals, Region.items,
        ItemSeq.renameWires_append, hostRename, materialRename, host,
        material, pinItems] using
        reordered.castAmbient
          (WireEquiv.append_refl outer
            (hostLocals ++ materialLocals)).symm

private theorem ItemSeq.incidencePaths_append_nonempty_iff
    (first second : ItemSeq wires) (wireIndex itemIndex : Nat) :
    (first.append second).incidencePaths wireIndex itemIndex ≠ [] ↔
      first.incidencePaths wireIndex 0 ≠ [] ∨
        second.incidencePaths wireIndex 0 ≠ [] := by
  constructor
  · intro joinedNonempty
    by_cases firstEmpty : first.incidencePaths wireIndex 0 = []
    · apply Or.inr
      intro secondEmpty
      apply joinedNonempty
      rw [ItemSeq.incidencePaths_append]
      rw [(ItemSeq.incidencePaths_eq_nil_iff_itemIndex first wireIndex
        itemIndex 0).mpr firstEmpty]
      rw [(ItemSeq.incidencePaths_eq_nil_iff_itemIndex second wireIndex
        (itemIndex + first.length) 0).mpr secondEmpty]
      rfl
    · exact Or.inl firstEmpty
  · intro nonempty
    intro joinedEmpty
    rw [ItemSeq.incidencePaths_append] at joinedEmpty
    have parts := List.append_eq_nil_iff.mp joinedEmpty
    rcases nonempty with firstNonempty | secondNonempty
    · exact firstNonempty
        ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex first wireIndex
          itemIndex 0).mp parts.1)
    · exact secondNonempty
        ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex second wireIndex
          (itemIndex + first.length) 0).mp parts.2)

private theorem ItemSeq.incidencePaths_rotate_nonempty_iff
    (host material pins : ItemSeq wires) (wireIndex itemIndex : Nat) :
    ((host.append material).append pins).incidencePaths
        wireIndex itemIndex ≠ [] ↔
      ((host.append pins).append material).incidencePaths
        wireIndex itemIndex ≠ [] := by
  simp only [ItemSeq.incidencePaths_append_nonempty_iff]
  constructor
  · rintro ((hostNonempty | materialNonempty) | pinsNonempty)
    · exact Or.inl (Or.inl hostNonempty)
    · exact Or.inr materialNonempty
    · exact Or.inl (Or.inr pinsNonempty)
  · rintro ((hostNonempty | pinsNonempty) | materialNonempty)
    · exact Or.inl (Or.inl hostNonempty)
    · exact Or.inr pinsNonempty
    · exact Or.inl (Or.inr materialNonempty)

def contextPins (outer hostLocals : List Sig) :
    ItemSeq (outer ++ hostLocals) :=
  let pins := allPins (outer ++ hostLocals) WireRenaming.id
  pins.append pins

private theorem contextPins_incidence_nonempty
    (outer hostLocals : List Sig)
    (wire : Var (outer ++ hostLocals) signature) (itemIndex : Nat) :
    (contextPins outer hostLocals).incidencePaths
      wire.index.val itemIndex ≠ [] := by
  let pins := allPins (outer ++ hostLocals) WireRenaming.id
  have member : [] ∈ pins.incidencePaths wire.index.val itemIndex := by
    simpa only [WireRenaming.id] using
      allPins_mem_nil (outer ++ hostLocals) WireRenaming.id wire itemIndex
  rw [show contextPins outer hostLocals = pins.append pins by rfl,
    ItemSeq.incidencePaths_append]
  exact List.append_ne_nil_of_left_ne_nil (List.ne_nil_of_mem member) _

theorem pinnedHostCanonicalOfChildren
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (hostChildren : hostItems.ChildrenCanonical) :
    (Region.mk hostLocals
      (hostItems.append (contextPins outer hostLocals))).Canonical := by
  constructor
  · intro localIndex
    let localWire := Var.appendRight outer (Var.ofIndex localIndex)
    have pinRoot := allPins_twice_rooted
      (outer ++ hostLocals) WireRenaming.id localWire
      hostItems.length
    rw [ItemSeq.incidencePaths_append]
    apply RegionPath.RootedTwo.of_sublist
      (List.sublist_append_right _ _)
    simpa [contextPins, localWire, WireRenaming.id] using pinRoot
  · exact (ItemSeq.childrenCanonical_append _ _).mpr
      ⟨hostChildren,
        allPins_twice_childrenCanonical
          (outer ++ hostLocals) WireRenaming.id⟩

theorem pinnedHostCanonical
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    (sourceCanonical :
      (Region.adjoinAt hostLocals hostItems material).Canonical) :
    (Region.mk hostLocals
      (hostItems.append (contextPins outer hostLocals))).Canonical := by
  cases material with
  | mk materialLocals materialItems =>
      have hostRenamedChildren :
          (hostItems.renameWires
            (Region.adjoinHostWire outer hostLocals
              materialLocals)).ChildrenCanonical := by
        have sourceChildren := sourceCanonical.2
        simp only at sourceChildren
        exact (ItemSeq.childrenCanonical_append _ _).mp
          sourceChildren |>.1
      have hostChildren : hostItems.ChildrenCanonical :=
        (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
          hostItems).mp hostRenamedChildren
      exact pinnedHostCanonicalOfChildren hostLocals hostItems hostChildren
/-- Add the structural double-pin block around arbitrary adjoined material,
transporting the nonempty Vacuity derivation through the exact item
permutation that places those pins in the host block. -/
theorem adjoinPinsEquatesNonempty
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (material : Region (outer ++ hostLocals))
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems material) source)
    (nonempty : outer ++ hostLocals ≠ []) :
    let target := Region.adjoinAt hostLocals
      (hostItems.append (contextPins outer hostLocals)) material
    ∃ targetCanonical : (occurrence.context.fill target).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill target),
        Relation.TransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill target)
              targetCanonical targetExternalTwoEnded) ∧
          Relation.TransGen Step
            (occurrence.interface.withBody
              (occurrence.context.fill target)
              targetCanonical targetExternalTwoEnded)
            source := by
  dsimp only
  cases material with
  | mk materialLocals materialItems =>
      let hostRename :=
        Region.adjoinHostWire outer hostLocals materialLocals
      let materialRename :=
        Region.adjoinMaterialWire outer hostLocals materialLocals
      let host := hostItems.renameWires hostRename
      let material := materialItems.renameWires materialRename
      let pin := allPins (outer ++ hostLocals) hostRename
      let base := host.append material
      let directOccurrence : Occurrence
          (.mk (hostLocals ++ materialLocals) base) source := by
        simpa only [Region.adjoinAt, hostRename, materialRename, host,
          material, base] using occurrence
      obtain ⟨rawCanonical, rawExternalTwoEnded, rawSteps⟩ :=
        pinAllTwiceOfNonempty directOccurrence hostRename nonempty
      let raw := Region.mk (hostLocals ++ materialLocals)
        ((base.append pin).append pin)
      have rawCanonical' : (occurrence.context.fill raw).Canonical := by
        simpa only [directOccurrence, pin, base, raw] using rawCanonical
      have rawExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill raw) := by
        intro wireSignature wire
        simpa only [directOccurrence, pin, base, raw] using
          rawExternalTwoEnded wire
      have compId : WireRenaming.comp hostRename WireRenaming.id =
          hostRename := by
        apply WireRenaming.ext
        intro wireSignature wire
        rfl
      have pinsRename :
          (contextPins outer hostLocals).renameWires hostRename =
            pin.append pin := by
        simp only [contextPins, ItemSeq.renameWires_append,
          allPins_renameWires, compId, pin]
      have rawEq : raw = appendAdjoinedPins hostLocals hostItems
          (contextPins outer hostLocals)
          (.mk materialLocals materialItems) := by
        simp only [raw, appendAdjoinedPins, hostRename, materialRename,
          host, material, base, pinsRename, ItemSeq.append_assoc]
      let target := Region.adjoinAt hostLocals
        (hostItems.append (contextPins outer hostLocals))
        (.mk materialLocals materialItems)
      let presentation : RegionIso (WireEquiv.refl outer) raw target := by
        rw [rawEq]
        exact adjoinPinsIso hostLocals hostItems
          (contextPins outer hostLocals)
          (.mk materialLocals materialItems)
      have sourceLocalCanonical :
          (Region.adjoinAt hostLocals hostItems
            (.mk materialLocals materialItems)).Canonical :=
        occurrence.context.holeCanonical _ occurrence.sourceCanonical
      have materialCanonical :
          (Region.mk materialLocals materialItems).Canonical :=
        Region.Canonical.material_of_adjoinAt hostLocals hostItems _
          sourceLocalCanonical
      have targetLocalCanonical : target.Canonical := by
        exact Region.Canonical.adjoinAt hostLocals
          (hostItems.append (contextPins outer hostLocals))
          (.mk materialLocals materialItems)
          (pinnedHostCanonical hostLocals hostItems
            (.mk materialLocals materialItems) sourceLocalCanonical)
          materialCanonical
      have sameNonempty : ∀ {wireSignature}
          (wire : Var outer wireSignature),
          raw.incidencePaths wire.index.val ≠ [] ↔
            target.incidencePaths wire.index.val ≠ [] := by
        intro wireSignature wire
        simpa only [raw, target, Region.adjoinAt, Region.incidencePaths,
          hostRename, materialRename, host, material, base, pinsRename,
          ItemSeq.renameWires_append, ItemSeq.append_assoc] using
          ItemSeq.incidencePaths_rotate_nonempty_iff host material
            (pin.append pin) wire.index.val 0
      have replacement := occurrence.context.replaceCanonical raw target
        rawCanonical' targetLocalCanonical sameNonempty
      let targetCanonical := replacement.1
      let rawEndpoint := occurrence.interface.withBody
        (occurrence.context.fill raw) rawCanonical' rawExternalTwoEnded'
      have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill target) :=
        rawEndpoint.externalTwoEnded_of_nonempty_iff
          (occurrence.context.fill target) replacement.2
      let targetEndpoint := occurrence.interface.withBody
        (occurrence.context.fill target) targetCanonical
          targetExternalTwoEnded
      let endpointIso : OpenDiagramIso rawEndpoint targetEndpoint :=
        OpenDiagram.withBody_iso rawCanonical' targetCanonical
          rawExternalTwoEnded' targetExternalTwoEnded
          (DiagramContext.fillIso occurrence.context presentation)
      have rawForward : Relation.TransGen Step source rawEndpoint := by
        simpa only [directOccurrence, pin, base, raw, rawEndpoint] using
          rawSteps.1
      have rawReverse : Relation.TransGen Step rawEndpoint source := by
        simpa only [directOccurrence, pin, base, raw, rawEndpoint] using
          rawSteps.2
      refine ⟨targetCanonical, targetExternalTwoEnded, ?_, ?_⟩
      · exact transGen_iso (OpenDiagramIso.refl source) rawForward endpointIso
      · exact transGen_iso endpointIso rawReverse
          (OpenDiagramIso.refl source)

theorem pinnedHost_incidence_nonempty
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (wire : Var outer signature) :
    (Region.mk hostLocals
      (hostItems.append
        (contextPins outer hostLocals))).incidencePaths
          wire.index.val ≠ [] := by
  let embedded := wire.appendLeft hostLocals
  have pinsNonempty := contextPins_incidence_nonempty
    outer hostLocals embedded hostItems.length
  simp only [Region.incidencePaths, ItemSeq.incidencePaths_append,
    Nat.zero_add]
  exact List.append_ne_nil_of_right_ne_nil _ (by
    simpa only [embedded, Var.index_appendLeft] using pinsNonempty)

/-- Change only the adjoined material presentation beneath a host whose
existing syntax is canonical and incident at every inherited wire. -/
noncomputable def supportedAdjoinOccurrence
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems before) source)
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    (afterCanonical : after.Canonical)
    (presentation : RegionIso (WireEquiv.refl (outer ++ hostLocals))
      before after) :
    Occurrence (Region.adjoinAt hostLocals hostItems after) source := by
  have targetLocalCanonical :
      (Region.adjoinAt hostLocals hostItems after).Canonical :=
    Region.Canonical.adjoinAt hostLocals hostItems after hostCanonical
      afterCanonical
  have sameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals hostItems before).incidencePaths
            wire.index.val ≠ [] ↔
        (Region.adjoinAt hostLocals hostItems after).incidencePaths
            wire.index.val ≠ [] := by
    intro signature wire
    have hostPositive : 0 <
        ((Region.mk hostLocals hostItems).incidencePaths
          wire.index.val).length :=
      List.length_pos_iff.mpr (hostNonempty wire)
    have beforeSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems before wire
    have afterSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems after wire
    have beforeNonempty :
        (Region.adjoinAt hostLocals hostItems before).incidencePaths
          wire.index.val ≠ [] :=
      List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive beforeSublist.length_le)
    have afterNonempty :
        (Region.adjoinAt hostLocals hostItems after).incidencePaths
          wire.index.val ≠ [] :=
      List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive afterSublist.length_le)
    exact ⟨fun _ => afterNonempty, fun _ => beforeNonempty⟩
  exact presentationOccurrence occurrence targetLocalCanonical sameNonempty
    (RegionIso.adjoinAt hostLocals hostItems presentation)

theorem supportedAdjoinValidity
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems before) source)
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    (afterCanonical : after.Canonical) :
    (occurrence.context.fill
      (Region.adjoinAt hostLocals hostItems after)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems after)) := by
  have targetLocalCanonical :
      (Region.adjoinAt hostLocals hostItems after).Canonical :=
    Region.Canonical.adjoinAt hostLocals hostItems after hostCanonical
      afterCanonical
  have sameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals hostItems before).incidencePaths
            wire.index.val ≠ [] ↔
        (Region.adjoinAt hostLocals hostItems after).incidencePaths
            wire.index.val ≠ [] := by
    intro signature wire
    have hostPositive := List.length_pos_iff.mpr (hostNonempty wire)
    have beforeSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems before wire
    have afterSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems after wire
    exact ⟨fun _ => List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive afterSublist.length_le),
      fun _ => List.length_pos_iff.mp
        (Nat.lt_of_lt_of_le hostPositive beforeSublist.length_le)⟩
  have replacement := occurrence.context.replaceCanonical _ _
    occurrence.sourceCanonical targetLocalCanonical sameNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (Region.adjoinAt hostLocals hostItems before))
    occurrence.sourceCanonical occurrence.sourceExternalTwoEnded
  exact ⟨replacement.1,
    sourceEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2⟩

theorem extendHostCanonical
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (leading : Region (outer ++ hostLocals))
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (leadingCanonical : leading.Canonical) :
    (Region.mk (hostLocals ++ leading.locals)
      (Region.extendHostItems hostLocals hostItems leading)).Canonical := by
  cases leading with
  | mk leadingLocals leadingItems =>
      simpa only [Region.adjoinAt, Region.extendHostItems, Region.locals,
        Region.items] using
        Region.Canonical.adjoinAt hostLocals hostItems
          (Region.mk leadingLocals leadingItems) hostCanonical
          leadingCanonical

theorem extendHost_incidence_nonempty
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (leading : Region (outer ++ hostLocals))
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    {signature} (wire : Var outer signature) :
    (Region.mk (hostLocals ++ leading.locals)
      (Region.extendHostItems hostLocals hostItems leading)).incidencePaths
        wire.index.val ≠ [] := by
  cases leading with
  | mk leadingLocals leadingItems =>
      have sublist := Region.incidencePaths_adjoinAt_host_sublist
        hostLocals hostItems (Region.mk leadingLocals leadingItems) wire
      have positive := List.length_pos_iff.mpr (hostNonempty wire)
      have targetPositive := Nat.lt_of_lt_of_le positive sublist.length_le
      simpa only [Region.adjoinAt, Region.extendHostItems, Region.locals,
        Region.items] using
        (List.length_pos_iff.mp targetPositive)

noncomputable def flattenAdjoinOccurrence
    {boundary outer : List Sig}
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (first second : Region (outer ++ hostLocals))
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems (first.conjoin second)) source)
    (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
    (hostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical) :
    Occurrence
      (Region.adjoinAt (hostLocals ++ first.locals)
        (Region.extendHostItems hostLocals hostItems first)
        (second.renameWires
          (Region.adjoinHostWire outer hostLocals first.locals))) source := by
  let nextHostItems := Region.extendHostItems hostLocals hostItems first
  have nextHostCanonical :
      (Region.mk (hostLocals ++ first.locals) nextHostItems).Canonical :=
    extendHostCanonical hostLocals hostItems first hostCanonical firstCanonical
  have renamedSecondCanonical :
      (second.renameWires
        (Region.adjoinHostWire outer hostLocals first.locals)).Canonical :=
    (Region.Canonical.renameWires_iff second
      (Region.adjoinHostWire outer hostLocals first.locals)).mpr
        secondCanonical
  have targetLocalCanonical :
      (Region.adjoinAt (hostLocals ++ first.locals) nextHostItems
        (second.renameWires
          (Region.adjoinHostWire outer hostLocals first.locals))).Canonical :=
    Region.Canonical.adjoinAt (hostLocals ++ first.locals) nextHostItems _
      nextHostCanonical renamedSecondCanonical
  have sameNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.adjoinAt hostLocals hostItems
          (first.conjoin second)).incidencePaths wire.index.val ≠ [] ↔
        (Region.adjoinAt (hostLocals ++ first.locals) nextHostItems
          (second.renameWires
            (Region.adjoinHostWire outer hostLocals first.locals))).incidencePaths
              wire.index.val ≠ [] := by
    intro signature wire
    have beforeSublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals hostItems (first.conjoin second) wire
    have beforePositive := Nat.lt_of_lt_of_le
      (List.length_pos_iff.mpr (hostNonempty wire)) beforeSublist.length_le
    have nextHostNonempty := extendHost_incidence_nonempty hostLocals
      hostItems first hostNonempty wire
    have afterSublist := Region.incidencePaths_adjoinAt_host_sublist
      (hostLocals ++ first.locals) nextHostItems
      (second.renameWires
        (Region.adjoinHostWire outer hostLocals first.locals)) wire
    have afterPositive := Nat.lt_of_lt_of_le
      (List.length_pos_iff.mpr nextHostNonempty) afterSublist.length_le
    exact ⟨fun _ => List.length_pos_iff.mp afterPositive,
      fun _ => List.length_pos_iff.mp beforePositive⟩
  exact presentationOccurrence occurrence targetLocalCanonical sameNonempty
    (RegionIso.adjoinAtConjoinLeft hostLocals hostItems first second)

/-- Expose one erasure description at an arbitrary nested occurrence. The
caller identifies the actual source and exposed endpoint and supplies the
already-derived validity of the erased intermediate. -/
theorem exposureCore
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    (description : Rule.Erasure.Description holeWires)
    (sourceEq : description.source = before)
    (erasedCanonical :
      (occurrence.context.fill description.target).Canonical)
    (erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target))
    (exposedEq : ∀ materialCanonical : description.material.Canonical,
      Erasure.Exposure.exposedRegion description materialCanonical = after) :
    ∃ targetCanonical : (occurrence.context.fill after).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire (occurrence.context.fill after),
        Equates occurrence after targetCanonical targetExternalTwoEnded := by
  let exposureOccurrence : Occurrence description.source source := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := by
      rw [sourceEq]
      exact occurrence.sourceCanonical
    sourceExternalTwoEnded := by
      intro signature wire
      rw [sourceEq]
      exact occurrence.sourceExternalTwoEnded wire
    host_iso := by
      simpa only [sourceEq] using occurrence.host_iso
  }
  obtain ⟨materialCanonical, exposedCanonical,
      exposedExternalTwoEnded, exposedEquates⟩ :=
    Erasure.Exposure.equates description exposureOccurrence erasedCanonical
      erasedExternalTwoEnded
  refine ⟨?_, ?_, ?_⟩
  · simpa only [exposedEq materialCanonical] using exposedCanonical
  · intro signature wire
    simpa only [exposedEq materialCanonical] using
      exposedExternalTwoEnded wire
  · simpa only [Equates, exposureOccurrence, sourceEq,
      exposedEq materialCanonical] using exposedEquates

/-- Expose one erasure description while the host already carries the shared
temporary pin block. The result remains inside that same pin envelope. -/
theorem pinnedExposureCore
    {boundary outer : List Sig}
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals
        (hostItems.append (contextPins outer hostLocals)) before) source)
    (description : Rule.Erasure.Description outer)
    (sourceEq : description.source =
      Region.adjoinAt hostLocals
        (hostItems.append (contextPins outer hostLocals)) before)
    (targetEq : description.target =
      Region.mk hostLocals
        (hostItems.append (contextPins outer hostLocals)))
    (exposedEq : ∀ materialCanonical : description.material.Canonical,
      Erasure.Exposure.exposedRegion description materialCanonical =
        Region.adjoinAt hostLocals
          (hostItems.append (contextPins outer hostLocals)) after) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) after)).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals
              (hostItems.append (contextPins outer hostLocals)) after)),
        Equates occurrence
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) after)
          targetCanonical targetExternalTwoEnded := by
  let pinnedItems := hostItems.append (contextPins outer hostLocals)
  let pinnedSource := Region.adjoinAt hostLocals pinnedItems before
  have sourceLocalCanonical : pinnedSource.Canonical := by
    simpa only [pinnedItems, pinnedSource] using
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have pinnedChildren : pinnedItems.ChildrenCanonical := by
    cases before with
    | mk materialLocals materialItems =>
        have renamedChildren :
            (pinnedItems.renameWires
              (Region.adjoinHostWire outer hostLocals
                materialLocals)).ChildrenCanonical := by
          have sourceChildren := sourceLocalCanonical.2
          exact (ItemSeq.childrenCanonical_append _ _).mp sourceChildren |>.1
        exact (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
          pinnedItems).mp renamedChildren
  have erasedLocalCanonical : description.target.Canonical := by
    rw [targetEq]
    simpa only [pinnedItems] using
      pinnedHostCanonicalOfChildren hostLocals hostItems
        ((ItemSeq.childrenCanonical_append _ _).mp pinnedChildren).1
  have erasedNonempty : ∀ {signature} (wire : Var outer signature),
      description.target.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [targetEq]
    exact pinnedHost_incidence_nonempty hostLocals hostItems wire
  have pinnedSourceNonempty : ∀ {signature}
      (wire : Var outer signature),
      pinnedSource.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have hostPositive := List.length_pos_iff.mpr
      (pinnedHost_incidence_nonempty hostLocals hostItems wire)
    have sublist := Region.incidencePaths_adjoinAt_host_sublist
      hostLocals pinnedItems before wire
    exact List.length_pos_iff.mp
      (Nat.lt_of_lt_of_le hostPositive sublist.length_le)
  have erasedSameNonempty : ∀ {signature} (wire : Var outer signature),
      pinnedSource.incidencePaths wire.index.val ≠ [] ↔
        description.target.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    exact ⟨fun _ => erasedNonempty wire,
      fun _ => pinnedSourceNonempty wire⟩
  have erasedReplacement := occurrence.context.replaceCanonical
    pinnedSource description.target occurrence.sourceCanonical
      erasedLocalCanonical erasedSameNonempty
  let pinnedSourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill pinnedSource) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target) :=
    pinnedSourceEndpoint.externalTwoEnded_of_nonempty_iff _
      erasedReplacement.2
  exact exposureCore occurrence description sourceEq erasedReplacement.1
    erasedExternalTwoEnded exposedEq

theorem strictEquates_of_equates
    {boundary holeWires : List Sig}
    {before after : Region holeWires}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence before source)
    {targetCanonical : (occurrence.context.fill after).Canonical}
    {targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after)}
    (equivalent : Equates occurrence after targetCanonical
      targetExternalTwoEnded) :
    StrictEquates occurrence after targetCanonical targetExternalTwoEnded := by
  have loop := StrictEquates.refl occurrence
  have sourceLoop : Relation.TransGen Step source source :=
    loop.1.trans loop.2
  exact ⟨sourceLoop.reflTransGen equivalent.1,
    equivalent.2.transGen sourceLoop⟩

theorem transGen_reflTransGen
    (steps : Relation.TransGen relation source target) :
    Relation.ReflTransGen relation source target := by
  induction steps with
  | single step => exact .tail .refl step
  | tail _ step induction => exact .tail induction step

theorem reflTransGen_iso
    {boundary : List Sig}
    {source source' target target' : OpenDiagram boundary}
    (sourceIso : OpenDiagramIso source source')
    (steps : Relation.ReflTransGen Step source target)
    (targetIso : OpenDiagramIso target target') :
    Relation.ReflTransGen Step source' target' := by
  induction steps generalizing source' target' with
  | refl =>
      let rootOccurrence : Occurrence source.body source :=
        exactOccurrence source DiagramContext.hole source.body
          source.canonical source.externalTwoEnded
      have loop := (StrictEquates.refl rootOccurrence).1
      have transported := transGen_iso sourceIso loop targetIso
      exact transGen_reflTransGen transported
  | tail _ step induction =>
      exact .tail (induction sourceIso (OpenDiagramIso.refl _))
        (Step.iso (OpenDiagramIso.refl _) step targetIso)

/-- Run one or more already-pinned exposure cores inside one shared temporary
pin envelope. Pin validity and both envelope endpoints are constructed here;
the caller supplies only the relation proof between the pinned endpoints. -/
theorem withPinnedEnvelopeNonempty
    {boundary outer : List Sig}
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems before) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems after)).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems after)))
    (nonempty : outer ++ hostLocals ≠ [])
    (core : ∀
      (pinnedSourceCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before)).Canonical)
      (pinnedSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before))),
      ∃ pinnedTargetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals
              (hostItems.append (contextPins outer hostLocals)) after)).Canonical,
        ∃ pinnedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (Region.adjoinAt hostLocals
                (hostItems.append (contextPins outer hostLocals)) after)),
          Equates
            (exactOccurrence occurrence.interface occurrence.context
              (Region.adjoinAt hostLocals
                (hostItems.append (contextPins outer hostLocals)) before)
              pinnedSourceCanonical pinnedSourceExternalTwoEnded)
            (Region.adjoinAt hostLocals
              (hostItems.append (contextPins outer hostLocals)) after)
            pinnedTargetCanonical pinnedTargetExternalTwoEnded) :
    StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems after)
      targetCanonical targetExternalTwoEnded := by
  obtain ⟨pinnedSourceCanonical, pinnedSourceExternalTwoEnded,
      sourcePins⟩ := adjoinPinsEquatesNonempty hostLocals hostItems
    before occurrence nonempty
  obtain ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded,
      coreEquates⟩ := core pinnedSourceCanonical
    pinnedSourceExternalTwoEnded
  let targetOccurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems after)
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems after)) targetCanonical
          targetExternalTwoEnded) :=
    exactOccurrence occurrence.interface occurrence.context
      (Region.adjoinAt hostLocals hostItems after)
      targetCanonical targetExternalTwoEnded
  obtain ⟨pinnedTargetCanonical', pinnedTargetExternalTwoEnded',
      targetPins⟩ := adjoinPinsEquatesNonempty hostLocals hostItems
    after targetOccurrence nonempty
  have forwardCore : Relation.ReflTransGen Step
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before))
        pinnedSourceCanonical pinnedSourceExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) after))
        pinnedTargetCanonical' pinnedTargetExternalTwoEnded') := by
    simpa only [exactOccurrence] using coreEquates.1
  have reverseCore : Relation.ReflTransGen Step
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) after))
        pinnedTargetCanonical' pinnedTargetExternalTwoEnded')
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before))
        pinnedSourceCanonical pinnedSourceExternalTwoEnded) := by
    simpa only [exactOccurrence] using coreEquates.2
  have forward : Relation.TransGen Step source
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems after)) targetCanonical
          targetExternalTwoEnded) :=
    (sourcePins.1.reflTransGen forwardCore).trans (by
      simpa only [targetOccurrence, exactOccurrence] using targetPins.2)
  have reverse : Relation.TransGen Step
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems after)) targetCanonical
          targetExternalTwoEnded) source :=
    (Relation.TransGen.reflTransGen (by
      simpa only [targetOccurrence, exactOccurrence] using targetPins.1)
      reverseCore).trans sourcePins.2
  have strict : StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems after)
      targetCanonical targetExternalTwoEnded := ⟨forward, reverse⟩
  exact strictEquates_of_equates occurrence strict.toEquates

theorem withPinnedEnvelope
    {boundary outer : List Sig}
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems before) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems after)).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems after)))
    (core : ∀
      (pinnedSourceCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before)).Canonical)
      (pinnedSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before))),
      ∃ pinnedTargetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals
              (hostItems.append (contextPins outer hostLocals)) after)).Canonical,
        ∃ pinnedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (Region.adjoinAt hostLocals
                (hostItems.append (contextPins outer hostLocals)) after)),
          Equates
            (exactOccurrence occurrence.interface occurrence.context
              (Region.adjoinAt hostLocals
                (hostItems.append (contextPins outer hostLocals)) before)
              pinnedSourceCanonical pinnedSourceExternalTwoEnded)
            (Region.adjoinAt hostLocals
              (hostItems.append (contextPins outer hostLocals)) after)
            pinnedTargetCanonical pinnedTargetExternalTwoEnded) :
    StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems after)
      targetCanonical targetExternalTwoEnded := by
  by_cases nonempty : outer ++ hostLocals ≠ []
  · exact withPinnedEnvelopeNonempty occurrence targetCanonical
      targetExternalTwoEnded nonempty core
  · have empty : outer ++ hostLocals = [] := Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] := (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    have pinnedSourceCanonical :
        (occurrence.context.fill
          (Region.adjoinAt []
            (hostItems.append (contextPins [] [])) before)).Canonical := by
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using occurrence.sourceCanonical
    have pinnedSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt []
            (hostItems.append (contextPins [] [])) before)) := by
      intro signature wire
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using
        occurrence.sourceExternalTwoEnded wire
    obtain ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded,
        coreEquates⟩ := core pinnedSourceCanonical
      pinnedSourceExternalTwoEnded
    have exactTargetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt [] hostItems after)).Canonical := by
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using pinnedTargetCanonical
    have exactTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill (Region.adjoinAt [] hostItems after)) := by
      intro signature wire
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using pinnedTargetExternalTwoEnded wire
    let exactTarget := occurrence.interface.withBody
      (occurrence.context.fill (Region.adjoinAt [] hostItems after))
      exactTargetCanonical exactTargetExternalTwoEnded
    let requestedTarget := occurrence.interface.withBody
      (occurrence.context.fill (Region.adjoinAt [] hostItems after))
      targetCanonical targetExternalTwoEnded
    let targetIso : OpenDiagramIso exactTarget requestedTarget :=
      OpenDiagram.withBody_iso exactTargetCanonical targetCanonical
        exactTargetExternalTwoEnded targetExternalTwoEnded
        (RegionIso.refl _)
    have equivalent : Equates occurrence
        (Region.adjoinAt [] hostItems after)
        targetCanonical targetExternalTwoEnded := by
      constructor
      · exact reflTransGen_iso occurrence.host_iso.symm (by
          simpa [contextPins, allPins, ItemSeq.pinWires,
            ItemSeq.append_nil, exactOccurrence, exactTarget] using
              coreEquates.1) targetIso
      · exact reflTransGen_iso targetIso (by
          simpa [contextPins, allPins, ItemSeq.pinWires,
            ItemSeq.append_nil, exactOccurrence, exactTarget] using
              coreEquates.2) occurrence.host_iso.symm
    exact strictEquates_of_equates occurrence equivalent

/-- Run a directed telescope inside one shared temporary support-pin envelope.
The endpoint validity for both pinned diagrams is constructed here; the caller
supplies only the structural telescope between those endpoints. -/
theorem withPinnedTelescope
    {boundary outer : List Sig}
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    {before after : Region (outer ++ hostLocals)}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (beforeCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems before)).Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems before)))
    (afterCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems after)).Canonical)
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems after)))
    (polarityEq : context.polarity = polarity)
    (core : ∀
      (pinnedBeforeCanonical :
        (context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before)).Canonical)
      (pinnedBeforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire
        (context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) before)))
      (pinnedAfterCanonical :
        (context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) after)).Canonical)
      (pinnedAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire
        (context.fill
          (Region.adjoinAt hostLocals
            (hostItems.append (contextPins outer hostLocals)) after))),
      Telescope polarity interface context
        (Region.adjoinAt hostLocals
          (hostItems.append (contextPins outer hostLocals)) before)
        (Region.adjoinAt hostLocals
          (hostItems.append (contextPins outer hostLocals)) after)
        pinnedBeforeCanonical pinnedBeforeExternalTwoEnded
        pinnedAfterCanonical pinnedAfterExternalTwoEnded) :
    Telescope polarity interface context
      (Region.adjoinAt hostLocals hostItems before)
      (Region.adjoinAt hostLocals hostItems after)
      beforeCanonical beforeExternalTwoEnded
      afterCanonical afterExternalTwoEnded := by
  by_cases nonempty : outer ++ hostLocals ≠ []
  · let beforeOpen := interface.withBody
      (context.fill (Region.adjoinAt hostLocals hostItems before))
      beforeCanonical beforeExternalTwoEnded
    let beforeOccurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems before) beforeOpen :=
      exactOccurrence interface context
        (Region.adjoinAt hostLocals hostItems before)
        beforeCanonical beforeExternalTwoEnded
    obtain ⟨pinnedBeforeCanonical, pinnedBeforeExternalTwoEnded,
        beforePins⟩ := adjoinPinsEquatesNonempty hostLocals hostItems
      before beforeOccurrence nonempty
    let afterOpen := interface.withBody
      (context.fill (Region.adjoinAt hostLocals hostItems after))
      afterCanonical afterExternalTwoEnded
    let afterOccurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems after) afterOpen :=
      exactOccurrence interface context
        (Region.adjoinAt hostLocals hostItems after)
        afterCanonical afterExternalTwoEnded
    obtain ⟨pinnedAfterCanonical, pinnedAfterExternalTwoEnded,
        afterPins⟩ := adjoinPinsEquatesNonempty hostLocals hostItems
      after afterOccurrence nonempty
    have middle := core pinnedBeforeCanonical pinnedBeforeExternalTwoEnded
      pinnedAfterCanonical pinnedAfterExternalTwoEnded
    refine ⟨polarityEq, ?_⟩
    cases polarity with
    | positive =>
        exact (transGen_reflTransGen (by
          simpa only [beforeOccurrence, exactOccurrence, beforeOpen] using
            beforePins.1)).trans
          (middle.2.trans (transGen_reflTransGen (by
            simpa only [afterOccurrence, exactOccurrence, afterOpen] using
              afterPins.2)))
    | negative =>
        exact (transGen_reflTransGen (by
          simpa only [afterOccurrence, exactOccurrence, afterOpen] using
            afterPins.1)).trans
          (middle.2.trans (transGen_reflTransGen (by
            simpa only [beforeOccurrence, exactOccurrence, beforeOpen] using
              beforePins.2)))
  · have empty : outer ++ hostLocals = [] := Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] :=
      (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    have pinnedBeforeCanonical :
        (context.fill
          (Region.adjoinAt []
            (hostItems.append (contextPins [] [])) before)).Canonical := by
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using beforeCanonical
    have pinnedBeforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire
        (context.fill
          (Region.adjoinAt []
            (hostItems.append (contextPins [] [])) before)) := by
      intro signature wire
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using beforeExternalTwoEnded wire
    have pinnedAfterCanonical :
        (context.fill
          (Region.adjoinAt []
            (hostItems.append (contextPins [] [])) after)).Canonical := by
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using afterCanonical
    have pinnedAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire
        (context.fill
          (Region.adjoinAt []
            (hostItems.append (contextPins [] [])) after)) := by
      intro signature wire
      simpa [contextPins, allPins, ItemSeq.pinWires,
        ItemSeq.append_nil] using afterExternalTwoEnded wire
    have exactCore := core pinnedBeforeCanonical
      pinnedBeforeExternalTwoEnded pinnedAfterCanonical
      pinnedAfterExternalTwoEnded
    simpa [contextPins, allPins, ItemSeq.pinWires,
      ItemSeq.append_nil] using exactCore


/-- Add temporary support pins, expose one erasure description, and remove the
same pins at the exposed endpoint. The description equations are the sole
presentation bridge between the actual endpoints and the shared exposure
construction. -/
theorem pinnedExposureStrict
    {boundary outer : List Sig}
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    {before after : Region (outer ++ hostLocals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems before) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems after)).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems after)))
    (nonempty : outer ++ hostLocals ≠ [])
    (description : Rule.Erasure.Description outer)
    (sourceEq : description.source =
      Region.adjoinAt hostLocals
        (hostItems.append (contextPins outer hostLocals)) before)
    (targetEq : description.target =
      Region.mk hostLocals
        (hostItems.append (contextPins outer hostLocals)))
    (exposedEq : ∀ materialCanonical : description.material.Canonical,
      Erasure.Exposure.exposedRegion description materialCanonical =
        Region.adjoinAt hostLocals
          (hostItems.append (contextPins outer hostLocals)) after) :
    StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems after)
      targetCanonical targetExternalTwoEnded := by
  apply withPinnedEnvelopeNonempty occurrence targetCanonical
    targetExternalTwoEnded nonempty
  intro pinnedSourceCanonical pinnedSourceExternalTwoEnded
  let pinnedOccurrence :=
    exactOccurrence occurrence.interface occurrence.context
      (Region.adjoinAt hostLocals
        (hostItems.append (contextPins outer hostLocals)) before)
      pinnedSourceCanonical pinnedSourceExternalTwoEnded
  exact pinnedExposureCore pinnedOccurrence description sourceEq targetEq
    exposedEq

private theorem identityBoundaryMaterial_scope
    (pattern : OpenDiagram arguments)
    (ports : Vars wires arguments) :
    ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (identityBoundary pattern) ports) := by
  constructor
  · intro _
    exact
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        (identityBoundary pattern) ports
  · intro signature wire
    rw [instantiate_incidence_nonempty_iff,
      instantiate_incidence_nonempty_iff]
  · intro signature wire sourceRoot
    rw [instantiate_rootedTwo_iff] at sourceRoot ⊢
    exact sourceRoot

/-- One selected instantiation in its exact inferred retained host is
bidirectionally equivalent to the same application through the ordered
identity boundary. The normalized combined endpoint and both validity proofs
are constructed internally. -/
theorem equatesIdentityBoundary
    {boundary outer arguments : List Sig}
    (pattern : OpenDiagram arguments)
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (ports : Vars (outer ++ hostLocals) arguments)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports)) source) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (identityBoundary pattern) ports))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                (identityBoundary pattern) ports))),
        Equates occurrence
          (Region.adjoinAt hostLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (identityBoundary pattern) ports))
          targetCanonical targetExternalTwoEnded := by
  let sourceMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports
  let targetMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (identityBoundary pattern) ports
  let sourceRegion := Region.adjoinAt hostLocals hostItems sourceMaterial
  let targetRegion := Region.adjoinAt hostLocals hostItems targetMaterial
  have sourceLocalCanonical : sourceRegion.Canonical := by
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have regionScope : ScopePreservation sourceRegion targetRegion := by
    exact adjoinAt_preserves_scope hostLocals hostItems sourceMaterial
      targetMaterial (identityBoundaryMaterial_scope pattern ports)
  have targetLocalCanonical : targetRegion.Canonical :=
    regionScope.canonical sourceLocalCanonical
  have replacement := occurrence.context.replaceCanonical sourceRegion
    targetRegion occurrence.sourceCanonical targetLocalCanonical
      regionScope.incidenceNonempty
  let targetCanonical := replacement.1
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill sourceRegion) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  let targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetRegion) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2
  refine ⟨targetCanonical, targetExternalTwoEnded, ?_⟩
  by_cases nonempty : outer ++ hostLocals ≠ []
  · let pinnedItems := hostItems.append (contextPins outer hostLocals)
    let description := exposureDescriptionWithHost pattern hostLocals
      pinnedItems ports
    have sourceEq : description.source =
        Region.adjoinAt hostLocals pinnedItems sourceMaterial := by
      simpa only [description, sourceMaterial] using
        exposureDescriptionWithHost_source pattern hostLocals pinnedItems ports
    have targetEq : description.target =
        Region.mk hostLocals pinnedItems := by
      rfl
    have exposedEq : ∀ materialCanonical : description.material.Canonical,
        Erasure.Exposure.exposedRegion description materialCanonical =
          Region.adjoinAt hostLocals pinnedItems targetMaterial := by
      intro materialCanonical
      simpa only [description, targetMaterial] using
        exposureDescriptionWithHost_exposedRegion pattern hostLocals
          pinnedItems ports materialCanonical
    have strict := pinnedExposureStrict
      (occurrence := by simpa only [sourceMaterial] using occurrence)
      (targetCanonical := by
        simpa only [targetRegion, targetMaterial] using targetCanonical)
      (targetExternalTwoEnded := by
        intro signature wire
        simpa only [targetRegion, targetMaterial] using
          targetExternalTwoEnded wire)
      nonempty description sourceEq targetEq exposedEq
    simpa only [targetRegion, targetMaterial] using strict.toEquates
  · have empty : outer ++ hostLocals = [] :=
      Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] :=
      (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    let description := exposureDescriptionWithHost pattern [] hostItems ports
    have sourceEq : description.source = sourceRegion := by
      simpa only [description, sourceRegion, sourceMaterial] using
        exposureDescriptionWithHost_source pattern [] hostItems ports
    let exposureOccurrence : Occurrence description.source source := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := by
        rw [sourceEq]
        exact occurrence.sourceCanonical
      sourceExternalTwoEnded := by
        intro signature wire
        rw [sourceEq]
        exact occurrence.sourceExternalTwoEnded wire
      host_iso := by
        simpa only [sourceEq, sourceRegion, sourceMaterial] using
          occurrence.host_iso
    }
    have erasedLocalCanonical : description.target.Canonical := by
      have canonical := pinnedHostCanonical ([] : List Sig) hostItems
        sourceMaterial sourceLocalCanonical
      simpa only [description, exposureDescriptionWithHost,
        Rule.Erasure.Description.target, contextPins, allPins,
        List.nil_append, ItemSeq.pinWires, ItemSeq.nil_append,
        ItemSeq.append_nil] using canonical
    have erasedSameNonempty : ∀ {signature} (wire : Var [] signature),
        sourceRegion.incidencePaths wire.index.val ≠ [] ↔
          description.target.incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact Fin.elim0 wire.index
    have erasedReplacement := occurrence.context.replaceCanonical
      sourceRegion description.target occurrence.sourceCanonical
        erasedLocalCanonical erasedSameNonempty
    have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill description.target) :=
      sourceEndpoint.externalTwoEnded_of_nonempty_iff _
        erasedReplacement.2
    obtain ⟨materialCanonical, exposedCanonical,
        exposedExternalTwoEnded, exposedEquates⟩ :=
      Erasure.Exposure.equates description exposureOccurrence
        erasedReplacement.1 erasedExternalTwoEnded
    have exposedEq :
        Erasure.Exposure.exposedRegion description materialCanonical =
          targetRegion := by
      simpa only [description, targetRegion, targetMaterial] using
        exposureDescriptionWithHost_exposedRegion pattern [] hostItems ports
          materialCanonical
    simpa only [Equates, exposureOccurrence, sourceEq, exposedEq,
      sourceRegion, sourceMaterial, targetRegion, targetMaterial] using
      exposedEquates

mutual
  private noncomputable def normalizedRegionStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected sourceRegion result)
      (sites : RegionSites operation data evidence)
      (hasSelection : regionHasSelection sites = true) :
      ∀ (outer : List Sig) (rename : WireRenaming common outer)
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence (result.renameWires rename) source)
        (targetCanonical :
          (occurrence.context.fill
            (Region.renameWires rename
              (normalizedRegion pattern evidence sites).1)).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.renameWires rename
              (normalizedRegion pattern evidence sites).1))),
        StrictEquates occurrence
          (Region.renameWires rename (normalizedRegion pattern evidence sites).1)
          targetCanonical (fun wire => targetExternalTwoEnded wire) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        intro outer rename boundary source occurrence targetCanonical
          targetExternalTwoEnded
        let childRename := rename.appendRight locals
        let childHostItems : ItemSeq (outer ++ locals) := .nil
        change Occurrence
          ((Region.adjoinAt locals .nil childResult).renameWires rename) source
          at occurrence
        have sourceEq := Region.renameWires_adjoinAt_nil childResult rename
        have childSourceCanonical :
            (Region.adjoinAt locals childHostItems
              (childResult.renameWires childRename)).Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            ((Region.adjoinAt locals .nil childResult).renameWires rename).incidencePaths
                  wire.index.val ≠ [] ↔
              (Region.adjoinAt locals childHostItems
                (childResult.renameWires childRename)).incidencePaths
                  wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let childOccurrence : Occurrence
            (Region.adjoinAt locals childHostItems
              (childResult.renameWires childRename)) source :=
          presentationOccurrence occurrence childSourceCanonical sourceNonempty
            (by
              simpa only [childHostItems, childRename] using
                RegionIso.renameWiresAdjoinAtNil childResult rename)
        let normalizedChild :=
          (normalizedItems pattern childEvidence childSites).1
        let targetBefore :=
          (Region.adjoinAt locals (.nil : ItemSeq (common ++ locals))
            normalizedChild).renameWires rename
        let targetAfter := Region.adjoinAt locals childHostItems
          (normalizedChild.renameWires childRename)
        have targetEq : targetBefore = targetAfter := by
          simpa only [targetBefore, targetAfter, childHostItems, childRename] using
            Region.renameWires_adjoinAt_nil normalizedChild rename
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have childTargetCanonical :
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                (Region.renameWires childRename
                  (normalizedItems pattern childEvidence childSites).1))).Canonical := by
          exact targetReplacement.1
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                (Region.renameWires childRename
                  (normalizedItems pattern childEvidence childSites).1))) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childSelection : itemsHaveSelection childSites = true := by
          simpa only [regionHasSelection] using hasSelection
        have folded := normalizedItemsStrict pattern
          childEvidence childSites childSelection locals childRename childHostItems
          childOccurrence childTargetCanonical childTargetExternalTwoEnded
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          simpa only [targetAfter, targetBefore, childHostItems, childRename] using
            (RegionIso.renameWiresAdjoinAtNil normalizedChild rename).symm
        have finalIso : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill targetAfter)
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso childTargetCanonical targetCanonical
            childTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have presented := StrictEquates.targetIso folded finalIso
        simpa only [normalizedRegion, normalizedChild, targetBefore, targetAfter,
          childHostItems, childRename, childOccurrence] using presented
  termination_by 5 * sizeOf sites

  private noncomputable def normalizedItemsStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected sourceItems result)
      (sites : ItemsSites operation data evidence)
      (hasSelection : itemsHaveSelection sites = true)
      (hostLocals : List Sig)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals))
      {boundary : List Sig} {source : OpenDiagram boundary}
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems
          (result.renameWires rename)) source)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename
              (normalizedItems pattern evidence sites).1))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename
              (normalizedItems pattern evidence sites).1)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          (Region.renameWires rename (normalizedItems pattern evidence sites).1))
        targetCanonical (fun wire => targetExternalTwoEnded wire) := by
    let sourceMaterial := result.renameWires rename
    let targetMaterial :=
      (Region.renameWires rename (normalizedItems pattern evidence sites).1)
    by_cases nonempty : outer ++ hostLocals ≠ []
    · exact (by
    obtain ⟨pinnedSourceCanonical, pinnedSourceExternalTwoEnded,
        sourcePins⟩ := adjoinPinsEquatesNonempty hostLocals
      hostItems sourceMaterial occurrence nonempty
    let pinnedItems := hostItems.append
      (contextPins outer hostLocals)
    let pinnedSource := Region.adjoinAt hostLocals pinnedItems sourceMaterial
    let pinnedSourceOccurrence : Occurrence pinnedSource
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context pinnedSource
        pinnedSourceCanonical pinnedSourceExternalTwoEnded
    have sourceLocalCanonical :
        (Region.adjoinAt hostLocals hostItems sourceMaterial).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have pinnedHostCanonical :
        (Region.mk hostLocals pinnedItems).Canonical := by
      exact pinnedHostCanonical hostLocals hostItems
        sourceMaterial sourceLocalCanonical
    have pinnedHostNonempty : ∀ {signature}
        (wire : Var outer signature),
        (Region.mk hostLocals pinnedItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact pinnedHost_incidence_nonempty hostLocals hostItems wire
    have targetLocalCanonical :
        (Region.adjoinAt hostLocals hostItems targetMaterial).Canonical :=
      occurrence.context.holeCanonical _ targetCanonical
    have targetMaterialCanonical : targetMaterial.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals hostItems _
        targetLocalCanonical
    have pinnedTargetValidity := supportedAdjoinValidity hostLocals
      pinnedItems pinnedSourceOccurrence pinnedHostCanonical
      pinnedHostNonempty targetMaterialCanonical
    have folded := normalizedItemsSupportedStrict pattern evidence
      sites hasSelection outer hostLocals rename pinnedItems pinnedSourceOccurrence
      pinnedHostCanonical pinnedHostNonempty pinnedTargetValidity.1
      pinnedTargetValidity.2
    let targetOccurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems targetMaterial)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context _
        targetCanonical targetExternalTwoEnded
    obtain ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded,
        targetPins⟩ := adjoinPinsEquatesNonempty hostLocals
      hostItems targetMaterial targetOccurrence nonempty
    have forwardPins : Relation.TransGen Step source
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using sourcePins.1
    have reversePins : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) source := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using sourcePins.2
    have middleForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using folded.1
    have middleReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using folded.2
    have unpinForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.2
    have unpinReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.1
    exact ⟨(forwardPins.trans middleForward).trans unpinForward,
      (unpinReverse.trans middleReverse).trans reversePins⟩)
    · have empty : outer ++ hostLocals = [] :=
        Classical.not_not.mp nonempty
      have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
      have localsEmpty : hostLocals = [] :=
        (List.append_eq_nil_iff.mp empty).2
      subst outer
      subst hostLocals
      have sourceLocalCanonical :
          (Region.adjoinAt [] hostItems sourceMaterial).Canonical :=
        occurrence.context.holeCanonical _ occurrence.sourceCanonical
      have hostCanonical : (Region.mk [] hostItems).Canonical := by
        have canonical := pinnedHostCanonical ([] : List Sig) hostItems
          sourceMaterial sourceLocalCanonical
        simpa only [contextPins, allPins, List.nil_append,
          ItemSeq.pinWires, ItemSeq.nil_append, ItemSeq.append_nil] using
          canonical
      have hostNonempty : ∀ {signature} (wire : Var [] signature),
          (Region.mk [] hostItems).incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        exact Fin.elim0 wire.index
      have folded := normalizedItemsSupportedStrict pattern evidence sites
        hasSelection [] [] rename hostItems occurrence hostCanonical
          hostNonempty targetCanonical targetExternalTwoEnded
      simpa only [sourceMaterial, targetMaterial] using folded
  termination_by 5 * sizeOf sites + 4

  private noncomputable def normalizedItemsSupportedStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected sourceItems result)
      (sites : ItemsSites operation data evidence)
      (hasSelection : itemsHaveSelection sites = true) :
      ∀ (outer : List Sig) (hostLocals : List Sig)
        (rename : WireRenaming common (outer ++ hostLocals))
        (hostItems : ItemSeq (outer ++ hostLocals))
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence
          (Region.adjoinAt hostLocals hostItems
            (result.renameWires rename)) source)
        (_hostCanonical : (Region.mk hostLocals hostItems).Canonical)
        (_hostNonempty : ∀ {signature} (wire : Var outer signature),
          (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
        (targetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItems pattern evidence sites).1))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItems pattern evidence sites).1)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename (normalizedItems pattern evidence sites).1))
          targetCanonical targetExternalTwoEnded :=
    match sites with
    | .nil _ => by
        simp only [itemsHaveSelection, Bool.false_eq_true] at hasSelection
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemEndpoint tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        intro outer hostLocals rename hostItems boundary source occurrence
          hostCanonical hostNonempty targetCanonical targetExternalTwoEnded
        let itemBefore := itemEndpoint.renameWires rename
        let tailBefore := tailResult.renameWires rename
        let itemAfter :=
          (Region.renameWires rename (normalizedItem pattern itemEvidence itemSites).1)
        let tailAfter :=
          (Region.renameWires rename (normalizedItems pattern tailEvidence tailSites).1)
        change Occurrence
          (Region.adjoinAt hostLocals hostItems
            ((itemEndpoint.conjoin tailResult).renameWires rename)) source
          at occurrence
        have sourceBeforeCanonical :
            ((itemEndpoint.conjoin tailResult).renameWires rename).Canonical :=
          Region.Canonical.material_of_adjoinAt hostLocals hostItems _
            (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
        have sourceMaterialCanonical :
            (itemBefore.conjoin tailBefore).Canonical := by
          rw [← Region.renameWires_conjoin]
          exact sourceBeforeCanonical
        let sourceOccurrence : Occurrence
            (Region.adjoinAt hostLocals hostItems
              (itemBefore.conjoin tailBefore)) source :=
          supportedAdjoinOccurrence hostLocals hostItems occurrence hostCanonical
            hostNonempty sourceMaterialCanonical (by
              simpa only [itemBefore, tailBefore] using
                RegionIso.renameWiresConjoin itemEndpoint tailResult rename)
        have itemBeforeCanonical :=
          canonical_left_of_conjoin sourceMaterialCanonical
        have tailBeforeCanonical :=
          canonical_right_of_conjoin sourceMaterialCanonical
        let normalizedHead := (normalizedItem pattern itemEvidence itemSites).1
        let normalizedTail := (normalizedItems pattern tailEvidence tailSites).1
        let targetBefore :=
          (normalizedHead.conjoin normalizedTail).renameWires rename
        change (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems targetBefore)).Canonical
          at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetBefore))
          at targetExternalTwoEnded
        have presentedTargetCanonical :
            (sourceOccurrence.context.fill
              (Region.adjoinAt hostLocals hostItems targetBefore)).Canonical := by
          exact targetCanonical
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            sourceOccurrence.interface.boundaryWire
            (sourceOccurrence.context.fill
              (Region.adjoinAt hostLocals hostItems targetBefore)) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        have targetBeforeCanonical : targetBefore.Canonical :=
          Region.Canonical.material_of_adjoinAt hostLocals hostItems _
            (occurrence.context.holeCanonical _ targetCanonical)
        have targetMaterialCanonical :
            (itemAfter.conjoin tailAfter).Canonical := by
          rw [← Region.renameWires_conjoin]
          exact targetBeforeCanonical
        have itemAfterCanonical :=
          canonical_left_of_conjoin targetMaterialCanonical
        have tailAfterCanonical :=
          canonical_right_of_conjoin targetMaterialCanonical
        by_cases itemSelected : itemHasSelection itemSites = true
        · by_cases tailSelected : itemsHaveSelection tailSites = true
          · exact (by
        have itemPhaseValidity := supportedAdjoinValidity hostLocals hostItems
          sourceOccurrence hostCanonical hostNonempty
          (canonical_conjoin itemAfterCanonical tailBeforeCanonical)
        have itemPhase := normalizedItemWithTailStrict pattern
          itemEvidence itemSites itemSelected hostLocals rename hostItems tailBefore
          sourceOccurrence hostCanonical hostNonempty itemBeforeCanonical
          tailBeforeCanonical itemAfterCanonical itemPhaseValidity.1
          itemPhaseValidity.2
        let afterItem := Region.adjoinAt hostLocals hostItems
          (itemAfter.conjoin tailBefore)
        let afterItemOccurrence : Occurrence afterItem
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill afterItem) itemPhaseValidity.1
                itemPhaseValidity.2) :=
          exactOccurrence sourceOccurrence.interface sourceOccurrence.context afterItem
            itemPhaseValidity.1 itemPhaseValidity.2
        let flattened := flattenAdjoinOccurrence hostLocals hostItems
          itemAfter tailBefore afterItemOccurrence hostCanonical hostNonempty
          itemAfterCanonical tailBeforeCanonical
        let nextHostItems := Region.extendHostItems hostLocals hostItems
          itemAfter
        let hostWire :=
          Region.adjoinHostWire outer hostLocals itemAfter.locals
        let nextRename := WireRenaming.comp
          hostWire rename
        have nextHostCanonical := extendHostCanonical hostLocals hostItems
          itemAfter hostCanonical itemAfterCanonical
        have nextHostNonempty : ∀ {signature}
            (wire : Var outer signature),
            (Region.mk (hostLocals ++ itemAfter.locals) nextHostItems).incidencePaths
              wire.index.val ≠ [] := by
          intro signature wire
          exact extendHost_incidence_nonempty hostLocals hostItems itemAfter
            hostNonempty wire
        have tailResultCanonical : tailResult.Canonical :=
          (Region.Canonical.renameWires_iff tailResult rename).mp
            tailBeforeCanonical
        have alignedTailCanonical :
            (tailResult.renameWires nextRename).Canonical :=
          (Region.Canonical.renameWires_iff tailResult nextRename).mpr
            tailResultCanonical
        let alignedFlattened : Occurrence
            (Region.adjoinAt (hostLocals ++ itemAfter.locals) nextHostItems
              (tailResult.renameWires nextRename))
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill afterItem) itemPhaseValidity.1
                itemPhaseValidity.2) :=
          supportedAdjoinOccurrence (hostLocals ++ itemAfter.locals)
            nextHostItems flattened nextHostCanonical nextHostNonempty
            alignedTailCanonical (by
              simpa only [tailBefore, hostWire, nextRename] using
                RegionIso.renameWiresComp tailResult rename hostWire)
        have normalizedTailCanonical : normalizedTail.Canonical :=
          (Region.Canonical.renameWires_iff normalizedTail rename).mp
            tailAfterCanonical
        let flatTargetMaterial := normalizedTail.renameWires nextRename
        have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
          (Region.Canonical.renameWires_iff normalizedTail nextRename).mpr
            normalizedTailCanonical
        have tailTargetValidity := supportedAdjoinValidity
          (hostLocals ++ itemAfter.locals) nextHostItems alignedFlattened
          nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
        have tailPhase := normalizedItemsSupportedStrict pattern
          tailEvidence tailSites tailSelected outer
          (hostLocals ++ itemAfter.locals) nextRename
          nextHostItems alignedFlattened nextHostCanonical nextHostNonempty
          tailTargetValidity.1 tailTargetValidity.2
        let flatTarget := Region.adjoinAt
          (hostLocals ++ itemAfter.locals) nextHostItems
          flatTargetMaterial
        let flatTargetEndpoint := alignedFlattened.interface.withBody
          (alignedFlattened.context.fill flatTarget) tailTargetValidity.1
            tailTargetValidity.2
        have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
            (Region.adjoinAt hostLocals hostItems targetBefore) := by
          exact (RegionIso.adjoinAt (hostLocals ++ itemAfter.locals)
            nextHostItems (by
            simpa only [flatTargetMaterial, tailAfter, normalizedTail,
              nextRename, hostWire] using
                (RegionIso.renameWiresComp normalizedTail rename hostWire).symm)).trans
            ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemAfter
              tailAfter).symm.trans
              (RegionIso.adjoinAt hostLocals hostItems (by
                simpa only [itemAfter, tailAfter, normalizedHead,
                  normalizedTail, targetBefore] using
                  (RegionIso.renameWiresConjoin normalizedHead normalizedTail rename).symm)))
        have finalIso : OpenDiagramIso flatTargetEndpoint
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill
                (Region.adjoinAt hostLocals hostItems
                  targetBefore))
              presentedTargetCanonical presentedTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso tailTargetValidity.1
            presentedTargetCanonical tailTargetValidity.2
            presentedTargetExternalTwoEnded
            (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
        have tailPhase' : StrictEquates alignedFlattened
            (Region.adjoinAt hostLocals hostItems targetBefore)
            presentedTargetCanonical presentedTargetExternalTwoEnded :=
          StrictEquates.targetIso tailPhase finalIso
        have itemPhase' : StrictEquates sourceOccurrence afterItem
            itemPhaseValidity.1 itemPhaseValidity.2 := by
          simpa only [afterItem, itemBefore, tailBefore, itemAfter,
            sourceOccurrence] using itemPhase
        have combined := StrictEquates.trans
          (targetExternalTwoEnded := presentedTargetExternalTwoEnded)
          itemPhase' tailPhase'
        have outputIso : OpenDiagramIso
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill
                (Region.adjoinAt hostLocals hostItems targetBefore))
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Region.adjoinAt hostLocals hostItems targetBefore))
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded
            (RegionIso.refl _)
        have exactCombined : StrictEquates occurrence
            (Region.adjoinAt hostLocals hostItems targetBefore)
            targetCanonical targetExternalTwoEnded :=
          ⟨transGen_iso (OpenDiagramIso.refl source) combined.1 outputIso,
            transGen_iso outputIso combined.2 (OpenDiagramIso.refl source)⟩
        simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
          sourceOccurrence, afterItem, afterItemOccurrence, flattened,
          alignedFlattened, nextHostItems, hostWire, nextRename,
          flatTargetMaterial, flatTarget, flatTargetEndpoint,
          normalizedHead, normalizedTail, targetBefore, normalizedItems]
          using exactCombined)
          · have tailNone : itemsHaveSelection tailSites = false := by
              cases selected : itemsHaveSelection tailSites with
              | false => rfl
              | true => exact False.elim (tailSelected selected)
            have normalizedTailEq : normalizedTail = tailResult := by
              simpa only [normalizedTail] using
                normalizedItems_eq_of_noSelection pattern tailEvidence
                  tailSites tailNone
            have tailAfterEq : tailAfter = tailBefore := by
              change Region.renameWires rename normalizedTail =
                Region.renameWires rename tailResult
              rw [normalizedTailEq]
            have itemPhaseValidity := supportedAdjoinValidity hostLocals
              hostItems sourceOccurrence hostCanonical hostNonempty
              (canonical_conjoin itemAfterCanonical tailBeforeCanonical)
            have itemPhase := normalizedItemWithTailStrict pattern
              itemEvidence itemSites itemSelected hostLocals rename hostItems
              tailBefore sourceOccurrence hostCanonical hostNonempty
              itemBeforeCanonical tailBeforeCanonical itemAfterCanonical
              itemPhaseValidity.1 itemPhaseValidity.2
            let afterItem := Region.adjoinAt hostLocals hostItems
              (itemAfter.conjoin tailBefore)
            have itemPhase' : StrictEquates sourceOccurrence afterItem
                itemPhaseValidity.1 itemPhaseValidity.2 := by
              simpa only [afterItem, itemBefore, tailBefore, itemAfter,
                sourceOccurrence] using itemPhase
            have materialIso : RegionIso
                (WireEquiv.refl (outer ++ hostLocals))
                (itemAfter.conjoin tailBefore) targetBefore := by
              rw [← tailAfterEq]
              simpa only [itemAfter, tailAfter, normalizedHead,
                normalizedTail, targetBefore] using
                (RegionIso.renameWiresConjoin normalizedHead normalizedTail
                  rename).symm
            have finalBodyIso : RegionIso (WireEquiv.refl outer) afterItem
                (Region.adjoinAt hostLocals hostItems targetBefore) := by
              exact RegionIso.adjoinAt hostLocals hostItems materialIso
            have finalIso : OpenDiagramIso
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill afterItem)
                  itemPhaseValidity.1 itemPhaseValidity.2)
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  presentedTargetCanonical
                    presentedTargetExternalTwoEnded) :=
              OpenDiagram.withBody_iso itemPhaseValidity.1
                presentedTargetCanonical itemPhaseValidity.2
                presentedTargetExternalTwoEnded
                (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
            have presented := StrictEquates.targetIso itemPhase' finalIso
            have outputIso : OpenDiagramIso
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  presentedTargetCanonical
                    presentedTargetExternalTwoEnded)
                (occurrence.interface.withBody
                  (occurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  targetCanonical targetExternalTwoEnded) :=
              OpenDiagram.withBody_iso presentedTargetCanonical
                targetCanonical presentedTargetExternalTwoEnded
                targetExternalTwoEnded (RegionIso.refl _)
            have exactPresented : StrictEquates occurrence
                (Region.adjoinAt hostLocals hostItems targetBefore)
                targetCanonical targetExternalTwoEnded :=
              ⟨transGen_iso (OpenDiagramIso.refl source) presented.1
                  outputIso,
                transGen_iso outputIso presented.2
                  (OpenDiagramIso.refl source)⟩
            simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
              sourceOccurrence, afterItem, normalizedHead, normalizedTail,
              targetBefore, normalizedItems] using exactPresented
        · have itemNone : itemHasSelection itemSites = false := by
            cases selected : itemHasSelection itemSites with
            | false => rfl
            | true => exact False.elim (itemSelected selected)
          have tailSelected : itemsHaveSelection tailSites = true := by
            cases selected : itemsHaveSelection tailSites with
            | true => rfl
            | false =>
                simp only [itemsHaveSelection, itemNone, selected,
                  Bool.false_or, Bool.false_eq_true] at hasSelection
          have normalizedHeadEq : normalizedHead = itemEndpoint := by
            simpa only [normalizedHead] using
              normalizedItem_eq_of_noSelection pattern itemEvidence itemSites
                itemNone
          have itemAfterEq : itemAfter = itemBefore := by
            change Region.renameWires rename normalizedHead =
              Region.renameWires rename itemEndpoint
            rw [normalizedHeadEq]
          let flattened := flattenAdjoinOccurrence hostLocals hostItems
            itemBefore tailBefore sourceOccurrence hostCanonical hostNonempty
            itemBeforeCanonical tailBeforeCanonical
          let nextHostItems := Region.extendHostItems hostLocals hostItems
            itemBefore
          let hostWire :=
            Region.adjoinHostWire outer hostLocals itemBefore.locals
          let nextRename := WireRenaming.comp hostWire rename
          have nextHostCanonical := extendHostCanonical hostLocals hostItems
            itemBefore hostCanonical itemBeforeCanonical
          have nextHostNonempty : ∀ {signature}
              (wire : Var outer signature),
              (Region.mk (hostLocals ++ itemBefore.locals)
                nextHostItems).incidencePaths wire.index.val ≠ [] := by
            intro signature wire
            exact extendHost_incidence_nonempty hostLocals hostItems itemBefore
              hostNonempty wire
          have tailResultCanonical : tailResult.Canonical :=
            (Region.Canonical.renameWires_iff tailResult rename).mp
              tailBeforeCanonical
          have alignedTailCanonical :
              (tailResult.renameWires nextRename).Canonical :=
            (Region.Canonical.renameWires_iff tailResult nextRename).mpr
              tailResultCanonical
          let alignedFlattened : Occurrence
              (Region.adjoinAt (hostLocals ++ itemBefore.locals)
                nextHostItems (tailResult.renameWires nextRename)) source :=
            supportedAdjoinOccurrence (hostLocals ++ itemBefore.locals)
              nextHostItems flattened nextHostCanonical nextHostNonempty
              alignedTailCanonical (by
                simpa only [tailBefore, hostWire, nextRename] using
                  RegionIso.renameWiresComp tailResult rename hostWire)
          have normalizedTailCanonical : normalizedTail.Canonical :=
            (Region.Canonical.renameWires_iff normalizedTail rename).mp
              tailAfterCanonical
          let flatTargetMaterial := normalizedTail.renameWires nextRename
          have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
            (Region.Canonical.renameWires_iff normalizedTail nextRename).mpr
              normalizedTailCanonical
          have tailTargetValidity := supportedAdjoinValidity
            (hostLocals ++ itemBefore.locals) nextHostItems alignedFlattened
            nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
          have tailPhase := normalizedItemsSupportedStrict pattern
            tailEvidence tailSites tailSelected outer
            (hostLocals ++ itemBefore.locals) nextRename nextHostItems
            alignedFlattened nextHostCanonical nextHostNonempty
            tailTargetValidity.1 tailTargetValidity.2
          let flatTarget := Region.adjoinAt
            (hostLocals ++ itemBefore.locals) nextHostItems flatTargetMaterial
          let flatTargetEndpoint := alignedFlattened.interface.withBody
            (alignedFlattened.context.fill flatTarget) tailTargetValidity.1
              tailTargetValidity.2
          have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
              (Region.adjoinAt hostLocals hostItems targetBefore) := by
            exact (RegionIso.adjoinAt (hostLocals ++ itemBefore.locals)
              nextHostItems (by
                simpa only [flatTargetMaterial, tailAfter, normalizedTail,
                  nextRename, hostWire] using
                    (RegionIso.renameWiresComp normalizedTail rename hostWire).symm)).trans
              ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemBefore
                tailAfter).symm.trans
                (RegionIso.adjoinAt hostLocals hostItems (by
                  rw [← itemAfterEq]
                  simpa only [itemAfter, tailAfter, normalizedHead,
                    normalizedTail, targetBefore] using
                    (RegionIso.renameWiresConjoin normalizedHead normalizedTail
                      rename).symm)))
          have finalIso : OpenDiagramIso flatTargetEndpoint
              (sourceOccurrence.interface.withBody
                (sourceOccurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                presentedTargetCanonical
                  presentedTargetExternalTwoEnded) :=
            OpenDiagram.withBody_iso tailTargetValidity.1
              presentedTargetCanonical tailTargetValidity.2
              presentedTargetExternalTwoEnded
              (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
          have tailPhase' : StrictEquates alignedFlattened
              (Region.adjoinAt hostLocals hostItems targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded :=
            StrictEquates.targetIso tailPhase finalIso
          have presented : StrictEquates sourceOccurrence
              (Region.adjoinAt hostLocals hostItems targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded := by
            simpa only [sourceOccurrence, flattened, alignedFlattened,
              supportedAdjoinOccurrence] using tailPhase'
          have outputIso : OpenDiagramIso
              (sourceOccurrence.interface.withBody
                (sourceOccurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                presentedTargetCanonical presentedTargetExternalTwoEnded)
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                targetCanonical targetExternalTwoEnded) :=
            OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
              presentedTargetExternalTwoEnded targetExternalTwoEnded
              (RegionIso.refl _)
          have exactPresented : StrictEquates occurrence
              (Region.adjoinAt hostLocals hostItems targetBefore)
              targetCanonical targetExternalTwoEnded :=
            ⟨transGen_iso (OpenDiagramIso.refl source) presented.1 outputIso,
              transGen_iso outputIso presented.2
                (OpenDiagramIso.refl source)⟩
          simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
            sourceOccurrence, flattened, alignedFlattened, nextHostItems,
            hostWire, nextRename, flatTargetMaterial, flatTarget,
            flatTargetEndpoint, normalizedHead, normalizedTail, targetBefore,
            normalizedItems] using exactPresented
  termination_by 5 * sizeOf sites + 3

  private noncomputable def normalizedItemWithTailStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected sourceItem result)
      (sites : ItemSites operation data evidence)
      (hasSelection : itemHasSelection sites = true)
      (hostLocals : List Sig)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals))
      (tail : Region (outer ++ hostLocals))
      {boundary : List Sig} {source : OpenDiagram boundary}
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems
          ((result.renameWires rename).conjoin tail)) source)
      (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
      (hostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
      (itemBeforeCanonical : (result.renameWires rename).Canonical)
      (tailCanonical : tail.Canonical)
      (itemAfterCanonical :
        (Region.renameWires rename
          (normalizedItem pattern evidence sites).1).Canonical)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.renameWires rename
              (normalizedItem pattern evidence sites).1).conjoin
                tail))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.renameWires rename
              (normalizedItem pattern evidence sites).1).conjoin tail)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          ((Region.renameWires rename
            (normalizedItem pattern evidence sites).1).conjoin tail))
        targetCanonical targetExternalTwoEnded := by
    let itemBefore := result.renameWires rename
    let itemAfter :=
      (Region.renameWires rename (normalizedItem pattern evidence sites).1)
    have swappedCanonical : (tail.conjoin itemBefore).Canonical :=
      canonical_conjoin tailCanonical itemBeforeCanonical
    let swapped := supportedAdjoinOccurrence hostLocals hostItems occurrence
      hostCanonical hostNonempty swappedCanonical
      (RegionIso.conjoinComm itemBefore tail)
    let flattened := flattenAdjoinOccurrence hostLocals hostItems tail
      itemBefore swapped hostCanonical hostNonempty tailCanonical
      itemBeforeCanonical
    let nextHostItems := Region.extendHostItems hostLocals hostItems tail
    let hostWire := Region.adjoinHostWire outer hostLocals tail.locals
    let nextRename := WireRenaming.comp
      hostWire rename
    have nextHostCanonical := extendHostCanonical hostLocals hostItems tail
      hostCanonical tailCanonical
    have nextHostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk (hostLocals ++ tail.locals) nextHostItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact extendHost_incidence_nonempty hostLocals hostItems tail
        hostNonempty wire
    have resultCanonical : result.Canonical :=
      (Region.Canonical.renameWires_iff result rename).mp itemBeforeCanonical
    have alignedSourceCanonical : (result.renameWires nextRename).Canonical :=
      (Region.Canonical.renameWires_iff result nextRename).mpr resultCanonical
    let alignedFlattened : Occurrence
        (Region.adjoinAt (hostLocals ++ tail.locals) nextHostItems
          (result.renameWires nextRename)) source :=
      supportedAdjoinOccurrence (hostLocals ++ tail.locals) nextHostItems
        flattened nextHostCanonical nextHostNonempty alignedSourceCanonical (by
          simpa only [itemBefore, hostWire, nextRename] using
            RegionIso.renameWiresComp result rename hostWire)
    let normalized := (normalizedItem pattern evidence sites).1
    have normalizedCanonical : normalized.Canonical :=
      (Region.Canonical.renameWires_iff normalized rename).mp
        itemAfterCanonical
    let flatTargetMaterial := normalized.renameWires nextRename
    have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
      (Region.Canonical.renameWires_iff normalized nextRename).mpr
        normalizedCanonical
    have flatTargetValidity := supportedAdjoinValidity
      (hostLocals ++ tail.locals) nextHostItems alignedFlattened
      nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
    have core := normalizedItemStrict pattern evidence sites hasSelection
      outer (hostLocals ++ tail.locals) nextRename nextHostItems alignedFlattened
      flatTargetValidity.1 flatTargetValidity.2
    let flatTarget := Region.adjoinAt (hostLocals ++ tail.locals)
      nextHostItems flatTargetMaterial
    let flatEndpoint := alignedFlattened.interface.withBody
      (alignedFlattened.context.fill flatTarget) flatTargetValidity.1
        flatTargetValidity.2
    have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
        (Region.adjoinAt hostLocals hostItems
          (itemAfter.conjoin tail)) := by
      exact (RegionIso.adjoinAt (hostLocals ++ tail.locals) nextHostItems (by
        simpa only [flatTargetMaterial, itemAfter, normalized, nextRename,
          hostWire] using
            (RegionIso.renameWiresComp normalized rename hostWire).symm)).trans
        ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems tail
          itemAfter).symm.trans
          (RegionIso.adjoinAt hostLocals hostItems
            (RegionIso.conjoinComm tail itemAfter)))
    have presentedTargetCanonical :
        (alignedFlattened.context.fill
          (Region.adjoinAt hostLocals hostItems
            (itemAfter.conjoin tail))).Canonical := by
      exact targetCanonical
    have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        alignedFlattened.interface.boundaryWire
        (alignedFlattened.context.fill
          (Region.adjoinAt hostLocals hostItems
            (itemAfter.conjoin tail))) := by
      intro signature wire
      exact targetExternalTwoEnded wire
    have finalIso : OpenDiagramIso flatEndpoint
        (alignedFlattened.interface.withBody
          (alignedFlattened.context.fill
            (Region.adjoinAt hostLocals hostItems
              (itemAfter.conjoin tail))) presentedTargetCanonical
          presentedTargetExternalTwoEnded) :=
      OpenDiagram.withBody_iso flatTargetValidity.1 presentedTargetCanonical
        flatTargetValidity.2 presentedTargetExternalTwoEnded
        (DiagramContext.fillIso alignedFlattened.context finalBodyIso)
    have presented : StrictEquates alignedFlattened
        (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail))
        presentedTargetCanonical presentedTargetExternalTwoEnded :=
      StrictEquates.targetIso core finalIso
    have outputIso : OpenDiagramIso
        (alignedFlattened.interface.withBody
          (alignedFlattened.context.fill
            (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail)))
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail)))
          targetCanonical targetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
        presentedTargetExternalTwoEnded targetExternalTwoEnded (RegionIso.refl _)
    have exactPresented : StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail))
        targetCanonical targetExternalTwoEnded :=
      ⟨transGen_iso (OpenDiagramIso.refl source) presented.1 outputIso,
        transGen_iso outputIso presented.2 (OpenDiagramIso.refl source)⟩
    simpa only [itemBefore, itemAfter, swapped, flattened, alignedFlattened,
      nextHostItems, hostWire, nextRename, normalized, flatTargetMaterial,
      flatTarget, flatEndpoint] using exactPresented
  termination_by 5 * sizeOf sites + 2

  private noncomputable def normalizedItemStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected sourceItem result)
      (sites : ItemSites operation data evidence)
      (hasSelection : itemHasSelection sites = true) :
      ∀ (outer : List Sig) (hostLocals : List Sig)
        (rename : WireRenaming common (outer ++ hostLocals))
        (hostItems : ItemSeq (outer ++ hostLocals))
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence
          (Region.adjoinAt hostLocals hostItems
            (result.renameWires rename)) source)
        (targetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItem pattern evidence sites).1))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItem pattern evidence sites).1)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename (normalizedItem pattern evidence sites).1))
          targetCanonical targetExternalTwoEnded :=
    match sites with
    | .atom head ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | .selectedAtom ports _ => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let mappedPorts := ports.map fun wire => rename wire
        let sourceBefore :=
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports).renameWires rename
        let sourceAfter :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern mappedPorts
        let sourceHostBefore := Region.adjoinAt hostLocals hostItems
          sourceBefore
        let sourceHostAfter := Region.adjoinAt hostLocals hostItems sourceAfter
        change Occurrence sourceHostBefore source at occurrence
        have sourceHostEq : sourceHostBefore = sourceHostAfter := by
          simp only [sourceHostBefore, sourceHostAfter, sourceBefore,
            sourceAfter, mappedPorts, instantiate_renameWires]
        have sourceAfterCanonical : sourceHostAfter.Canonical := by
          rw [← sourceHostEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceHostEq]
        let presentedOccurrence : Occurrence sourceHostAfter source :=
          presentationOccurrence occurrence sourceAfterCanonical
            sourceNonempty
            (RegionIso.adjoinAt hostLocals hostItems
              (instantiateRenameIso pattern ports rename))
        let targetBefore := Region.adjoinAt hostLocals hostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports).renameWires rename)
        let targetAfter := Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) mappedPorts)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [targetBefore, targetAfter, mappedPorts,
            instantiate_renameWires]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedOccurrence.interface.boundaryWire
            (presentedOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        obtain ⟨ownedTargetCanonical, ownedTargetExternalTwoEnded,
            equivalent⟩ :=
          equatesIdentityBoundary pattern mappedPorts presentedOccurrence
        have strict := strictEquates_of_equates presentedOccurrence equivalent
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore :=
          RegionIso.adjoinAt hostLocals hostItems
            (instantiateRenameIso (identityBoundary pattern) ports rename).symm
        have finalIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              ownedTargetCanonical ownedTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso ownedTargetCanonical targetCanonical
            ownedTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have presented := StrictEquates.targetIso strict finalIso
        simpa only [normalizedItem, targetBefore, sourceHostBefore,
          sourceBefore] using presented
    | .identity signature arity ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let appendNil : WireRenaming common (common ++ []) :=
          ⟨fun wire => wire.appendLeft []⟩
        let materialRename := Region.adjoinMaterialWire outer hostLocals []
        let childRename := WireRenaming.comp materialRename
          (WireRenaming.comp (rename.appendRight []) appendNil)
        let retained := hostItems.renameWires
          (Region.adjoinHostWire outer hostLocals [])
        let inner : DiagramContext outer (outer ++ (hostLocals ++ [])) :=
          .cut (hostLocals ++ []) retained .nil .hole
        have childRename_eq (region : Region common) :
            Region.renameWires materialRename
                (Region.renameWires (rename.appendRight [])
                  (Region.renameWires appendNil region)) =
              Region.renameWires childRename region := by
          rw [Region.renameWires_comp, Region.renameWires_comp]
          apply congrArg (fun map => Region.renameWires map region)
          apply WireRenaming.ext
          intro signature wire
          rfl
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childResult)).renameWires rename)
        let sourceAfter := inner.fill (childResult.renameWires childRename)
        change Occurrence sourceBefore source at occurrence
        have sourceEq : sourceBefore = sourceAfter := by
          simp only [inner, retained, childRename, materialRename, appendNil,
            sourceBefore, sourceAfter, DiagramContext.fill,
            Region.renameWires, Region.singleton, Region.ofItems,
            Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have sourceAfterCanonical : sourceAfter.Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let outerOccurrence : Occurrence sourceAfter source :=
          presentationOccurrence occurrence sourceAfterCanonical
            sourceNonempty (by
              rw [← sourceEq]
              exact RegionIso.refl _)
        let childOccurrence := Occurrence.nest outerOccurrence
        let normalizedChild :=
          (normalizedRegion pattern childEvidence childSites).1
        let targetBefore := Region.adjoinAt hostLocals hostItems
          (Region.renameWires rename
            (normalizedItem pattern evidence (.cut childSites)).1)
        let targetAfter := inner.fill
          (Region.renameWires childRename normalizedChild)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [normalizedItem, inner, retained, childRename,
            materialRename, appendNil, normalizedChild, targetBefore,
            targetAfter, DiagramContext.fill, Region.renameWires,
            Region.singleton, Region.ofItems, Region.adjoinAt,
            ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have outerTargetCanonical :
            (outerOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have outerTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            outerOccurrence.interface.boundaryWire
            (outerOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childTargetCanonical :
            (childOccurrence.context.fill
              (Region.renameWires childRename normalizedChild)).Canonical := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerTargetCanonical
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (Region.renameWires childRename normalizedChild)) := by
          intro signature wire
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              outerTargetExternalTwoEnded wire
        have childSelection : regionHasSelection childSites = true := by
          simpa only [itemHasSelection] using hasSelection
        have child := normalizedRegionStrict pattern childEvidence
          childSites childSelection (outer ++ (hostLocals ++ [])) childRename
          childOccurrence
          childTargetCanonical
          childTargetExternalTwoEnded
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          rw [← targetEq]
          exact RegionIso.refl _
        have outerFinalIso : OpenDiagramIso
            (outerOccurrence.interface.withBody
              (outerOccurrence.context.fill targetAfter)
              outerTargetCanonical outerTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso outerTargetCanonical targetCanonical
            outerTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have finalIso : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                (Region.renameWires childRename normalizedChild))
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerFinalIso
        have exactChild : StrictEquates occurrence targetBefore targetCanonical
            targetExternalTwoEnded :=
          ⟨transGen_iso (OpenDiagramIso.refl source) child.1 finalIso,
            transGen_iso finalIso child.2 (OpenDiagramIso.refl source)⟩
        simpa only [targetBefore, normalizedItem, sourceBefore] using exactChild
  termination_by 5 * sizeOf sites + 1
end

/-- Normalize every selected application in one exact authoritative item
sequence and connect the actual occurrence bidirectionally to the generated
identity-boundary instantiation. -/
theorem normalizeItemsEquates
    {arguments outer hostLocals sourceWires targetWires : List Sig}
    (pattern : OpenDiagram arguments)
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments (outer ++ hostLocals) sourceWires
      targetWires}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires}
    {result : Region (outer ++ hostLocals)}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals .nil result) host) :
    ∃ normalized : Region (outer ++ hostLocals),
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized ∧
        ∃ targetCanonical :
            (occurrence.context.fill
              (Region.adjoinAt hostLocals .nil normalized)).Canonical,
          ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Region.adjoinAt hostLocals .nil normalized)),
            let reconstructed := occurrence.interface.withBody
              (occurrence.context.fill
                (Region.adjoinAt hostLocals .nil normalized))
              targetCanonical targetExternalTwoEnded
            let target := if itemsHaveSelection sites = false then host
              else reconstructed
            OpenDiagram.Isomorphic target reconstructed ∧
              Relation.ReflTransGen Step host target ∧
                Relation.ReflTransGen Step target host := by
  let output := normalizedItems pattern evidence sites
  by_cases noSelection : itemsHaveSelection sites = false
  · have outputEq : output.1 = result := by
      simpa only [output] using
        normalizedItems_eq_of_noSelection pattern evidence sites noSelection
    have targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output.1)).Canonical := by
      rw [outputEq]
      exact occurrence.sourceCanonical
    have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output.1)) := by
      intro signature wire
      rw [outputEq]
      exact occurrence.sourceExternalTwoEnded wire
    have targetIsomorphic : OpenDiagram.Isomorphic host
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals .nil output.1))
          targetCanonical targetExternalTwoEnded) := by
      exact ⟨by simpa only [outputEq] using occurrence.host_iso⟩
    refine ⟨output.1, output.2, targetCanonical,
      targetExternalTwoEnded, ?_⟩
    dsimp only
    rw [if_pos noSelection]
    exact ⟨targetIsomorphic,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  · exact (by
  let sourceRegion := Region.adjoinAt hostLocals .nil result
  let targetRegion := Region.adjoinAt hostLocals .nil output.1
  let materialScope := normalizedItems_scope pattern evidence sites
  let regionScope := adjoinAt_preserves_scope hostLocals
    (.nil : ItemSeq (outer ++ hostLocals)) result output.1 materialScope
  have sourceLocalCanonical : sourceRegion.Canonical := by
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have targetLocalCanonical : targetRegion.Canonical :=
    regionScope.canonical sourceLocalCanonical
  have replacement := occurrence.context.replaceCanonical sourceRegion
    targetRegion occurrence.sourceCanonical targetLocalCanonical
      regionScope.incidenceNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill sourceRegion) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetRegion) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill targetRegion) replacement.2
  have targetCanonical : (occurrence.context.fill targetRegion).Canonical :=
    replacement.1
  have hasSelection : itemsHaveSelection sites = true := by
    cases selected : itemsHaveSelection sites with
    | false => exact False.elim (noSelection selected)
    | true => rfl
  let identity : WireRenaming (outer ++ hostLocals)
      (outer ++ hostLocals) := WireRenaming.id
  let presentedOccurrence : Occurrence
      (Region.adjoinAt hostLocals .nil (result.renameWires identity)) host := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := by
      simpa only [identity, Region.renameWires_id] using occurrence.sourceCanonical
    sourceExternalTwoEnded := by
      intro signature wire
      simpa only [identity, Region.renameWires_id] using
        occurrence.sourceExternalTwoEnded wire
    host_iso := by
      simpa only [identity, Region.renameWires_id] using occurrence.host_iso
  }
  have folded := normalizedItemsStrict (outer := outer) pattern evidence sites
    hasSelection hostLocals identity (.nil : ItemSeq (outer ++ hostLocals))
      presentedOccurrence (by
        simpa only [presentedOccurrence, targetRegion, identity,
          Region.renameWires_id] using
          targetCanonical) (by
        intro signature wire
        simpa only [presentedOccurrence, targetRegion, identity,
          Region.renameWires_id] using
          targetExternalTwoEnded wire)
  have exactStrict : StrictEquates occurrence targetRegion targetCanonical
      targetExternalTwoEnded := by
    simpa only [presentedOccurrence, targetRegion, identity,
      Region.renameWires_id] using folded
  have equivalent := exactStrict.toEquates
  refine ⟨output.1, output.2, targetCanonical,
    targetExternalTwoEnded, ?_⟩
  dsimp only
  rw [if_neg noSelection]
  exact ⟨OpenDiagram.Isomorphic.refl _, equivalent.1, equivalent.2⟩)

end EqualityNormalization

/-! One edit-indexed traversal materializes an argument primitive directly
from the recorded full external tuple at every selected Formal site. The
current argument tuple lives in the authoritative external context, so every
site is obtained only by substitution through its recorded tuple. -/

mutual
  def argumentRegionEdit
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire))) :
      Σ source : Region sourceWires,
        Transform.RegionEdit operation frame data source :=
    match recordedSites with
    | .mk childSites =>
        let child := argumentItemsEdit childSites current operation
          (frame.append _) (operation.appendData frame data _) selectedSite
        ⟨.mk _ child.1, .mk child.2⟩
  termination_by structural recordedSites

  def argumentItemsEdit
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire))) :
      Σ source : ItemSeq sourceWires,
        Transform.ItemsEdit operation frame data source :=
    match recordedSites with
    | .nil _ => ⟨.nil, .nil⟩
    | .cons itemSites tailSites =>
        let item := argumentItemEdit itemSites current operation frame data
          selectedSite
        let tail := argumentItemsEdit tailSites current operation frame data
          selectedSite
        ⟨.cons item.1 tail.1, .cons item.2 tail.2⟩
  termination_by structural recordedSites

  def argumentItemEdit
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire))) :
      Σ source : Item sourceWires,
        Transform.ItemEdit operation frame data source :=
    match recordedSites with
    | .atom head ports => ⟨_, .atom head ports⟩
    | .selectedAtom _ siteData =>
        let application := current.map (fun wire =>
          EqualityNormalization.formalSubstitution siteData.2 wire)
        ⟨_, .selectedAtom application
          (selectedSite frame data siteData.2)⟩
    | .identity signature arity ports =>
        ⟨_, .identity signature arity ports⟩
    | .cut childSites =>
        let child := argumentRegionEdit childSites current operation frame data
          selectedSite
        ⟨.cut child.1, .cut child.2⟩
  termination_by structural recordedSites
end

mutual
  theorem argumentRegionEdit_selectedPaths
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (invariant : Transform.RetainedIndexInvariant frame) :
      (argumentRegionEdit recordedSites current operation frame data
        selectedSite).1.incidencePaths frame.selected.index.val =
        recordedSites.selectedPaths :=
    match recordedSites with
    | .mk childSites => by
        simpa [argumentRegionEdit, Region.incidencePaths,
          RegionSites.selectedPaths, Transform.Frame.append] using
          argumentItemsEdit_selectedPaths childSites current operation
            (frame.append _) _ _ (invariant.append _) 0
  termination_by structural recordedSites

  theorem argumentItemsEdit_selectedPaths
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (invariant : Transform.RetainedIndexInvariant frame)
      (itemIndex : Nat) :
      (argumentItemsEdit recordedSites current operation frame data
        selectedSite).1.incidencePaths frame.selected.index.val itemIndex =
        recordedSites.selectedPaths itemIndex :=
    match recordedSites with
    | .nil _ => rfl
    | .cons itemSites tailSites => by
        simp only [argumentItemsEdit, ItemSeq.incidencePaths,
          ItemsSites.selectedPaths]
        rw [argumentItemEdit_selectedPaths itemSites current operation frame
          data selectedSite invariant itemIndex,
          argumentItemsEdit_selectedPaths tailSites current operation frame
            data selectedSite invariant (itemIndex + 1)]
  termination_by structural recordedSites

  theorem argumentItemEdit_selectedPaths
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires targetWires : List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (operation : Transform.Operation currentArguments)
      (frame : Transform.Frame currentArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (invariant : Transform.RetainedIndexInvariant frame)
      (itemIndex : Nat) :
      (argumentItemEdit recordedSites current operation frame data
        selectedSite).1.incidencePaths frame.selected.index.val itemIndex =
        recordedSites.selectedPaths itemIndex :=
    match recordedSites with
    | .atom head ports => by
        have headNe := Ne.symm (invariant.selectedFresh head)
        have portsZero := Vars.countIndex_map_eq_zero_of_no_preimage ports
          frame.sourceKeep frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh wire))
        simp [argumentItemEdit, ItemSites.selectedPaths,
          Item.incidencePaths, headNe, portsZero]
    | .selectedAtom ports siteData => by
        have portsZero := Vars.countIndex_map_eq_zero_of_no_preimage current
          (WireRenaming.comp frame.sourceKeep
            (EqualityNormalization.formalSubstitution siteData.2))
          frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh
            (EqualityNormalization.formalSubstitution siteData.2 wire)))
        simp only [argumentItemEdit, ItemSites.selectedPaths,
          Item.incidencePaths]
        change Vars.countIndex frame.selected.index.val
          (current.map (fun wire => frame.sourceKeep
            (EqualityNormalization.formalSubstitution siteData.2 wire))) = 0
          at portsZero
        rw [Vars.map_map, portsZero]
        rfl
    | .identity signature arity ports => by
        have portsZero := countPorts_map_eq_zero_of_no_preimage arity ports
          frame.sourceKeep frame.selected.index.val
          (fun wire => Ne.symm (invariant.selectedFresh wire))
        simp [argumentItemEdit, ItemSites.selectedPaths,
          Item.incidencePaths, portsZero]
    | .cut childSites => by
        simp only [argumentItemEdit, Item.incidencePaths,
          ItemSites.selectedPaths]
        rw [argumentRegionEdit_selectedPaths childSites current operation
          frame data selectedSite invariant]
  termination_by structural recordedSites
end

mutual
  theorem argumentRegionEdit_source_independent
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires firstTargetWires secondTargetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (firstOperation : Transform.Operation currentArguments)
      (firstFrame : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (firstData : firstOperation.Data firstFrame)
      (firstSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : firstOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        firstOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (secondOperation : Transform.Operation currentArguments)
      (secondFrame : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (secondData : secondOperation.Data secondFrame)
      (secondSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : secondOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        secondOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (sourceKeepEq : ∀ {wireSignature} (wire : Var common wireSignature),
        firstFrame.sourceKeep wire = secondFrame.sourceKeep wire)
      (selectedEq : firstFrame.selected = secondFrame.selected) :
      (argumentRegionEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current firstOperation firstFrame
        firstData firstSelected).1 =
      (argumentRegionEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current secondOperation secondFrame
        secondData secondSelected).1 :=
    match recordedSites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals _ _ _ childSites =>
      by
        unfold argumentRegionEdit
        apply congrArg (Region.mk _)
        exact argumentItemsEdit_source_independent
          (recordedOperation := recordedOperation) (external := external)
          childSites current
          firstOperation (firstFrame.append _) _ _ secondOperation
          (secondFrame.append _) _ _ (by
            intro wireSignature wire
            apply Var.appendCases (left := common) (right := _)
              (motive := fun wire =>
                (firstFrame.append _).sourceKeep wire =
                  (secondFrame.append _).sourceKeep wire)
            · intro inheritedSignature inherited
              simpa [Transform.Frame.append, WireRenaming.appendRight] using
                congrArg
                  (fun wire : Var sourceWires inheritedSignature =>
                    wire.appendLeft locals)
                  (sourceKeepEq inherited)
            · intro localSignature localWire
              simp [Transform.Frame.append, WireRenaming.appendRight])
          (congrArg
            (fun wire : Var sourceWires (.rel currentArguments) =>
              wire.appendLeft locals)
            selectedEq)
  termination_by structural recordedSites

  theorem argumentItemsEdit_source_independent
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires firstTargetWires secondTargetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (firstOperation : Transform.Operation currentArguments)
      (firstFrame : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (firstData : firstOperation.Data firstFrame)
      (firstSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : firstOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        firstOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (secondOperation : Transform.Operation currentArguments)
      (secondFrame : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (secondData : secondOperation.Data secondFrame)
      (secondSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : secondOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        secondOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (sourceKeepEq : ∀ {wireSignature} (wire : Var common wireSignature),
        firstFrame.sourceKeep wire = secondFrame.sourceKeep wire)
      (selectedEq : firstFrame.selected = secondFrame.selected) :
      (argumentItemsEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current firstOperation firstFrame
        firstData firstSelected).1 =
      (argumentItemsEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current secondOperation secondFrame
        secondData secondSelected).1 :=
    match recordedSites with
    | .nil evidence => rfl
    | .cons itemSites tailSites =>
      by
        unfold argumentItemsEdit
        have itemEq := argumentItemEdit_source_independent
            (recordedOperation := recordedOperation) (external := external)
            itemSites current
            firstOperation firstFrame firstData firstSelected secondOperation
            secondFrame secondData secondSelected sourceKeepEq selectedEq
        have tailEq := argumentItemsEdit_source_independent
            (recordedOperation := recordedOperation) (external := external)
            tailSites current
            firstOperation firstFrame firstData firstSelected secondOperation
            secondFrame secondData secondSelected sourceKeepEq selectedEq
        change ItemSeq.cons
            (argumentItemEdit itemSites current firstOperation firstFrame
              firstData firstSelected).1
            (argumentItemsEdit tailSites current firstOperation firstFrame
              firstData firstSelected).1 =
          ItemSeq.cons
            (argumentItemEdit itemSites current secondOperation secondFrame
              secondData secondSelected).1
            (argumentItemsEdit tailSites current secondOperation secondFrame
              secondData secondSelected).1
        rw [itemEq, tailEq]
  termination_by structural recordedSites

  theorem argumentItemEdit_source_independent
      {recordedArguments external currentArguments common recordedSourceWires
        recordedTargetWires sourceWires firstTargetWires secondTargetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external currentArguments)
      (firstOperation : Transform.Operation currentArguments)
      (firstFrame : Transform.Frame currentArguments common sourceWires
        firstTargetWires)
      (firstData : firstOperation.Data firstFrame)
      (firstSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : firstOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        firstOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (secondOperation : Transform.Operation currentArguments)
      (secondFrame : Transform.Frame currentArguments common sourceWires
        secondTargetWires)
      (secondData : secondOperation.Data secondFrame)
      (secondSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame currentArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : secondOperation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        secondOperation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication
              wire)))
      (sourceKeepEq : ∀ {wireSignature} (wire : Var common wireSignature),
        firstFrame.sourceKeep wire = secondFrame.sourceKeep wire)
      (selectedEq : firstFrame.selected = secondFrame.selected) :
      (argumentItemEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current firstOperation firstFrame
        firstData firstSelected).1 =
      (argumentItemEdit (recordedOperation := recordedOperation)
        (external := external) recordedSites current secondOperation secondFrame
        secondData secondSelected).1 :=
    match recordedSites with
    | .atom head ports =>
      by
        unfold argumentItemEdit
        change Item.atom (firstFrame.sourceKeep head)
            (ports.map fun wire => firstFrame.sourceKeep wire) =
          Item.atom (secondFrame.sourceKeep head)
            (ports.map fun wire => secondFrame.sourceKeep wire)
        rw [sourceKeepEq head, Vars.map_congr ports _ _ sourceKeepEq]
    | .selectedAtom ports siteData =>
      by
        unfold argumentItemEdit
        change Item.atom firstFrame.selected
            ((current.map fun wire =>
              EqualityNormalization.formalSubstitution siteData.2 wire).map
                fun wire => firstFrame.sourceKeep wire) =
          Item.atom secondFrame.selected
            ((current.map fun wire =>
              EqualityNormalization.formalSubstitution siteData.2 wire).map
                fun wire => secondFrame.sourceKeep wire)
        rw [selectedEq]
        apply congrArg (Item.atom secondFrame.selected)
        apply Vars.map_congr
        exact sourceKeepEq
    | .identity signature arity ports =>
      by
        unfold argumentItemEdit
        change Item.identity signature arity
            (fun position => firstFrame.sourceKeep (ports position)) =
          Item.identity signature arity
            (fun position => secondFrame.sourceKeep (ports position))
        apply congrArg (Item.identity signature arity)
        funext position
        exact sourceKeepEq (ports position)
    | .cut childSites =>
      by
        unfold argumentItemEdit
        exact congrArg Item.cut
          (argumentRegionEdit_source_independent
            (recordedOperation := recordedOperation) (external := external)
            childSites current
            firstOperation firstFrame firstData firstSelected secondOperation
            secondFrame secondData secondSelected sourceKeepEq selectedEq)
  termination_by structural recordedSites
end

mutual
  theorem argumentRegionEdit_endpoint_eq
      {recordedArguments external sourceArguments targetArguments common
        recordedSourceWires recordedTargetWires sourceWires targetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Region recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : RegionSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external sourceArguments)
      (next : Vars external targetArguments)
      (operation : Transform.Operation sourceArguments)
      (frame : Transform.Frame sourceArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (targetSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires), operation.Data siteFrame →
          Var siteTargetWires (.rel targetArguments))
      (targetSelected_append : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame) (locals : List Sig),
        targetSelected (siteFrame.append locals)
            (operation.appendData siteFrame siteData locals) =
          (targetSelected siteFrame siteData).appendLeft locals)
      (siteEndpoint : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.site siteFrame siteData
            (current.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication wire))
            (selectedSite siteFrame siteData externalApplication) =
          Region.singleton (.atom (targetSelected siteFrame siteData)
            ((next.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication
                wire)).map fun wire => siteFrame.targetKeep wire))) :
      (argumentRegionEdit recordedSites current operation frame data
        selectedSite).2.run =
      retainedRegionPresentation (argumentRegionEdit recordedSites next
        (normalizationOperation targetArguments)
        ({ sourceKeep := frame.targetKeep
           targetKeep := frame.targetKeep
           selected := targetSelected frame data } :
          Transform.Frame targetArguments common targetWires targetWires)
        PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
    match recordedSites with
    | .mk childSites => by
        unfold argumentRegionEdit
        change Region.adjoinAt _ .nil
            (argumentItemsEdit childSites current operation
              (frame.append _) (operation.appendData frame data _)
              selectedSite).2.run =
          Region.adjoinAt _ .nil
            (retainedItemsPresentation
              (argumentItemsEdit childSites next
                (normalizationOperation targetArguments)
                ({ sourceKeep := (frame.append _).targetKeep
                   targetKeep := (frame.append _).targetKeep
                   selected := (targetSelected frame data).appendLeft _ } :
                  Transform.Frame targetArguments _ _ _)
                PUnit.unit (fun _ _ _ => PUnit.unit)).1)
        rw [← targetSelected_append frame data]
        exact congrArg (Region.adjoinAt _ .nil)
          (argumentItemsEdit_endpoint_eq childSites current next operation
            (frame.append _) (operation.appendData frame data _) selectedSite
            targetSelected targetSelected_append siteEndpoint)
  termination_by structural recordedSites

  theorem argumentItemsEdit_endpoint_eq
      {recordedArguments external sourceArguments targetArguments common
        recordedSourceWires recordedTargetWires sourceWires targetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : ItemSeq recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemsSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external sourceArguments)
      (next : Vars external targetArguments)
      (operation : Transform.Operation sourceArguments)
      (frame : Transform.Frame sourceArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (targetSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires), operation.Data siteFrame →
          Var siteTargetWires (.rel targetArguments))
      (targetSelected_append : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame) (locals : List Sig),
        targetSelected (siteFrame.append locals)
            (operation.appendData siteFrame siteData locals) =
          (targetSelected siteFrame siteData).appendLeft locals)
      (siteEndpoint : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.site siteFrame siteData
            (current.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication wire))
            (selectedSite siteFrame siteData externalApplication) =
          Region.singleton (.atom (targetSelected siteFrame siteData)
            ((next.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication
                wire)).map fun wire => siteFrame.targetKeep wire))) :
      (argumentItemsEdit recordedSites current operation frame data
        selectedSite).2.run =
      retainedItemsPresentation (argumentItemsEdit recordedSites next
        (normalizationOperation targetArguments)
        ({ sourceKeep := frame.targetKeep
           targetKeep := frame.targetKeep
           selected := targetSelected frame data } :
          Transform.Frame targetArguments common targetWires targetWires)
        PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
    match recordedSites with
    | .nil evidence => rfl
    | .cons itemSites tailSites => by
        unfold argumentItemsEdit
        change
          (argumentItemEdit itemSites current operation frame data
              selectedSite).2.run.conjoin
            (argumentItemsEdit tailSites current operation frame data
              selectedSite).2.run =
          retainedItemsPresentation (.cons
            (argumentItemEdit itemSites next
              (normalizationOperation targetArguments)
              ({ sourceKeep := frame.targetKeep
                 targetKeep := frame.targetKeep
                 selected := targetSelected frame data } :
                Transform.Frame targetArguments common targetWires targetWires)
              PUnit.unit (fun _ _ _ => PUnit.unit)).1
            (argumentItemsEdit tailSites next
              (normalizationOperation targetArguments)
              ({ sourceKeep := frame.targetKeep
                 targetKeep := frame.targetKeep
                 selected := targetSelected frame data } :
                Transform.Frame targetArguments common targetWires targetWires)
              PUnit.unit (fun _ _ _ => PUnit.unit)).1)
        rw [argumentItemEdit_endpoint_eq itemSites current next operation frame
          data selectedSite targetSelected targetSelected_append siteEndpoint]
        rw [argumentItemsEdit_endpoint_eq tailSites current next operation frame
          data selectedSite targetSelected targetSelected_append siteEndpoint]
        rfl
  termination_by structural recordedSites

  theorem argumentItemEdit_endpoint_eq
      {recordedArguments external sourceArguments targetArguments common
        recordedSourceWires recordedTargetWires sourceWires targetWires :
        List Sig}
      {recordedPattern : OpenDiagram recordedArguments}
      {recordedOperation : Transform.Operation recordedArguments}
      {recordedFrame : Transform.Frame recordedArguments common
        recordedSourceWires recordedTargetWires}
      {recordedData : recordedOperation.Data recordedFrame}
      {recordedSource : Item recordedSourceWires}
      {recordedResult : Region common}
      {recordedEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          recordedPattern recordedFrame.sourceKeep recordedFrame.selected
          recordedSource recordedResult}
      (recordedSites : ItemSites
        (recordingOperation recordedOperation external) recordedData
        recordedEvidence)
      (current : Vars external sourceArguments)
      (next : Vars external targetArguments)
      (operation : Transform.Operation sourceArguments)
      (frame : Transform.Frame sourceArguments common sourceWires targetWires)
      (data : operation.Data frame)
      (selectedSite : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.SiteData siteFrame siteData
          (current.map (fun wire =>
            EqualityNormalization.formalSubstitution externalApplication wire)))
      (targetSelected : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires), operation.Data siteFrame →
          Var siteTargetWires (.rel targetArguments))
      (targetSelected_append : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame) (locals : List Sig),
        targetSelected (siteFrame.append locals)
            (operation.appendData siteFrame siteData locals) =
          (targetSelected siteFrame siteData).appendLeft locals)
      (siteEndpoint : ∀
        {siteCommon siteSourceWires siteTargetWires : List Sig}
        (siteFrame : Transform.Frame sourceArguments siteCommon
          siteSourceWires siteTargetWires)
        (siteData : operation.Data siteFrame)
        (externalApplication : Vars siteCommon external),
        operation.site siteFrame siteData
            (current.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication wire))
            (selectedSite siteFrame siteData externalApplication) =
          Region.singleton (.atom (targetSelected siteFrame siteData)
            ((next.map (fun wire =>
              EqualityNormalization.formalSubstitution externalApplication
                wire)).map fun wire => siteFrame.targetKeep wire))) :
      (argumentItemEdit recordedSites current operation frame data
        selectedSite).2.run =
      retainedItemPresentation (argumentItemEdit recordedSites next
        (normalizationOperation targetArguments)
        ({ sourceKeep := frame.targetKeep
           targetKeep := frame.targetKeep
           selected := targetSelected frame data } :
          Transform.Frame targetArguments common targetWires targetWires)
        PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
    match recordedSites with
    | .atom head ports => rfl
    | .selectedAtom ports siteData => by
        unfold argumentItemEdit Transform.ItemEdit.run
        exact siteEndpoint frame data siteData.2
    | .identity signature arity ports => rfl
    | .cut childSites => by
        unfold argumentItemEdit Transform.ItemEdit.run
        exact congrArg (fun child => Region.singleton (.cut child))
          (argumentRegionEdit_endpoint_eq childSites current next operation
            frame data selectedSite targetSelected targetSelected_append
            siteEndpoint)
  termination_by structural recordedSites
end


/-- The computed Projection target is the canonical generated source for the
shorter tuple, up to the repository's standard retained presentation. -/
noncomputable def argumentProjectionEndpointIso
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (before ++ signature :: after)) :
    let frame := Argument.Projection.rootFrame outer localBefore localAfter
      before after signature
    let head := Argument.Projection.targetHead outer localBefore localAfter
      before after
    let generated := argumentItemsEdit recordedSites current
      (Argument.Projection.operation before after signature) frame head
      (fun _ _ _ => PUnit.unit)
    let follow := argumentItemsEdit recordedSites
      (Argument.Projection.Vars.dropAt before current)
      (normalizationOperation (before ++ after))
      ({ sourceKeep := frame.targetKeep
         targetKeep := frame.targetKeep
         selected := head } : Transform.Frame (before ++ after)
        (outer ++ (localBefore ++ localAfter))
        (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
        (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt
        (localBefore ++ .rel (before ++ after) :: localAfter) .nil
        generated.2.run)
      (.mk (localBefore ++ .rel (before ++ after) :: localAfter) follow.1) := by
  dsimp only
  let frame := Argument.Projection.rootFrame outer localBefore localAfter
    before after signature
  let head := Argument.Projection.targetHead outer localBefore localAfter
    before after
  let follow := argumentItemsEdit recordedSites
    (Argument.Projection.Vars.dropAt before current)
    (normalizationOperation (before ++ after))
    ({ sourceKeep := frame.targetKeep
       targetKeep := frame.targetKeep
       selected := head } : Transform.Frame (before ++ after)
      (outer ++ (localBefore ++ localAfter))
      (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
      (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter)))
    PUnit.unit (fun _ _ _ => PUnit.unit)
  let shorter : Region outer :=
    .mk (localBefore ++ .rel (before ++ after) :: localAfter) follow.1
  have endpointEq := argumentItemsEdit_endpoint_eq recordedSites current
    (Argument.Projection.Vars.dropAt before current)
    (Argument.Projection.operation before after signature) frame head
    (fun _ _ _ => PUnit.unit) (fun _ targetHead => targetHead)
    (by intro; intros; rfl) (by
      intro siteCommon siteSourceWires siteTargetWires siteFrame siteData
        externalApplication
      dsimp only [Argument.Projection.operation]
      rw [Argument.Projection.Vars.dropAt_map,
        Argument.Projection.Vars.dropAt_map])
  have presentationEq : Region.adjoinAt
      (localBefore ++ .rel (before ++ after) :: localAfter) .nil
      (argumentItemsEdit recordedSites current
        (Argument.Projection.operation before after signature) frame head
        (fun _ _ _ => PUnit.unit)).2.run =
      retainedRegionPresentation shorter := by
    change Region.adjoinAt _ .nil _ = Region.adjoinAt _ .nil
      (retainedItemsPresentation follow.1)
    exact congrArg (Region.adjoinAt _ .nil) endpointEq
  exact (RegionIso.ofEq presentationEq).trans
    (retainedRegionPresentationIso shorter)

/-- The computed Permutation target is the canonical generated source for the
shorter tuple, up to the repository's standard retained presentation. -/
noncomputable def argumentPermutationEndpointIso
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (signature :: before ++ after)) :
    let frame := ArgumentPermutation.rootFrame outer localBefore localAfter
      (signature :: before ++ after) (before ++ signature :: after)
    let head := ArgumentPermutation.targetHead outer localBefore localAfter
      (before ++ signature :: after)
    let generated := argumentItemsEdit recordedSites current
      (ArgumentPermutation.operation (signature :: before ++ after)
        (before ++ signature :: after)
        (ArgumentPermutation.Permutation.moveHead signature before after)) frame head
      (fun _ _ _ => PUnit.unit)
    let follow := argumentItemsEdit recordedSites
      ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars current)
      (normalizationOperation (before ++ signature :: after))
      ({ sourceKeep := frame.targetKeep
         targetKeep := frame.targetKeep
         selected := head } : Transform.Frame (before ++ signature :: after)
        (outer ++ (localBefore ++ localAfter))
        (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter))
        (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt
        (localBefore ++ .rel (before ++ signature :: after) :: localAfter) .nil
        generated.2.run)
      (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter) follow.1) := by
  dsimp only
  let frame := ArgumentPermutation.rootFrame outer localBefore localAfter
    (signature :: before ++ after) (before ++ signature :: after)
  let head := ArgumentPermutation.targetHead outer localBefore localAfter
    (before ++ signature :: after)
  let follow := argumentItemsEdit recordedSites
    ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars current)
    (normalizationOperation (before ++ signature :: after))
    ({ sourceKeep := frame.targetKeep
       targetKeep := frame.targetKeep
       selected := head } : Transform.Frame (before ++ signature :: after)
      (outer ++ (localBefore ++ localAfter))
      (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter))
      (outer ++ (localBefore ++ .rel (before ++ signature :: after) :: localAfter)))
    PUnit.unit (fun _ _ _ => PUnit.unit)
  let shorter : Region outer :=
    .mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter) follow.1
  have endpointEq := argumentItemsEdit_endpoint_eq recordedSites current
    ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars
      current)
    (ArgumentPermutation.operation (signature :: before ++ after)
      (before ++ signature :: after)
      (ArgumentPermutation.Permutation.moveHead signature before after))
    frame head (fun _ _ _ => PUnit.unit) (fun _ targetHead => targetHead)
    (by intro; intros; rfl) (by
      intro siteCommon siteSourceWires siteTargetWires siteFrame siteData
        externalApplication
      dsimp only [ArgumentPermutation.operation]
      rw [ArgumentPermutation.Permutation.moveHead_map,
        ArgumentPermutation.Permutation.moveHead_map])
  have presentationEq : Region.adjoinAt
      (localBefore ++ .rel (before ++ signature :: after) :: localAfter) .nil
      (argumentItemsEdit recordedSites current
        (ArgumentPermutation.operation (signature :: before ++ after)
          (before ++ signature :: after)
          (ArgumentPermutation.Permutation.moveHead signature before after)) frame head
        (fun _ _ _ => PUnit.unit)).2.run =
      retainedRegionPresentation shorter := by
    change Region.adjoinAt _ .nil _ = Region.adjoinAt _ .nil
      (retainedItemsPresentation follow.1)
    exact congrArg (Region.adjoinAt _ .nil) endpointEq
  exact (RegionIso.ofEq presentationEq).trans
    (retainedRegionPresentationIso shorter)


/-- The computed Duplicate target is the canonical generated source for the
duplicated tuple, up to the repository's standard retained presentation. -/
noncomputable def argumentDuplicateEndpointIso
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (before ++ signature :: after)) :
    let frame := Argument.Duplicate.rootFrame outer localBefore localAfter
      before after signature
    let head := Argument.Duplicate.targetHead outer localBefore localAfter
      before after signature
    let generated := argumentItemsEdit recordedSites current
      (Argument.Duplicate.operation before after signature) frame head
      (fun _ _ _ => PUnit.unit)
    let follow := argumentItemsEdit recordedSites
      (Argument.Duplicate.Vars.duplicateAt before current)
      (normalizationOperation (before ++ signature :: signature :: after))
      ({ sourceKeep := frame.targetKeep
         targetKeep := frame.targetKeep
         selected := head } : Transform.Frame
        (before ++ signature :: signature :: after)
        (outer ++ (localBefore ++ localAfter))
        (outer ++ (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter))
        (outer ++ (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
    RegionIso (WireEquiv.refl outer)
      (Region.adjoinAt
        (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter)
        .nil generated.2.run)
      (.mk (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter)
        follow.1) := by
  dsimp only
  let frame := Argument.Duplicate.rootFrame outer localBefore localAfter
    before after signature
  let head := Argument.Duplicate.targetHead outer localBefore localAfter before
    after signature
  let follow := argumentItemsEdit recordedSites
    (Argument.Duplicate.Vars.duplicateAt before current)
    (normalizationOperation (before ++ signature :: signature :: after))
    ({ sourceKeep := frame.targetKeep
       targetKeep := frame.targetKeep
       selected := head } : Transform.Frame
      (before ++ signature :: signature :: after)
      (outer ++ (localBefore ++ localAfter))
      (outer ++ (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter))
      (outer ++ (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter)))
    PUnit.unit (fun _ _ _ => PUnit.unit)
  let duplicated : Region outer :=
    .mk (localBefore ++
      .rel (before ++ signature :: signature :: after) :: localAfter)
      follow.1
  have endpointEq := argumentItemsEdit_endpoint_eq recordedSites current
    (Argument.Duplicate.Vars.duplicateAt before current)
    (Argument.Duplicate.operation before after signature) frame head
    (fun _ _ _ => PUnit.unit) (fun _ targetHead => targetHead)
    (by intro; intros; rfl) (by
      intro siteCommon siteSourceWires siteTargetWires siteFrame siteData
        externalApplication
      dsimp only [Argument.Duplicate.operation]
      rw [Argument.Duplicate.Vars.duplicateAt_map,
        Argument.Duplicate.Vars.duplicateAt_map])
  have presentationEq : Region.adjoinAt
      (localBefore ++
        .rel (before ++ signature :: signature :: after) :: localAfter)
      .nil
      (argumentItemsEdit recordedSites current
        (Argument.Duplicate.operation before after signature) frame head
        (fun _ _ _ => PUnit.unit)).2.run =
      retainedRegionPresentation duplicated := by
    change Region.adjoinAt _ .nil _ = Region.adjoinAt _ .nil
      (retainedItemsPresentation follow.1)
    exact congrArg (Region.adjoinAt _ .nil) endpointEq
  exact (RegionIso.ofEq presentationEq).trans
    (retainedRegionPresentationIso duplicated)


/-- One actual projection-extension CPS stage. The long-argument source and
its dropping edit are derived together from the single recorded traversal;
the directed local rule is then used in its extension orientation. -/
theorem argumentProjectionStage
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (next : Vars external (before ++ signature :: after))
    {instantiated pending : Region outer}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl outer) pending
      (.mk (localBefore ++
        .rel (before ++ signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites next
          (Argument.Projection.operation before after signature)
          (Argument.Projection.rootFrame outer localBefore localAfter before
            after signature)
          (Argument.Projection.targetHead outer localBefore localAfter before
            after)
          (fun _ _ _ => PUnit.unit)).1))
    (prepare : request.Preparation
      (.mk (localBefore ++ .rel (before ++ after) :: localAfter)
        (argumentItemsEdit recordedSites
          (Argument.Projection.Vars.dropAt before next)
          (normalizationOperation (before ++ after))
          ({
            sourceKeep :=
              (Argument.Projection.rootFrame outer localBefore localAfter
                before after signature).targetKeep
            targetKeep :=
              (Argument.Projection.rootFrame outer localBefore localAfter
                before after signature).targetKeep
            selected := Argument.Projection.targetHead outer localBefore
              localAfter before after
          } : Transform.Frame (before ++ after)
            (outer ++ (localBefore ++ localAfter))
            (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter))
            (outer ++ (localBefore ++ .rel (before ++ after) :: localAfter)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1)) :
    request.Result := by
  let generated := argumentItemsEdit recordedSites next
    (Argument.Projection.operation before after signature)
    (Argument.Projection.rootFrame outer localBefore localAfter before after
      signature)
    (Argument.Projection.targetHead outer localBefore localAfter before after)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Projection.Drops.Description outer := {
    before := before
    after := after
    localBefore := localBefore
    localAfter := localAfter
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  let prepare := prepare.rawIso
    (argumentProjectionEndpointIso recordedSites next).symm
  have localTargetCanonical : description.target.Canonical :=
    request.occurrence.context.holeCanonical description.target
      prepare.rawPreparedCanonical
  have localExtension :=
    description.target_source_extension localTargetCanonical
  have filledExtension := request.occurrence.context.extendCanonical
    description.target description.source prepare.rawPreparedCanonical
      localExtension.1 localExtension.2
  have rawPendingCanonical :
      (request.occurrence.context.fill description.source).Canonical :=
    filledExtension.1
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    intro wireSignature wire
    exact Nat.le_trans (prepare.rawPreparedExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExtension.2 wire).length_le _)
  let branch : request.Branch prepare.prepared := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := Argument.Projection.Local
    inject := fun step => Step.argumentProjection step
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := prepare.rawPreparedCanonical
    rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := prepare.preparedIso
    pendingIso := pendingIso
    localStep := .mk (.extend description)
    preparation := prepare.telescope
  }
  exact branch.compile

/-- One actual argument-permutation CPS stage, generated directly from the
recorded selected applications. -/
theorem argumentPermutationStage
    {recordedArguments external before after outer
      localBefore localAfter recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (signature :: before ++ after))
    {instantiated pending : Region outer}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl outer) pending
      (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites
          ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars
            current)
          (normalizationOperation (before ++ signature :: after))
          ({ sourceKeep :=
              (ArgumentPermutation.rootFrame outer localBefore localAfter
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             targetKeep :=
              (ArgumentPermutation.rootFrame outer localBefore localAfter
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             selected := ArgumentPermutation.targetHead outer localBefore
               localAfter (before ++ signature :: after) } :
            Transform.Frame (before ++ signature :: after)
              (outer ++ (localBefore ++ localAfter))
              (outer ++ (localBefore ++
                .rel (before ++ signature :: after) :: localAfter))
              (outer ++ (localBefore ++
                .rel (before ++ signature :: after) :: localAfter)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1))
    (prepare : request.Preparation
      (.mk (localBefore ++ .rel (signature :: before ++ after) :: localAfter)
        (argumentItemsEdit recordedSites current
          (ArgumentPermutation.operation (signature :: before ++ after)
            (before ++ signature :: after)
            (ArgumentPermutation.Permutation.moveHead signature before after))
          (ArgumentPermutation.rootFrame outer localBefore localAfter
            (signature :: before ++ after) (before ++ signature :: after))
          (ArgumentPermutation.targetHead outer localBefore localAfter
            (before ++ signature :: after))
          (fun _ _ _ => PUnit.unit)).1)) :
    request.Result := by
  let generated := argumentItemsEdit recordedSites current
    (ArgumentPermutation.operation (signature :: before ++ after)
      (before ++ signature :: after)
      (ArgumentPermutation.Permutation.moveHead signature before after))
    (ArgumentPermutation.rootFrame outer localBefore localAfter
      (signature :: before ++ after) (before ++ signature :: after))
    (ArgumentPermutation.targetHead outer localBefore localAfter
      (before ++ signature :: after))
    (fun _ _ _ => PUnit.unit)
  let description : ArgumentPermutation.Permutes.Description outer := {
    sourceArguments := signature :: before ++ after
    targetArguments := before ++ signature :: after
    before := localBefore
    after := localAfter
    permutation := ArgumentPermutation.Permutation.moveHead signature before after
    items := generated.1
    itemsEdit := generated.2
  }
  have preparedEq :
      (.mk (localBefore ++ .rel (signature :: before ++ after) :: localAfter)
        generated.1 :
        Region outer) = description.source := by
    rfl
  have localSourceCanonical : description.source.Canonical :=
    request.occurrence.context.holeCanonical description.source
      prepare.rawPreparedCanonical
  have localExtension :=
    ArgumentPermutation.moveHead_source_target_extension
      description.itemsEdit localSourceCanonical
  have filledExtension := request.occurrence.context.extendCanonical
    description.source description.target prepare.rawPreparedCanonical
      localExtension.1 localExtension.2
  have rawPendingCanonical :
      (request.occurrence.context.fill description.target).Canonical :=
    filledExtension.1
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.target) := by
    intro wireSignature wire
    exact Nat.le_trans (prepare.rawPreparedExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExtension.2 wire).length_le _)
  let branch : request.Branch prepare.prepared := {
    rawPrepared := description.source
    rawPending := description.target
    localRule := symmetric ArgumentPermutation.Local
    inject := fun step => Step.argumentPermutation step
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := prepare.rawPreparedCanonical
    rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := prepare.preparedIso
    pendingIso := pendingIso.trans
      (argumentPermutationEndpointIso recordedSites current).symm
    localStep := Or.inl (.permute (.mk description))
    preparation := prepare.telescope
  }
  exact branch.compile

/-- One actual reverse-duplicate contraction CPS stage, generated directly
from the recorded selected applications. -/
theorem argumentDuplicateContractStage
    {recordedArguments external before after outer localBefore localAfter
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments
      (outer ++ (localBefore ++ localAfter)) recordedSourceWires
      recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (outer ++ (localBefore ++ localAfter))}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (next : Vars external (before ++ signature :: after))
    {instantiated pending : Region outer}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl outer) pending
      (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites next
          (Argument.Duplicate.operation before after signature)
          (Argument.Duplicate.rootFrame outer localBefore localAfter before
            after signature)
          (Argument.Duplicate.targetHead outer localBefore localAfter before
            after signature)
          (fun _ _ _ => PUnit.unit)).1))
    (prepare : request.Preparation
      (.mk (localBefore ++
          .rel (before ++ signature :: signature :: after) :: localAfter)
        (argumentItemsEdit recordedSites
          (Argument.Duplicate.Vars.duplicateAt before next)
          (normalizationOperation
            (before ++ signature :: signature :: after))
          ({ sourceKeep :=
              (Argument.Duplicate.rootFrame outer localBefore localAfter
                before after signature).targetKeep
             targetKeep :=
              (Argument.Duplicate.rootFrame outer localBefore localAfter
                before after signature).targetKeep
             selected := Argument.Duplicate.targetHead outer localBefore
               localAfter before after signature } : Transform.Frame
            (before ++ signature :: signature :: after)
            (outer ++ (localBefore ++ localAfter))
            (outer ++ (localBefore ++
              .rel (before ++ signature :: signature :: after) :: localAfter))
            (outer ++ (localBefore ++
              .rel (before ++ signature :: signature :: after) :: localAfter)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1)) :
    request.Result := by
  let generated := argumentItemsEdit recordedSites next
    (Argument.Duplicate.operation before after signature)
    (Argument.Duplicate.rootFrame outer localBefore localAfter before after
      signature)
    (Argument.Duplicate.targetHead outer localBefore localAfter before after
      signature)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Duplicate.Duplicates.Description outer := {
    before := before
    after := after
    localBefore := localBefore
    localAfter := localAfter
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  let prepare := prepare.rawIso
    (argumentDuplicateEndpointIso recordedSites next).symm
  have rawPendingCanonical :
      (request.occurrence.context.fill description.source).Canonical := by
    let exactPendingIso := pendingIso.trans
      (RegionIso.ofEq (show
        (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
          generated.1 : Region outer) = description.source from rfl))
    exact (DiagramContext.fillIso request.occurrence.context exactPendingIso)
      |>.canonical_iff.mp request.pendingCanonical
  have rawPendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    let exactPendingIso := pendingIso.trans
      (RegionIso.ofEq (show
        (.mk (localBefore ++ .rel (before ++ signature :: after) :: localAfter)
          generated.1 : Region outer) = description.source from rfl))
    let filledIso := DiagramContext.fillIso request.occurrence.context
      exactPendingIso
    let pendingEndpoint := request.occurrence.interface.withBody
      (request.occurrence.context.fill pending) request.pendingCanonical
        request.pendingExternalTwoEnded
    apply pendingEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · change (request.occurrence.context.fill pending).incidencePaths
          wire.index.val ≠ [] at nonempty
      rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
    · change (request.occurrence.context.fill pending).incidencePaths
          wire.index.val ≠ []
      rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
  have localSourceCanonical : description.source.Canonical :=
    request.occurrence.context.holeCanonical description.source
      rawPendingCanonical
  have localExpansion :=
    description.source_target_extension localSourceCanonical
  have filledExpansion := request.occurrence.context.extendCanonical
    description.source description.target rawPendingCanonical
      localExpansion.1 localExpansion.2
  have derivedRawPreparedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.target) := by
    intro wireSignature wire
    exact Nat.le_trans (rawPendingExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExpansion.2 wire).length_le _)
  let branch : request.Branch prepare.prepared := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := symmetric Argument.Duplicate.Local
    inject := fun step => Step.argumentDuplicate step
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := filledExpansion.1
    rawPreparedExternalTwoEnded := derivedRawPreparedExternalTwoEnded
    rawPendingCanonical := rawPendingCanonical
    rawPendingExternalTwoEnded := rawPendingExternalTwoEnded
    preparedIso := prepare.preparedIso
    pendingIso := pendingIso
    localStep := Or.inr (.duplicate (.mk description))
    preparation := prepare.telescope
  }
  exact branch.compile

/-- Normalized generated regions are structurally identical after one generic
argument-index equality and the corresponding heterogeneous tuple equality. -/
noncomputable def argumentNormalizationPresentation
    {recordedArguments external firstArguments secondArguments common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (firstValues : Vars external firstArguments)
    (secondValues : Vars external secondArguments)
    (argumentsEq : firstArguments = secondArguments)
    (valuesEq : HEq firstValues secondValues) :
    RegionIso (WireEquiv.refl common)
      (.mk (.rel firstArguments :: retained)
        (argumentItemsEdit recordedSites firstValues
          (normalizationOperation firstArguments)
          ({ sourceKeep := Transform.Frame.keep common []
              [.rel firstArguments] retained
             targetKeep := Transform.Frame.keep common []
              [.rel firstArguments] retained
             selected := Transform.Frame.insertedHead common [] retained
              (.rel firstArguments) } : Transform.Frame firstArguments
            (common ++ retained)
            (common ++ (.rel firstArguments :: retained))
            (common ++ (.rel firstArguments :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1)
      (.mk (.rel secondArguments :: retained)
        (argumentItemsEdit recordedSites secondValues
          (normalizationOperation secondArguments)
          ({ sourceKeep := Transform.Frame.keep common []
              [.rel secondArguments] retained
             targetKeep := Transform.Frame.keep common []
              [.rel secondArguments] retained
             selected := Transform.Frame.insertedHead common [] retained
              (.rel secondArguments) } : Transform.Frame secondArguments
            (common ++ retained)
            (common ++ (.rel secondArguments :: retained))
            (common ++ (.rel secondArguments :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
  subst secondArguments
  cases valuesEq
  exact RegionIso.refl _

/-- The authoritative all-sites region generated by a normalized argument
tuple. Every argument stage consumes this exact representation. -/
def argumentNormalizedRegion
    {recordedArguments external arguments common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (values : Vars external arguments) : Region common :=
  .mk (.rel arguments :: retained)
    (argumentItemsEdit recordedSites values
      (normalizationOperation arguments)
      ({ sourceKeep := Transform.Frame.keep common [] [.rel arguments] retained
         targetKeep := Transform.Frame.keep common [] [.rel arguments] retained
         selected := Transform.Frame.insertedHead common [] retained
           (.rel arguments) } : Transform.Frame arguments (common ++ retained)
        (common ++ (.rel arguments :: retained))
        (common ++ (.rel arguments :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)).1

/-- One normalized Projection CPS phase. The only mismatch is the dependent
`arguments ++ [] = arguments` presentation, discharged once here. -/
theorem argumentProjectionNormalized
    {recordedArguments external arguments common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external arguments) (inserted : Var external signature)
    {instantiated pending : Region common}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites
        (Theory.Vars.extend current (.cons inserted .nil))))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current)) :
    request.Result := by
  let next := Theory.Vars.extend current (.cons inserted .nil)
  have droppedEq : HEq
      (Argument.Projection.Vars.dropAt arguments next) current :=
    Argument.Projection.Vars.dropAt_extend_singleton current inserted
  let presentation := argumentNormalizationPresentation recordedSites current
    (Argument.Projection.Vars.dropAt arguments next)
    (List.append_nil arguments).symm droppedEq.symm
  let rawPending : Region common :=
    .mk ([] ++ .rel (arguments ++ signature :: []) :: retained)
      (argumentItemsEdit recordedSites next
        (Argument.Projection.operation arguments [] signature)
        (Argument.Projection.rootFrame common [] retained arguments []
          signature)
        (Argument.Projection.targetHead common [] retained arguments [])
        (fun _ _ _ => PUnit.unit)).1
  have pendingEq : argumentNormalizedRegion recordedSites next = rawPending := by
    dsimp only [argumentNormalizedRegion, rawPending]
    apply congrArg (Region.mk (.rel (arguments ++ signature :: []) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (normalizationOperation (arguments ++ signature :: []))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (arguments ++ signature :: [])) } : Transform.Frame
        (arguments ++ signature :: []) (common ++ retained)
        (common ++ (.rel (arguments ++ signature :: []) :: retained))
        (common ++ (.rel (arguments ++ signature :: []) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Projection.operation arguments [] signature)
      (Argument.Projection.rootFrame common [] retained arguments [] signature)
      (Argument.Projection.targetHead common [] retained arguments [])
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Projection.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Projection.rootFrame, Transform.Frame.replace])
  have stagedPrepare : request.Preparation
      (.mk ([] ++ .rel (arguments ++ []) :: retained)
        (argumentItemsEdit recordedSites
          (Argument.Projection.Vars.dropAt arguments next)
          (normalizationOperation (arguments ++ []))
          ({ sourceKeep :=
              (Argument.Projection.rootFrame common [] retained arguments []
                signature).targetKeep
             targetKeep :=
              (Argument.Projection.rootFrame common [] retained arguments []
                signature).targetKeep
             selected := Argument.Projection.targetHead common [] retained
               arguments [] } : Transform.Frame (arguments ++ [])
            (common ++ ([] ++ retained))
            (common ++ ([] ++ .rel (arguments ++ []) :: retained))
            (common ++ ([] ++ .rel (arguments ++ []) :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
    simpa only [argumentNormalizedRegion, Argument.Projection.rootFrame,
      Transform.Frame.replace] using prepare.rawIso presentation
  exact argumentProjectionStage (before := arguments) (after := [])
    (outer := common) (localBefore := []) (localAfter := retained)
      (instantiated := instantiated) recordedSites next
      (request := request) (pendingIso.trans (RegionIso.ofEq pendingEq))
      stagedPrepare

/-- Prepending one recorded argument preserves occurrence validity because it
is exactly Projection's extension direction. -/
theorem argumentPrependValidity
    {recordedArguments external arguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (inserted : Var external signature) (current : Vars external arguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (currentCanonical : (context.fill
      (argumentNormalizedRegion recordedSites current)).Canonical)
    (currentExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill
        (argumentNormalizedRegion recordedSites current))) :
    (context.fill (argumentNormalizedRegion recordedSites
      (.cons inserted current))).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill (argumentNormalizedRegion recordedSites
          (.cons inserted current))) := by
  let next : Vars external ([] ++ signature :: arguments) :=
    .cons inserted current
  let generated := argumentItemsEdit recordedSites next
    (Argument.Projection.operation [] arguments signature)
    (Argument.Projection.rootFrame common [] retained [] arguments signature)
    (Argument.Projection.targetHead common [] retained [] arguments)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Projection.Drops.Description common := {
    before := []
    after := arguments
    localBefore := []
    localAfter := retained
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  have sourceEq : argumentNormalizedRegion recordedSites
      (.cons inserted current) = description.source := by
    dsimp only [argumentNormalizedRegion, description, generated, next]
    apply congrArg (Region.mk (.rel (signature :: arguments) :: retained))
    exact argumentItemsEdit_source_independent recordedSites
      (.cons inserted current) (normalizationOperation (signature :: arguments))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (signature :: arguments)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (signature :: arguments)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (signature :: arguments)) } : Transform.Frame
        (signature :: arguments) (common ++ retained)
        (common ++ (.rel (signature :: arguments) :: retained))
        (common ++ (.rel (signature :: arguments) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Projection.operation [] arguments signature)
      (Argument.Projection.rootFrame common [] retained [] arguments signature)
      (Argument.Projection.targetHead common [] retained [] arguments)
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Projection.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Projection.rootFrame, Transform.Frame.replace])
  let targetIso : RegionIso (WireEquiv.refl common) description.target
      (argumentNormalizedRegion recordedSites current) := by
    simpa only [description, generated, next, argumentNormalizedRegion] using
      argumentProjectionEndpointIso (outer := common) (localBefore := [])
        (localAfter := retained) (before := []) (after := arguments)
        recordedSites next
  let filledTargetIso := DiagramContext.fillIso context targetIso
  have filledTargetCanonical : (context.fill description.target).Canonical :=
    filledTargetIso.canonical_iff.mpr currentCanonical
  have filledTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill description.target) := by
    let currentEndpoint := interface.withBody
      (context.fill (argumentNormalizedRegion recordedSites current))
      currentCanonical currentExternalTwoEnded
    apply currentEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledTargetIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
  have localTargetCanonical : description.target.Canonical :=
    context.holeCanonical description.target filledTargetCanonical
  have localExtension := description.target_source_extension localTargetCanonical
  have filledExtension := context.extendCanonical description.target
    description.source filledTargetCanonical localExtension.1 localExtension.2
  have filledSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill description.source) := by
    intro wireSignature wire
    exact Nat.le_trans (filledTargetExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExtension.2 wire).length_le _)
  rw [sourceEq]
  exact ⟨filledExtension.1, filledSourceExternalTwoEnded⟩

/-- Adding a whole tuple in front of the canonical external tuple preserves
validity, by repeated Projection extension. -/
theorem argumentExtendedValidity
    {recordedArguments external arguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (added : Vars external arguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (finalCanonical : (context.fill
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (finalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill
        (argumentNormalizedRegion recordedSites
          (EqualityNormalization.formalPorts external)))) :
    (context.fill (argumentNormalizedRegion recordedSites
      (Theory.Vars.extend added
        (EqualityNormalization.formalPorts external)))).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill (argumentNormalizedRegion recordedSites
          (Theory.Vars.extend added
            (EqualityNormalization.formalPorts external)))) := by
  induction added with
  | nil => exact ⟨finalCanonical, finalExternalTwoEnded⟩
  | @cons signature rest head tail induction =>
      exact argumentPrependValidity recordedSites head
        (Theory.Vars.extend tail
          (EqualityNormalization.formalPorts external)) interface context
        induction.1 induction.2

/-- Move the current tuple head behind `before`, preserving the authoritative
normalized representation on both sides of the permutation step. -/
theorem argumentPermutationNormalized
    {recordedArguments external before after common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external (signature :: before ++ after))
    {instantiated : Region common}
    (request : Telescope.Request instantiated
      (argumentNormalizedRegion recordedSites
        ((ArgumentPermutation.Permutation.moveHead signature before after).mapVars
          current)))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current)) :
    request.Result := by
  let moved :=
    (ArgumentPermutation.Permutation.moveHead signature before after).mapVars
      current
  let rawPrepared : Region common :=
    .mk (.rel (signature :: before ++ after) :: retained)
      (argumentItemsEdit recordedSites current
        (ArgumentPermutation.operation (signature :: before ++ after)
          (before ++ signature :: after)
          (ArgumentPermutation.Permutation.moveHead signature before after))
        (ArgumentPermutation.rootFrame common [] retained
          (signature :: before ++ after) (before ++ signature :: after))
        (ArgumentPermutation.targetHead common [] retained
          (before ++ signature :: after))
        (fun _ _ _ => PUnit.unit)).1
  have preparedEq : argumentNormalizedRegion recordedSites current =
      rawPrepared := by
    dsimp only [argumentNormalizedRegion, rawPrepared]
    apply congrArg (Region.mk (.rel (signature :: before ++ after) :: retained))
    exact argumentItemsEdit_source_independent recordedSites current
      (normalizationOperation (signature :: before ++ after))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (signature :: before ++ after)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (signature :: before ++ after)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (signature :: before ++ after)) } : Transform.Frame
        (signature :: before ++ after) (common ++ retained)
        (common ++ (.rel (signature :: before ++ after) :: retained))
        (common ++ (.rel (signature :: before ++ after) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (ArgumentPermutation.operation (signature :: before ++ after)
        (before ++ signature :: after)
        (ArgumentPermutation.Permutation.moveHead signature before after))
      (ArgumentPermutation.rootFrame common [] retained
        (signature :: before ++ after) (before ++ signature :: after))
      (ArgumentPermutation.targetHead common [] retained
        (before ++ signature :: after))
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [ArgumentPermutation.rootFrame, Transform.Frame.replace]) (by
          simp [ArgumentPermutation.rootFrame, Transform.Frame.replace])
  have pendingEq : argumentNormalizedRegion recordedSites moved =
      (.mk ([] ++ .rel (before ++ signature :: after) :: retained)
        (argumentItemsEdit recordedSites moved
          (normalizationOperation (before ++ signature :: after))
          ({ sourceKeep :=
              (ArgumentPermutation.rootFrame common [] retained
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             targetKeep :=
              (ArgumentPermutation.rootFrame common [] retained
                (signature :: before ++ after)
                (before ++ signature :: after)).targetKeep
             selected := ArgumentPermutation.targetHead common [] retained
               (before ++ signature :: after) } : Transform.Frame
            (before ++ signature :: after) (common ++ ([] ++ retained))
            (common ++ ([] ++ .rel (before ++ signature :: after) :: retained))
            (common ++ ([] ++ .rel (before ++ signature :: after) :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
    rfl
  exact argumentPermutationStage (outer := common) (localBefore := [])
    (localAfter := retained) (instantiated := instantiated) recordedSites current
    (request := request) (RegionIso.ofEq pendingEq)
    (prepare.rawIso (RegionIso.ofEq preparedEq))

/-- Contract one adjacent duplicated argument while preserving normalized
all-sites regions as the authoritative continuation endpoints. -/
theorem argumentDuplicateNormalized
    {recordedArguments external before after common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (next : Vars external (before ++ signature :: after))
    {instantiated pending : Region common}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites next))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites
        (Argument.Duplicate.Vars.duplicateAt before next))) :
    request.Result := by
  let duplicated := Argument.Duplicate.Vars.duplicateAt before next
  let rawPending : Region common :=
    .mk (.rel (before ++ signature :: after) :: retained)
      (argumentItemsEdit recordedSites next
        (Argument.Duplicate.operation before after signature)
        (Argument.Duplicate.rootFrame common [] retained before after signature)
        (Argument.Duplicate.targetHead common [] retained before after signature)
        (fun _ _ _ => PUnit.unit)).1
  have pendingEq : argumentNormalizedRegion recordedSites next = rawPending := by
    dsimp only [argumentNormalizedRegion, rawPending]
    apply congrArg (Region.mk (.rel (before ++ signature :: after) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (normalizationOperation (before ++ signature :: after))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (before ++ signature :: after)) } : Transform.Frame
        (before ++ signature :: after) (common ++ retained)
        (common ++ (.rel (before ++ signature :: after) :: retained))
        (common ++ (.rel (before ++ signature :: after) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Duplicate.operation before after signature)
      (Argument.Duplicate.rootFrame common [] retained before after signature)
      (Argument.Duplicate.targetHead common [] retained before after signature)
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Duplicate.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Duplicate.rootFrame, Transform.Frame.replace])
  have preparedEq : argumentNormalizedRegion recordedSites duplicated =
      (.mk ([] ++ .rel (before ++ signature :: signature :: after) :: retained)
        (argumentItemsEdit recordedSites duplicated
          (normalizationOperation (before ++ signature :: signature :: after))
          ({ sourceKeep :=
              (Argument.Duplicate.rootFrame common [] retained before after
                signature).targetKeep
             targetKeep :=
              (Argument.Duplicate.rootFrame common [] retained before after
                signature).targetKeep
             selected := Argument.Duplicate.targetHead common [] retained
               before after signature } : Transform.Frame
            (before ++ signature :: signature :: after)
            (common ++ ([] ++ retained))
            (common ++ ([] ++
              .rel (before ++ signature :: signature :: after) :: retained))
            (common ++ ([] ++
              .rel (before ++ signature :: signature :: after) :: retained)))
          PUnit.unit (fun _ _ _ => PUnit.unit)).1) := by
    rfl
  exact argumentDuplicateContractStage (outer := common) (localBefore := [])
    (localAfter := retained) (instantiated := instantiated) recordedSites next
    (request := request) (pendingIso.trans (RegionIso.ofEq pendingEq))
    (prepare.rawIso (RegionIso.ofEq preparedEq))

/-- Eliminate an intrinsic wire position into the unique list prefix and
suffix surrounding its signature.  The witness lives only in `Prop`; the
argument telescope consumes it immediately and does not expose a position
certificate as data. -/
theorem intrinsicVar_position
    (wire : Var external signature) :
    ∃ before after, external = before ++ signature :: after ∧
      HEq wire (Var.appendRight before
        (.here : Var (signature :: after) signature)) := by
  induction wire with
  | @here signature after =>
      exact ⟨[], after, rfl, HEq.rfl⟩
  | there wire induction =>
      obtain ⟨before, after, contextEq, wireEq⟩ := induction
      cases contextEq
      cases wireEq
      refine ⟨_ :: before, after, rfl, ?_⟩
      exact heq_of_eq rfl

/-- One argument occurrence is moved next to its canonical external copy and
contracted.  Both primitives are packaged here so the intrinsic-position
eliminator has no caller-visible intermediate endpoint. -/
theorem argumentMoveDuplicateNormalized
    {recordedArguments external before after common retained
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external
      (signature :: before ++ signature :: after))
    (next : Vars external (before ++ signature :: after))
    (movedEq :
      (ArgumentPermutation.Permutation.moveHead signature before
        (signature :: after)).mapVars
          current =
        Argument.Duplicate.Vars.duplicateAt before next)
    {instantiated pending : Region common}
    (request : Telescope.Request instantiated pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites next))
    (prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current)) :
    request.Result := by
  let duplicated := Argument.Duplicate.Vars.duplicateAt before next
  let moved :=
    (ArgumentPermutation.Permutation.moveHead signature before
      (signature :: after)).mapVars
      current
  have movedRegionEq : argumentNormalizedRegion recordedSites moved =
      argumentNormalizedRegion recordedSites duplicated := by
    exact congrArg (argumentNormalizedRegion recordedSites) movedEq
  let generated := argumentItemsEdit recordedSites next
    (Argument.Duplicate.operation before after signature)
    (Argument.Duplicate.rootFrame common [] retained before after signature)
    (Argument.Duplicate.targetHead common [] retained before after signature)
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Duplicate.Duplicates.Description common := {
    before := before
    after := after
    localBefore := []
    localAfter := retained
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  have sourceEq : description.source =
      argumentNormalizedRegion recordedSites next := by
    dsimp only [description, generated, argumentNormalizedRegion]
    apply congrArg (Region.mk (.rel (before ++ signature :: after) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (Argument.Duplicate.operation before after signature)
      (Argument.Duplicate.rootFrame common [] retained before after signature)
      (Argument.Duplicate.targetHead common [] retained before after signature)
      (fun _ _ _ => PUnit.unit)
      (normalizationOperation (before ++ signature :: after))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (before ++ signature :: after)] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (before ++ signature :: after)) } : Transform.Frame
        (before ++ signature :: after) (common ++ retained)
        (common ++ (.rel (before ++ signature :: after) :: retained))
        (common ++ (.rel (before ++ signature :: after) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Duplicate.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Duplicate.rootFrame, Transform.Frame.replace])
  let sourceIso : RegionIso (WireEquiv.refl common) description.source
      (argumentNormalizedRegion recordedSites next) := RegionIso.ofEq sourceEq
  let exactSourceIso := sourceIso.trans pendingIso.symm
  let filledSourceIso := DiagramContext.fillIso request.occurrence.context
    exactSourceIso
  have filledSourceCanonical :
      (request.occurrence.context.fill description.source).Canonical :=
    filledSourceIso.canonical_iff.mpr request.pendingCanonical
  have filledSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.source) := by
    let pendingEndpoint := request.occurrence.interface.withBody
      (request.occurrence.context.fill pending)
      request.pendingCanonical request.pendingExternalTwoEnded
    apply pendingEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledSourceIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
  have localSourceCanonical : description.source.Canonical :=
    request.occurrence.context.holeCanonical description.source
      filledSourceCanonical
  have localExpansion := description.source_target_extension
    localSourceCanonical
  have filledExpansion := request.occurrence.context.extendCanonical
    description.source description.target filledSourceCanonical
      localExpansion.1 localExpansion.2
  have filledTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill description.target) := by
    intro wireSignature wire
    exact Nat.le_trans (filledSourceExternalTwoEnded wire)
      (Nat.add_le_add_left (filledExpansion.2 wire).length_le _)
  have targetIso : RegionIso (WireEquiv.refl common) description.target
      (argumentNormalizedRegion recordedSites duplicated) := by
    simpa only [description, generated, argumentNormalizedRegion] using
      argumentDuplicateEndpointIso (outer := common) (localBefore := [])
        (localAfter := retained) recordedSites next
  let filledTargetIso := DiagramContext.fillIso request.occurrence.context
    targetIso
  have duplicatedCanonical : (request.occurrence.context.fill
      (argumentNormalizedRegion recordedSites duplicated)).Canonical :=
    filledTargetIso.canonical_iff.mp filledExpansion.1
  have duplicatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill
        (argumentNormalizedRegion recordedSites duplicated)) := by
    let targetEndpoint := request.occurrence.interface.withBody
      (request.occurrence.context.fill description.target) filledExpansion.1
      filledTargetExternalTwoEnded
    apply targetEndpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledTargetIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
  have movedCanonical : (request.occurrence.context.fill
      (argumentNormalizedRegion recordedSites moved)).Canonical := by
    rw [movedRegionEq]
    exact duplicatedCanonical
  have movedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill
        (argumentNormalizedRegion recordedSites moved)) := by
    rw [movedRegionEq]
    exact duplicatedExternalTwoEnded
  let stageInterface : OpenDiagram request.boundary :=
    request.occurrence.interface
  let stageContext : DiagramContext stageInterface.external common :=
    request.occurrence.context
  have duplicateSourceCanonical :
      (stageContext.fill (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated)
        request.endpoint)).Canonical := by
    exact match request.polarity with
      | .positive => by
          simpa only [stageContext] using duplicatedCanonical
      | .negative => by
          simpa only [stageContext] using request.endpointCanonical
  have duplicateSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      stageInterface.boundaryWire
      (stageContext.fill (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated)
        request.endpoint)) := by
    exact match request.polarity with
      | .positive => by
          simpa only [stageInterface, stageContext] using
            duplicatedExternalTwoEnded
      | .negative => by
          simpa only [stageInterface, stageContext] using
            request.endpointExternalTwoEnded
  let duplicateRequest : Telescope.Request
      (argumentNormalizedRegion recordedSites duplicated)
      pending := {
    boundary := request.boundary
    source := stageInterface.withBody
      (stageContext.fill (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated) request.endpoint))
      duplicateSourceCanonical duplicateSourceExternalTwoEnded
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := exactOccurrence stageInterface
      stageContext (polaritySource request.polarity
        (argumentNormalizedRegion recordedSites duplicated) request.endpoint)
      duplicateSourceCanonical duplicateSourceExternalTwoEnded
    instantiatedCanonical := duplicatedCanonical
    instantiatedExternalTwoEnded := duplicatedExternalTwoEnded
    pendingCanonical := request.pendingCanonical
    pendingExternalTwoEnded := request.pendingExternalTwoEnded
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := request.continuation
  }
  let duplicatePreparation : duplicateRequest.Preparation
      (argumentNormalizedRegion recordedSites duplicated) := {
    prepared := argumentNormalizedRegion recordedSites duplicated
    preparedCanonical := duplicatedCanonical
    preparedExternalTwoEnded := duplicatedExternalTwoEnded
    rawPreparedCanonical := duplicatedCanonical
    rawPreparedExternalTwoEnded := duplicatedExternalTwoEnded
    preparedIso := RegionIso.refl _
    telescope := Telescope.refl request.polarity request.occurrence.interface
      request.occurrence.context duplicatedCanonical
      duplicatedExternalTwoEnded request.continuation.1
  }
  have duplicateCompiled := argumentDuplicateNormalized recordedSites next
    duplicateRequest pendingIso duplicatePreparation
  have duplicateTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      (argumentNormalizedRegion recordedSites moved) request.endpoint
      movedCanonical movedExternalTwoEnded request.endpointCanonical
      request.endpointExternalTwoEnded := by
    simpa only [movedRegionEq] using
      Telescope.Compiles.toTelescope request.polarity
      request.occurrence.interface request.occurrence.context
      duplicatedCanonical duplicatedExternalTwoEnded request.endpointCanonical
      request.endpointExternalTwoEnded request.continuation.1
      duplicateCompiled
  let permutationRequest : Telescope.Request instantiated
      (argumentNormalizedRegion recordedSites moved) := {
    boundary := request.boundary
    source := request.source
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := request.occurrence
    instantiatedCanonical := request.instantiatedCanonical
    instantiatedExternalTwoEnded := request.instantiatedExternalTwoEnded
    pendingCanonical := movedCanonical
    pendingExternalTwoEnded := movedExternalTwoEnded
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := duplicateTelescope
  }
  let permutationPreparation : permutationRequest.Preparation
      (argumentNormalizedRegion recordedSites current) := {
    prepared := prepare.prepared
    preparedCanonical := prepare.preparedCanonical
    preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
    rawPreparedCanonical := prepare.rawPreparedCanonical
    rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
    preparedIso := prepare.preparedIso
    telescope := prepare.telescope
  }
  exact argumentPermutationNormalized recordedSites current permutationRequest
    permutationPreparation

/-- Contract every leading actual argument against its canonical occurrence
in the external tuple.  The recursion is on the existing intrinsic `Vars`
value; each head position is eliminated in `Prop` and immediately consumed by
the combined move/duplicate phase. -/
theorem argumentVarsContractTelescope
    {recordedArguments external addedArguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (added : Vars external addedArguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    {endpoint : Region common}
    (finalCanonical : (context.fill (argumentNormalizedRegion recordedSites
      (EqualityNormalization.formalPorts external))).Canonical)
    (finalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill (argumentNormalizedRegion
        recordedSites (EqualityNormalization.formalPorts external))))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint))
    (polarity : Polarity) (polarityEq : context.polarity = polarity)
    (continuation : Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)) endpoint
      finalCanonical finalExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded) :
    Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (Theory.Vars.extend added
          (EqualityNormalization.formalPorts external))) endpoint
      (argumentExtendedValidity recordedSites added interface context
        finalCanonical finalExternalTwoEnded).1
      (argumentExtendedValidity recordedSites added interface context
        finalCanonical finalExternalTwoEnded).2
      endpointCanonical endpointExternalTwoEnded := by
  induction added with
  | nil => exact continuation
  | @cons signature restArguments head tail induction =>
      let next := Theory.Vars.extend tail
        (EqualityNormalization.formalPorts external)
      let current := Theory.Vars.cons head next
      have nextValidity := argumentExtendedValidity recordedSites tail
        interface context finalCanonical finalExternalTwoEnded
      have currentValidity := argumentExtendedValidity recordedSites
        (.cons head tail) interface context finalCanonical
        finalExternalTwoEnded
      have tailTelescope := induction
      obtain ⟨before, after, externalEq, headEq⟩ := intrinsicVar_position head
      cases externalEq
      cases headEq
      let prefixValues : Vars (before ++ signature :: after) before :=
        (EqualityNormalization.formalPorts before).map fun wire =>
          wire.appendLeft (signature :: after)
      let suffixValues : Vars (before ++ signature :: after) after :=
        (EqualityNormalization.formalPorts after).map fun wire =>
          Var.appendRight before (.there wire)
      let selected : Var (before ++ signature :: after) signature :=
        Var.appendRight before (.here : Var (signature :: after) signature)
      have formalEq : EqualityNormalization.formalPorts
          (before ++ signature :: after) =
          Theory.Vars.extend prefixValues (.cons selected suffixValues) := by
        rw [EqualityNormalization.formalPorts_append before
          (signature :: after)]
        dsimp only [prefixValues, selected, suffixValues]
        apply congrArg (Theory.Vars.extend
          ((EqualityNormalization.formalPorts before).map fun wire =>
            wire.appendLeft (signature :: after)))
        simp only [EqualityNormalization.formalPorts,
          Erasure.Exposure.identityBoundary, Theory.Vars.map,
          Theory.Vars.extend]
        apply congrArg (Theory.Vars.cons
          (Var.appendRight before
            (.here : Var (signature :: after) signature)))
        rw [Theory.Vars.map_map]
      let stageBeforeValues := Theory.Vars.extend tail prefixValues
      let stageNext := Theory.Vars.extend stageBeforeValues
        (Theory.Vars.cons selected suffixValues)
      let stageCurrent := Theory.Vars.cons selected
        (Theory.Vars.extend stageBeforeValues
          (Theory.Vars.cons selected suffixValues))
      have nextEq : HEq stageNext next := by
        dsimp only [stageNext, stageBeforeValues, next]
        exact (Theory.Vars.extend_assoc tail prefixValues
          (Theory.Vars.cons selected suffixValues)).trans
            (heq_of_eq (congrArg (Theory.Vars.extend tail) formalEq.symm))
      have currentEq : HEq stageCurrent current := by
        dsimp only [stageCurrent, current]
        congr 1
        exact List.append_assoc _ _ _
      have movedEq :
          (ArgumentPermutation.Permutation.moveHead signature
            (restArguments ++ before) (signature :: after)).mapVars
              stageCurrent =
            Argument.Duplicate.Vars.duplicateAt
              (restArguments ++ before) stageNext := by
        dsimp only [stageCurrent, stageNext, stageBeforeValues]
        rw [ArgumentPermutation.Permutation.moveHead_cons_extend]
        rw [Argument.Duplicate.Vars.duplicateAt_extend]
      let pendingPresentation := argumentNormalizationPresentation
        recordedSites next stageNext
        (List.append_assoc restArguments before
          (signature :: after)).symm nextEq.symm
      let preparedPresentation := argumentNormalizationPresentation
        recordedSites current stageCurrent
        (congrArg (List.cons signature)
          (List.append_assoc restArguments before
            (signature :: after)).symm) currentEq.symm
      let request : Telescope.Request
          (argumentNormalizedRegion recordedSites current)
          (argumentNormalizedRegion recordedSites next) := {
        boundary := boundary
        source := interface.withBody
          (context.fill (polaritySource polarity
            (argumentNormalizedRegion recordedSites current) endpoint))
          (match polarity with
          | .positive => currentValidity.1
          | .negative => endpointCanonical)
          (match polarity with
          | .positive => currentValidity.2
          | .negative => endpointExternalTwoEnded)
        endpoint := endpoint
        polarity := polarity
        occurrence := exactOccurrence interface context
          (polaritySource polarity
            (argumentNormalizedRegion recordedSites current) endpoint)
          (match polarity with
          | .positive => currentValidity.1
          | .negative => endpointCanonical)
          (match polarity with
          | .positive => currentValidity.2
          | .negative => endpointExternalTwoEnded)
        instantiatedCanonical := currentValidity.1
        instantiatedExternalTwoEnded := currentValidity.2
        pendingCanonical := nextValidity.1
        pendingExternalTwoEnded := nextValidity.2
        endpointCanonical := endpointCanonical
        endpointExternalTwoEnded := endpointExternalTwoEnded
        continuation := tailTelescope
      }
      let prepare : request.Preparation
          (argumentNormalizedRegion recordedSites current) := {
        prepared := argumentNormalizedRegion recordedSites current
        preparedCanonical := currentValidity.1
        preparedExternalTwoEnded := currentValidity.2
        rawPreparedCanonical := currentValidity.1
        rawPreparedExternalTwoEnded := currentValidity.2
        preparedIso := RegionIso.refl _
        telescope := Telescope.refl polarity interface context
          currentValidity.1 currentValidity.2 polarityEq
      }
      have compiled := argumentMoveDuplicateNormalized recordedSites
        stageCurrent stageNext movedEq request pendingPresentation
        (prepare.rawIso preparedPresentation)
      exact Telescope.Compiles.toTelescope polarity interface context
        currentValidity.1 currentValidity.2 endpointCanonical
        endpointExternalTwoEnded polarityEq compiled

/-- Appending one argument preserves occurrence validity by Projection's
extension direction. -/
theorem argumentAppendValidity
    {recordedArguments external arguments common retained boundary
      recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external arguments) (inserted : Var external signature)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (currentCanonical : (context.fill
      (argumentNormalizedRegion recordedSites current)).Canonical)
    (currentExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill
        (argumentNormalizedRegion recordedSites current))) :
    (context.fill (argumentNormalizedRegion recordedSites
      (Theory.Vars.extend current
        (Theory.Vars.cons inserted Theory.Vars.nil)))).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill (argumentNormalizedRegion recordedSites
          (Theory.Vars.extend current
            (Theory.Vars.cons inserted Theory.Vars.nil)))) := by
  let next := Theory.Vars.extend current
    (Theory.Vars.cons inserted Theory.Vars.nil)
  let generated := argumentItemsEdit recordedSites next
    (Argument.Projection.operation arguments [] signature)
    (Argument.Projection.rootFrame common [] retained arguments [] signature)
    (Argument.Projection.targetHead common [] retained arguments [])
    (fun _ _ _ => PUnit.unit)
  let description : Argument.Projection.Drops.Description common := {
    before := arguments
    after := []
    localBefore := []
    localAfter := retained
    signature := signature
    items := generated.1
    itemsEdit := generated.2
  }
  have sourceEq : argumentNormalizedRegion recordedSites next =
      description.source := by
    dsimp only [argumentNormalizedRegion, description, generated, next]
    apply congrArg (Region.mk (.rel (arguments ++ signature :: []) :: retained))
    exact argumentItemsEdit_source_independent recordedSites next
      (normalizationOperation (arguments ++ signature :: []))
      ({ sourceKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         targetKeep := Transform.Frame.keep common []
          [.rel (arguments ++ signature :: [])] retained
         selected := Transform.Frame.insertedHead common [] retained
          (.rel (arguments ++ signature :: [])) } : Transform.Frame
        (arguments ++ signature :: []) (common ++ retained)
        (common ++ (.rel (arguments ++ signature :: []) :: retained))
        (common ++ (.rel (arguments ++ signature :: []) :: retained)))
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (Argument.Projection.operation arguments [] signature)
      (Argument.Projection.rootFrame common [] retained arguments [] signature)
      (Argument.Projection.targetHead common [] retained arguments [])
      (fun _ _ _ => PUnit.unit) (by
        intro wireSignature wire
        simp [Argument.Projection.rootFrame, Transform.Frame.replace]) (by
          simp [Argument.Projection.rootFrame, Transform.Frame.replace])
  let targetPresentation := argumentNormalizationPresentation recordedSites
    current (Argument.Projection.Vars.dropAt arguments next)
    (List.append_nil arguments).symm
    (Argument.Projection.Vars.dropAt_extend_singleton current inserted).symm
  let targetIso : RegionIso (WireEquiv.refl common) description.target
      (argumentNormalizedRegion recordedSites current) := by
    simpa only [description, generated, next, argumentNormalizedRegion] using
      (argumentProjectionEndpointIso (outer := common) (localBefore := [])
        (localAfter := retained) (before := arguments) (after := [])
        recordedSites next).trans targetPresentation.symm
  let filledTargetIso := DiagramContext.fillIso context targetIso
  have targetCanonical : (context.fill description.target).Canonical :=
    filledTargetIso.canonical_iff.mpr currentCanonical
  have targetExternal : OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill description.target) := by
    let endpoint := interface.withBody
      (context.fill (argumentNormalizedRegion recordedSites current))
      currentCanonical currentExternalTwoEnded
    apply endpoint.externalTwoEnded_of_nonempty_iff
    intro wireSignature wire
    have lengthEq := filledTargetIso.incidencePaths_length_eq wire
    constructor <;> intro nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq.symm ▸ nonempty
    · rw [← List.length_pos_iff] at nonempty ⊢
      exact lengthEq ▸ nonempty
  have localTarget := context.holeCanonical description.target targetCanonical
  have extension := description.target_source_extension localTarget
  have filled := context.extendCanonical description.target description.source
    targetCanonical extension.1 extension.2
  have sourceExternal : OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill description.source) := by
    intro wireSignature wire
    exact Nat.le_trans (targetExternal wire)
      (Nat.add_le_add_left (filled.2 wire).length_le _)
  rw [sourceEq]
  exact ⟨filled.1, sourceExternal⟩

/-- Append a nonempty tuple by Projection, retaining an arbitrary presented
final endpoint.  The recursive result is used immediately as the
continuation of the head Projection, so no stage certificate escapes. -/
theorem argumentVarsProjectionCompiles
    {recordedArguments external currentArguments restArguments common retained
      boundary recordedSourceWires recordedTargetWires : List Sig}
    {signature : Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (current : Vars external currentArguments)
    (head : Var external signature) (tail : Vars external restArguments)
    {pending : Region common}
    (request : Telescope.Request
      (argumentNormalizedRegion recordedSites current) pending)
    (pendingIso : RegionIso (WireEquiv.refl common) pending
      (argumentNormalizedRegion recordedSites
        (Theory.Vars.extend current (Theory.Vars.cons head tail))))
    (baseCanonical : (request.occurrence.context.fill
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (baseExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)))) :
    request.Result := by
  let first := Theory.Vars.extend current
    (Theory.Vars.cons head Theory.Vars.nil)
  have firstValidity := argumentAppendValidity recordedSites current head
    request.occurrence.interface request.occurrence.context
    request.instantiatedCanonical request.instantiatedExternalTwoEnded
  let prepare : request.Preparation
      (argumentNormalizedRegion recordedSites current) := {
    prepared := argumentNormalizedRegion recordedSites current
    preparedCanonical := request.instantiatedCanonical
    preparedExternalTwoEnded := request.instantiatedExternalTwoEnded
    rawPreparedCanonical := request.instantiatedCanonical
    rawPreparedExternalTwoEnded := request.instantiatedExternalTwoEnded
    preparedIso := RegionIso.refl _
    telescope := Telescope.refl request.polarity request.occurrence.interface
      request.occurrence.context request.instantiatedCanonical
      request.instantiatedExternalTwoEnded request.continuation.1
  }
  cases tail with
  | nil =>
      let singletonPresentation := argumentNormalizationPresentation
        recordedSites (Theory.Vars.extend current
          (Theory.Vars.cons head Theory.Vars.nil))
          (Theory.Vars.extend current
            (Theory.Vars.cons head Theory.Vars.nil)) rfl HEq.rfl
      exact argumentProjectionNormalized recordedSites current head request
        (pendingIso.trans singletonPresentation) prepare
  | @cons nextSignature nextRest nextHead nextTail =>
      let remaining := Theory.Vars.cons nextHead nextTail
      let nestedFinal := Theory.Vars.extend first remaining
      have assocEq : HEq nestedFinal
          (Theory.Vars.extend current
            (Theory.Vars.cons head remaining)) := by
        exact Theory.Vars.extend_assoc current
          (Theory.Vars.cons head Theory.Vars.nil) remaining
      let associationPresentation := argumentNormalizationPresentation
        recordedSites
        (Theory.Vars.extend current (Theory.Vars.cons head remaining))
        nestedFinal (List.append_assoc currentArguments [signature]
          (nextSignature :: nextRest)).symm assocEq.symm
      let stageInterface : OpenDiagram request.boundary :=
        request.occurrence.interface
      let stageContext : DiagramContext stageInterface.external common :=
        request.occurrence.context
      have recursiveSourceCanonical : (stageContext.fill
          (polaritySource request.polarity
            (argumentNormalizedRegion recordedSites first)
            request.endpoint)).Canonical := by
        exact match request.polarity with
          | .positive => by simpa only [stageContext] using firstValidity.1
          | .negative => by
              simpa only [stageContext] using request.endpointCanonical
      have recursiveSourceExternal : OpenDiagram.ExternalTwoEnded
          stageInterface.boundaryWire (stageContext.fill
            (polaritySource request.polarity
              (argumentNormalizedRegion recordedSites first)
              request.endpoint)) := by
        exact match request.polarity with
          | .positive => by
              simpa only [stageInterface, stageContext] using firstValidity.2
          | .negative => by
              simpa only [stageInterface, stageContext] using
                request.endpointExternalTwoEnded
      let recursiveRequest : Telescope.Request
          (argumentNormalizedRegion recordedSites first) pending := {
        boundary := request.boundary
        source := stageInterface.withBody
          (stageContext.fill (polaritySource request.polarity
            (argumentNormalizedRegion recordedSites first) request.endpoint))
          recursiveSourceCanonical recursiveSourceExternal
        endpoint := request.endpoint
        polarity := request.polarity
        occurrence := exactOccurrence stageInterface
          stageContext (polaritySource request.polarity
            (argumentNormalizedRegion recordedSites first) request.endpoint)
          recursiveSourceCanonical recursiveSourceExternal
        instantiatedCanonical := firstValidity.1
        instantiatedExternalTwoEnded := firstValidity.2
        pendingCanonical := request.pendingCanonical
        pendingExternalTwoEnded := request.pendingExternalTwoEnded
        endpointCanonical := request.endpointCanonical
        endpointExternalTwoEnded := request.endpointExternalTwoEnded
        continuation := request.continuation
      }
      have recursiveCompiled := argumentVarsProjectionCompiles
        (boundary := request.boundary) recordedSites
        first nextHead nextTail recursiveRequest
        (pendingIso.trans associationPresentation) baseCanonical
        baseExternalTwoEnded
      have recursiveTelescope := Telescope.Compiles.toTelescope
        request.polarity request.occurrence.interface request.occurrence.context
        firstValidity.1 firstValidity.2 request.endpointCanonical
        request.endpointExternalTwoEnded request.continuation.1
        recursiveCompiled
      let firstRequest : Telescope.Request
          (argumentNormalizedRegion recordedSites current)
          (argumentNormalizedRegion recordedSites first) := {
        boundary := request.boundary
        source := request.source
        endpoint := request.endpoint
        polarity := request.polarity
        occurrence := request.occurrence
        instantiatedCanonical := request.instantiatedCanonical
        instantiatedExternalTwoEnded := request.instantiatedExternalTwoEnded
        pendingCanonical := firstValidity.1
        pendingExternalTwoEnded := firstValidity.2
        endpointCanonical := request.endpointCanonical
        endpointExternalTwoEnded := request.endpointExternalTwoEnded
        continuation := recursiveTelescope
      }
      let firstPrepare : firstRequest.Preparation
          (argumentNormalizedRegion recordedSites current) := {
        prepared := prepare.prepared
        preparedCanonical := prepare.preparedCanonical
        preparedExternalTwoEnded := prepare.preparedExternalTwoEnded
        rawPreparedCanonical := prepare.rawPreparedCanonical
        rawPreparedExternalTwoEnded := prepare.rawPreparedExternalTwoEnded
        preparedIso := prepare.preparedIso
        telescope := prepare.telescope
      }
      exact argumentProjectionNormalized recordedSites current head firstRequest
        (RegionIso.refl _) firstPrepare


/-- The fixed traversal frame retains the exact source-side instantiation
indices and uses the identity target context only as an inert site annotation
index. -/
def normalizationFrame (outer before after arguments : List Sig) :
    Transform.Frame arguments (outer ++ (before ++ after))
      (outer ++ (before ++ .rel arguments :: after))
      (outer ++ (before ++ after)) where
  sourceKeep := _root_.VisualProof.Rule.Comprehension.retain outer before after
    arguments
  targetKeep := WireRenaming.id
  selected := _root_.VisualProof.Rule.Comprehension.selected outer before after
    arguments

mutual
  /-- Unit site annotations exist for every exact authoritative region
  result. The existential stays in `Prop`, so no Instantiation proof is
  eliminated into caller-selectable data. -/
  theorem normalizationRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (RegionSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | mk itemsEvidence =>
        obtain ⟨sites⟩ := normalizationItemsSites_nonempty
          (frame := frame.append _) itemsEvidence
        exact ⟨.mk sites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item-sequence
  result. -/
  theorem normalizationItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemsSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := normalizationItemSites_nonempty itemEvidence
        obtain ⟨tailSites⟩ := normalizationItemsSites_nonempty tailEvidence
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  /-- Unit site annotations exist for every exact authoritative item result. -/
  theorem normalizationItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result) :
      Nonempty (ItemSites (normalizationOperation arguments) PUnit.unit
        evidence) := by
    cases evidence with
    | atom head ports =>
        exact ⟨ItemSites.atom (pattern := pattern) (frame := frame) head ports⟩
    | selectedAtom ports =>
        exact ⟨ItemSites.selectedAtom (pattern := pattern) (frame := frame)
          ports PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨ItemSites.identity (pattern := pattern) (frame := frame)
          signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨sites⟩ := normalizationRegionSites_nonempty childEvidence
        exact ⟨.cut sites⟩
  termination_by sizeOf source
end

/-- A fixed unit-data site traversal selected internally from exact
Instantiation evidence. -/
noncomputable def normalizationSites
    {arguments common sourceWires targetWires : List Sig}
    {pattern : OpenDiagram arguments}
    {frame : Transform.Frame arguments common sourceWires targetWires}
    {source : ItemSeq sourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result) :
    ItemsSites (normalizationOperation arguments) PUnit.unit evidence :=
  Classical.choice (normalizationItemsSites_nonempty evidence)

/-! The literal positional atom required by `Leaf.Formal.operation []`.
Its head and every argument occupy distinct boundary positions. -/

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
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
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
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)) nestedPositional :=
    {
      canonical := fun canonical =>
        nestedScope.canonical (hostedSourceIso.canonical_iff.mp canonical)
      incidenceNonempty := fun wire => by
        have sourceIsoNonempty :
            (Region.adjoinAt hostLocals outerHostItems
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
as literal positional-Formal evidence.  The exact compiler-owned edit
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
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
    simp only [raw, Rule.Erasure.Description.source, Region.spliceAt,
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
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application)
      (Region.adjoinAt retainedLocals hostItems direct) :=
    rawSourceIso.symm.trans (RegionIso.ofEq rawSourceEq)
  have originalHostedCanonical :
      (Region.adjoinAt hostLocals outerHostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)).Canonical :=
    occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have originalLocalCanonical :
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      {arguments external common mappedCommon sourceWires mappedSourceWires
        targetWires mappedTargetWires : List Sig}
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep
          frame.selected source result)
      (sites : RegionSites (recordingOperation baseOperation external)
        data evidence)
      (current : Vars external arguments)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (targetRename : WireRenaming targetWires mappedTargetWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (targetKeepCommutes : ∀ {signature} (wire : Var common signature),
        targetRename (frame.targetKeep wire) =
          mappedFrame.targetKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected)
      (siteNatural : ∀
        {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
          siteTargetWires siteMappedTargetWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteMappedFrame : Transform.Frame arguments siteMappedCommon
          siteMappedSourceWires siteMappedTargetWires}
        {siteData : baseOperation.Data siteFrame}
        {siteMappedData : baseOperation.Data siteMappedFrame}
        (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
        (siteTargetRename : WireRenaming siteTargetWires
          siteMappedTargetWires)
        (_siteTargetKeepCommutes : ∀ {wireSignature}
          (wire : Var siteCommon wireSignature),
          siteTargetRename (siteFrame.targetKeep wire) =
            siteMappedFrame.targetKeep (siteCommonRename wire))
        (ports : Vars siteCommon arguments)
        (site : (recordingOperation baseOperation external).SiteData
          siteFrame siteData ports),
        ∃ mappedSite : (recordingOperation baseOperation external).SiteData
            siteMappedFrame siteMappedData
            (ports.map fun wire => siteCommonRename wire),
          Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
            (((recordingOperation baseOperation external).site
              siteFrame siteData ports site).renameWires
              siteTargetRename)
            ((recordingOperation baseOperation external).site
              siteMappedFrame siteMappedData
              (ports.map fun wire => siteCommonRename wire) mappedSite))) :
      ∃ mappedSource : Region mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
            mappedChildSites, mappedChildSourceEq,
            mappedChildArgumentEq,
            ⟨mappedChildIso⟩, ⟨mappedChildEndpointIso⟩⟩ :=
          targetItemsReindex childEvidence childSites current
            (commonRename.appendRight locals)
            (sourceRename.appendRight locals) (targetRename.appendRight locals)
            appendedKeep (by
              intro signature wire
              change targetRename.appendRight locals
                  (frame.targetKeep.appendRight locals wire) =
                mappedFrame.targetKeep.appendRight locals
                  (commonRename.appendRight locals wire)
              rw [WireRenaming.appendRight_comp_apply,
                WireRenaming.appendRight_comp_apply, targetMaps])
            appendedSelected siteNatural
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
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
          ⟨exposed.trans child⟩,
          ⟨exposedEndpoint.trans childEndpoint⟩⟩
  termination_by sizeOf source

  theorem targetItemsReindex
      {arguments external common mappedCommon sourceWires mappedSourceWires
        targetWires mappedTargetWires : List Sig}
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep
          frame.selected source result)
      (sites : ItemsSites (recordingOperation baseOperation external)
        data evidence)
      (current : Vars external arguments)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (targetRename : WireRenaming targetWires mappedTargetWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (targetKeepCommutes : ∀ {signature} (wire : Var common signature),
        targetRename (frame.targetKeep wire) =
          mappedFrame.targetKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected)
      (siteNatural : ∀
        {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
          siteTargetWires siteMappedTargetWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteMappedFrame : Transform.Frame arguments siteMappedCommon
          siteMappedSourceWires siteMappedTargetWires}
        {siteData : baseOperation.Data siteFrame}
        {siteMappedData : baseOperation.Data siteMappedFrame}
        (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
        (siteTargetRename : WireRenaming siteTargetWires
          siteMappedTargetWires)
        (_siteTargetKeepCommutes : ∀ {wireSignature}
          (wire : Var siteCommon wireSignature),
          siteTargetRename (siteFrame.targetKeep wire) =
            siteMappedFrame.targetKeep (siteCommonRename wire))
        (ports : Vars siteCommon arguments)
        (site : (recordingOperation baseOperation external).SiteData
          siteFrame siteData ports),
        ∃ mappedSite : (recordingOperation baseOperation external).SiteData
            siteMappedFrame siteMappedData
            (ports.map fun wire => siteCommonRename wire),
          Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
            (((recordingOperation baseOperation external).site
              siteFrame siteData ports site).renameWires
              siteTargetRename)
            ((recordingOperation baseOperation external).site
              siteMappedFrame siteMappedData
              (ports.map fun wire => siteCommonRename wire) mappedSite))) :
      ∃ mappedSource : ItemSeq mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := pattern)
            (retain := mappedFrame.sourceKeep)
            (selected := mappedFrame.selected)
        exact ⟨.nil, Region.blank mappedCommon, mappedEvidence,
          .nil mappedEvidence, rfl, rfl, ⟨RegionIso.refl _⟩,
          ⟨by
            unfold itemsEdit ExactEdit.refl
            exact RegionIso.refl _⟩⟩
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        obtain ⟨mappedItemSource, mappedItemResult, mappedItemEvidence,
            mappedItemSites, mappedItemSourceEq,
            mappedItemArgumentEq,
            ⟨mappedItemIso⟩,
            ⟨mappedItemEndpointIso⟩⟩ :=
          targetItemReindex itemEvidence itemSites current commonRename
            sourceRename targetRename keepCommutes targetKeepCommutes
            selectedCommutes siteNatural
        obtain ⟨mappedTailSource, mappedTailResult, mappedTailEvidence,
            mappedTailSites, mappedTailSourceEq,
            mappedTailArgumentEq,
            ⟨mappedTailIso⟩,
            ⟨mappedTailEndpointIso⟩⟩ :=
          targetItemsReindex tailEvidence tailSites current commonRename
            sourceRename targetRename keepCommutes targetKeepCommutes
            selectedCommutes siteNatural
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
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
          ⟨exposed.trans children⟩,
          ⟨exposedEndpoint.trans endpointChildren⟩⟩
  termination_by sizeOf source

  theorem targetItemReindex
      {arguments external common mappedCommon sourceWires mappedSourceWires
        targetWires mappedTargetWires : List Sig}
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep
          frame.selected source result)
      (sites : ItemSites (recordingOperation baseOperation external)
        data originalEvidence)
      (current : Vars external arguments)
      (commonRename : WireRenaming common mappedCommon)
      (sourceRename : WireRenaming sourceWires mappedSourceWires)
      (targetRename : WireRenaming targetWires mappedTargetWires)
      (keepCommutes : ∀ {signature} (wire : Var common signature),
        sourceRename (frame.sourceKeep wire) =
          mappedFrame.sourceKeep (commonRename wire))
      (targetKeepCommutes : ∀ {signature} (wire : Var common signature),
        targetRename (frame.targetKeep wire) =
          mappedFrame.targetKeep (commonRename wire))
      (selectedCommutes : sourceRename frame.selected =
        mappedFrame.selected)
      (siteNatural : ∀
        {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
          siteTargetWires siteMappedTargetWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteTargetWires}
        {siteMappedFrame : Transform.Frame arguments siteMappedCommon
          siteMappedSourceWires siteMappedTargetWires}
        {siteData : baseOperation.Data siteFrame}
        {siteMappedData : baseOperation.Data siteMappedFrame}
        (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
        (siteTargetRename : WireRenaming siteTargetWires
          siteMappedTargetWires)
        (_siteTargetKeepCommutes : ∀ {wireSignature}
          (wire : Var siteCommon wireSignature),
          siteTargetRename (siteFrame.targetKeep wire) =
            siteMappedFrame.targetKeep (siteCommonRename wire))
        (ports : Vars siteCommon arguments)
        (site : (recordingOperation baseOperation external).SiteData
          siteFrame siteData ports),
        ∃ mappedSite : (recordingOperation baseOperation external).SiteData
            siteMappedFrame siteMappedData
            (ports.map fun wire => siteCommonRename wire),
          Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
            (((recordingOperation baseOperation external).site
              siteFrame siteData ports site).renameWires
              siteTargetRename)
            ((recordingOperation baseOperation external).site
              siteMappedFrame siteMappedData
              (ports.map fun wire => siteCommonRename wire) mappedSite))) :
      ∃ mappedSource : Item mappedSourceWires,
        ∃ mappedResult : Region mappedCommon,
          ∃ mappedEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
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
          mappedSource,
          ⟨RegionIso.ofEq mappedResult⟩,
          ⟨RegionIso.ofEq mappedEndpoint⟩⟩
    | .selectedAtom application siteData => by
        let mappedApplication := application.map fun wire => commonRename wire
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
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
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              pattern application).renameWires
                commonRename =
              _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern mappedApplication := by
          exact EqualityNormalization.instantiate_renameWires
            pattern application commonRename
        obtain ⟨mappedSite, ⟨mappedEndpointIso⟩⟩ :=
          siteNatural commonRename targetRename targetKeepCommutes
            application siteData
        let coherentMappedSite :
            (recordingOperation baseOperation external).SiteData
              mappedFrame mappedData mappedApplication :=
          ⟨mappedSite.1, siteData.2.map fun wire => commonRename wire⟩
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
        exact ⟨_, _, mappedEvidence, mappedSites, mappedSource,
          by
            simpa only [argumentItemEdit, Vars.map_map, mappedSites,
              coherentMappedSite] using mappedArgumentEq,
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
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
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
          mappedSource, ⟨RegionIso.ofEq mappedResult⟩,
          ⟨RegionIso.ofEq mappedEndpoint⟩⟩
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
            mappedChildSites, mappedChildSourceEq,
            mappedChildArgumentEq,
            ⟨mappedChildIso⟩, ⟨mappedChildEndpointIso⟩⟩ :=
          targetRegionReindex childEvidence childSites current commonRename
            sourceRename targetRename keepCommutes targetKeepCommutes
            selectedCommutes siteNatural
        let mappedEvidence :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
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
          ⟨exposed.trans child⟩,
          ⟨exposedEndpoint.trans endpointChild⟩⟩
  termination_by sizeOf source
end

/-! Concatenating two reindexed literal Formal segments preserves their
authoritative evidence and sites; conjunction reassociation is presentation
only. -/
theorem targetItemsAppend
    {arguments external common sourceWires targetWires : List Sig}
    {pattern : OpenDiagram arguments}
    {baseOperation : Transform.Operation arguments}
    {frame : Transform.Frame arguments common
      sourceWires targetWires}
    {data : baseOperation.Data frame}
    {firstSource secondSource : ItemSeq sourceWires}
    {firstResult secondResult : Region common}
    (firstEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected
        firstSource firstResult)
    (firstSites : ItemsSites
      (recordingOperation baseOperation external) data firstEvidence)
    (secondEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected
        secondSource secondResult)
    (secondSites : ItemsSites
      (recordingOperation baseOperation external) data secondEvidence)
    (current : Vars external arguments) :
    ∃ combinedResult : Region common,
      ∃ combinedEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
      exact ⟨secondResult, secondEvidence, secondSites, rfl,
        ⟨RegionIso.blankConjoin secondResult⟩,
        ⟨by
          unfold itemsEdit ExactEdit.refl
          simp only [Transform.ItemsEdit.run]
          exact RegionIso.blankConjoin _⟩⟩
  | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemResult tailResult
      itemEvidence tailEvidence itemSites tailSites => by
      obtain ⟨combinedTailResult, combinedTailEvidence,
          combinedTailSites, combinedTailArgumentEq, ⟨combinedTailIso⟩,
          ⟨combinedTailEndpointIso⟩⟩ :=
        targetItemsAppend tailEvidence tailSites secondEvidence secondSites
          current
      let combinedEvidence :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
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
        ⟨associated.trans tailPresented⟩,
        ⟨by
          simpa only [itemsEdit, itemOutput, tailOutput, secondOutput,
            combinedSites] using
            endpointAssociated.trans endpointTailPresented⟩⟩
  termination_by sizeOf firstSource

/-- Scope preservation composes without introducing another diagram
authority. -/
theorem ScopePreservation.trans
    {first second third : Region wires}
    (firstScope : ScopePreservation first second)
    (secondScope : ScopePreservation second third) :
    ScopePreservation first third := {
  canonical := fun canonical =>
    secondScope.canonical (firstScope.canonical canonical)
  incidenceNonempty := fun wire =>
    (firstScope.incidenceNonempty wire).trans
      (secondScope.incidenceNonempty wire)
  rootedTwo := fun wire rooted =>
    secondScope.rootedTwo wire (firstScope.rootedTwo wire rooted)
}

/-- A region presentation preserves exactly the scope facts used by the
compiler fold. -/
theorem ScopePreservation.ofIso
    {before after : Region wires}
    (iso : RegionIso (WireEquiv.refl wires) before after) :
    ScopePreservation before after := {
  canonical := iso.canonical_iff.mp
  incidenceNonempty := fun wire => by
    rw [← List.length_pos_iff, ← List.length_pos_iff,
      iso.incidencePaths_length_eq wire]
  rootedTwo := fun wire rooted =>
    (iso.rootedTwo_incidencePaths_iff wire).mp rooted
}

theorem ScopePreservation.refl (region : Region wires) :
    ScopePreservation region region := {
  canonical := fun canonical => canonical
  incidenceNonempty := fun _ => Iff.rfl
  rootedTwo := fun _ rooted => rooted
}

theorem ScopePreservation.conjoin
    {firstBefore firstAfter secondBefore secondAfter : Region wires}
    (firstScope : ScopePreservation firstBefore firstAfter)
    (secondScope : ScopePreservation secondBefore secondAfter) :
    ScopePreservation (firstBefore.conjoin secondBefore)
      (firstAfter.conjoin secondAfter) := by
  have combined := Region.conjoin_preserves_scope firstBefore secondBefore
    firstAfter secondAfter firstScope.canonical secondScope.canonical
    firstScope.incidenceNonempty secondScope.incidenceNonempty
    firstScope.rootedTwo secondScope.rootedTwo
  exact {
    canonical := combined.1
    incidenceNonempty := fun wire => (combined.2 wire).1
    rootedTwo := fun wire => (combined.2 wire).2
  }

theorem ScopePreservation.cut {before after : Region wires}
    (childScope : ScopePreservation before after) :
    ScopePreservation (Region.singleton (.cut before))
      (Region.singleton (.cut after)) := by
  constructor
  · intro sourceCanonical
    apply (Region.singleton_cut_canonical_iff after).mpr
    exact childScope.canonical
      ((Region.singleton_cut_canonical_iff before).mp sourceCanonical)
  · intro signature wire
    rw [Region.incidencePaths_singleton_cut,
      Region.incidencePaths_singleton_cut]
    constructor
    · intro sourceNonempty
      have childSourceNonempty :
          before.incidencePaths wire.index.val ≠ [] := by
        intro sourceEmpty
        exact sourceNonempty ((List.map_eq_nil_iff).mpr sourceEmpty)
      have childTargetNonempty :=
        (childScope.incidenceNonempty wire).mp childSourceNonempty
      intro targetEmpty
      exact childTargetNonempty ((List.map_eq_nil_iff).mp targetEmpty)
    · intro targetNonempty
      have childTargetNonempty :
          after.incidencePaths wire.index.val ≠ [] := by
        intro targetEmpty
        exact targetNonempty ((List.map_eq_nil_iff).mpr targetEmpty)
      have childSourceNonempty :=
        (childScope.incidenceNonempty wire).mpr childTargetNonempty
      intro sourceEmpty
      exact childSourceNonempty ((List.map_eq_nil_iff).mp sourceEmpty)
  · intro signature wire sourceRoot
    have sameEmpty : before.incidencePaths wire.index.val = [] ↔
        after.incidencePaths wire.index.val = [] := by
      constructor
      · intro beforeEmpty
        by_cases afterEmpty : after.incidencePaths wire.index.val = []
        · exact afterEmpty
        · exact False.elim
            (((childScope.incidenceNonempty wire).mpr afterEmpty) beforeEmpty)
      · intro afterEmpty
        by_cases beforeEmpty : before.incidencePaths wire.index.val = []
        · exact beforeEmpty
        · exact False.elim
            (((childScope.incidenceNonempty wire).mp beforeEmpty) afterEmpty)
    rw [Region.incidencePaths_singleton_cut] at sourceRoot ⊢
    have replaced := RegionPath.rootedTwo_replace []
      (before.incidencePaths wire.index.val)
      (after.incidencePaths wire.index.val) [] 0 sameEmpty
    simpa only [List.nil_append, List.append_nil] using
      replaced.mp (by simpa using sourceRoot)

/-- A strict transformation stable under every surrounding supported item
host and every inherited-wire renaming. -/
def HostedStrict (before after : Region common) : Prop :=
  ∀ (outer hostLocals : List Sig)
    (rename : WireRenaming common (outer ++ hostLocals))
    (hostItems : ItemSeq (outer ++ hostLocals))
    {boundary : List Sig} {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename)) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (after.renameWires rename))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (after.renameWires rename)))),
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems (after.renameWires rename))
      targetCanonical targetExternalTwoEnded

/-- The canonical nonempty loop witnesses hosted strict reflexivity. -/
theorem HostedStrict.refl (region : Region common) :
    HostedStrict region region := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  exact EqualityNormalization.StrictEquates.refl occurrence

/-- Specialize a hosted transformation along one fixed wire substitution. -/
theorem HostedStrict.specialize
    {before after : Region sourceWires}
    (transformation : HostedStrict before after)
    (baseRename : WireRenaming sourceWires common)
    {mappedBefore mappedAfter : Region common}
    (beforeEq : before.renameWires baseRename = mappedBefore)
    (afterEq : after.renameWires baseRename = mappedAfter) :
    HostedStrict mappedBefore mappedAfter := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let combined := WireRenaming.comp rename baseRename
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    (mappedBefore.renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems
    (before.renameWires combined)
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    simp only [sourceBefore, sourceAfter, combined, ← beforeEq,
      Region.renameWires_comp]
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical sourceBefore
      occurrence.sourceCanonical
  have sourceNonempty : ∀ {signature} (wire : Var outer signature),
      sourceBefore.incidencePaths wire.index.val ≠ [] ↔
        sourceAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [sourceEq]
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical sourceNonempty (RegionIso.ofEq sourceEq)
  let targetBefore := Region.adjoinAt hostLocals hostItems
    (mappedAfter.renameWires rename)
  let targetAfter := Region.adjoinAt hostLocals hostItems
    (after.renameWires combined)
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  have targetEq : targetBefore = targetAfter := by
    simp only [targetBefore, targetAfter, combined, ← afterEq,
      Region.renameWires_comp]
  have targetAfterCanonical : targetAfter.Canonical := by
    rw [← targetEq]
    exact occurrence.context.holeCanonical targetBefore targetCanonical
  have targetNonempty : ∀ {signature} (wire : Var outer signature),
      targetBefore.incidencePaths wire.index.val ≠ [] ↔
        targetAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [targetEq]
  have targetReplacement := occurrence.context.replaceCanonical
    targetBefore targetAfter targetCanonical targetAfterCanonical targetNonempty
  let targetBeforeEndpoint := occurrence.interface.withBody
    (occurrence.context.fill targetBefore) targetCanonical
      targetExternalTwoEnded
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetAfter) :=
    targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
      targetReplacement.2
  have core := transformation outer hostLocals combined hostItems
    presentedOccurrence targetReplacement.1 targetAfterExternalTwoEnded
  let targetIso : OpenDiagramIso
      (presentedOccurrence.interface.withBody
        (presentedOccurrence.context.fill targetAfter)
        targetReplacement.1 targetAfterExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore)
        targetCanonical targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetReplacement.1 targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context
        (RegionIso.ofEq targetEq.symm))
  exact ⟨transGen_iso (OpenDiagramIso.refl source) core.1 targetIso,
    transGen_iso targetIso core.2 (OpenDiagramIso.refl source)⟩

/-- Lift a hosted strict transformation beneath one locally bound region. -/
theorem HostedStrict.adjoinAt
    {common : List Sig} (locals : List Sig)
    (before after : Region (common ++ locals))
    (transformation : HostedStrict before after) :
    HostedStrict (Region.adjoinAt locals .nil before)
      (Region.adjoinAt locals .nil after) := by
  intro outer hostLocals rename hostItems boundary source
    hostedOccurrence targetCanonical targetExternalTwoEnded
  let childRename := rename.appendRight locals
  let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
    locals
  let nextRename := WireRenaming.comp assoc.toRenaming childRename
  let nextHostItems := Region.extendHostItems hostLocals hostItems
    (.mk locals .nil)
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((Region.adjoinAt locals .nil before).renameWires rename)
  let sourceAfter := Region.adjoinAt (hostLocals ++ locals)
    nextHostItems (before.renameWires nextRename)
  change Occurrence sourceBefore source at hostedOccurrence
  let sourceNested := RegionIso.adjoinAt hostLocals hostItems
    (RegionIso.renameWiresAdjoinAtNil before rename)
  let sourceAssociated :=
    (RegionIso.adjoinAtAssoc hostLocals hostItems locals .nil
      (before.renameWires childRename)).symm
  let sourceCombined := RegionIso.adjoinAt
    (hostLocals ++ locals) nextHostItems
    (RegionIso.renameWiresComp before childRename
      assoc.toRenaming)
  let sourcePresentation : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter :=
    (sourceNested.trans sourceAssociated).trans sourceCombined
  have sourceAfterCanonical : sourceAfter.Canonical :=
    sourcePresentation.canonical_iff.mp
      (hostedOccurrence.context.holeCanonical _
        hostedOccurrence.sourceCanonical)
  have sourceSameNonempty : ∀ {signature} (wire : Var outer signature),
      sourceBefore.incidencePaths wire.index.val ≠ [] ↔
        sourceAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourcePresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence hostedOccurrence
      sourceAfterCanonical sourceSameNonempty sourcePresentation
  let targetBefore := Region.adjoinAt hostLocals hostItems
    ((Region.adjoinAt locals .nil after).renameWires rename)
  let targetAfter := Region.adjoinAt (hostLocals ++ locals)
    nextHostItems (after.renameWires nextRename)
  let targetNested := RegionIso.adjoinAt hostLocals hostItems
    (RegionIso.renameWiresAdjoinAtNil after rename)
  let targetAssociated :=
    (RegionIso.adjoinAtAssoc hostLocals hostItems locals .nil
      (after.renameWires childRename)).symm
  let targetCombined := RegionIso.adjoinAt
    (hostLocals ++ locals) nextHostItems
    (RegionIso.renameWiresComp after childRename
      assoc.toRenaming)
  let targetPresentation : RegionIso (WireEquiv.refl outer)
      targetBefore targetAfter :=
    (targetNested.trans targetAssociated).trans targetCombined
  have targetAfterLocalCanonical : targetAfter.Canonical :=
    targetPresentation.canonical_iff.mp
      (hostedOccurrence.context.holeCanonical _ targetCanonical)
  have targetSameNonempty : ∀ {signature} (wire : Var outer signature),
      targetBefore.incidencePaths wire.index.val ≠ [] ↔
        targetAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := targetPresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have targetReplacement := hostedOccurrence.context.replaceCanonical
    targetBefore targetAfter targetCanonical targetAfterLocalCanonical
    targetSameNonempty
  let targetBeforeEndpoint := hostedOccurrence.interface.withBody
    (hostedOccurrence.context.fill targetBefore) targetCanonical
    targetExternalTwoEnded
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      hostedOccurrence.interface.boundaryWire
      (hostedOccurrence.context.fill targetAfter) :=
    targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
      targetReplacement.2
  have presentedTargetCanonical :
      (presentedOccurrence.context.fill targetAfter).Canonical := by
    exact targetReplacement.1
  have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedOccurrence.interface.boundaryWire
      (presentedOccurrence.context.fill targetAfter) := by
    intro signature wire
    exact targetAfterExternalTwoEnded wire
  have childStrict := transformation outer
    (hostLocals ++ locals) nextRename nextHostItems
    presentedOccurrence presentedTargetCanonical
    presentedTargetExternalTwoEnded
  let finalBodyIso := DiagramContext.fillIso
    presentedOccurrence.context targetPresentation.symm
  let finalIso : OpenDiagramIso
      (presentedOccurrence.interface.withBody
        (presentedOccurrence.context.fill targetAfter)
        presentedTargetCanonical presentedTargetExternalTwoEnded)
      (hostedOccurrence.interface.withBody
        (hostedOccurrence.context.fill targetBefore)
        targetCanonical targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
      presentedTargetExternalTwoEnded targetExternalTwoEnded finalBodyIso
  exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
      finalIso,
    transGen_iso finalIso childStrict.2 (OpenDiagramIso.refl source)⟩

/-- Combine hosted strict transformations under region conjunction. -/
theorem HostedStrict.conjoin
    {common : List Sig}
    (firstBefore secondBefore firstAfter secondAfter : Region common)
    (firstTransformation : HostedStrict firstBefore firstAfter)
    (secondTransformation : HostedStrict secondBefore secondAfter) :
    HostedStrict (firstBefore.conjoin secondBefore)
      (firstAfter.conjoin secondAfter) := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let sourceMaterial :=
    (firstBefore.conjoin secondBefore).renameWires rename
  let targetMaterial :=
    (firstAfter.conjoin secondAfter).renameWires rename
  have supportedSequence : ∀
      (activeHostItems : ItemSeq (outer ++ hostLocals))
      {activeSource : OpenDiagram boundary}
      (activeOccurrence : Occurrence
        (Region.adjoinAt hostLocals activeHostItems sourceMaterial)
        activeSource)
      (_hostCanonical :
        (Region.mk hostLocals activeHostItems).Canonical)
      (_hostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk hostLocals activeHostItems).incidencePaths
          wire.index.val ≠ [])
      (activeTargetCanonical :
        (activeOccurrence.context.fill
          (Region.adjoinAt hostLocals activeHostItems
            targetMaterial)).Canonical)
      (activeTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        activeOccurrence.interface.boundaryWire
        (activeOccurrence.context.fill
          (Region.adjoinAt hostLocals activeHostItems
            targetMaterial))),
      EqualityNormalization.StrictEquates activeOccurrence
        (Region.adjoinAt hostLocals activeHostItems targetMaterial)
        activeTargetCanonical activeTargetExternalTwoEnded := by
    intro activeHostItems activeSource activeOccurrence hostCanonical
      hostNonempty activeTargetCanonical activeTargetExternalTwoEnded
    let itemBefore := firstBefore.renameWires rename
    let tailBefore := secondBefore.renameWires rename
    let itemAfter := firstAfter.renameWires rename
    let tailAfter := secondAfter.renameWires rename
    change Occurrence
      (Region.adjoinAt hostLocals activeHostItems
        ((firstBefore.conjoin secondBefore).renameWires rename))
      activeSource at activeOccurrence
    have sourceBeforeCanonical :
        ((firstBefore.conjoin secondBefore).renameWires rename).Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals activeHostItems _
        (activeOccurrence.context.holeCanonical _
          activeOccurrence.sourceCanonical)
    have sourceMaterialCanonical :
        (itemBefore.conjoin tailBefore).Canonical := by
      rw [← Region.renameWires_conjoin]
      exact sourceBeforeCanonical
    let sourceOccurrence : Occurrence
        (Region.adjoinAt hostLocals activeHostItems
          (itemBefore.conjoin tailBefore)) activeSource :=
      EqualityNormalization.supportedAdjoinOccurrence hostLocals
        activeHostItems activeOccurrence hostCanonical hostNonempty
        sourceMaterialCanonical (by
          simpa only [itemBefore, tailBefore] using
            RegionIso.renameWiresConjoin firstBefore secondBefore rename)
    have itemBeforeCanonical :=
      EqualityNormalization.canonical_left_of_conjoin
        sourceMaterialCanonical
    have tailBeforeCanonical :=
      EqualityNormalization.canonical_right_of_conjoin
        sourceMaterialCanonical
    let targetBefore :=
      (firstAfter.conjoin secondAfter).renameWires rename
    change (activeOccurrence.context.fill
      (Region.adjoinAt hostLocals activeHostItems
        targetBefore)).Canonical at activeTargetCanonical
    change OpenDiagram.ExternalTwoEnded
      activeOccurrence.interface.boundaryWire
      (activeOccurrence.context.fill
        (Region.adjoinAt hostLocals activeHostItems targetBefore)) at activeTargetExternalTwoEnded
    have targetBeforeCanonical : targetBefore.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals activeHostItems _
        (activeOccurrence.context.holeCanonical _
          activeTargetCanonical)
    have targetMaterialCanonical :
        (itemAfter.conjoin tailAfter).Canonical := by
      rw [← Region.renameWires_conjoin]
      exact targetBeforeCanonical
    have itemAfterCanonical :=
      EqualityNormalization.canonical_left_of_conjoin
        targetMaterialCanonical
    have tailAfterCanonical :=
      EqualityNormalization.canonical_right_of_conjoin
        targetMaterialCanonical
    have presentedTargetCanonical :
        (sourceOccurrence.context.fill
          (Region.adjoinAt hostLocals activeHostItems
            targetBefore)).Canonical := by
      exact activeTargetCanonical
    have presentedTargetExternalTwoEnded :
        OpenDiagram.ExternalTwoEnded
          sourceOccurrence.interface.boundaryWire
          (sourceOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems
              targetBefore)) := by
      intro signature wire
      exact activeTargetExternalTwoEnded wire
    have itemPhaseValidity :=
      EqualityNormalization.supportedAdjoinValidity hostLocals
        activeHostItems sourceOccurrence hostCanonical hostNonempty
        (EqualityNormalization.canonical_conjoin itemAfterCanonical
          tailBeforeCanonical)
    let afterItem := Region.adjoinAt hostLocals activeHostItems
      (itemAfter.conjoin tailBefore)
    have itemPhase : EqualityNormalization.StrictEquates
        sourceOccurrence afterItem itemPhaseValidity.1
          itemPhaseValidity.2 := by
      have swappedCanonical :
          (tailBefore.conjoin itemBefore).Canonical :=
        EqualityNormalization.canonical_conjoin tailBeforeCanonical
          itemBeforeCanonical
      let swapped :=
        EqualityNormalization.supportedAdjoinOccurrence hostLocals
          activeHostItems sourceOccurrence hostCanonical hostNonempty
          swappedCanonical
          (RegionIso.conjoinComm itemBefore tailBefore)
      let flattened := EqualityNormalization.flattenAdjoinOccurrence
        hostLocals activeHostItems tailBefore itemBefore swapped
        hostCanonical hostNonempty tailBeforeCanonical
        itemBeforeCanonical
      let nextHostItems := Region.extendHostItems hostLocals
        activeHostItems tailBefore
      let hostWire := Region.adjoinHostWire outer hostLocals
        tailBefore.locals
      let nextRename := WireRenaming.comp hostWire rename
      have nextHostCanonical :=
        EqualityNormalization.extendHostCanonical hostLocals
          activeHostItems tailBefore hostCanonical tailBeforeCanonical
      have nextHostNonempty : ∀ {signature}
          (wire : Var outer signature),
          (Region.mk (hostLocals ++ tailBefore.locals)
            nextHostItems).incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        exact EqualityNormalization.extendHost_incidence_nonempty
          hostLocals activeHostItems tailBefore hostNonempty wire
      have firstBeforeCanonical : firstBefore.Canonical :=
        (Region.Canonical.renameWires_iff firstBefore rename).mp
          itemBeforeCanonical
      have alignedSourceCanonical :
          (firstBefore.renameWires nextRename).Canonical :=
        (Region.Canonical.renameWires_iff firstBefore nextRename).mpr
          firstBeforeCanonical
      let alignedFlattened : Occurrence
          (Region.adjoinAt (hostLocals ++ tailBefore.locals)
            nextHostItems (firstBefore.renameWires nextRename))
          activeSource :=
        EqualityNormalization.supportedAdjoinOccurrence
          (hostLocals ++ tailBefore.locals) nextHostItems flattened
          nextHostCanonical nextHostNonempty alignedSourceCanonical (by
            simpa only [itemBefore, hostWire, nextRename] using
              RegionIso.renameWiresComp firstBefore rename hostWire)
      have firstAfterCanonical : firstAfter.Canonical :=
        (Region.Canonical.renameWires_iff firstAfter rename).mp
          itemAfterCanonical
      let flatTargetMaterial := firstAfter.renameWires nextRename
      have flatTargetMaterialCanonical :
          flatTargetMaterial.Canonical :=
        (Region.Canonical.renameWires_iff firstAfter nextRename).mpr
          firstAfterCanonical
      have flatTargetValidity :=
        EqualityNormalization.supportedAdjoinValidity
          (hostLocals ++ tailBefore.locals) nextHostItems
          alignedFlattened nextHostCanonical nextHostNonempty
          flatTargetMaterialCanonical
      have core := firstTransformation outer
        (hostLocals ++ tailBefore.locals) nextRename nextHostItems
        alignedFlattened flatTargetValidity.1 flatTargetValidity.2
      let flatTarget := Region.adjoinAt
        (hostLocals ++ tailBefore.locals) nextHostItems
        flatTargetMaterial
      let flatEndpoint := alignedFlattened.interface.withBody
        (alignedFlattened.context.fill flatTarget)
        flatTargetValidity.1 flatTargetValidity.2
      have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
          afterItem := by
        exact (RegionIso.adjoinAt
          (hostLocals ++ tailBefore.locals) nextHostItems (by
            simpa only [flatTargetMaterial, itemAfter, nextRename,
              hostWire] using
              (RegionIso.renameWiresComp firstAfter rename
                hostWire).symm)).trans
          ((RegionIso.adjoinAtConjoinLeft hostLocals activeHostItems
            tailBefore itemAfter).symm.trans
            (RegionIso.adjoinAt hostLocals activeHostItems
              (RegionIso.conjoinComm tailBefore itemAfter)))
      have flatPresentedTargetCanonical :
          (alignedFlattened.context.fill afterItem).Canonical := by
        exact itemPhaseValidity.1
      have flatPresentedTargetExternalTwoEnded :
          OpenDiagram.ExternalTwoEnded
            alignedFlattened.interface.boundaryWire
            (alignedFlattened.context.fill afterItem) := by
        intro signature wire
        exact itemPhaseValidity.2 wire
      have finalIso : OpenDiagramIso flatEndpoint
          (alignedFlattened.interface.withBody
            (alignedFlattened.context.fill afterItem)
            flatPresentedTargetCanonical
            flatPresentedTargetExternalTwoEnded) :=
        OpenDiagram.withBody_iso flatTargetValidity.1
          flatPresentedTargetCanonical flatTargetValidity.2
          flatPresentedTargetExternalTwoEnded
          (DiagramContext.fillIso alignedFlattened.context
            finalBodyIso)
      have presented : EqualityNormalization.StrictEquates
          alignedFlattened afterItem flatPresentedTargetCanonical
            flatPresentedTargetExternalTwoEnded :=
        EqualityNormalization.StrictEquates.targetIso core finalIso
      have outputIso : OpenDiagramIso
          (alignedFlattened.interface.withBody
            (alignedFlattened.context.fill afterItem)
            flatPresentedTargetCanonical
            flatPresentedTargetExternalTwoEnded)
          (sourceOccurrence.interface.withBody
            (sourceOccurrence.context.fill afterItem)
            itemPhaseValidity.1 itemPhaseValidity.2) :=
        OpenDiagram.withBody_iso flatPresentedTargetCanonical
          itemPhaseValidity.1 flatPresentedTargetExternalTwoEnded
          itemPhaseValidity.2 (RegionIso.refl _)
      have exactPresented : EqualityNormalization.StrictEquates
          sourceOccurrence afterItem itemPhaseValidity.1
            itemPhaseValidity.2 :=
        ⟨transGen_iso (OpenDiagramIso.refl activeSource)
            presented.1 outputIso,
          transGen_iso outputIso presented.2
            (OpenDiagramIso.refl activeSource)⟩
      simpa only [itemBefore, itemAfter, swapped, flattened,
        alignedFlattened, nextHostItems, hostWire, nextRename,
        flatTargetMaterial, flatTarget, flatEndpoint] using
          exactPresented
    let afterItemOccurrence : Occurrence afterItem
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill afterItem)
          itemPhaseValidity.1 itemPhaseValidity.2) :=
      exactOccurrence sourceOccurrence.interface sourceOccurrence.context
        afterItem itemPhaseValidity.1 itemPhaseValidity.2
    let flattened := EqualityNormalization.flattenAdjoinOccurrence
      hostLocals activeHostItems itemAfter tailBefore
      afterItemOccurrence hostCanonical hostNonempty itemAfterCanonical
      tailBeforeCanonical
    let nextHostItems := Region.extendHostItems hostLocals
      activeHostItems itemAfter
    let hostWire := Region.adjoinHostWire outer hostLocals
      itemAfter.locals
    let nextRename := WireRenaming.comp hostWire rename
    have nextHostCanonical :=
      EqualityNormalization.extendHostCanonical hostLocals
        activeHostItems itemAfter hostCanonical itemAfterCanonical
    have nextHostNonempty : ∀ {signature}
        (wire : Var outer signature),
        (Region.mk (hostLocals ++ itemAfter.locals)
          nextHostItems).incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact EqualityNormalization.extendHost_incidence_nonempty
        hostLocals activeHostItems itemAfter hostNonempty wire
    have secondBeforeCanonical : secondBefore.Canonical :=
      (Region.Canonical.renameWires_iff secondBefore rename).mp
        tailBeforeCanonical
    have alignedTailCanonical :
        (secondBefore.renameWires nextRename).Canonical :=
      (Region.Canonical.renameWires_iff secondBefore nextRename).mpr
        secondBeforeCanonical
    let alignedFlattened : Occurrence
        (Region.adjoinAt (hostLocals ++ itemAfter.locals)
          nextHostItems (secondBefore.renameWires nextRename))
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill afterItem)
          itemPhaseValidity.1 itemPhaseValidity.2) :=
      EqualityNormalization.supportedAdjoinOccurrence
        (hostLocals ++ itemAfter.locals) nextHostItems flattened
        nextHostCanonical nextHostNonempty alignedTailCanonical (by
          simpa only [tailBefore, hostWire, nextRename] using
            RegionIso.renameWiresComp secondBefore rename hostWire)
    have secondAfterCanonical : secondAfter.Canonical :=
      (Region.Canonical.renameWires_iff secondAfter rename).mp
        tailAfterCanonical
    let flatTargetMaterial := secondAfter.renameWires nextRename
    have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
      (Region.Canonical.renameWires_iff secondAfter nextRename).mpr
        secondAfterCanonical
    have tailTargetValidity :=
      EqualityNormalization.supportedAdjoinValidity
        (hostLocals ++ itemAfter.locals) nextHostItems
        alignedFlattened nextHostCanonical nextHostNonempty
        flatTargetMaterialCanonical
    have tailPhase := secondTransformation outer
      (hostLocals ++ itemAfter.locals) nextRename nextHostItems
      alignedFlattened tailTargetValidity.1 tailTargetValidity.2
    let flatTarget := Region.adjoinAt
      (hostLocals ++ itemAfter.locals) nextHostItems
      flatTargetMaterial
    let flatTargetEndpoint := alignedFlattened.interface.withBody
      (alignedFlattened.context.fill flatTarget)
      tailTargetValidity.1 tailTargetValidity.2
    have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
        (Region.adjoinAt hostLocals activeHostItems targetBefore) := by
      exact (RegionIso.adjoinAt
        (hostLocals ++ itemAfter.locals) nextHostItems (by
          simpa only [flatTargetMaterial, tailAfter, nextRename,
            hostWire] using
            (RegionIso.renameWiresComp secondAfter rename
              hostWire).symm)).trans
        ((RegionIso.adjoinAtConjoinLeft hostLocals activeHostItems
          itemAfter tailAfter).symm.trans
          (RegionIso.adjoinAt hostLocals activeHostItems (by
            simpa only [itemAfter, tailAfter, targetBefore] using
              (RegionIso.renameWiresConjoin firstAfter secondAfter
                rename).symm)))
    have finalIso : OpenDiagramIso flatTargetEndpoint
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems targetBefore))
          presentedTargetCanonical
          presentedTargetExternalTwoEnded) :=
      OpenDiagram.withBody_iso tailTargetValidity.1
        presentedTargetCanonical tailTargetValidity.2
        presentedTargetExternalTwoEnded
        (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
    have tailPhase' : EqualityNormalization.StrictEquates
        alignedFlattened
        (Region.adjoinAt hostLocals activeHostItems targetBefore)
        presentedTargetCanonical presentedTargetExternalTwoEnded :=
      EqualityNormalization.StrictEquates.targetIso tailPhase finalIso
    have itemPhase' : EqualityNormalization.StrictEquates
        sourceOccurrence afterItem itemPhaseValidity.1
          itemPhaseValidity.2 := by
      simpa only [afterItem, itemBefore, tailBefore, itemAfter,
        sourceOccurrence] using itemPhase
    have combined := EqualityNormalization.StrictEquates.trans
      (targetExternalTwoEnded := presentedTargetExternalTwoEnded)
      itemPhase' tailPhase'
    have outputIso : OpenDiagramIso
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems targetBefore))
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (activeOccurrence.interface.withBody
          (activeOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems targetBefore))
          activeTargetCanonical activeTargetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical
        activeTargetCanonical presentedTargetExternalTwoEnded
        activeTargetExternalTwoEnded (RegionIso.refl _)
    have exactCombined : EqualityNormalization.StrictEquates
        activeOccurrence
        (Region.adjoinAt hostLocals activeHostItems targetBefore)
        activeTargetCanonical activeTargetExternalTwoEnded :=
      ⟨transGen_iso (OpenDiagramIso.refl activeSource) combined.1
          outputIso,
        transGen_iso outputIso combined.2
          (OpenDiagramIso.refl activeSource)⟩
    simpa only [sourceMaterial, targetMaterial, itemBefore,
      tailBefore, itemAfter, tailAfter, sourceOccurrence, afterItem,
      afterItemOccurrence, flattened, alignedFlattened, nextHostItems,
      hostWire, nextRename, flatTargetMaterial, flatTarget,
      flatTargetEndpoint, targetBefore] using exactCombined
  by_cases nonempty : outer ++ hostLocals ≠ []
  · obtain ⟨pinnedSourceCanonical, pinnedSourceExternalTwoEnded,
        sourcePins⟩ :=
      EqualityNormalization.adjoinPinsEquatesNonempty hostLocals
        hostItems sourceMaterial occurrence nonempty
    let pinnedItems := hostItems.append
      (EqualityNormalization.contextPins outer hostLocals)
    let pinnedSource := Region.adjoinAt hostLocals pinnedItems
      sourceMaterial
    let pinnedSourceOccurrence : Occurrence pinnedSource
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context
        pinnedSource pinnedSourceCanonical pinnedSourceExternalTwoEnded
    have sourceLocalCanonical :
        (Region.adjoinAt hostLocals hostItems
          sourceMaterial).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have pinnedHostCanonical :
        (Region.mk hostLocals pinnedItems).Canonical :=
      EqualityNormalization.pinnedHostCanonical hostLocals hostItems
        sourceMaterial sourceLocalCanonical
    have pinnedHostNonempty : ∀ {signature}
        (wire : Var outer signature),
        (Region.mk hostLocals pinnedItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact EqualityNormalization.pinnedHost_incidence_nonempty
        hostLocals hostItems wire
    have targetLocalCanonical :
        (Region.adjoinAt hostLocals hostItems
          targetMaterial).Canonical :=
      occurrence.context.holeCanonical _ targetCanonical
    have targetMaterialCanonical : targetMaterial.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals hostItems _
        targetLocalCanonical
    have pinnedTargetValidity :=
      EqualityNormalization.supportedAdjoinValidity hostLocals
        pinnedItems pinnedSourceOccurrence pinnedHostCanonical
        pinnedHostNonempty targetMaterialCanonical
    have folded := supportedSequence pinnedItems pinnedSourceOccurrence
      pinnedHostCanonical pinnedHostNonempty pinnedTargetValidity.1
      pinnedTargetValidity.2
    let targetOccurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems targetMaterial)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context _
        targetCanonical targetExternalTwoEnded
    obtain ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded,
        targetPins⟩ :=
      EqualityNormalization.adjoinPinsEquatesNonempty hostLocals
        hostItems targetMaterial targetOccurrence nonempty
    have forwardPins : Relation.TransGen Step source
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using
        sourcePins.1
    have reversePins : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) source := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using
        sourcePins.2
    have middleForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using
        folded.1
    have middleReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using
        folded.2
    have unpinForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.2
    have unpinReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.1
    exact ⟨(forwardPins.trans middleForward).trans unpinForward,
      (unpinReverse.trans middleReverse).trans reversePins⟩
  · have empty : outer ++ hostLocals = [] :=
      Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] :=
      (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    have sourceLocalCanonical :
        (Region.adjoinAt [] hostItems sourceMaterial).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have hostCanonical : (Region.mk [] hostItems).Canonical := by
      have canonical := EqualityNormalization.pinnedHostCanonical
        ([] : List Sig) hostItems sourceMaterial sourceLocalCanonical
      simpa only [EqualityNormalization.contextPins,
        EqualityNormalization.allPins, List.nil_append,
        ItemSeq.pinWires, ItemSeq.nil_append,
        ItemSeq.append_nil] using canonical
    have hostNonempty : ∀ {signature} (wire : Var [] signature),
        (Region.mk [] hostItems).incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact Fin.elim0 wire.index
    simpa only [sourceMaterial, targetMaterial] using
      supportedSequence hostItems occurrence hostCanonical hostNonempty
        targetCanonical targetExternalTwoEnded

/-- Lift a hosted strict transformation beneath one cut. -/
theorem HostedStrict.cut
    {common : List Sig} (before after : Region common)
    (transformation : HostedStrict before after) :
    HostedStrict (Region.singleton (.cut before))
      (Region.singleton (.cut after)) := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let appendNil : WireRenaming common (common ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  let materialRename := Region.adjoinMaterialWire outer hostLocals []
  let childRename := WireRenaming.comp materialRename
    (WireRenaming.comp (rename.appendRight []) appendNil)
  let retained := hostItems.renameWires
    (Region.adjoinHostWire outer hostLocals [])
  let inner : DiagramContext outer (outer ++ (hostLocals ++ [])) :=
    .cut (hostLocals ++ []) retained .nil .hole
  have childRename_eq (region : Region common) :
      Region.renameWires materialRename
          (Region.renameWires (rename.appendRight [])
            (Region.renameWires appendNil region)) =
        Region.renameWires childRename region := by
    rw [Region.renameWires_comp, Region.renameWires_comp]
    apply congrArg (fun map => Region.renameWires map region)
    apply WireRenaming.ext
    intro signature wire
    rfl
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((Region.singleton (.cut before)).renameWires rename)
  let sourceAfter := inner.fill
    (before.renameWires childRename)
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    simp only [inner, retained, childRename, materialRename, appendNil,
      sourceBefore, sourceAfter, DiagramContext.fill,
      Region.renameWires, Region.singleton, Region.ofItems,
      Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
    rw [childRename_eq]
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have sourceNonempty : ∀ {signature} (wire : Var outer signature),
      sourceBefore.incidencePaths wire.index.val ≠ [] ↔
        sourceAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [sourceEq]
  let outerOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical sourceNonempty (by
        rw [← sourceEq]
        exact RegionIso.refl _)
  let childOccurrence := EqualityNormalization.Occurrence.nest
    outerOccurrence
  let targetBefore := Region.adjoinAt hostLocals hostItems
    ((Region.singleton (.cut after)).renameWires rename)
  let targetAfter := inner.fill
    (after.renameWires childRename)
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  have targetEq : targetBefore = targetAfter := by
    simp only [inner, retained, childRename, materialRename,
      appendNil, targetBefore, targetAfter, DiagramContext.fill,
      Region.renameWires, Region.singleton, Region.ofItems,
      Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
    rw [childRename_eq]
  have targetAfterCanonical : targetAfter.Canonical := by
    rw [← targetEq]
    exact occurrence.context.holeCanonical _ targetCanonical
  have targetNonempty : ∀ {signature} (wire : Var outer signature),
      targetBefore.incidencePaths wire.index.val ≠ [] ↔
        targetAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [targetEq]
  have targetReplacement := occurrence.context.replaceCanonical
    targetBefore targetAfter targetCanonical targetAfterCanonical
      targetNonempty
  let targetBeforeEndpoint := occurrence.interface.withBody
    (occurrence.context.fill targetBefore) targetCanonical
      targetExternalTwoEnded
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetAfter) :=
    targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
      targetReplacement.2
  have childTargetCanonical :
      (childOccurrence.context.fill
        (after.renameWires childRename)).Canonical := by
    simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
      DiagramContext.fill_comp, targetAfter] using
        targetReplacement.1
  have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      childOccurrence.interface.boundaryWire
      (childOccurrence.context.fill
        (after.renameWires childRename)) := by
    intro signature wire
    simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
      DiagramContext.fill_comp, targetAfter] using
        targetAfterExternalTwoEnded wire
  let childOuter := outer ++ (hostLocals ++ [])
  let childEmptyEquiv := WireEquiv.appendNil childOuter
  let childAppend : WireRenaming childOuter (childOuter ++ []) :=
    childEmptyEquiv.symm.toRenaming
  let hostedChildRename := WireRenaming.comp childAppend childRename
  let emptyHostIso (region : Region common) :
      RegionIso (WireEquiv.refl childOuter)
        (region.renameWires childRename)
        (Region.adjoinAt [] .nil
          (region.renameWires hostedChildRename)) := by
    let directToCollapsed := RegionIso.renameWires region childRename
      (WireRenaming.comp childEmptyEquiv.toRenaming
        hostedChildRename)
      (WireEquiv.refl childOuter) (by
        intro signature wire
        exact (childEmptyEquiv.right_inv (childRename wire)).symm)
    let collapsedFromHosted :=
      (RegionIso.renameWiresComp region hostedChildRename
        childEmptyEquiv.toRenaming).symm
    exact (directToCollapsed.trans collapsedFromHosted).trans
      (RegionIso.adjoinAtNil
        (region.renameWires hostedChildRename))
  let sourceHosted := Region.adjoinAt [] .nil
    (before.renameWires hostedChildRename)
  let sourcePresentation : RegionIso (WireEquiv.refl childOuter)
      (before.renameWires childRename) sourceHosted :=
    emptyHostIso before
  have sourceHostedCanonical : sourceHosted.Canonical :=
    sourcePresentation.canonical_iff.mp
      (childOccurrence.context.holeCanonical _
        childOccurrence.sourceCanonical)
  have sourceHostedNonempty : ∀ {signature}
      (wire : Var childOuter signature),
      (before.renameWires childRename).incidencePaths
          wire.index.val ≠ [] ↔
        sourceHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourcePresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let presentedChildOccurrence : Occurrence sourceHosted source :=
    EqualityNormalization.presentationOccurrence childOccurrence
      sourceHostedCanonical sourceHostedNonempty sourcePresentation
  let targetHosted := Region.adjoinAt [] .nil
    (after.renameWires hostedChildRename)
  let targetPresentation : RegionIso (WireEquiv.refl childOuter)
      (after.renameWires childRename) targetHosted :=
    emptyHostIso after
  have targetHostedCanonical : targetHosted.Canonical :=
    targetPresentation.canonical_iff.mp
      (childOccurrence.context.holeCanonical _ childTargetCanonical)
  have targetHostedNonempty : ∀ {signature}
      (wire : Var childOuter signature),
      (after.renameWires childRename).incidencePaths
          wire.index.val ≠ [] ↔
        targetHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := targetPresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have targetHostedReplacement :=
    childOccurrence.context.replaceCanonical
      (after.renameWires childRename) targetHosted
      childTargetCanonical targetHostedCanonical targetHostedNonempty
  let childTargetEndpoint := childOccurrence.interface.withBody
    (childOccurrence.context.fill
      (after.renameWires childRename))
    childTargetCanonical childTargetExternalTwoEnded
  have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      childOccurrence.interface.boundaryWire
      (childOccurrence.context.fill targetHosted) :=
    childTargetEndpoint.externalTwoEnded_of_nonempty_iff _
      targetHostedReplacement.2
  have presentedTargetCanonical :
      (presentedChildOccurrence.context.fill targetHosted).Canonical := by
    exact targetHostedReplacement.1
  have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedChildOccurrence.interface.boundaryWire
      (presentedChildOccurrence.context.fill targetHosted) := by
    intro signature wire
    exact targetHostedExternalTwoEnded wire
  have childStrict := transformation childOuter [] hostedChildRename .nil
    presentedChildOccurrence presentedTargetCanonical
      presentedTargetExternalTwoEnded
  let hostedToDirect : OpenDiagramIso
      (presentedChildOccurrence.interface.withBody
        (presentedChildOccurrence.context.fill targetHosted)
        presentedTargetCanonical presentedTargetExternalTwoEnded)
      (childOccurrence.interface.withBody
        (childOccurrence.context.fill
          (after.renameWires childRename))
        childTargetCanonical childTargetExternalTwoEnded) :=
    OpenDiagram.withBody_iso presentedTargetCanonical
      childTargetCanonical presentedTargetExternalTwoEnded
      childTargetExternalTwoEnded
      (DiagramContext.fillIso childOccurrence.context
        targetPresentation.symm)
  have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
      targetBefore := by
    rw [← targetEq]
    exact RegionIso.refl _
  have outerFinalIso : OpenDiagramIso
      (outerOccurrence.interface.withBody
        (outerOccurrence.context.fill targetAfter)
        targetReplacement.1 targetAfterExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetReplacement.1 targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context finalBodyIso)
  have directToOuter : OpenDiagramIso
      (childOccurrence.interface.withBody
        (childOccurrence.context.fill
          (after.renameWires childRename))
        childTargetCanonical childTargetExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded) := by
    simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
      DiagramContext.fill_comp, targetAfter] using outerFinalIso
  let finalIso := hostedToDirect.trans directToOuter
  exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
      finalIso,
    transGen_iso finalIso childStrict.2
      (OpenDiagramIso.refl source)⟩



/-- Move the support completion of a singleton cut from outside the cut to
the child body. The equivalence is stable under every enclosing host and wire
substitution used by the structural accumulator. -/
theorem supportCutHosted
    (body : Region materialWires) (bodyCanonical : body.Canonical) :
    HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.singleton (.cut body))
          ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
        (EqualityNormalization.formalPorts materialWires))
      (Region.singleton (.cut
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern body bodyCanonical)
          (EqualityNormalization.formalPorts materialWires)))) := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  apply EqualityNormalization.withPinnedEnvelope occurrence targetCanonical
    targetExternalTwoEnded
  intro pinnedSourceCanonical pinnedSourceExternalTwoEnded
  let outerMaterial := Region.singleton (.cut body)
  let outerCanonical : outerMaterial.Canonical :=
    (Region.singleton_cut_canonical_iff body).mpr bodyCanonical
  let outerPattern := Erasure.Exposure.supportPattern outerMaterial
    outerCanonical
  let childPattern := Erasure.Exposure.supportPattern body bodyCanonical
  let before :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      outerPattern (EqualityNormalization.formalPorts materialWires)
  let after := Region.singleton (.cut
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      childPattern (EqualityNormalization.formalPorts materialWires)))
  let pinnedItems := hostItems.append
    (EqualityNormalization.contextPins outer hostLocals)
  let pinnedOccurrence := exactOccurrence
    occurrence.interface occurrence.context
    (Region.adjoinAt hostLocals pinnedItems (before.renameWires rename))
    pinnedSourceCanonical pinnedSourceExternalTwoEnded
  have sourceLocalCanonical :
      (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename)).Canonical := by
    simpa only [before, outerPattern, outerCanonical, outerMaterial] using
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have pinnedHostCanonical :
      (Region.mk hostLocals pinnedItems).Canonical := by
    simpa only [pinnedItems] using
      EqualityNormalization.pinnedHostCanonical hostLocals hostItems
        (before.renameWires rename) sourceLocalCanonical
  have pinnedHostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals pinnedItems).incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    simpa only [pinnedItems] using
      EqualityNormalization.pinnedHost_incidence_nonempty hostLocals
        hostItems wire
  have mappedBodyCanonical : (body.renameWires rename).Canonical :=
    (Region.Canonical.renameWires_iff body rename).mpr bodyCanonical
  let directMaterial := Region.singleton (.cut (body.renameWires rename))
  have directMaterialCanonical : directMaterial.Canonical := by
    exact (Region.singleton_cut_canonical_iff _).mpr mappedBodyCanonical
  obtain ⟨directCanonical, directExternalTwoEnded⟩ :=
    EqualityNormalization.supportedAdjoinValidity hostLocals pinnedItems
      pinnedOccurrence pinnedHostCanonical pinnedHostNonempty
      directMaterialCanonical
  let direct := Region.adjoinAt hostLocals pinnedItems directMaterial
  let directOccurrence := exactOccurrence
    occurrence.interface occurrence.context direct directCanonical
      directExternalTwoEnded
  let outerDescription : Rule.Erasure.Description outer := {
    materialWires := materialWires
    hostLocals := hostLocals
    hostItems := pinnedItems
    material := outerMaterial
    wireMap := rename
  }
  have outerSourceEq : outerDescription.source = direct := by
    simp [outerDescription, Rule.Erasure.Description.source,
      Region.spliceAt, direct, directMaterial, outerMaterial,
      Region.singleton_renameWires, Item.renameWires]
  have outerTargetEq : outerDescription.target =
      Region.mk hostLocals pinnedItems := by
    rfl
  have outerExposedEq : ∀ materialCanonical :
      outerDescription.material.Canonical,
      Erasure.Exposure.exposedRegion outerDescription materialCanonical =
        Region.adjoinAt hostLocals pinnedItems
          (before.renameWires rename) := by
    intro materialCanonical
    simp only [Erasure.Exposure.exposedRegion, outerDescription,
      Erasure.Exposure.applicationPorts]
    change Region.adjoinAt hostLocals pinnedItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern outerMaterial materialCanonical)
          ((Erasure.Exposure.identityBoundary materialWires).map
            (fun wire => rename wire))) = _
    have canonicalEq : materialCanonical = outerCanonical :=
      Subsingleton.elim _ _
    subst materialCanonical
    simpa only [before, outerPattern, EqualityNormalization.formalPorts,
      EqualityNormalization.instantiate_renameWires]
  obtain ⟨outerExposedCanonical, outerExposedExternalTwoEnded,
      outerEquates⟩ := EqualityNormalization.pinnedExposureCore
    directOccurrence outerDescription outerSourceEq outerTargetEq
      outerExposedEq
  let innerContext : DiagramContext outer (outer ++ hostLocals) :=
    .cut hostLocals pinnedItems .nil .hole
  let innerDirect := innerContext.fill (body.renameWires rename)
  let directPresentation : RegionIso (WireEquiv.refl outer)
      direct innerDirect := by
    simpa only [direct, directMaterial, innerDirect, innerContext,
      DiagramContext.fill, ItemSeq.append_nil] using
      RegionIso.adjoinAtSingleton hostLocals pinnedItems
        (.cut (body.renameWires rename))
  let fullDirectPresentation :=
    occurrence.context.fillIso directPresentation
  have innerDirectCanonical :
      (occurrence.context.fill innerDirect).Canonical :=
    fullDirectPresentation.canonical_iff.mp directCanonical
  have innerDirectExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
        (occurrence.context.fill innerDirect) := by
    intro signature wire
    rw [← fullDirectPresentation.incidencePaths_length_eq wire]
    exact directExternalTwoEnded wire
  let nestedContext := occurrence.context.comp innerContext
  let directEndpoint := occurrence.interface.withBody
    (occurrence.context.fill direct) directCanonical directExternalTwoEnded
  let childOccurrence : Occurrence (body.renameWires rename)
      directEndpoint := {
    interface := occurrence.interface
    context := nestedContext
    sourceCanonical := by
      simpa only [nestedContext, DiagramContext.fill_comp, innerDirect,
        directEndpoint] using innerDirectCanonical
    sourceExternalTwoEnded := by
      intro signature wire
      simpa only [nestedContext, DiagramContext.fill_comp, innerDirect,
        directEndpoint] using innerDirectExternalTwoEnded wire
    host_iso := by
      simpa only [nestedContext, DiagramContext.fill_comp, innerDirect,
        directEndpoint] using
        OpenDiagram.withBody_iso directCanonical innerDirectCanonical
          directExternalTwoEnded innerDirectExternalTwoEnded
          fullDirectPresentation
  }
  let childWireMap : WireRenaming materialWires
      ((outer ++ hostLocals) ++ []) :=
    WireRenaming.comp
      (WireEquiv.appendNil (outer ++ hostLocals)).symm.toRenaming rename
  have spliceNilRename (material : Region materialWires) :
      Region.spliceAt [] .nil material childWireMap =
        material.renameWires rename := by
    cases material with
    | mk locals items =>
        simp only [Region.spliceAt, Region.adjoinAt, Region.renameWires,
          ItemSeq.renameWires, ItemSeq.nil_append]
        rw [ItemSeq.renameWires_comp]
        have mapEq : WireRenaming.comp
            (Region.adjoinMaterialWire (outer ++ hostLocals) [] locals)
            (childWireMap.appendRight locals) =
              rename.appendRight locals := by
          apply WireRenaming.ext
          intro signature wire
          apply Var.appendCases (left := materialWires) (right := locals)
            (motive := fun wire =>
              WireRenaming.comp
                (Region.adjoinMaterialWire (outer ++ hostLocals) [] locals)
                (childWireMap.appendRight locals) wire =
                  rename.appendRight locals wire)
            (fun inherited => by
              simp [childWireMap, WireRenaming.appendRight,
                WireRenaming.comp, Region.adjoinMaterialWire])
            (fun localWire => by
              simp only [childWireMap, WireRenaming.appendRight,
                WireRenaming.comp, Region.adjoinMaterialWire,
                Var.appendMap_right]
              change Var.appendRight (outer ++ hostLocals)
                  (Var.appendRight [] localWire) =
                Var.appendRight (outer ++ hostLocals) localWire
              rfl) wire
        rw [mapEq]
        simp only [List.nil_append]
  let childDescription : Rule.Erasure.Description (outer ++ hostLocals) := {
    materialWires := materialWires
    hostLocals := []
    hostItems := .nil
    material := body
    wireMap := childWireMap
  }
  have childSourceEq : childDescription.source = body.renameWires rename := by
    simpa only [childDescription, Rule.Erasure.Description.source] using
      spliceNilRename body
  let erasedChildMaterial :=
    Region.singleton (.cut (Region.blank (outer ++ hostLocals)))
  have erasedChildMaterialCanonical : erasedChildMaterial.Canonical := by
    apply (Region.singleton_cut_canonical_iff _).mpr
    exact ⟨fun localIndex => Fin.elim0 localIndex, True.intro⟩
  obtain ⟨erasedChildCanonical, erasedChildExternalTwoEnded⟩ :=
    EqualityNormalization.supportedAdjoinValidity hostLocals pinnedItems
      pinnedOccurrence pinnedHostCanonical pinnedHostNonempty
      erasedChildMaterialCanonical
  let erasedChild := Region.adjoinAt hostLocals pinnedItems erasedChildMaterial
  let innerErased := innerContext.fill childDescription.target
  let erasedPresentation : RegionIso (WireEquiv.refl outer)
      erasedChild innerErased := by
    simpa only [erasedChild, erasedChildMaterial, innerErased, innerContext,
      childDescription, Rule.Erasure.Description.target,
      DiagramContext.fill, ItemSeq.append_nil] using
      RegionIso.adjoinAtSingleton hostLocals pinnedItems
        (.cut (Region.blank (outer ++ hostLocals)))
  let fullErasedPresentation :=
    occurrence.context.fillIso erasedPresentation
  have erasedChildCanonical' :
      (childOccurrence.context.fill childDescription.target).Canonical := by
    have presented := fullErasedPresentation.canonical_iff.mp
      erasedChildCanonical
    simpa only [childOccurrence, nestedContext, DiagramContext.fill_comp,
      innerErased] using presented
  have erasedChildExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      childOccurrence.interface.boundaryWire
      (childOccurrence.context.fill childDescription.target) := by
    have presented : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill innerErased) := by
      intro signature wire
      rw [← fullErasedPresentation.incidencePaths_length_eq wire]
      exact erasedChildExternalTwoEnded wire
    intro signature wire
    simpa only [childOccurrence, nestedContext, DiagramContext.fill_comp,
      innerErased] using presented wire
  let childAfter :=
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      childPattern (EqualityNormalization.formalPorts materialWires)).renameWires
        rename
  let childExposed :=
    Erasure.Exposure.exposedRegion childDescription bodyCanonical
  have childExposedEq : ∀ materialCanonical :
      childDescription.material.Canonical,
      Erasure.Exposure.exposedRegion childDescription materialCanonical =
        childExposed := by
    intro materialCanonical
    have canonicalEq : materialCanonical = bodyCanonical := Subsingleton.elim _ _
    subst materialCanonical
    rfl
  obtain ⟨childExposedCanonical, childExposedExternalTwoEnded,
      childEquates⟩ := EqualityNormalization.exposureCore childOccurrence
    childDescription childSourceEq erasedChildCanonical'
      erasedChildExternalTwoEnded' childExposedEq
  let rawChildExposed :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      childPattern
      ((Erasure.Exposure.identityBoundary materialWires).map
        (fun wire => childWireMap wire))
  let collapse := WireEquiv.appendNil (outer ++ hostLocals)
  have rawChildExposedEq : rawChildExposed.renameWires collapse.toRenaming =
      childAfter := by
    rw [EqualityNormalization.instantiate_renameWires]
    simp only [childAfter]
    rw [EqualityNormalization.instantiate_renameWires]
    simp only [rawChildExposed, childPattern,
      EqualityNormalization.formalPorts, collapse, Vars.map_map]
    congr 1
    apply Vars.map_congr
    intro signature wire
    exact collapse.right_inv (rename wire)
  let childExposedPresentation : RegionIso
      (WireEquiv.refl (outer ++ hostLocals)) childExposed childAfter := by
    let adjoining := RegionIso.adjoinAtNil rawChildExposed
    simpa only [childExposed, Erasure.Exposure.exposedRegion,
      childDescription, Erasure.Exposure.applicationPorts,
      rawChildExposed, collapse] using
      adjoining.symm.trans (RegionIso.ofEq rawChildExposedEq)
  let pinnedAfter := Region.adjoinAt hostLocals pinnedItems
    (after.renameWires rename)
  let innerAfter := innerContext.fill childAfter
  let afterPresentation : RegionIso (WireEquiv.refl outer)
      pinnedAfter innerAfter := by
    simpa only [pinnedAfter, after, Region.singleton_renameWires,
      Item.renameWires, childAfter, innerAfter, innerContext,
      DiagramContext.fill, ItemSeq.append_nil] using
      RegionIso.adjoinAtSingleton hostLocals pinnedItems (.cut childAfter)
  let fullAfterPresentation :=
    occurrence.context.fillIso afterPresentation
  let fullChildPresentation :=
    nestedContext.fillIso childExposedPresentation
  let targetPresentation : RegionIso
      (WireEquiv.refl occurrence.interface.external)
      (occurrence.context.fill pinnedAfter)
      (nestedContext.fill childExposed) := by
    let alignedAfter : RegionIso
        (WireEquiv.refl occurrence.interface.external)
        (occurrence.context.fill pinnedAfter)
        (nestedContext.fill childAfter) := by
      simpa only [nestedContext, DiagramContext.fill_comp, innerAfter] using
        fullAfterPresentation
    exact alignedAfter.trans fullChildPresentation.symm
  have pinnedTargetCanonical :
      (occurrence.context.fill pinnedAfter).Canonical := by
    apply targetPresentation.canonical_iff.mpr
    simpa only [childOccurrence] using childExposedCanonical
  have pinnedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill pinnedAfter) := by
    intro signature wire
    rw [targetPresentation.incidencePaths_length_eq wire]
    simpa only [childOccurrence] using childExposedExternalTwoEnded wire
  let pinnedTargetEndpoint := occurrence.interface.withBody
    (occurrence.context.fill pinnedAfter) pinnedTargetCanonical
      pinnedTargetExternalTwoEnded
  let childTargetEndpoint := occurrence.interface.withBody
    (nestedContext.fill childExposed) childExposedCanonical
      childExposedExternalTwoEnded
  let afterIso : OpenDiagramIso pinnedTargetEndpoint childTargetEndpoint :=
    OpenDiagram.withBody_iso pinnedTargetCanonical childExposedCanonical
      pinnedTargetExternalTwoEnded childExposedExternalTwoEnded
      targetPresentation
  refine ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded, ?_⟩
  constructor
  · have first : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems (before.renameWires rename)))
          pinnedSourceCanonical pinnedSourceExternalTwoEnded)
        directEndpoint := by
      simpa only [pinnedOccurrence, exactOccurrence, directOccurrence,
        directEndpoint, before, outerPattern, outerCanonical, outerMaterial]
        using outerEquates.2
    have second : Relation.ReflTransGen Step directEndpoint
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedAfter) pinnedTargetCanonical
            pinnedTargetExternalTwoEnded) := by
      have raw : Relation.ReflTransGen Step directEndpoint
          childTargetEndpoint := by
        simpa only [childOccurrence, directEndpoint, childTargetEndpoint,
          nestedContext] using
          childEquates.1
      simpa only [pinnedTargetEndpoint] using
        EqualityNormalization.reflTransGen_iso (OpenDiagramIso.refl _)
          raw afterIso.symm
    exact first.trans second
  · have first : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedAfter) pinnedTargetCanonical
            pinnedTargetExternalTwoEnded) directEndpoint := by
      have raw : Relation.ReflTransGen Step childTargetEndpoint
          directEndpoint := by
        simpa only [childOccurrence, directEndpoint, childTargetEndpoint,
          nestedContext] using
          childEquates.2
      simpa only [pinnedTargetEndpoint] using
        EqualityNormalization.reflTransGen_iso afterIso.symm raw
          (OpenDiagramIso.refl _)
    have second : Relation.ReflTransGen Step directEndpoint
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems (before.renameWires rename)))
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) := by
      simpa only [pinnedOccurrence, exactOccurrence, directOccurrence,
        directEndpoint, before, outerPattern, outerCanonical, outerMaterial]
        using outerEquates.1
    exact first.trans second

/-- The support-cut bridge at an arbitrary selected application. -/
theorem supportCutInstantiatedHosted
    (body : Region materialWires) (bodyCanonical : body.Canonical)
    (application : Vars wires materialWires) :
    HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.singleton (.cut body))
          ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
        application)
      (Region.singleton (.cut
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern body bodyCanonical)
          application))) := by
  let baseRename := EqualityNormalization.formalSubstitution application
  apply HostedStrict.specialize (supportCutHosted body bodyCanonical)
    baseRename
  · simpa only [baseRename,
      EqualityNormalization.instantiate_renameWires,
      EqualityNormalization.formalPorts_map_substitution]
  · simp only [Region.singleton_renameWires, Item.renameWires]
    congr 2
    simpa only [baseRename,
      EqualityNormalization.instantiate_renameWires,
      EqualityNormalization.formalPorts_map_substitution]

def TargetRegion
    {targetArguments targetExternal common sourceWires targetWires originalArguments
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram originalArguments}
    {originalFrame : Transform.Frame originalArguments common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation originalArguments}
    {data : operation.Data originalFrame}
    {source : Region originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (_sites : RegionSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetFrame : Transform.Frame targetArguments
      common sourceWires targetWires)
    (targetData : targetOperation.Data targetFrame)
    (K : ∀ (formalSource : Region sourceWires)
        (formalResult : Region common)
        (formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
            targetPattern targetFrame.sourceKeep targetFrame.selected
            formalSource formalResult)
        (formalSites : RegionSites
          (recordingOperation targetOperation targetExternal) targetData
          formalEvidence),
        formalSource =
          (argumentRegionEdit formalSites targetValues
            (normalizationOperation targetArguments) targetFrame
            PUnit.unit (fun _ _ _ => PUnit.unit)).1 → Prop) : Prop :=
  ∃ formalSource : Region sourceWires,
    ∃ formalResult : Region common,
      ∃ formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
            targetPattern targetFrame.sourceKeep targetFrame.selected
            formalSource formalResult,
        ∃ formalSites : RegionSites
            (recordingOperation targetOperation targetExternal) targetData
            formalEvidence,
          ∃ coherence : formalSource =
              (argumentRegionEdit formalSites targetValues
                (normalizationOperation targetArguments) targetFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1,
            K formalSource formalResult formalEvidence formalSites coherence

def TargetItems
    {targetArguments targetExternal common sourceWires targetWires originalArguments
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram originalArguments}
    {originalFrame : Transform.Frame originalArguments common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation originalArguments}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (_sites : ItemsSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetFrame : Transform.Frame targetArguments
      common sourceWires targetWires)
    (targetData : targetOperation.Data targetFrame)
    (K : ∀ (retained : List Sig)
        (formalSource : ItemSeq (sourceWires ++ retained))
        (formalResult : Region (common ++ retained))
        (formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern (targetFrame.append retained).sourceKeep
            (targetFrame.append retained).selected formalSource formalResult)
        (formalSites : ItemsSites
          (recordingOperation targetOperation targetExternal)
          (targetOperation.appendData targetFrame targetData retained)
          formalEvidence),
        formalSource =
          (argumentItemsEdit formalSites targetValues
            (normalizationOperation targetArguments)
            (targetFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 → Prop) : Prop :=
  ∃ retained : List Sig,
    ∃ formalSource : ItemSeq (sourceWires ++ retained),
      ∃ formalResult : Region (common ++ retained),
        ∃ formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              targetPattern
              (targetFrame.append retained).sourceKeep
              (targetFrame.append retained).selected
              formalSource formalResult,
          ∃ formalSites : ItemsSites
              (recordingOperation targetOperation targetExternal)
              (targetOperation.appendData targetFrame targetData retained)
              formalEvidence,
            ∃ coherence : formalSource =
                (argumentItemsEdit formalSites targetValues
                  (normalizationOperation targetArguments)
                  (targetFrame.append retained) PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1,
              K retained formalSource formalResult formalEvidence formalSites
                coherence

def TargetItem
    {targetArguments targetExternal common sourceWires targetWires originalArguments
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram originalArguments}
    {originalFrame : Transform.Frame originalArguments common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation originalArguments}
    {data : operation.Data originalFrame}
    {source : Item originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (_sites : ItemSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetFrame : Transform.Frame targetArguments
      common sourceWires targetWires)
    (targetData : targetOperation.Data targetFrame)
    (K : ∀ (retained : List Sig)
        (formalSource : ItemSeq (sourceWires ++ retained))
        (formalResult : Region (common ++ retained))
        (formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern (targetFrame.append retained).sourceKeep
            (targetFrame.append retained).selected formalSource formalResult)
        (formalSites : ItemsSites
          (recordingOperation targetOperation targetExternal)
          (targetOperation.appendData targetFrame targetData retained)
          formalEvidence),
        formalSource =
          (argumentItemsEdit formalSites targetValues
            (normalizationOperation targetArguments)
            (targetFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 → Prop) : Prop :=
  ∃ retained : List Sig,
    ∃ formalSource : ItemSeq (sourceWires ++ retained),
      ∃ formalResult : Region (common ++ retained),
        ∃ formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              targetPattern
              (targetFrame.append retained).sourceKeep
              (targetFrame.append retained).selected
              formalSource formalResult,
          ∃ formalSites : ItemsSites
              (recordingOperation targetOperation targetExternal)
              (targetOperation.appendData targetFrame targetData retained)
              formalEvidence,
            ∃ coherence : formalSource =
                (argumentItemsEdit formalSites targetValues
                  (normalizationOperation targetArguments)
                  (targetFrame.append retained) PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1,
              K retained formalSource formalResult formalEvidence formalSites
                coherence

/-- The singleton-atom selected-site premise consumed by the shared target
fold. It is nonrecursive: all recursive traversal remains owned by the existing
Instantiation/Sites induction. -/
theorem atomSelectedTargetItem
    {patternWires atomArguments itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {itemFrame : Transform.Frame patternWires itemCommon
      itemSourceWires itemTargetWires}
    {itemOperation : Transform.Operation patternWires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon patternWires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame (positionalAtomWires atomArguments)
      itemCommon formalSourceWires formalTargetWires) :
    TargetItem
      (targetPattern := positionalAtomPattern atomArguments)
      (targetOperation := Leaf.Formal.operation [] atomArguments)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := pattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := pattern) (frame := itemFrame) application siteData)
      (positionalAtomSelection head ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern application) staged ∧
            ScopePreservation
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult))) := by
      unfold TargetItem
      let retainedLocals := EqualityNormalization.locals pattern
      let childFrame := formalFrame.append retainedLocals
      let hostItems := atomSiteHostItems pattern tail application
      let formal : Var (itemCommon ++ retainedLocals)
          (.rel atomArguments) := atomBodyWire pattern itemCommon head
      let retainedPorts : Vars (itemCommon ++ retainedLocals)
          atomArguments :=
        ports.map fun wire => atomBodyWire pattern itemCommon wire
      let formalSource := atomFormalPrefixSource childFrame hostItems formal
        retainedPorts
      let formalResult := atomFormalPrefixResult hostItems formal retainedPorts
      let formalEvidence := atomFormalPrefixEvidence childFrame hostItems formal
        retainedPorts
      let childApplication : Vars (itemCommon ++ retainedLocals)
          pattern.external :=
        (Erasure.Exposure.identityBoundary pattern.external).map
          (fun wire => atomBodyWire pattern itemCommon wire)
      let formalSites := atomFormalPrefixRecordingSites childFrame hostItems
        formal retainedPorts childApplication
      refine ⟨retainedLocals, formalSource, formalResult, formalEvidence,
        formalSites, ?_, ?_⟩
      · let rename := atomBodyWire pattern itemCommon
        apply atomFormalPrefixSource_eq_argumentItemsEdit childFrame
          hostItems formal retainedPorts childApplication
          (positionalAtomSelection head ports) rename
        · rfl
        · rfl
      let staged := Region.adjoinAt retainedLocals .nil formalResult
      have hosted : HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) staged := by
        intro outer hostLocals rename outerHostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let mappedApplication := application.map fun wire => rename wire
        let sourceBefore :=
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename
        let sourceAfter :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern mappedApplication
        let sourceHostBefore := Region.adjoinAt hostLocals outerHostItems
          sourceBefore
        let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems
          sourceAfter
        change Occurrence sourceHostBefore source at hostedOccurrence
        have sourceHostEq : sourceHostBefore = sourceHostAfter := by
          simp only [sourceHostBefore, sourceHostAfter, sourceBefore,
            sourceAfter, mappedApplication,
            EqualityNormalization.instantiate_renameWires]
        have sourceAfterCanonical : sourceHostAfter.Canonical := by
          rw [← sourceHostEq]
          exact hostedOccurrence.context.holeCanonical _
            hostedOccurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceHostEq]
        let presentedOccurrence : Occurrence sourceHostAfter source :=
          EqualityNormalization.presentationOccurrence hostedOccurrence
            sourceAfterCanonical sourceNonempty
            (RegionIso.adjoinAt hostLocals outerHostItems
              (EqualityNormalization.instantiateRenameIso pattern
                application rename))
        let mappedHostItems := atomSiteHostItems pattern tail
          mappedApplication
        let mappedFormal : Var
            ((outer ++ hostLocals) ++ retainedLocals)
            (.rel atomArguments) :=
          atomBodyWire pattern (outer ++ hostLocals) head
        let mappedRetainedPorts : Vars
            ((outer ++ hostLocals) ++ retainedLocals) atomArguments :=
          ports.map fun wire =>
            atomBodyWire pattern (outer ++ hostLocals) wire
        let mappedFormalResult := atomFormalPrefixResult mappedHostItems
          mappedFormal mappedRetainedPorts
        let targetAfter := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil mappedFormalResult)
        obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
            outputCanonical, outputExternalTwoEnded, outputStrict⟩ :=
          accumulateSelectedAtomFormal body_eq outerHostItems
            mappedApplication presentedOccurrence
        change EqualityNormalization.StrictEquates presentedOccurrence
          targetAfter ownedCanonical ownedExternalTwoEnded at ownedStrict
        let retainedRename :=
          rename.appendRight (EqualityNormalization.locals pattern)
        have hostItemsEq : hostItems.renameWires retainedRename =
            mappedHostItems := by
          simpa only [hostItems, mappedHostItems, mappedApplication,
            retainedLocals, retainedRename] using
            atomSiteHostItems_renameWires pattern tail application rename
        have formalEq : retainedRename formal = mappedFormal := by
          have natural := congrArg
            (fun embedding : WireRenaming pattern.external
                ((outer ++ hostLocals) ++
                  EqualityNormalization.locals pattern) =>
              embedding head)
            (atomBodyWire_natural pattern rename)
          simpa only [formal, mappedFormal, retainedLocals, retainedRename,
            WireRenaming.comp] using natural
        have retainedPortsEq :
            retainedPorts.map (fun wire => retainedRename wire) =
              mappedRetainedPorts := by
          calc
            _ = ports.map (fun wire =>
                retainedRename (atomBodyWire pattern itemCommon wire)) :=
              Diagram.vars_map_comp ports (atomBodyWire pattern itemCommon)
                retainedRename
            _ = ports.map (fun wire =>
                atomBodyWire pattern (outer ++ hostLocals) wire) := by
              simpa only [WireRenaming.comp] using congrArg
                (fun embedding : WireRenaming pattern.external
                    ((outer ++ hostLocals) ++
                      EqualityNormalization.locals pattern) =>
                  ports.map fun wire => embedding wire)
                (atomBodyWire_natural pattern rename)
            _ = mappedRetainedPorts := rfl
        have formalResultEq : formalResult.renameWires retainedRename =
            mappedFormalResult := by
          calc
            _ = atomFormalPrefixResult
                (hostItems.renameWires retainedRename)
                (retainedRename formal)
                (retainedPorts.map fun wire => retainedRename wire) :=
              atomFormalPrefixResult_renameWires hostItems formal
                retainedPorts retainedRename
            _ = mappedFormalResult := by
              rw [hostItemsEq, formalEq, retainedPortsEq]
        let targetBefore := Region.adjoinAt hostLocals outerHostItems
          (staged.renameWires rename)
        have targetEq : targetBefore = targetAfter := by
          simp only [targetBefore, targetAfter, staged,
            Region.renameWires_adjoinAt_nil, retainedLocals]
          rw [formalResultEq]
        let targetPresentation : RegionIso (WireEquiv.refl outer)
            targetAfter targetBefore := RegionIso.ofEq targetEq.symm
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetBefore).Canonical := by
          exact targetCanonical
        have presentedTargetExternalTwoEnded :
            OpenDiagram.ExternalTwoEnded
              presentedOccurrence.interface.boundaryWire
              (presentedOccurrence.context.fill targetBefore) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        let ownedTargetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              ownedCanonical ownedExternalTwoEnded)
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso ownedCanonical presentedTargetCanonical
            ownedExternalTwoEnded presentedTargetExternalTwoEnded
            (DiagramContext.fillIso presentedOccurrence.context
              targetPresentation)
        have presentedStrict : EqualityNormalization.StrictEquates
            presentedOccurrence targetBefore presentedTargetCanonical
              presentedTargetExternalTwoEnded := by
          exact EqualityNormalization.StrictEquates.targetIso ownedStrict
            ownedTargetIso
        let targetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (hostedOccurrence.interface.withBody
              (hostedOccurrence.context.fill targetBefore)
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded
            (RegionIso.refl
              (presentedOccurrence.context.fill targetBefore))
        exact ⟨transGen_iso (OpenDiagramIso.refl source)
            presentedStrict.1 targetIso,
          transGen_iso targetIso presentedStrict.2
            (OpenDiagramIso.refl source)⟩
      /- The deterministic edit endpoint is deliberately outside the semantic
      accumulator; leaf consumers prepare it at the primitive boundary.
      let outputStaged := Region.adjoinAt retainedLocals .nil
        (output.endpoint.renameWires (targetRename.appendRight retainedLocals))
      have outputHosted : HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged := by
        intro outer hostLocals rename outerHostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let mappedApplication := application.map fun wire => rename wire
        let sourceBefore :=
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename
        let sourceAfter :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern mappedApplication
        let sourceHostBefore := Region.adjoinAt hostLocals outerHostItems
          sourceBefore
        let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems
          sourceAfter
        change Occurrence sourceHostBefore source at hostedOccurrence
        have sourceHostEq : sourceHostBefore = sourceHostAfter := by
          simp only [sourceHostBefore, sourceHostAfter, sourceBefore,
            sourceAfter, mappedApplication,
            EqualityNormalization.instantiate_renameWires]
        have sourceAfterCanonical : sourceHostAfter.Canonical := by
          rw [← sourceHostEq]
          exact hostedOccurrence.context.holeCanonical _
            hostedOccurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceHostEq]
        let presentedOccurrence : Occurrence sourceHostAfter source :=
          EqualityNormalization.presentationOccurrence hostedOccurrence
            sourceAfterCanonical sourceNonempty
            (RegionIso.adjoinAt hostLocals outerHostItems
              (EqualityNormalization.instantiateRenameIso pattern
                application rename))
        let mappedHostItems := atomSiteHostItems pattern tail
          mappedApplication
        let mappedFormal : Var
            ((outer ++ hostLocals) ++ retainedLocals)
            (.rel atomArguments) :=
          atomBodyWire pattern (outer ++ hostLocals) head
        let mappedRetainedPorts : Vars
            ((outer ++ hostLocals) ++ retainedLocals) atomArguments :=
          ports.map fun wire =>
            atomBodyWire pattern (outer ++ hostLocals) wire
        let mappedFormalResult := atomFormalPrefixResult mappedHostItems
          mappedFormal mappedRetainedPorts
        let mappedFrame := Leaf.Formal.rootFrame (outer ++ hostLocals) []
          retainedLocals [] atomArguments
        let mappedEvidence := atomFormalPrefixEvidence mappedFrame
          mappedHostItems mappedFormal mappedRetainedPorts
        let mappedExternalApplication : Vars
            ((outer ++ hostLocals) ++ retainedLocals) pattern.external :=
          (Erasure.Exposure.identityBoundary pattern.external).map
            (fun wire => atomBodyWire pattern (outer ++ hostLocals) wire)
        let mappedSites := atomFormalPrefixRecordingSites mappedFrame
          mappedHostItems mappedFormal mappedRetainedPorts
          mappedExternalApplication
        let mappedOutput := itemsEdit
          (operation := recordingOperation
            (Leaf.Formal.operation [] atomArguments) pattern.external)
          PUnit.unit mappedEvidence mappedSites
        have mappedTargetIdentity : mappedFrame.targetKeep =
            WireRenaming.id := by
          exact formalRootFrame_targetKeep (outer ++ hostLocals)
            retainedLocals atomArguments
        have mappedOutputEq : mappedOutput.endpoint =
            atomFormalPrefixEndpoint mappedHostItems mappedFormal
              mappedRetainedPorts := by
          have endpoint := atomFormalPrefixRecordingItemsEditEndpoint atomArguments
            pattern.external mappedFrame mappedHostItems mappedFormal
              mappedRetainedPorts mappedExternalApplication
          rw [mappedTargetIdentity] at endpoint
          exact endpoint.trans (Region.renameWires_id _)
        let targetMiddle := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil mappedFormalResult)
        let targetAfter := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil mappedOutput.endpoint)
        let primitiveSites := atomFormalPrefixSites mappedFrame mappedHostItems
          mappedFormal mappedRetainedPorts
        let primitiveOutput := itemsEdit
          (operation := Leaf.Formal.operation [] atomArguments)
          PUnit.unit mappedEvidence primitiveSites
        let primitiveTargetAfter := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil primitiveOutput.endpoint)
        have primitiveOutputEq : primitiveOutput.endpoint =
            atomFormalPrefixEndpoint mappedHostItems mappedFormal
              mappedRetainedPorts := by
          have endpoint := atomFormalPrefixItemsEditEndpoint atomArguments
            mappedFrame mappedHostItems mappedFormal mappedRetainedPorts
          rw [mappedTargetIdentity] at endpoint
          exact endpoint.trans (Region.renameWires_id _)
        have targetAfterEq : targetAfter = primitiveTargetAfter := by
          unfold targetAfter primitiveTargetAfter
          rw [mappedOutputEq, primitiveOutputEq]
        obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
            outputCanonical, outputExternalTwoEnded, outputStrict⟩ :=
          accumulateSelectedAtomFormal body_eq outerHostItems
            mappedApplication presentedOccurrence
        change EqualityNormalization.StrictEquates presentedOccurrence
          targetMiddle ownedCanonical ownedExternalTwoEnded at ownedStrict
        have targetAfterCanonical :
            (presentedOccurrence.context.fill targetAfter).Canonical := by
          rw [targetAfterEq]
          exact outputCanonical
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedOccurrence.interface.boundaryWire
            (presentedOccurrence.context.fill targetAfter) := by
          intro signature wire
          rw [targetAfterEq]
          exact outputExternalTwoEnded wire
        have outputStrictRecorded : EqualityNormalization.StrictEquates
          (exactOccurrence presentedOccurrence.interface
            presentedOccurrence.context targetMiddle ownedCanonical
              ownedExternalTwoEnded)
          targetAfter targetAfterCanonical targetAfterExternalTwoEnded := by
          let targetIso : OpenDiagramIso
              (presentedOccurrence.interface.withBody
                (presentedOccurrence.context.fill primitiveTargetAfter)
                outputCanonical outputExternalTwoEnded)
              (presentedOccurrence.interface.withBody
                (presentedOccurrence.context.fill targetAfter)
                targetAfterCanonical targetAfterExternalTwoEnded) :=
            OpenDiagram.withBody_iso outputCanonical targetAfterCanonical
              outputExternalTwoEnded targetAfterExternalTwoEnded
              (DiagramContext.fillIso presentedOccurrence.context
                (RegionIso.ofEq targetAfterEq.symm))
          exact EqualityNormalization.StrictEquates.targetIso outputStrict
            targetIso
        have combinedStrict : EqualityNormalization.StrictEquates
            presentedOccurrence targetAfter targetAfterCanonical
              targetAfterExternalTwoEnded :=
          EqualityNormalization.StrictEquates.trans ownedStrict
            outputStrictRecorded
        let retainedRename :=
          rename.appendRight (EqualityNormalization.locals pattern)
        have hostItemsEq : hostItems.renameWires retainedRename =
            mappedHostItems := by
          simpa only [hostItems, mappedHostItems, mappedApplication,
            retainedLocals, retainedRename] using
            atomSiteHostItems_renameWires pattern tail application rename
        have formalEq : retainedRename formal = mappedFormal := by
          have natural := congrArg
            (fun embedding : WireRenaming pattern.external
                ((outer ++ hostLocals) ++
                  EqualityNormalization.locals pattern) =>
              embedding head)
            (atomBodyWire_natural pattern rename)
          simpa only [formal, mappedFormal, retainedLocals, retainedRename,
            WireRenaming.comp] using natural
        have retainedPortsEq :
            retainedPorts.map (fun wire => retainedRename wire) =
              mappedRetainedPorts := by
          calc
            _ = ports.map (fun wire =>
                retainedRename (atomBodyWire pattern itemCommon wire)) :=
              Diagram.vars_map_comp ports (atomBodyWire pattern itemCommon)
                retainedRename
            _ = ports.map (fun wire =>
                atomBodyWire pattern (outer ++ hostLocals) wire) := by
              simpa only [WireRenaming.comp] using congrArg
                (fun embedding : WireRenaming pattern.external
                    ((outer ++ hostLocals) ++
                      EqualityNormalization.locals pattern) =>
                  ports.map fun wire => embedding wire)
                (atomBodyWire_natural pattern rename)
            _ = mappedRetainedPorts := rfl
        have endpointEq :
            (output.endpoint.renameWires
              (targetRename.appendRight retainedLocals)).renameWires
                retainedRename = mappedOutput.endpoint := by
          calc
            _ = Region.renameWires retainedRename
                (atomFormalPrefixEndpoint hostItems formal retainedPorts) :=
              congrArg
                  (fun region => region.renameWires retainedRename) outputEq
            _ = atomFormalPrefixEndpoint
                (hostItems.renameWires retainedRename)
                (retainedRename formal)
                (retainedPorts.map fun wire => retainedRename wire) :=
              atomFormalPrefixEndpoint_renameWires hostItems formal
                retainedPorts retainedRename
            _ = atomFormalPrefixEndpoint mappedHostItems mappedFormal
                mappedRetainedPorts := by
              rw [hostItemsEq, formalEq, retainedPortsEq]
            _ = mappedOutput.endpoint := mappedOutputEq.symm
        let targetBefore := Region.adjoinAt hostLocals outerHostItems
          (outputStaged.renameWires rename)
        have targetEq : targetBefore = targetAfter := by
          simp only [targetBefore, targetAfter, outputStaged,
            Region.renameWires_adjoinAt_nil, retainedLocals]
          rw [endpointEq]
        let targetPresentation : RegionIso (WireEquiv.refl outer)
            targetAfter targetBefore := RegionIso.ofEq targetEq.symm
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetBefore).Canonical := by
          exact targetCanonical
        have presentedTargetExternalTwoEnded :
            OpenDiagram.ExternalTwoEnded
              presentedOccurrence.interface.boundaryWire
              (presentedOccurrence.context.fill targetBefore) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        let combinedTargetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              targetAfterCanonical targetAfterExternalTwoEnded)
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso targetAfterCanonical presentedTargetCanonical
            targetAfterExternalTwoEnded presentedTargetExternalTwoEnded
            (DiagramContext.fillIso presentedOccurrence.context
              targetPresentation)
        have presentedStrict : EqualityNormalization.StrictEquates
            presentedOccurrence targetBefore presentedTargetCanonical
              presentedTargetExternalTwoEnded := by
          exact EqualityNormalization.StrictEquates.targetIso combinedStrict
            combinedTargetIso
        let targetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (hostedOccurrence.interface.withBody
              (hostedOccurrence.context.fill targetBefore)
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded
            (RegionIso.refl
              (presentedOccurrence.context.fill targetBefore))
        exact ⟨transGen_iso (OpenDiagramIso.refl source)
            presentedStrict.1 targetIso,
          transGen_iso targetIso presentedStrict.2
            (OpenDiagramIso.refl source)⟩
      -/
      let direct : Region (itemCommon ++ retainedLocals) :=
        Region.singleton (.atom formal retainedPorts)
      let positional : Region (itemCommon ++ retainedLocals) :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retainedPorts)
      let raw := atomExposureDescription (head := head) (ports := ports)
        tail application
      have rawSourceEq : raw.source =
          Region.adjoinAt retainedLocals hostItems direct := by
        simp only [raw, Rule.Erasure.Description.source, Region.spliceAt,
          atomExposureDescription, retainedLocals, hostItems, direct]
        exact congrArg
          (fun material => Region.adjoinAt retainedLocals hostItems material)
          (by
            simpa only [atomExposureDescription, formal, retainedPorts] using
              atomExposureMaterialRename tail application)
      let rawSourceIso := atomExposureSourceIso body_eq application
      let directSourceIso : RegionIso (WireEquiv.refl itemCommon)
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application)
          (Region.adjoinAt retainedLocals hostItems direct) :=
        rawSourceIso.symm.trans (RegionIso.ofEq rawSourceEq)
      have exposureScope : ScopePreservation
          (Region.adjoinAt retainedLocals hostItems direct)
          (Region.adjoinAt retainedLocals hostItems positional) :=
        adjoinAt_preserves_scope retainedLocals hostItems direct positional
          (positionalAtomInstantiation_scope formal retainedPorts)
      let formalIso := atomFormalSelectedResultIso
        (pattern := pattern) (head := head) (ports := ports) tail application
      have selectedScope : ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) staged := by
        exact ScopePreservation.trans (ScopePreservation.ofIso directSourceIso)
          (ScopePreservation.trans exposureScope (ScopePreservation.ofIso formalIso.symm))
      /-
      let outputEndpointIso : RegionIso
          (WireEquiv.refl (itemCommon ++ retainedLocals))
          (output.endpoint.renameWires
            (targetRename.appendRight retainedLocals))
          ((Region.ofItems hostItems).conjoin direct) :=
        (RegionIso.ofEq outputEq).trans
          (atomFormalPrefixEndpointIso hostItems formal retainedPorts)
      let outputLocalIso : RegionIso (WireEquiv.refl itemCommon)
          outputStaged
          (Region.adjoinAt retainedLocals hostItems direct) :=
        (RegionIso.adjoinAt retainedLocals .nil outputEndpointIso).trans
          (RegionIso.ofEq
            (adjoinAt_hostedMaterial retainedLocals hostItems direct).symm)
      let originalOutputIso : RegionIso (WireEquiv.refl itemCommon)
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged :=
        directSourceIso.trans outputLocalIso.symm
      have outputScope : ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged :=
        ScopePreservation.ofIso originalOutputIso
      -/
      exact ⟨staged, hosted, selectedScope, ⟨RegionIso.refl staged⟩⟩

/-- The nonrecursive selected-site premise for the positional identity leaf. -/
theorem identitySelectedTargetItem
    {patternWires itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {itemFrame : Transform.Frame patternWires itemCommon
      itemSourceWires itemTargetWires}
    {itemOperation : Transform.Operation patternWires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon patternWires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame (List.replicate arity signature)
      itemCommon formalSourceWires formalTargetWires) :
    TargetItem
      (targetPattern := positionalIdentityPattern signature arity)
      (targetOperation := Leaf.Identity.operation signature arity)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := pattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := pattern) (frame := itemFrame) application siteData)
      (Leaf.Identity.Vars.fromFn ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern application) staged ∧
            ScopePreservation
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult))) := by
  unfold TargetItem
  let retainedLocals := EqualityNormalization.locals pattern
  let childFrame := formalFrame.append retainedLocals
  let hostItems := atomSiteHostItems pattern tail application
  let retained : Vars (itemCommon ++ retainedLocals)
      (List.replicate arity signature) :=
    Leaf.Identity.Vars.fromFn
      (fun position => atomBodyWire pattern itemCommon (ports position))
  let formalSource := identityFormalPrefixSource childFrame hostItems retained
  let formalResult := identityFormalPrefixResult signature arity hostItems
    retained
  let formalEvidence := identityFormalPrefixEvidence childFrame hostItems
    retained
  let childApplication : Vars (itemCommon ++ retainedLocals)
      pattern.external :=
    (Erasure.Exposure.identityBoundary pattern.external).map
      (fun wire => atomBodyWire pattern itemCommon wire)
  let formalSites := identityFormalPrefixRecordingSites childFrame hostItems
    retained childApplication
  refine ⟨retainedLocals, formalSource, formalResult, formalEvidence,
    formalSites, ?_, ?_⟩
  · let rename := atomBodyWire pattern itemCommon
    apply identityFormalPrefixSource_eq_argumentItemsEdit childFrame
      hostItems retained childApplication (Leaf.Identity.Vars.fromFn ports)
      rename
    · rfl
    · rw [Leaf.Identity.Vars.fromFn_map]
  let staged := Region.adjoinAt retainedLocals .nil formalResult
  have hosted : HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) staged := by
    intro outer hostLocals rename outerHostItems boundary source
      hostedOccurrence targetCanonical targetExternalTwoEnded
    let mappedApplication := application.map fun wire => rename wire
    let sourceBefore :=
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application).renameWires rename
    let sourceAfter :=
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern mappedApplication
    let sourceHostBefore := Region.adjoinAt hostLocals outerHostItems
      sourceBefore
    let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems
      sourceAfter
    change Occurrence sourceHostBefore source at hostedOccurrence
    have sourceHostEq : sourceHostBefore = sourceHostAfter := by
      simp only [sourceHostBefore, sourceHostAfter, sourceBefore, sourceAfter,
        mappedApplication, EqualityNormalization.instantiate_renameWires]
    have sourceAfterCanonical : sourceHostAfter.Canonical := by
      rw [← sourceHostEq]
      exact hostedOccurrence.context.holeCanonical _
        hostedOccurrence.sourceCanonical
    have sourceNonempty : ∀ {wireSignature} (wire : Var outer wireSignature),
        sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
          sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
      intro wireSignature wire
      rw [sourceHostEq]
    let presentedOccurrence : Occurrence sourceHostAfter source :=
      EqualityNormalization.presentationOccurrence hostedOccurrence
        sourceAfterCanonical sourceNonempty
        (RegionIso.adjoinAt hostLocals outerHostItems
          (EqualityNormalization.instantiateRenameIso pattern application
            rename))
    let mappedHostItems := atomSiteHostItems pattern tail mappedApplication
    let mappedRetained : Vars
        ((outer ++ hostLocals) ++ retainedLocals)
        (List.replicate arity signature) :=
      Leaf.Identity.Vars.fromFn
        (fun position => atomBodyWire pattern (outer ++ hostLocals)
          (ports position))
    let mappedFormalResult := identityFormalPrefixResult signature arity
      mappedHostItems mappedRetained
    let targetAfter := Region.adjoinAt hostLocals outerHostItems
      (Region.adjoinAt retainedLocals .nil mappedFormalResult)
    obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
        outputCanonical, outputExternalTwoEnded, outputStrict⟩ :=
      accumulateSelectedIdentity body_eq outerHostItems mappedApplication
        presentedOccurrence
    change EqualityNormalization.StrictEquates presentedOccurrence targetAfter
      ownedCanonical ownedExternalTwoEnded at ownedStrict
    let retainedRename := rename.appendRight retainedLocals
    have hostItemsEq : hostItems.renameWires retainedRename =
        mappedHostItems := by
      simpa only [hostItems, mappedHostItems, mappedApplication,
        retainedLocals, retainedRename] using
        atomSiteHostItems_renameWires pattern tail application rename
    have retainedEq : retained.map (fun wire => retainedRename wire) =
        mappedRetained := by
      unfold retained mappedRetained
      rw [Leaf.Identity.Vars.fromFn_map]
      apply congrArg Leaf.Identity.Vars.fromFn
      funext position
      have natural := congrArg
        (fun embedding : WireRenaming pattern.external
            ((outer ++ hostLocals) ++ EqualityNormalization.locals pattern) =>
          embedding (ports position))
        (atomBodyWire_natural pattern rename)
      simpa only [retainedLocals, retainedRename, WireRenaming.comp] using
        natural
    have formalResultEq : formalResult.renameWires retainedRename =
        mappedFormalResult := by
      calc
        _ = identityFormalPrefixResult signature arity
            (hostItems.renameWires retainedRename)
            (retained.map fun wire => retainedRename wire) :=
          identityFormalPrefixResult_renameWires signature arity hostItems
            retained retainedRename
        _ = mappedFormalResult := by rw [hostItemsEq, retainedEq]
    let targetBefore := Region.adjoinAt hostLocals outerHostItems
      (staged.renameWires rename)
    have targetEq : targetBefore = targetAfter := by
      simp only [targetBefore, targetAfter, staged,
        Region.renameWires_adjoinAt_nil, retainedLocals]
      rw [formalResultEq]
    let targetPresentation : RegionIso (WireEquiv.refl outer)
        targetAfter targetBefore := RegionIso.ofEq targetEq.symm
    have presentedTargetCanonical :
        (presentedOccurrence.context.fill targetBefore).Canonical :=
      targetCanonical
    have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        presentedOccurrence.interface.boundaryWire
        (presentedOccurrence.context.fill targetBefore) := by
      intro wireSignature wire
      exact targetExternalTwoEnded wire
    let ownedTargetIso := OpenDiagram.withBody_iso ownedCanonical
      presentedTargetCanonical ownedExternalTwoEnded
      presentedTargetExternalTwoEnded
      (DiagramContext.fillIso presentedOccurrence.context targetPresentation)
    have presentedStrict :=
      EqualityNormalization.StrictEquates.targetIso ownedStrict
        ownedTargetIso
    let targetIso : OpenDiagramIso
        (presentedOccurrence.interface.withBody
          (presentedOccurrence.context.fill targetBefore)
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (hostedOccurrence.interface.withBody
          (hostedOccurrence.context.fill targetBefore)
          targetCanonical targetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
        presentedTargetExternalTwoEnded targetExternalTwoEnded
        (RegionIso.refl _)
    exact ⟨transGen_iso (OpenDiagramIso.refl source) presentedStrict.1
        targetIso,
      transGen_iso targetIso presentedStrict.2
        (OpenDiagramIso.refl source)⟩
  /- The deterministic edit endpoint is prepared by the identity consumer.
  let outputStaged := Region.adjoinAt retainedLocals .nil
    (output.endpoint.renameWires (targetRename.appendRight retainedLocals))
  have outputHosted : HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) outputStaged := by
    intro outer hostLocals rename outerHostItems boundary source
      hostedOccurrence targetCanonical targetExternalTwoEnded
    let mappedApplication := application.map fun wire => rename wire
    let sourceAfter :=
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern mappedApplication
    let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems sourceAfter
    have sourceHostEq :
        Region.adjoinAt hostLocals outerHostItems
            ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              pattern application).renameWires rename) = sourceHostAfter := by
      simp only [sourceHostAfter, sourceAfter, mappedApplication,
        EqualityNormalization.instantiate_renameWires]
    change Occurrence
      (Region.adjoinAt hostLocals outerHostItems
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application).renameWires rename)) source at hostedOccurrence
    have sourceAfterCanonical : sourceHostAfter.Canonical := by
      rw [← sourceHostEq]
      exact hostedOccurrence.context.holeCanonical _
        hostedOccurrence.sourceCanonical
    have sourceNonempty : ∀ {wireSignature} (wire : Var outer wireSignature),
        (Region.adjoinAt hostLocals outerHostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename)).incidencePaths
              wire.index.val ≠ [] ↔
          sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
      intro wireSignature wire
      rw [sourceHostEq]
    let presentedOccurrence : Occurrence sourceHostAfter source :=
      EqualityNormalization.presentationOccurrence hostedOccurrence
        sourceAfterCanonical sourceNonempty
        (RegionIso.adjoinAt hostLocals outerHostItems
          (EqualityNormalization.instantiateRenameIso pattern application
            rename))
    let mappedHostItems := atomSiteHostItems pattern tail mappedApplication
    let mappedRetained : Vars
        ((outer ++ hostLocals) ++ retainedLocals)
        (List.replicate arity signature) :=
      Leaf.Identity.Vars.fromFn
        (fun position => atomBodyWire pattern (outer ++ hostLocals)
          (ports position))
    let mappedFrame := Leaf.Identity.rootFrame (outer ++ hostLocals) []
      retainedLocals signature arity
    let mappedEvidence := identityFormalPrefixEvidence mappedFrame
      mappedHostItems mappedRetained
    let mappedSites := identityFormalPrefixSites mappedFrame mappedHostItems
      mappedRetained
    let mappedOutput := itemsEdit
      (operation := Leaf.Identity.operation signature arity)
      PUnit.unit mappedEvidence mappedSites
    let targetAfter := Region.adjoinAt hostLocals outerHostItems
      (Region.adjoinAt retainedLocals .nil mappedOutput.endpoint)
    obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
        mappedOutputCanonical, mappedOutputExternalTwoEnded,
        mappedOutputStrict⟩ :=
      accumulateSelectedIdentity body_eq outerHostItems mappedApplication
        presentedOccurrence
    have combinedStrict := EqualityNormalization.StrictEquates.trans
      ownedStrict mappedOutputStrict
    let retainedRename := rename.appendRight retainedLocals
    have hostItemsEq : hostItems.renameWires retainedRename =
        mappedHostItems := by
      simpa only [hostItems, mappedHostItems, mappedApplication,
        retainedLocals, retainedRename] using
        atomSiteHostItems_renameWires pattern tail application rename
    have retainedEq : retained.map (fun wire => retainedRename wire) =
        mappedRetained := by
      unfold retained mappedRetained
      rw [Leaf.Identity.Vars.fromFn_map]
      apply congrArg Leaf.Identity.Vars.fromFn
      funext position
      have natural := congrArg
        (fun embedding : WireRenaming pattern.external
            ((outer ++ hostLocals) ++ EqualityNormalization.locals pattern) =>
          embedding (ports position))
        (atomBodyWire_natural pattern rename)
      simpa only [retainedLocals, retainedRename, WireRenaming.comp] using
        natural
    have mappedTargetIdentity : mappedFrame.targetKeep = WireRenaming.id := by
      apply WireRenaming.ext
      intro wireSignature wire
      apply Var.appendCases (left := outer ++ hostLocals)
        (right := retainedLocals)
        (motive := fun wire => mappedFrame.targetKeep wire =
          WireRenaming.id wire)
      · intro inheritedSignature inherited
        simp [mappedFrame, Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
      · intro localSignature localWire
        simp [mappedFrame, Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
          Var.appendMap, Var.appendRight]
    have mappedOutputEq : mappedOutput.endpoint =
        identityFormalPrefixEndpoint signature arity mappedHostItems
          mappedRetained :=
      by
        have endpoint := identityFormalPrefixItemsEditEndpoint signature arity
          mappedFrame mappedHostItems mappedRetained
        rw [mappedTargetIdentity] at endpoint
        exact endpoint.trans (Region.renameWires_id _)
    have endpointEq :
        (output.endpoint.renameWires
          (targetRename.appendRight retainedLocals)).renameWires
            retainedRename = mappedOutput.endpoint := by
      calc
        _ = (identityFormalPrefixEndpoint signature arity hostItems retained
              ).renameWires retainedRename :=
          congrArg (fun region => region.renameWires retainedRename) outputEq
        _ = identityFormalPrefixEndpoint signature arity
            (hostItems.renameWires retainedRename)
            (retained.map fun wire => retainedRename wire) :=
          identityFormalPrefixEndpoint_renameWires signature arity hostItems
            retained retainedRename
        _ = identityFormalPrefixEndpoint signature arity mappedHostItems
            mappedRetained := by rw [hostItemsEq, retainedEq]
        _ = mappedOutput.endpoint := mappedOutputEq.symm
    let targetBefore := Region.adjoinAt hostLocals outerHostItems
      (outputStaged.renameWires rename)
    have targetEq : targetBefore = targetAfter := by
      simp only [targetBefore, targetAfter, outputStaged,
        Region.renameWires_adjoinAt_nil, retainedLocals]
      rw [endpointEq]
    let targetPresentation : RegionIso (WireEquiv.refl outer)
        targetAfter targetBefore := RegionIso.ofEq targetEq.symm
    have presentedTargetCanonical :
        (presentedOccurrence.context.fill targetBefore).Canonical :=
      targetCanonical
    have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        presentedOccurrence.interface.boundaryWire
        (presentedOccurrence.context.fill targetBefore) := by
      intro wireSignature wire
      exact targetExternalTwoEnded wire
    let combinedTargetIso := OpenDiagram.withBody_iso mappedOutputCanonical
      presentedTargetCanonical mappedOutputExternalTwoEnded
      presentedTargetExternalTwoEnded
      (DiagramContext.fillIso presentedOccurrence.context targetPresentation)
    have presentedStrict :=
      EqualityNormalization.StrictEquates.targetIso combinedStrict
        combinedTargetIso
    let targetIso : OpenDiagramIso
        (presentedOccurrence.interface.withBody
          (presentedOccurrence.context.fill targetBefore)
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (hostedOccurrence.interface.withBody
          (hostedOccurrence.context.fill targetBefore)
          targetCanonical targetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
        presentedTargetExternalTwoEnded targetExternalTwoEnded
        (RegionIso.refl _)
    exact ⟨transGen_iso (OpenDiagramIso.refl source) presentedStrict.1
        targetIso,
      transGen_iso targetIso presentedStrict.2
        (OpenDiagramIso.refl source)⟩
  -/
  let sourceIso := identitySelectedSourceIso body_eq application
  let materialScopeForward := positionalIdentityInstantiation_scope
    signature arity retained
  have materialScope : ScopePreservation
      (positionalIdentityApplication signature arity retained)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) retained) := {
    canonical := fun _ =>
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        (positionalIdentityPattern signature arity) retained
    incidenceNonempty := fun wire =>
      (materialScopeForward.incidenceNonempty wire).symm
    rootedTwo := fun wire rooted => by
      rw [EqualityNormalization.instantiate_rootedTwo_iff]
      rw [← positionalIdentityApplication_incidencePaths_length]
      exact rooted.1
  }
  let direct := positionalIdentityApplication signature arity retained
  let positional :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) retained
  have stagedScope : ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) staged := by
    let directScope : ScopePreservation
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)
        (Region.adjoinAt retainedLocals hostItems direct) :=
      ScopePreservation.ofIso sourceIso
    let exposedScope := adjoinAt_preserves_scope retainedLocals hostItems
      direct positional materialScope
    let formalIso := identityFormalSelectedResultIso
      (pattern := pattern) (ports := ports) tail application
    exact ScopePreservation.trans directScope
      (ScopePreservation.trans exposedScope
        (ScopePreservation.ofIso formalIso.symm))
  /-
  let outputEndpointIso : RegionIso
      (WireEquiv.refl (itemCommon ++ retainedLocals))
      (output.endpoint.renameWires
        (targetRename.appendRight retainedLocals))
      ((Region.ofItems hostItems).conjoin direct) :=
    (RegionIso.ofEq outputEq).trans
      (identityFormalPrefixEndpointIso signature arity hostItems retained)
  let outputLocalIso : RegionIso (WireEquiv.refl itemCommon) outputStaged
      (Region.adjoinAt retainedLocals hostItems direct) :=
    (RegionIso.adjoinAt retainedLocals .nil outputEndpointIso).trans
      (RegionIso.ofEq
        (adjoinAt_hostedMaterial retainedLocals hostItems direct).symm)
  let originalOutputIso := sourceIso.trans outputLocalIso.symm
  have outputScope : ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) outputStaged :=
    ScopePreservation.ofIso originalOutputIso
  -/
  exact ⟨staged, hosted, stagedScope, ⟨RegionIso.refl staged⟩⟩




mutual
  /-- Leaf-only endpoint traversal for a region whose edit retains the common
  wire context literally. -/
  theorem leafRegionEndpoint
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id)
      (selected : ∀
        {siteCommon siteSourceWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteCommon}
        {siteData : operation.Data siteFrame}
        (siteTargetKeepEq : siteFrame.targetKeep = WireRenaming.id)
        (ports : Vars siteCommon arguments)
        (site : operation.SiteData siteFrame siteData ports),
        HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site)) :
      HostedStrict result (regionEdit data evidence sites).endpoint ∧
        ScopePreservation result (regionEdit data evidence sites).endpoint := by
    cases sites with
    | @mk _ _ _ _ _ _ locals _ _ _ childSites =>
        have childTargetKeep : (frame.append locals).targetKeep =
            WireRenaming.id := by
          apply WireRenaming.ext
          intro signature wire
          change frame.targetKeep.appendRight locals wire = wire
          rw [targetKeepEq]
          exact WireRenaming.appendRight_id_apply locals wire
        obtain ⟨childHosted, childScope⟩ :=
          leafItemsEndpoint _ childSites childTargetKeep selected
        exact ⟨HostedStrict.adjoinAt _ _ _ childHosted,
          adjoinAt_preserves_scope _ .nil _ _ childScope⟩
  termination_by sizeOf source

  /-- Leaf-only endpoint traversal for an item sequence. -/
  theorem leafItemsEndpoint
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id)
      (selected : ∀
        {siteCommon siteSourceWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteCommon}
        {siteData : operation.Data siteFrame}
        (siteTargetKeepEq : siteFrame.targetKeep = WireRenaming.id)
        (ports : Vars siteCommon arguments)
        (site : operation.SiteData siteFrame siteData ports),
        HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site)) :
      HostedStrict result (itemsEdit data evidence sites).endpoint ∧
        ScopePreservation result (itemsEdit data evidence sites).endpoint := by
    cases sites with
    | nil _ =>
        exact ⟨HostedStrict.refl _, ScopePreservation.refl _⟩
    | cons itemSites tailSites =>
        obtain ⟨itemHosted, itemScope⟩ :=
          leafItemEndpoint _ itemSites targetKeepEq selected
        obtain ⟨tailHosted, tailScope⟩ :=
          leafItemsEndpoint _ tailSites targetKeepEq selected
        exact ⟨HostedStrict.conjoin _ _ _ _ itemHosted tailHosted,
          ScopePreservation.conjoin itemScope tailScope⟩
  termination_by sizeOf source

  /-- Leaf-only endpoint traversal for one item. -/
  theorem leafItemEndpoint
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id)
      (selected : ∀
        {siteCommon siteSourceWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteCommon}
        {siteData : operation.Data siteFrame}
        (siteTargetKeepEq : siteFrame.targetKeep = WireRenaming.id)
        (ports : Vars siteCommon arguments)
        (site : operation.SiteData siteFrame siteData ports),
        HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site)) :
      HostedStrict result (itemEdit data evidence sites).endpoint ∧
        ScopePreservation result (itemEdit data evidence sites).endpoint := by
    cases sites with
    | atom head ports =>
        have headEq : frame.targetKeep head = head := by
          rw [targetKeepEq]
          rfl
        have portsEq : ports.map (fun wire => frame.targetKeep wire) = ports := by
          rw [targetKeepEq]
          exact Diagram.vars_map_id ports
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          headEq, portsEq] using
          And.intro (HostedStrict.refl (Region.singleton (.atom head ports)))
            (ScopePreservation.refl (Region.singleton (.atom head ports)))
    | selectedAtom ports site =>
        simpa only [itemEdit, ExactEdit.refl] using
          selected targetKeepEq ports site
    | identity signature arity ports =>
        have portsEq : (fun index => frame.targetKeep (ports index)) = ports := by
          funext index
          rw [targetKeepEq]
          rfl
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          portsEq] using
          And.intro
            (HostedStrict.refl
              (Region.singleton (.identity signature arity ports)))
            (ScopePreservation.refl
              (Region.singleton (.identity signature arity ports)))
    | cut childSites =>
        obtain ⟨childHosted, childScope⟩ :=
          leafRegionEndpoint _ childSites targetKeepEq selected
        exact ⟨HostedStrict.cut _ _ childHosted,
          ScopePreservation.cut childScope⟩
  termination_by sizeOf source
end

/-- The selected-site endpoint transformation for the positional identity
leaf. The recording payload is irrelevant to the primitive endpoint. -/
theorem positionalIdentityLeafEndpoint
    (signature : Sig) (arity : Nat)
    {originalArguments common sourceWires : List Sig}
    {frame : Transform.Frame (List.replicate arity signature) common
      sourceWires common}
    (targetKeepEq : frame.targetKeep = WireRenaming.id)
    (application : Vars common (List.replicate arity signature))
    (site : (recordingOperation
      (Leaf.Identity.operation signature arity) originalArguments).SiteData
        frame PUnit.unit application) :
    HostedStrict
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application)
        ((recordingOperation
          (Leaf.Identity.operation signature arity) originalArguments).site
            frame PUnit.unit application site) ∧
      ScopePreservation
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application)
        ((recordingOperation
          (Leaf.Identity.operation signature arity) originalArguments).site
            frame PUnit.unit application site) := by
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
  refine ⟨?_, positionalIdentityInstantiation_scope signature arity
    (Leaf.Identity.Vars.fromFn identityPorts)⟩
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let mappedApplication :=
    (Leaf.Identity.Vars.fromFn identityPorts).map fun wire => rename wire
  let positional :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) mappedApplication
  let direct := positionalIdentityApplication signature arity
    mappedApplication
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity)
      (Leaf.Identity.Vars.fromFn identityPorts)).renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems positional
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    simp only [sourceBefore, sourceAfter, positional, mappedApplication,
      EqualityNormalization.instantiate_renameWires]
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  let sourcePresentation : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter := RegionIso.ofEq sourceEq
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical (fun _ => by rw [sourceEq]) sourcePresentation
  let targetBefore := Region.adjoinAt hostLocals hostItems
    ((positionalIdentityApplication signature arity
      (Leaf.Identity.Vars.fromFn identityPorts)).renameWires rename)
  let targetAfter := Region.adjoinAt hostLocals hostItems direct
  have targetEq' : targetBefore = targetAfter := by
    simp only [targetBefore, targetAfter, direct, mappedApplication,
      positionalIdentityApplication, Region.singleton_renameWires,
      Item.renameWires, Leaf.Identity.Vars.fromFn_map,
      Leaf.Identity.Vars.toFn_map, Leaf.Identity.Vars.toFn_fromFn]
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  have targetAfterCanonical :
      (presentedOccurrence.context.fill targetAfter).Canonical := by
    rw [← targetEq']
    exact targetCanonical
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedOccurrence.interface.boundaryWire
      (presentedOccurrence.context.fill targetAfter) := by
    intro wireSignature wire
    rw [← targetEq']
    exact targetExternalTwoEnded wire
  let targetOpen := presentedOccurrence.interface.withBody
    (presentedOccurrence.context.fill targetAfter) targetAfterCanonical
      targetAfterExternalTwoEnded
  let directOccurrence : Occurrence targetAfter targetOpen :=
    exactOccurrence presentedOccurrence.interface presentedOccurrence.context
      targetAfter targetAfterCanonical targetAfterExternalTwoEnded
  have core := equatesPositionalIdentityApplication signature arity
    mappedApplication directOccurrence presentedOccurrence.sourceCanonical
      presentedOccurrence.sourceExternalTwoEnded
  let targetIso : OpenDiagramIso targetOpen
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetAfterCanonical targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context
        (RegionIso.ofEq targetEq'.symm))
  exact ⟨transGen_iso presentedOccurrence.host_iso.symm core.2 targetIso,
    transGen_iso targetIso core.1 presentedOccurrence.host_iso.symm⟩

/-- Exposing the literal positional atom is a nonempty symmetric phase from
the direct atom to its positional-pattern instantiation. -/
theorem equatesPositionalAtomApplication
    {boundary outer atomArguments : List Sig}
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (formal : Var (outer ++ hostLocals) (.rel atomArguments))
    (retained : Vars (outer ++ hostLocals) atomArguments)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (Region.singleton (.atom formal retained))) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalAtomPattern atomArguments) (.cons formal retained)))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalAtomPattern atomArguments) (.cons formal retained))))) :
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retained)))
      targetCanonical targetExternalTwoEnded := by
  let description : Rule.Erasure.Description outer := {
    materialWires := positionalAtomWires atomArguments
    hostLocals := hostLocals
    hostItems := hostItems.append
      (EqualityNormalization.contextPins outer hostLocals)
    material := Region.singleton (positionalAtomItem atomArguments)
    wireMap := EqualityNormalization.formalSubstitution (.cons formal retained)
  }
  have nonempty : outer ++ hostLocals ≠ [] := by
    intro empty
    have bound := formal.index.isLt
    simpa [empty] using bound
  apply EqualityNormalization.pinnedExposureStrict occurrence
    targetCanonical targetExternalTwoEnded nonempty description
  · change Region.adjoinAt hostLocals
      (hostItems.append
        (EqualityNormalization.contextPins outer hostLocals))
      ((Region.singleton (positionalAtomItem atomArguments)).renameWires
        (EqualityNormalization.formalSubstitution (.cons formal retained))) = _
    apply congrArg
      (fun material => Region.adjoinAt hostLocals
        (hostItems.append
          (EqualityNormalization.contextPins outer hostLocals)) material)
    calc
      (Region.singleton (positionalAtomItem atomArguments)).renameWires
          (EqualityNormalization.formalSubstitution (.cons formal retained)) =
          Region.singleton
            ((positionalAtomItem atomArguments).renameWires
              (EqualityNormalization.formalSubstitution
                (.cons formal retained))) :=
        Region.singleton_renameWires _ _
      _ = Region.singleton (.atom formal retained) := by
        apply congrArg Region.singleton
        simpa only [positionalAtomCollapse, positionalAtomSelection] using
          positionalAtomItem_rename formal retained
  · rfl
  · intro materialCanonical
    have proofEq : materialCanonical = positionalAtomCanonical atomArguments :=
      Subsingleton.elim _ _
    subst materialCanonical
    simp only [description, Erasure.Exposure.exposedRegion,
      Erasure.Exposure.applicationPorts]
    rw [positionalAtomSupportPattern_eq]
    simpa only [
      ← EqualityNormalization.formalPorts_eq_exposure,
      EqualityNormalization.formalPorts_map_substitution]

/-- The selected-site endpoint transformation for the positional formal-atom
leaf. -/
theorem positionalAtomLeafEndpoint
    (atomArguments : List Sig)
    {originalArguments common sourceWires : List Sig}
    {frame : Transform.Frame (positionalAtomWires atomArguments) common
      sourceWires common}
    (targetKeepEq : frame.targetKeep = WireRenaming.id)
    (application : Vars common (positionalAtomWires atomArguments))
    (site : (recordingOperation
      (Leaf.Formal.operation [] atomArguments) originalArguments).SiteData
        frame PUnit.unit application) :
    HostedStrict
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) application)
        ((recordingOperation
          (Leaf.Formal.operation [] atomArguments) originalArguments).site
            frame PUnit.unit application site) ∧
      ScopePreservation
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) application)
        ((recordingOperation
          (Leaf.Formal.operation [] atomArguments) originalArguments).site
            frame PUnit.unit application site) := by
  rcases site with ⟨⟨formal, ⟨retained, applicationEq⟩⟩,
    recordedApplication⟩
  simp only [Argument.Projection.Vars.insertAt] at applicationEq
  subst application
  have targetEq :
      (recordingOperation
        (Leaf.Formal.operation [] atomArguments) originalArguments).site
          frame PUnit.unit (.cons formal retained)
          ⟨⟨formal, ⟨retained, rfl⟩⟩, recordedApplication⟩ =
        Region.singleton (.atom formal retained) := by
    change Region.singleton
      (.atom (frame.targetKeep formal)
        (retained.map fun wire => frame.targetKeep wire)) = _
    rw [targetKeepEq]
    simp [WireRenaming.id, Diagram.vars_map_id]
  rw [targetEq]
  have directScope : ScopePreservation
      (Region.singleton (.atom formal retained))
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained)) := by
    simpa only [List.nil_append] using
      positionalAtomInstantiation_scope formal retained
  have reverseScope : ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained))
      (Region.singleton (.atom formal retained)) := by
    constructor
    · intro _
      change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧ _
      exact ⟨fun localIndex => Fin.elim0 localIndex,
        ⟨True.intro, True.intro⟩⟩
    · intro signature wire
      exact (directScope.incidenceNonempty wire).symm
    · intro signature wire sourceRoot
      have countBound : 2 ≤ (Vars.cons formal retained).countIndex
          wire.index.val := by
        rw [← EqualityNormalization.instantiate_rootedTwo_iff]
        exact sourceRoot
      constructor
      · rw [selectedAtomIncidencePaths_length]
        exact countBound
      · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
        let appendNil : WireRenaming common (common ++ []) :=
          ⟨fun selected => selected.appendLeft []⟩
        have retainedCountEq :
            (retained.map (fun selected => appendNil selected)).countIndex
                wire.index.val = retained.countIndex wire.index.val :=
          Vars.countIndex_map_of_sameIndex retained appendNil
            (fun selected => Var.index_appendLeft selected []) wire.index.val
        simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
          ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
          Item.incidencePaths, List.append_nil, Var.index_appendLeft,
          List.mem_append]
        rw [List.mem_replicate, retainedCountEq]
        exact ⟨by
          simp only [Vars.countIndex] at countBound
          simpa only [Vars.countIndex] using
            Nat.ne_of_gt (by omega), rfl⟩
  refine ⟨?_, reverseScope⟩
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let mappedFormal := rename formal
  let mappedRetained := retained.map fun wire => rename wire
  let mappedApplication : Vars (outer ++ hostLocals)
      (positionalAtomWires atomArguments) :=
    .cons mappedFormal mappedRetained
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalAtomPattern atomArguments) (.cons formal retained)
      ).renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalAtomPattern atomArguments) mappedApplication)
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    apply congrArg (Region.adjoinAt hostLocals hostItems)
    simpa only [mappedApplication, mappedFormal, mappedRetained,
      Theory.Vars.map] using
        EqualityNormalization.instantiate_renameWires
          (positionalAtomPattern atomArguments) (.cons formal retained) rename
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  let sourcePresentation : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter := RegionIso.ofEq sourceEq
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical (fun _ => by rw [sourceEq]) sourcePresentation
  let direct := Region.singleton (.atom mappedFormal mappedRetained)
  have directEq :
      Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.atom formal retained)).renameWires rename) =
        Region.adjoinAt hostLocals hostItems direct := by
    simp [direct, mappedFormal, mappedRetained,
      Region.singleton_renameWires, Item.renameWires]
  have directCanonical :
      (presentedOccurrence.context.fill
        (Region.adjoinAt hostLocals hostItems direct)).Canonical := by
    simpa only [directEq] using targetCanonical
  have directExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedOccurrence.interface.boundaryWire
      (presentedOccurrence.context.fill
        (Region.adjoinAt hostLocals hostItems direct)) := by
    intro signature wire
    simpa only [directEq] using targetExternalTwoEnded wire
  let directEndpoint := presentedOccurrence.interface.withBody
    (presentedOccurrence.context.fill
      (Region.adjoinAt hostLocals hostItems direct))
    directCanonical directExternalTwoEnded
  let directOccurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems direct) directEndpoint :=
    exactOccurrence presentedOccurrence.interface presentedOccurrence.context
      (Region.adjoinAt hostLocals hostItems direct)
      directCanonical directExternalTwoEnded
  have core := equatesPositionalAtomApplication mappedFormal mappedRetained
    directOccurrence presentedOccurrence.sourceCanonical
      presentedOccurrence.sourceExternalTwoEnded
  let directIso : OpenDiagramIso directEndpoint
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.singleton (.atom formal retained)).renameWires rename)))
        targetCanonical targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso directCanonical targetCanonical
      directExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context (RegionIso.ofEq directEq.symm))
  exact ⟨transGen_iso presentedOccurrence.host_iso.symm core.2 directIso,
    transGen_iso directIso core.1 presentedOccurrence.host_iso.symm⟩

/-- Accumulate an authoritative instantiation into a caller-selected literal
target edit.  The selected-site premise is nonrecursive; this theorem owns the
only structural recursion over the authoritative sites. -/
theorem accumulateTarget
    {targetArguments patternWires outer before after targetInserted
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetBaseOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram patternWires}
    {originalFrame : Transform.Frame patternWires
      (outer ++ (before ++ after)) originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    (targetValues : Vars pattern.external targetArguments)
    (targetData : targetBaseOperation.Data
      (Transform.Frame.replace outer before after targetInserted
        targetArguments))
    (KRegion : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {localSource : Region sourceWires} {localResult : Region common}
      (localEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          localPattern localFrame.sourceKeep localFrame.selected
          localSource localResult)
      (localSites : RegionSites operation localData localEvidence)
      (values : Vars pattern.external targetArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame)
      (closeCommon : Region common → Region outer)
      (closeTarget : Region formalTargetWires → Region outer)
      (formalSource : Region formalSourceWires)
      (formalResult : Region common)
      (formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          targetPattern formalFrame.sourceKeep formalFrame.selected
          formalSource formalResult)
      (formalSites : RegionSites
        (recordingOperation targetBaseOperation pattern.external)
        formalData formalEvidence),
      formalSource =
        (argumentRegionEdit formalSites values
          (normalizationOperation targetArguments) formalFrame PUnit.unit
          (fun _ _ _ => PUnit.unit)).1 → Prop)
    (KItems : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {localSource : ItemSeq sourceWires} {localResult : Region common}
      (localEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern localFrame.sourceKeep localFrame.selected
          localSource localResult)
      (localSites : ItemsSites operation localData localEvidence)
      (values : Vars pattern.external targetArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame)
      (closeCommon : Region common → Region outer)
      (closeTarget : Region formalTargetWires → Region outer)
      (retained : List Sig)
        (formalSource : ItemSeq (formalSourceWires ++ retained))
      (formalResult : Region (common ++ retained))
      (formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          targetPattern (formalFrame.append retained).sourceKeep
          (formalFrame.append retained).selected formalSource formalResult)
      (formalSites : ItemsSites
        (recordingOperation targetBaseOperation pattern.external)
        (targetBaseOperation.appendData formalFrame formalData retained)
        formalEvidence),
      formalSource =
        (argumentItemsEdit formalSites values
          (normalizationOperation targetArguments)
          (formalFrame.append retained) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1 → Prop)
    (KItem : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {localSource : Item sourceWires} {localResult : Region common}
      (localEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          localPattern localFrame.sourceKeep localFrame.selected
          localSource localResult)
      (localSites : ItemSites operation localData localEvidence)
      (values : Vars pattern.external targetArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame)
      (closeCommon : Region common → Region outer)
      (closeTarget : Region formalTargetWires → Region outer)
      (retained : List Sig)
        (formalSource : ItemSeq (formalSourceWires ++ retained))
      (formalResult : Region (common ++ retained))
      (formalEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          targetPattern (formalFrame.append retained).sourceKeep
          (formalFrame.append retained).selected formalSource formalResult)
      (formalSites : ItemsSites
        (recordingOperation targetBaseOperation pattern.external)
        (targetBaseOperation.appendData formalFrame formalData retained)
        formalEvidence),
      formalSource =
        (argumentItemsEdit formalSites values
          (normalizationOperation targetArguments)
          (formalFrame.append retained) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1 → Prop)
    (nilCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (localEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern localFrame.sourceKeep localFrame.selected
          (.nil : ItemSeq sourceWires) (Region.blank common))
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItems localEvidence
        (.nil (operation := operation) (data := localData) localEvidence)
        targetValues formalFrame
        formalData
        (KItems localEvidence
          (.nil (operation := operation) (data := localData) localEvidence)
          targetValues formalFrame formalData closeCommon closeTarget))
    (regionCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {locals : List Sig}
      {items : ItemSeq (sourceWires ++ locals)}
      {childResult : Region (common ++ locals)}
      {childEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern (localFrame.sourceKeep.appendRight locals)
          (localFrame.selected.appendLeft locals) items childResult}
      (childSites : ItemsSites operation
        (operation.appendData localFrame localData locals) childEvidence)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItems childEvidence childSites targetValues
          (formalFrame.append locals)
          (targetBaseOperation.appendData formalFrame formalData locals)
          (KItems childEvidence childSites targetValues
            (formalFrame.append locals)
            (targetBaseOperation.appendData formalFrame formalData locals)
            (fun region =>
              closeCommon (Region.adjoinAt locals .nil region))
            (fun region =>
              closeTarget (Region.adjoinAt locals .nil region))) →
      TargetRegion
        (_root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
          childEvidence)
        (.mk childSites) targetValues formalFrame formalData
        (KRegion
          (_root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            childEvidence)
          (.mk childSites) targetValues formalFrame formalData closeCommon
            closeTarget))
    (consCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {item : Item sourceWires} {tail : ItemSeq sourceWires}
      {itemResult tailResult : Region common}
      {itemEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          localPattern localFrame.sourceKeep localFrame.selected item itemResult}
      {tailEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          localPattern localFrame.sourceKeep localFrame.selected tail tailResult}
      (itemSites : ItemSites operation localData itemEvidence)
      (tailSites : ItemsSites operation localData tailEvidence)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem itemEvidence itemSites targetValues formalFrame formalData
          (KItem itemEvidence itemSites targetValues formalFrame formalData
            closeCommon closeTarget) →
      TargetItems tailEvidence tailSites targetValues formalFrame formalData
          (KItems tailEvidence tailSites targetValues formalFrame formalData
            closeCommon closeTarget) →
      TargetItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
          itemEvidence tailEvidence)
        (.cons itemSites tailSites) targetValues formalFrame formalData
        (KItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemEvidence tailEvidence)
          (.cons itemSites tailSites) targetValues formalFrame formalData
            closeCommon closeTarget))
    (atomCase : ∀
      {common sourceWires targetWires atomArguments : List Sig}
      {evidencePattern localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (head : Var common (.rel atomArguments))
      (ports : Vars common atomArguments)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
          (pattern := evidencePattern) (retain := localFrame.sourceKeep)
          (selected := localFrame.selected) head ports)
        (@ItemSites.atom patternWires operation evidencePattern common
          sourceWires targetWires atomArguments localPattern localFrame
          localData head ports)
        targetValues formalFrame formalData
        (KItem
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            (pattern := evidencePattern) (retain := localFrame.sourceKeep)
            (selected := localFrame.selected) head ports)
          (@ItemSites.atom patternWires operation evidencePattern common
            sourceWires targetWires atomArguments localPattern localFrame
            localData head ports)
          targetValues formalFrame formalData closeCommon closeTarget))
    (selectedCase : ∀
      {common sourceWires targetWires : List Sig}
      {evidencePattern localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (application : Vars common patternWires)
      (siteData : operation.SiteData localFrame localData application)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := evidencePattern) (retain := localFrame.sourceKeep)
          (selected := localFrame.selected) application)
        (@ItemSites.selectedAtom patternWires operation evidencePattern common
          sourceWires targetWires localPattern localFrame localData
          application siteData)
        targetValues formalFrame formalData
        (KItem
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            (pattern := evidencePattern) (retain := localFrame.sourceKeep)
            (selected := localFrame.selected) application)
          (@ItemSites.selectedAtom patternWires operation evidencePattern common
            sourceWires targetWires localPattern localFrame localData
            application siteData)
          targetValues formalFrame formalData closeCommon closeTarget))
    (identityCase : ∀
      {common sourceWires targetWires : List Sig}
      {evidencePattern localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      (signature : Sig) (arity : Nat)
      (ports : Fin arity → Var common signature)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetItem
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
          (pattern := evidencePattern) (retain := localFrame.sourceKeep)
          (selected := localFrame.selected) signature arity ports)
        (@ItemSites.identity patternWires operation evidencePattern common
          sourceWires targetWires localPattern localFrame localData signature
          arity ports)
        targetValues formalFrame formalData
        (KItem
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            (pattern := evidencePattern) (retain := localFrame.sourceKeep)
            (selected := localFrame.selected) signature arity ports)
          (@ItemSites.identity patternWires operation evidencePattern common
            sourceWires targetWires localPattern localFrame localData signature
            arity ports)
          targetValues formalFrame formalData closeCommon closeTarget))
    (cutCase : ∀
      {common sourceWires targetWires : List Sig}
      {localPattern : OpenDiagram patternWires}
      {localFrame : Transform.Frame patternWires common sourceWires targetWires}
      {localData : operation.Data localFrame}
      {body : Region sourceWires} {childResult : Region common}
      {childEvidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          localPattern localFrame.sourceKeep localFrame.selected body childResult}
      (childSites : RegionSites operation localData childEvidence)
      {formalSourceWires formalTargetWires : List Sig}
      (formalFrame : Transform.Frame targetArguments common
        formalSourceWires formalTargetWires)
      (formalData : targetBaseOperation.Data formalFrame),
      (closeCommon : Region common → Region outer) →
      (closeTarget : Region formalTargetWires → Region outer) →
      TargetRegion childEvidence childSites targetValues formalFrame formalData
          (KRegion childEvidence childSites targetValues formalFrame formalData
            closeCommon closeTarget) →
      TargetItem
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
          childEvidence)
        (.cut childSites) targetValues formalFrame formalData
        (KItem
          (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            childEvidence)
          (.cut childSites) targetValues formalFrame formalData closeCommon
            closeTarget)) :
    TargetItems evidence sites targetValues
      (Transform.Frame.replace outer before after targetInserted targetArguments)
      targetData
      (KItems evidence sites targetValues
        (Transform.Frame.replace outer before after targetInserted targetArguments)
        targetData
        (fun region => Region.adjoinAt (before ++ after) .nil region)
        (fun region =>
          Region.adjoinAt (before ++ (targetInserted ++ after)) .nil
            region)) := by
  apply ItemsSites.rec
    (motive_1 := fun {common sourceWires targetWires} {localPattern} {frame}
        data {source result} evidence sites =>
      ∀ {formalSourceWires formalTargetWires : List Sig}
        (formalFrame : Transform.Frame targetArguments common
          formalSourceWires formalTargetWires)
        (formalData : targetBaseOperation.Data formalFrame),
        (closeCommon : Region common → Region outer) →
        (closeTarget : Region formalTargetWires → Region outer) →
        TargetRegion evidence sites targetValues formalFrame formalData
          (KRegion evidence sites targetValues formalFrame formalData closeCommon
            closeTarget))
    (motive_2 := fun {common sourceWires targetWires} {localPattern} {frame}
        data {source result} evidence sites =>
      ∀ {formalSourceWires formalTargetWires : List Sig}
        (formalFrame : Transform.Frame targetArguments common
          formalSourceWires formalTargetWires)
        (formalData : targetBaseOperation.Data formalFrame),
        (closeCommon : Region common → Region outer) →
        (closeTarget : Region formalTargetWires → Region outer) →
        TargetItems evidence sites targetValues formalFrame formalData
          (KItems evidence sites targetValues formalFrame formalData closeCommon
            closeTarget))
    (motive_3 := fun {common sourceWires targetWires} {localPattern} {frame}
        data {source result} evidence sites =>
      ∀ {formalSourceWires formalTargetWires : List Sig}
        (formalFrame : Transform.Frame targetArguments common
          formalSourceWires formalTargetWires)
        (formalData : targetBaseOperation.Data formalFrame),
        (closeCommon : Region common → Region outer) →
        (closeTarget : Region formalTargetWires → Region outer) →
        TargetItem evidence sites targetValues formalFrame formalData
          (KItem evidence sites targetValues formalFrame formalData closeCommon
            closeTarget))
  case nil =>
    intros
    apply nilCase
  case mk =>
    intros
    rename_i _ _ _ _ _ _ locals _ _ _ childSites childIH _ _
      formalFrame formalData closeCommon closeTarget
    exact regionCase childSites formalFrame formalData closeCommon
      closeTarget
      (childIH (formalFrame.append locals)
        (targetBaseOperation.appendData formalFrame formalData locals)
        (fun region => closeCommon (Region.adjoinAt locals .nil region))
        (fun region => closeTarget (Region.adjoinAt locals .nil region)))
  case cons =>
    intros
    solve_by_elim [consCase]
  case atom =>
    intros
    apply atomCase
  case selectedAtom =>
    intros
    apply selectedCase
  case identity =>
    intros
    apply identityCase
  case cut =>
    intros
    rename_i _ _ _ _ _ _ _ _ _ childSites childIH _ _ formalFrame
      formalData closeCommon closeTarget
    exact cutCase childSites formalFrame formalData closeCommon
      closeTarget (childIH formalFrame formalData closeCommon closeTarget)

/-- Accumulate a hosted target transformation together with an abstract
structural side condition.  The side condition is threaded through the same
authoritative target traversal, so specializations never need to reconstruct
or repeat the target witnesses. -/
theorem accumulateHostedTargetWith
    {targetArguments patternWires outer before after targetInserted originalSourceWires
      originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetBaseOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram patternWires}
    {originalFrame : Transform.Frame patternWires (outer ++ (before ++ after))
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    (targetValues : Vars pattern.external targetArguments)
    (targetData : targetBaseOperation.Data
      (Transform.Frame.replace outer before after targetInserted targetArguments))
    (Side : {wires : List Sig} → Region wires → Region wires → Prop)
    (sideRefl : ∀ {wires : List Sig} (region : Region wires),
      Side region region)
    (sideAdjoinAt : ∀ {common : List Sig} (locals : List Sig)
      (before after : Region (common ++ locals)),
      Side before after →
        Side (Region.adjoinAt locals .nil before)
          (Region.adjoinAt locals .nil after))
    (sideConjoin : ∀ {wires : List Sig}
      {firstBefore firstAfter secondBefore secondAfter : Region wires},
      Side firstBefore firstAfter → Side secondBefore secondAfter →
        Side (firstBefore.conjoin secondBefore)
          (firstAfter.conjoin secondAfter))
    (sideCut : ∀ {wires : List Sig} {before after : Region wires},
      Side before after →
        Side (Region.singleton (.cut before))
          (Region.singleton (.cut after)))
    (targetSiteNatural : ∀
      {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
        siteTargetWires siteMappedTargetWires : List Sig}
      {siteFrame : Transform.Frame targetArguments siteCommon siteSourceWires
        siteTargetWires}
      {siteMappedFrame : Transform.Frame targetArguments siteMappedCommon
        siteMappedSourceWires siteMappedTargetWires}
      {siteData : targetBaseOperation.Data siteFrame}
      {siteMappedData : targetBaseOperation.Data siteMappedFrame}
      (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
      (siteTargetRename : WireRenaming siteTargetWires
        siteMappedTargetWires)
      (_siteTargetKeepCommutes : ∀ {wireSignature}
        (wire : Var siteCommon wireSignature),
        siteTargetRename (siteFrame.targetKeep wire) =
          siteMappedFrame.targetKeep (siteCommonRename wire))
      (ports : Vars siteCommon targetArguments)
      (site : (recordingOperation targetBaseOperation
        pattern.external).SiteData siteFrame siteData ports),
      ∃ mappedSite : (recordingOperation targetBaseOperation
          pattern.external).SiteData siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire),
        Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
          (((recordingOperation targetBaseOperation pattern.external).site
            siteFrame siteData ports site).renameWires
            siteTargetRename)
          ((recordingOperation targetBaseOperation pattern.external).site
            siteMappedFrame siteMappedData
            (ports.map fun wire => siteCommonRename wire) mappedSite)))
    (selectedCase : ∀
      {itemCommon itemSourceWires itemTargetWires : List Sig}
      {itemFrame : Transform.Frame patternWires itemCommon
        itemSourceWires itemTargetWires}
      {itemOperation : Transform.Operation patternWires}
      {itemData : itemOperation.Data itemFrame}
      (application : Vars itemCommon patternWires)
      (siteData : itemOperation.SiteData itemFrame itemData application)
      {selectedTargetSourceWires selectedTargetWires : List Sig}
      (selectedTargetFrame : Transform.Frame targetArguments itemCommon
        selectedTargetSourceWires selectedTargetWires)
      (selectedTargetData : targetBaseOperation.Data selectedTargetFrame),
      TargetItem
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := pattern) (retain := itemFrame.sourceKeep)
          (selected := itemFrame.selected) application)
        (ItemSites.selectedAtom (operation := itemOperation)
          (pattern := pattern) (frame := itemFrame) application siteData)
        targetValues selectedTargetFrame selectedTargetData
        (fun retained _formalSource formalResult _formalEvidence _formalSites
            _coherence =>
          ∃ staged : Region itemCommon,
            HostedStrict
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Side
                  (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                    pattern application) staged ∧
                Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                  (Region.adjoinAt retained .nil formalResult)))) :
    TargetItems
      (targetPattern := targetPattern)
      (targetOperation := targetBaseOperation)
      evidence sites targetValues
      (Transform.Frame.replace outer before after targetInserted targetArguments) targetData
      (fun retained _formalSource formalResult _formalEvidence _formalSites
          _coherence =>
        ∃ staged : Region (outer ++ (before ++ after)),
          HostedStrict result staged ∧
            Side result staged ∧
              Nonempty (RegionIso (WireEquiv.refl (outer ++ (before ++ after))) staged
                (Region.adjoinAt retained .nil formalResult))) := by
  let common := outer ++ (before ++ after)
  let targetOperation := recordingOperation targetBaseOperation pattern.external
  let authoritativePattern := pattern
  let targetFrame := Transform.Frame.replace outer before after targetInserted targetArguments
  have foldedFamilyWithPattern :
      TargetItems
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        evidence sites targetValues targetFrame targetData
        (fun retained _formalSource formalResult _formalEvidence _formalSites
            _coherence =>
          pattern = authoritativePattern →
          ∃ staged : Region common,
            HostedStrict result staged ∧
              Side result staged ∧
                Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult))) := by
    refine accumulateTarget evidence sites targetValues targetData
      (KRegion := fun {common sourceWires targetWires} {localPattern}
        {localFrame} {localData} {localSource localResult}
        _localEvidence _localSites _values
        {formalSourceWires formalTargetWires} formalFrame formalData
        _closeCommon _closeTarget _formalSource formalResult
          _formalEvidence
        formalSites _coherence =>
          localPattern = authoritativePattern →
          ∃ staged : Region common, HostedStrict localResult staged ∧
              Side localResult staged ∧
              Nonempty (RegionIso (WireEquiv.refl common) staged
                  formalResult))
      (KItems := fun {common sourceWires targetWires} {localPattern}
        {localFrame} {localData} {localSource localResult}
        _localEvidence _localSites _values
        {formalSourceWires formalTargetWires} formalFrame formalData
        _closeCommon _closeTarget retained _formalSource formalResult
        _formalEvidence _formalSites _coherence =>
          localPattern = authoritativePattern →
          ∃ staged : Region common, HostedStrict localResult staged ∧
              Side localResult staged ∧
              Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult)))
      (KItem := fun {common sourceWires targetWires} {localPattern}
        {localFrame} {localData} {localSource localResult}
        _localEvidence _localSites _values
        {formalSourceWires formalTargetWires} formalFrame formalData
        _closeCommon _closeTarget retained _formalSource formalResult
        _formalEvidence _formalSites _coherence =>
          localPattern = authoritativePattern →
          ∃ staged : Region common, HostedStrict localResult staged ∧
              Side localResult staged ∧
              Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult)))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    case refine_1 =>
        intros
        rename_i nilCommon nilSourceWires nilTargetWires nilPattern nilFrame
          nilData nilEvidence formalSourceWires formalTargetWires
          formalFrame formalData _closeCommon _closeTarget
        unfold TargetItems
        let appendedData := targetOperation.appendData formalFrame formalData []
        let formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              targetPattern
              (formalFrame.append []).sourceKeep
              (formalFrame.append []).selected
              (.nil : ItemSeq (formalSourceWires ++ []))
              (Region.blank (nilCommon ++ [])) := .nil
        let formalSites : ItemsSites
            targetOperation appendedData
            formalEvidence := .nil formalEvidence
        have hosted : HostedStrict (Region.blank nilCommon)
            (Region.blank nilCommon) := by
          intro outer hostLocals rename hostItems boundary source occurrence
            targetCanonical targetExternalTwoEnded
          simpa only [EqualityNormalization.StrictEquates] using
            EqualityNormalization.StrictEquates.refl occurrence
        have presentationEq : Region.adjoinAt [] .nil
            (Region.blank (nilCommon ++ [])) =
            Region.blank nilCommon := by
          rfl
        refine ⟨[], .nil, Region.blank (nilCommon ++ []), formalEvidence,
          formalSites, rfl, ?_⟩
        intro patternEq
        cases patternEq
        exact ⟨Region.blank nilCommon, hosted,
          sideRefl (Region.blank nilCommon),
          ⟨RegionIso.ofEq presentationEq.symm⟩⟩
    case refine_2 =>
      intros
      rename_i regionCommon regionSourceWires regionTargetWires regionPattern
        regionFrame regionData regionLocals regionItems regionResult
        regionEvidence regionSites formalSourceWires formalTargetWires
        formalFrame formalData _closeCommon _closeTarget regionIH
      let values := targetValues
      unfold TargetRegion
      let childData := targetOperation.appendData formalFrame formalData
        regionLocals
      obtain ⟨retained, childFormalSource, childFormalResult,
          childFormalEvidence, childFormalSites, childCoherence,
          childSemantic⟩ :=
        regionIH
      let combinedRetained := regionLocals ++ retained
      let commonRename := Region.adjoinMaterialWire regionCommon
        regionLocals retained
      let sourceRename := Region.adjoinMaterialWire formalSourceWires
        regionLocals retained
      let targetSourceRename := Region.adjoinMaterialWire formalTargetWires
        regionLocals retained
      let combinedFrame := formalFrame.append combinedRetained
      let combinedData := targetOperation.appendData formalFrame formalData
        combinedRetained
      have keepCommutes : ∀ {signature}
          (wire : Var ((regionCommon ++ regionLocals) ++ retained)
            signature),
          sourceRename
              (((formalFrame.append regionLocals).append retained).sourceKeep
                wire) =
            combinedFrame.sourceKeep (commonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := regionCommon ++ regionLocals)
          (right := retained)
          (motive := fun wire => sourceRename
              (((formalFrame.append regionLocals).append retained).sourceKeep
                wire) =
            combinedFrame.sourceKeep (commonRename wire))
        · intro inheritedSignature inherited
          apply Var.appendCases (left := regionCommon) (right := regionLocals)
            (motive := fun inherited => sourceRename
                (((formalFrame.append regionLocals).append retained).sourceKeep
                  (inherited.appendLeft retained)) =
              combinedFrame.sourceKeep
                (commonRename (inherited.appendLeft retained)))
          · intro commonSignature commonWire
            simp [sourceRename, commonRename, combinedFrame,
              combinedRetained, Transform.Frame.append,
              WireRenaming.appendRight, Region.adjoinMaterialWire]
          · intro localSignature localWire
            simp [sourceRename, commonRename, combinedFrame,
              combinedRetained, Transform.Frame.append,
              WireRenaming.appendRight, Region.adjoinMaterialWire]
        · intro retainedSignature retainedWire
          simp [sourceRename, commonRename, combinedFrame,
            combinedRetained, Transform.Frame.append,
            WireRenaming.appendRight, Region.adjoinMaterialWire]
      have selectedCommutes :
          sourceRename
              (((formalFrame.append regionLocals).append retained).selected) =
            combinedFrame.selected := by
        simp [sourceRename, combinedFrame, combinedRetained,
          Transform.Frame.append, Region.adjoinMaterialWire]
      have targetKeepCommutes : ∀ {signature}
          (wire : Var ((regionCommon ++ regionLocals) ++ retained)
            signature),
          targetSourceRename
              (((formalFrame.append regionLocals).append retained).targetKeep
                wire) =
            combinedFrame.targetKeep (commonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := regionCommon ++ regionLocals)
          (right := retained)
          (motive := fun wire => targetSourceRename
              (((formalFrame.append regionLocals).append retained).targetKeep
                wire) =
            combinedFrame.targetKeep (commonRename wire))
        · intro inheritedSignature inherited
          apply Var.appendCases (left := regionCommon) (right := regionLocals)
            (motive := fun inherited => targetSourceRename
                (((formalFrame.append regionLocals).append retained).targetKeep
                  (inherited.appendLeft retained)) =
              combinedFrame.targetKeep
                (commonRename (inherited.appendLeft retained)))
          · intro commonSignature commonWire
            simp [targetSourceRename, commonRename, combinedFrame, combinedRetained,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.adjoinMaterialWire]
          · intro localSignature localWire
            simp [targetSourceRename, commonRename, combinedFrame, combinedRetained,
              Transform.Frame.append, WireRenaming.appendRight,
              Region.adjoinMaterialWire]
        · intro retainedSignature retainedWire
          simp [targetSourceRename, commonRename, combinedFrame, combinedRetained,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.adjoinMaterialWire]
      obtain ⟨mappedSource, mappedResult, mappedEvidence, mappedSites,
          mappedSourceEq, mappedArgumentEq,
          ⟨mappedResultIso⟩, ⟨mappedEndpointIso⟩⟩ :=
        targetItemsReindex (mappedData := combinedData)
          (baseOperation := targetBaseOperation)
          (external := authoritativePattern.external)
          childFormalEvidence childFormalSites values
          commonRename sourceRename targetSourceRename keepCommutes
          targetKeepCommutes selectedCommutes targetSiteNatural
      let formalSource : Region formalSourceWires :=
        .mk combinedRetained mappedSource
      let formalResult : Region regionCommon :=
        Region.adjoinAt combinedRetained .nil mappedResult
      let formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
            targetPattern formalFrame.sourceKeep
            formalFrame.selected formalSource formalResult := by
        apply _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
        exact mappedEvidence
      let formalSites : RegionSites
          targetOperation formalData
          formalEvidence := by
        apply RegionSites.mk
        exact mappedSites
      have childCoherence' : childFormalSource =
          (argumentItemsEdit childFormalSites values
            (normalizationOperation targetArguments)
            ((formalFrame.append regionLocals).append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        simpa using childCoherence
      have mappedCoherence : mappedSource =
          (argumentItemsEdit mappedSites values
            (normalizationOperation targetArguments) combinedFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedSource = childFormalSource.renameWires sourceRename :=
            mappedSourceEq.symm
          _ = (argumentItemsEdit childFormalSites values
                (normalizationOperation targetArguments)
                ((formalFrame.append regionLocals).append retained)
                PUnit.unit (fun _ _ _ => PUnit.unit)).1.renameWires
                sourceRename := congrArg
                  (fun items => items.renameWires sourceRename) childCoherence'
          _ = _ := mappedArgumentEq
      refine ⟨formalSource, formalResult, formalEvidence, formalSites,
        ?_, ?_⟩
      · unfold formalSource formalSites argumentRegionEdit
        exact congrArg (Region.mk combinedRetained) mappedCoherence
      intro patternEq
      cases patternEq
      obtain ⟨childStaged, childHosted, childScope, ⟨childPresentation⟩⟩ :=
        childSemantic rfl
      let staged := Region.adjoinAt regionLocals .nil childStaged
      have stagedSide : Side
          (Region.adjoinAt regionLocals .nil regionResult) staged := by
        simpa only [staged] using
          sideAdjoinAt regionLocals regionResult childStaged childScope
      have liftHosted : ∀ (childBefore childAfter :
          Region (regionCommon ++ regionLocals)),
          HostedStrict childBefore childAfter →
            HostedStrict
              (Region.adjoinAt regionLocals .nil childBefore)
              (Region.adjoinAt regionLocals .nil childAfter) := by
        intro childBefore childAfter childTransformation
        intro outer hostLocals rename hostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let childRename := rename.appendRight regionLocals
        let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
          regionLocals
        let nextRename := WireRenaming.comp assoc.toRenaming childRename
        let nextHostItems := Region.extendHostItems hostLocals hostItems
          (.mk regionLocals .nil)
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.adjoinAt regionLocals .nil childBefore).renameWires rename)
        let sourceAfter := Region.adjoinAt (hostLocals ++ regionLocals)
          nextHostItems (childBefore.renameWires nextRename)
        change Occurrence sourceBefore source at hostedOccurrence
        let sourceNested := RegionIso.adjoinAt hostLocals hostItems
          (RegionIso.renameWiresAdjoinAtNil childBefore rename)
        let sourceAssociated :=
          (RegionIso.adjoinAtAssoc hostLocals hostItems regionLocals .nil
            (childBefore.renameWires childRename)).symm
        let sourceCombined := RegionIso.adjoinAt
          (hostLocals ++ regionLocals) nextHostItems
          (RegionIso.renameWiresComp childBefore childRename
            assoc.toRenaming)
        let sourcePresentation : RegionIso (WireEquiv.refl outer)
            sourceBefore sourceAfter :=
          (sourceNested.trans sourceAssociated).trans sourceCombined
        have sourceAfterCanonical : sourceAfter.Canonical :=
          sourcePresentation.canonical_iff.mp
            (hostedOccurrence.context.holeCanonical _
              hostedOccurrence.sourceCanonical)
        have sourceSameNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := sourcePresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        let presentedOccurrence : Occurrence sourceAfter source :=
          EqualityNormalization.presentationOccurrence hostedOccurrence
            sourceAfterCanonical sourceSameNonempty sourcePresentation
        let targetBefore := Region.adjoinAt hostLocals hostItems
          ((Region.adjoinAt regionLocals .nil childAfter).renameWires rename)
        let targetAfter := Region.adjoinAt (hostLocals ++ regionLocals)
          nextHostItems (childAfter.renameWires nextRename)
        let targetNested := RegionIso.adjoinAt hostLocals hostItems
          (RegionIso.renameWiresAdjoinAtNil childAfter rename)
        let targetAssociated :=
          (RegionIso.adjoinAtAssoc hostLocals hostItems regionLocals .nil
            (childAfter.renameWires childRename)).symm
        let targetCombined := RegionIso.adjoinAt
          (hostLocals ++ regionLocals) nextHostItems
          (RegionIso.renameWiresComp childAfter childRename
            assoc.toRenaming)
        let targetPresentation : RegionIso (WireEquiv.refl outer)
            targetBefore targetAfter :=
          (targetNested.trans targetAssociated).trans targetCombined
        have targetAfterLocalCanonical : targetAfter.Canonical :=
          targetPresentation.canonical_iff.mp
            (hostedOccurrence.context.holeCanonical _ targetCanonical)
        have targetSameNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := targetPresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        have targetReplacement := hostedOccurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterLocalCanonical
          targetSameNonempty
        let targetBeforeEndpoint := hostedOccurrence.interface.withBody
          (hostedOccurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            hostedOccurrence.interface.boundaryWire
            (hostedOccurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedOccurrence.interface.boundaryWire
            (presentedOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childStrict := childTransformation outer
          (hostLocals ++ regionLocals) nextRename nextHostItems
          presentedOccurrence presentedTargetCanonical
          presentedTargetExternalTwoEnded
        let finalBodyIso := DiagramContext.fillIso
          presentedOccurrence.context targetPresentation.symm
        let finalIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (hostedOccurrence.interface.withBody
              (hostedOccurrence.context.fill targetBefore)
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded finalBodyIso
        exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
            finalIso,
          transGen_iso finalIso childStrict.2 (OpenDiagramIso.refl source)⟩
      have hosted : HostedStrict
          (Region.adjoinAt regionLocals .nil regionResult) staged := by
        simpa only [staged] using
          liftHosted regionResult childStaged childHosted
      have presentation : RegionIso (WireEquiv.refl regionCommon)
          staged formalResult := by
        let lifted := RegionIso.adjoinAt regionLocals .nil childPresentation
        let flattened :=
          (RegionIso.adjoinAtAssoc regionLocals .nil retained .nil
            childFormalResult).symm
        let mappedUnderHost := RegionIso.adjoinAt combinedRetained .nil
          mappedResultIso
        let chained := (lifted.trans flattened).trans mappedUnderHost
        have ambientEq :
            ((WireEquiv.refl regionCommon).trans
              (WireEquiv.refl regionCommon).symm).trans
                (WireEquiv.refl regionCommon) =
              WireEquiv.refl regionCommon := by
          apply WireEquiv.ext
          intro signature wire
          rfl
        simpa only [staged, formalResult, combinedRetained,
          List.append_assoc, commonRename, Region.extendHostItems,
          ItemSeq.renameWires, ItemSeq.append_nil, ItemSeq.nil_append] using
            chained.castAmbient ambientEq
      exact ⟨staged, hosted, stagedSide, ⟨presentation⟩⟩
    case refine_3 =>
      intros
      rename_i itemsCommon itemsSourceWires itemsTargetWires itemsPattern
        itemsFrame itemsData item tail itemResult tailResult itemEvidence
        tailEvidence itemSites tailSites formalSourceWires
        formalTargetWires formalFrame formalData _closeCommon _closeTarget
        itemIH tailIH
      let values := targetValues
      obtain ⟨itemRetained, itemFormalSource, itemFormalResult,
          itemFormalEvidence, itemFormalSites, itemCoherence, itemSemantic⟩ :=
        itemIH
      obtain ⟨tailRetained, tailFormalSource, tailFormalResult,
          tailFormalEvidence, tailFormalSites, tailCoherence, tailSemantic⟩ :=
        tailIH
      unfold TargetItems
      let combinedRetained := itemRetained ++ tailRetained
      let combinedFrame := formalFrame.append combinedRetained
      let combinedData := targetOperation.appendData formalFrame formalData
        combinedRetained
      let itemCommonRename := Region.conjoinLeftWire itemsCommon itemRetained
        tailRetained
      let tailCommonRename := Region.conjoinRightWire itemsCommon itemRetained
        tailRetained
      let itemSourceRename := Region.conjoinLeftWire formalSourceWires
        itemRetained tailRetained
      let tailSourceRename := Region.conjoinRightWire formalSourceWires
        itemRetained tailRetained
      let itemTargetRename := Region.conjoinLeftWire formalTargetWires
        itemRetained tailRetained
      let tailTargetRename := Region.conjoinRightWire formalTargetWires
        itemRetained tailRetained
      have itemKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ itemRetained) signature),
          itemSourceRename
              ((formalFrame.append itemRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (itemCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := itemRetained)
          (motive := fun wire => itemSourceRename
              ((formalFrame.append itemRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (itemCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, itemSourceRename,
            itemCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinLeftWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, itemSourceRename,
            itemCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinLeftWire]
      have itemSelectedCommutes :
          itemSourceRename (formalFrame.append itemRetained).selected =
            combinedFrame.selected := by
        simp [combinedFrame, combinedRetained, itemSourceRename,
          Transform.Frame.append, Region.conjoinLeftWire]
      have itemTargetKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ itemRetained) signature),
          itemTargetRename
              ((formalFrame.append itemRetained).targetKeep wire) =
            combinedFrame.targetKeep (itemCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := itemRetained)
          (motive := fun wire => itemTargetRename
              ((formalFrame.append itemRetained).targetKeep wire) =
            combinedFrame.targetKeep (itemCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, itemTargetRename,
            itemCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinLeftWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, itemTargetRename,
            itemCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinLeftWire]
      have tailKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ tailRetained) signature),
          tailSourceRename
              ((formalFrame.append tailRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (tailCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := tailRetained)
          (motive := fun wire => tailSourceRename
              ((formalFrame.append tailRetained).sourceKeep wire) =
            combinedFrame.sourceKeep (tailCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, tailSourceRename,
            tailCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinRightWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, tailSourceRename,
            tailCommonRename, Transform.Frame.append,
            WireRenaming.appendRight, Region.conjoinRightWire]
      have tailSelectedCommutes :
          tailSourceRename (formalFrame.append tailRetained).selected =
            combinedFrame.selected := by
        simp [combinedFrame, combinedRetained, tailSourceRename,
          Transform.Frame.append, Region.conjoinRightWire]
      have tailTargetKeepCommutes : ∀ {signature}
          (wire : Var (itemsCommon ++ tailRetained) signature),
          tailTargetRename
              ((formalFrame.append tailRetained).targetKeep wire) =
            combinedFrame.targetKeep (tailCommonRename wire) := by
        intro signature wire
        apply Var.appendCases (left := itemsCommon) (right := tailRetained)
          (motive := fun wire => tailTargetRename
              ((formalFrame.append tailRetained).targetKeep wire) =
            combinedFrame.targetKeep (tailCommonRename wire))
        · intro inheritedSignature inherited
          simp [combinedFrame, combinedRetained, tailTargetRename,
            tailCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinRightWire]
        · intro localSignature localWire
          simp [combinedFrame, combinedRetained, tailTargetRename,
            tailCommonRename,
            Transform.Frame.append, WireRenaming.appendRight,
            Region.conjoinRightWire]
      obtain ⟨mappedItemSource, mappedItemResult, mappedItemEvidence,
          mappedItemSites, mappedItemSourceEq, mappedItemArgumentEq,
          ⟨mappedItemPresentation⟩,
          ⟨mappedItemEndpointPresentation⟩⟩ :=
        targetItemsReindex (mappedData := combinedData)
          (baseOperation := targetBaseOperation)
          (external := authoritativePattern.external)
          itemFormalEvidence itemFormalSites values
          itemCommonRename itemSourceRename itemTargetRename itemKeepCommutes
          itemTargetKeepCommutes itemSelectedCommutes targetSiteNatural
      obtain ⟨mappedTailSource, mappedTailResult, mappedTailEvidence,
          mappedTailSites, mappedTailSourceEq, mappedTailArgumentEq,
          ⟨mappedTailPresentation⟩,
          ⟨mappedTailEndpointPresentation⟩⟩ :=
        targetItemsReindex (mappedData := combinedData)
          (baseOperation := targetBaseOperation)
          (external := authoritativePattern.external)
          tailFormalEvidence tailFormalSites values
          tailCommonRename tailSourceRename tailTargetRename tailKeepCommutes
          tailTargetKeepCommutes tailSelectedCommutes targetSiteNatural
      obtain ⟨combinedResult, combinedEvidence, combinedSites,
          combinedArgumentEq, ⟨combinedPresentation⟩,
          ⟨combinedEndpointPresentation⟩⟩ :=
        targetItemsAppend mappedItemEvidence mappedItemSites
          mappedTailEvidence mappedTailSites values
      have mappedItemCoherence : mappedItemSource =
          (argumentItemsEdit mappedItemSites values
            (normalizationOperation targetArguments) combinedFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedItemSource = itemFormalSource.renameWires itemSourceRename :=
            mappedItemSourceEq.symm
          _ = (argumentItemsEdit itemFormalSites values
                (normalizationOperation targetArguments)
                (formalFrame.append itemRetained) PUnit.unit
                (fun _ _ _ => PUnit.unit)).1.renameWires itemSourceRename :=
            congrArg (fun items => items.renameWires itemSourceRename)
              itemCoherence
          _ = _ := mappedItemArgumentEq
      have mappedTailCoherence : mappedTailSource =
          (argumentItemsEdit mappedTailSites values
            (normalizationOperation targetArguments) combinedFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedTailSource = tailFormalSource.renameWires tailSourceRename :=
            mappedTailSourceEq.symm
          _ = (argumentItemsEdit tailFormalSites values
                (normalizationOperation targetArguments)
                (formalFrame.append tailRetained) PUnit.unit
                (fun _ _ _ => PUnit.unit)).1.renameWires tailSourceRename :=
            congrArg (fun items => items.renameWires tailSourceRename)
              tailCoherence
          _ = _ := mappedTailArgumentEq
      have combinedCoherence : mappedItemSource.append mappedTailSource =
          (argumentItemsEdit combinedSites values
            (normalizationOperation targetArguments) combinedFrame
            PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedItemSource.append mappedTailSource =
              (argumentItemsEdit mappedItemSites values
                (normalizationOperation targetArguments) combinedFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1.append
                mappedTailSource := congrArg
                  (fun first => first.append mappedTailSource)
                  mappedItemCoherence
          _ = (argumentItemsEdit mappedItemSites values
                (normalizationOperation targetArguments) combinedFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1.append
                (argumentItemsEdit mappedTailSites values
                  (normalizationOperation targetArguments) combinedFrame
                  PUnit.unit (fun _ _ _ => PUnit.unit)).1 := congrArg
                    (fun second =>
                      (argumentItemsEdit mappedItemSites values
                        (normalizationOperation targetArguments)
                        combinedFrame PUnit.unit
                        (fun _ _ _ => PUnit.unit)).1.append second)
                    mappedTailCoherence
          _ = _ := combinedArgumentEq.symm
      refine ⟨combinedRetained,
        mappedItemSource.append mappedTailSource, combinedResult,
        combinedEvidence, combinedSites, combinedCoherence, ?_⟩
      intro patternEq
      cases patternEq
      obtain ⟨itemStaged, itemHosted, itemScope, ⟨itemPresentation⟩⟩ :=
        itemSemantic rfl
      obtain ⟨tailStaged, tailHosted, tailScope, ⟨tailPresentation⟩⟩ :=
        tailSemantic rfl
      let staged := itemStaged.conjoin tailStaged
      have stagedSide : Side
          (itemResult.conjoin tailResult) staged := by
        exact sideConjoin itemScope tailScope
      have hosted : HostedStrict
          (itemResult.conjoin tailResult) staged := by
        simpa only [staged] using HostedStrict.conjoin itemResult tailResult
          itemStaged tailStaged itemHosted tailHosted
      let endpointMerged :=
        (RegionIso.conjoinCongr itemPresentation tailPresentation).trans
          (RegionIso.conjoinAdjoinAt itemRetained tailRetained
            itemFormalResult tailFormalResult)
      let mappedChildren := RegionIso.conjoinCongr mappedItemPresentation
        mappedTailPresentation
      let mappedUnderHost := RegionIso.adjoinAt combinedRetained .nil
        mappedChildren
      let combinedUnderHost := RegionIso.adjoinAt combinedRetained .nil
        combinedPresentation
      have presentation : RegionIso (WireEquiv.refl itemsCommon) staged
          (Region.adjoinAt combinedRetained .nil combinedResult) := by
        simpa only [staged, combinedRetained] using
          (endpointMerged.trans mappedUnderHost).trans combinedUnderHost
      exact ⟨staged, hosted, stagedSide, ⟨presentation⟩⟩
    case refine_4 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires itemArguments
        evidencePattern itemPattern itemFrame itemData atomHead atomPorts
        formalSourceWires formalTargetWires formalFrame formalData
        _closeCommon _closeTarget
      let values := targetValues
      unfold TargetItem
      let commonEquiv := WireEquiv.appendNil itemCommon
      let commonAppend := commonEquiv.symm.toRenaming
      let mappedHead := commonAppend atomHead
      let mappedPorts := atomPorts.map fun wire => commonAppend wire
      let childFrame := formalFrame.append []
      let childData := targetOperation.appendData formalFrame formalData []
      let formalItemResult : Region (itemCommon ++ []) :=
        Region.singleton (.atom mappedHead mappedPorts)
      let formalItemSource : Item (formalSourceWires ++ []) :=
        .atom (childFrame.sourceKeep mappedHead)
          (mappedPorts.map fun wire => childFrame.sourceKeep wire)
      let formalItemEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalItemSource formalItemResult :=
        .atom mappedHead mappedPorts
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected (.nil : ItemSeq (formalSourceWires ++ []))
            (Region.blank (itemCommon ++ [])) := .nil
      let formalSource : ItemSeq (formalSourceWires ++ []) :=
        .cons formalItemSource .nil
      let formalResult : Region (itemCommon ++ []) :=
        formalItemResult.conjoin (Region.blank (itemCommon ++ []))
      let formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalSource formalResult :=
        .cons formalItemEvidence tailEvidence
      let formalItemSites : ItemSites
          targetOperation childData
          formalItemEvidence := ItemSites.atom
            (pattern := targetPattern)
            (frame := childFrame) mappedHead mappedPorts
      let formalSites : ItemsSites
          targetOperation childData
          formalEvidence := .cons formalItemSites (.nil tailEvidence)
      let staged := Region.singleton (.atom atomHead atomPorts)
      have hosted : HostedStrict staged staged := by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        simpa only [EqualityNormalization.StrictEquates] using
          EqualityNormalization.StrictEquates.refl occurrence
      let appendRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let stagedMapped := staged.renameWires appendRename
      have stagedMappedEq : stagedMapped = formalItemResult := by
        simp only [stagedMapped, staged, appendRename, formalItemResult,
          Region.singleton_renameWires, Item.renameWires, mappedHead,
          mappedPorts, commonAppend]
      let intoMapped : RegionIso commonEquiv.symm staged formalItemResult :=
        (by
          let renamed := RegionIso.renameWires staged WireRenaming.id
            appendRename commonEquiv.symm (by
              intro signature wire
              rfl)
          rw [Region.renameWires_id] at renamed
          have targetEq : staged.renameWires appendRename =
              formalItemResult := stagedMappedEq
          rw [targetEq] at renamed
          exact renamed)
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        intoMapped.trans
          ((RegionIso.conjoinBlank formalItemResult).symm)
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      let formalPresentation := closed.castAmbient ambientEq
      refine ⟨[], formalSource, formalResult, formalEvidence, formalSites,
        by rfl, ?_⟩
      intro patternEq
      cases patternEq
      exact ⟨staged, hosted, sideRefl staged, ⟨formalPresentation⟩⟩
    case refine_5 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires evidencePattern
        itemPattern itemFrame itemData application siteData formalSourceWires
        formalTargetWires formalFrame formalData _closeCommon _closeTarget
      unfold TargetItem
      obtain ⟨retained, formalSource, formalResult, formalEvidence,
          formalSites, coherence, selectedSemantic⟩ :=
        selectedCase application siteData formalFrame formalData
      refine ⟨retained, formalSource, formalResult, formalEvidence,
        formalSites, coherence, ?_⟩
      intro patternEq
      cases patternEq
      exact selectedSemantic
    case refine_6 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires evidencePattern
        itemPattern itemFrame itemData identitySignature identityArity identityPorts
        formalSourceWires formalTargetWires formalFrame formalData
        _closeCommon _closeTarget
      let values := targetValues
      unfold TargetItem
      let commonEquiv := WireEquiv.appendNil itemCommon
      let commonAppend := commonEquiv.symm.toRenaming
      let mappedPorts := fun position => commonAppend (identityPorts position)
      let childFrame := formalFrame.append []
      let childData := targetOperation.appendData formalFrame formalData []
      let formalItemResult : Region (itemCommon ++ []) :=
        Region.singleton
          (.identity identitySignature identityArity mappedPorts)
      let formalItemSource : Item (formalSourceWires ++ []) :=
        .identity identitySignature identityArity
          (fun position => childFrame.sourceKeep (mappedPorts position))
      let formalItemEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalItemSource formalItemResult :=
        .identity identitySignature identityArity mappedPorts
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected (.nil : ItemSeq (formalSourceWires ++ []))
            (Region.blank (itemCommon ++ [])) := .nil
      let formalSource : ItemSeq (formalSourceWires ++ []) :=
        .cons formalItemSource .nil
      let formalResult : Region (itemCommon ++ []) :=
        formalItemResult.conjoin (Region.blank (itemCommon ++ []))
      let formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalSource formalResult :=
        .cons formalItemEvidence tailEvidence
      let formalItemSites : ItemSites
          targetOperation childData
          formalItemEvidence := ItemSites.identity
            (pattern := targetPattern)
            (frame := childFrame) identitySignature identityArity mappedPorts
      let formalSites : ItemsSites
          targetOperation childData
          formalEvidence := .cons formalItemSites (.nil tailEvidence)
      let staged := Region.singleton
        (.identity identitySignature identityArity identityPorts)
      have hosted : HostedStrict staged staged := by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        simpa only [EqualityNormalization.StrictEquates] using
          EqualityNormalization.StrictEquates.refl occurrence
      let appendRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let stagedMapped := staged.renameWires appendRename
      have stagedMappedEq : stagedMapped = formalItemResult := by
        simp only [stagedMapped, staged, appendRename, formalItemResult,
          Region.singleton_renameWires, Item.renameWires, mappedPorts,
          commonAppend]
      let intoMapped : RegionIso commonEquiv.symm staged formalItemResult :=
        (by
          let renamed := RegionIso.renameWires staged WireRenaming.id
            appendRename commonEquiv.symm (by
              intro signature wire
              rfl)
          rw [Region.renameWires_id] at renamed
          have targetEq : staged.renameWires appendRename =
              formalItemResult := stagedMappedEq
          rw [targetEq] at renamed
          exact renamed)
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        intoMapped.trans
          ((RegionIso.conjoinBlank formalItemResult).symm)
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      let formalPresentation := closed.castAmbient ambientEq
      refine ⟨[], formalSource, formalResult, formalEvidence, formalSites,
        by rfl, ?_⟩
      intro patternEq
      cases patternEq
      exact ⟨staged, hosted, sideRefl staged, ⟨formalPresentation⟩⟩
    case refine_7 =>
      intros
      rename_i itemCommon itemSourceWires itemTargetWires itemPattern
        itemFrame itemData body childResult childEvidence childSites
        formalSourceWires formalTargetWires formalFrame formalData
        _closeCommon _closeTarget childIH
      let values := targetValues
      unfold TargetItem
      obtain ⟨childFormalSource, childFormalResult, childFormalEvidence,
          childFormalSites, childCoherence, childSemantic⟩ :=
        childIH
      let commonEquiv := WireEquiv.appendNil itemCommon
      let commonRename : WireRenaming itemCommon (itemCommon ++ []) :=
        commonEquiv.symm.toRenaming
      let sourceEquiv := WireEquiv.appendNil formalSourceWires
      let sourceRename : WireRenaming formalSourceWires
          (formalSourceWires ++ []) := sourceEquiv.symm.toRenaming
      let targetEquiv := WireEquiv.appendNil formalTargetWires
      let targetAppend : WireRenaming formalTargetWires
          (formalTargetWires ++ []) := targetEquiv.symm.toRenaming
      let childFrame := formalFrame.append []
      let childData := targetOperation.appendData formalFrame formalData []
      have keepCommutes : ∀ {signature} (wire : Var itemCommon signature),
          sourceRename (formalFrame.sourceKeep wire) =
            childFrame.sourceKeep (commonRename wire) := by
        intro signature wire
        rw [show sourceRename (formalFrame.sourceKeep wire) =
            (formalFrame.sourceKeep wire).appendLeft [] by
          exact WireEquiv.appendNil_symm_apply formalSourceWires
            (formalFrame.sourceKeep wire)]
        rw [show commonRename wire = wire.appendLeft [] by
          exact WireEquiv.appendNil_symm_apply itemCommon wire]
        simp [childFrame, Transform.Frame.append,
          WireRenaming.appendRight]
      have selectedCommutes : sourceRename formalFrame.selected =
          childFrame.selected := by
        exact WireEquiv.appendNil_symm_apply formalSourceWires
          formalFrame.selected
      have targetKeepCommutes : ∀ {signature}
          (wire : Var itemCommon signature),
          targetAppend (formalFrame.targetKeep wire) =
            childFrame.targetKeep (commonRename wire) := by
        intro signature wire
        rw [show targetAppend (formalFrame.targetKeep wire) =
            (formalFrame.targetKeep wire).appendLeft [] by
          exact WireEquiv.appendNil_symm_apply formalTargetWires
            (formalFrame.targetKeep wire)]
        rw [show commonRename wire = wire.appendLeft [] by
          exact WireEquiv.appendNil_symm_apply itemCommon wire]
        simp [childFrame, Transform.Frame.append,
          WireRenaming.appendRight]
      obtain ⟨mappedChildSource, mappedChildResult, mappedChildEvidence,
          mappedChildSites, mappedChildSourceEq,
          mappedChildArgumentEq,
          ⟨mappedChildPresentation⟩,
          ⟨mappedChildEndpointPresentation⟩⟩ :=
        targetRegionReindex (mappedData := childData)
          (baseOperation := targetBaseOperation)
          (external := authoritativePattern.external)
          childFormalEvidence childFormalSites values
          commonRename sourceRename targetAppend keepCommutes
          targetKeepCommutes selectedCommutes targetSiteNatural
      have mappedChildCoherence : mappedChildSource =
          (argumentRegionEdit mappedChildSites values
            (normalizationOperation targetArguments) childFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        calc
          mappedChildSource = childFormalSource.renameWires sourceRename :=
            mappedChildSourceEq.symm
          _ = (argumentRegionEdit childFormalSites values
                (normalizationOperation targetArguments) formalFrame PUnit.unit
                (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
            congrArg (fun region => region.renameWires sourceRename)
              childCoherence
          _ = _ := mappedChildArgumentEq
      let formalItemSource : Item (formalSourceWires ++ []) :=
        .cut mappedChildSource
      let formalItemResult : Region (itemCommon ++ []) :=
        Region.singleton (.cut mappedChildResult)
      let formalItemEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalItemSource formalItemResult :=
        .cut mappedChildEvidence
      let tailEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected (.nil : ItemSeq (formalSourceWires ++ []))
            (Region.blank (itemCommon ++ [])) := .nil
      let formalSource : ItemSeq (formalSourceWires ++ []) :=
        .cons formalItemSource .nil
      let formalResult : Region (itemCommon ++ []) :=
        formalItemResult.conjoin (Region.blank (itemCommon ++ []))
      let formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern childFrame.sourceKeep
            childFrame.selected formalSource formalResult :=
        .cons formalItemEvidence tailEvidence
      let formalItemSites : ItemSites
          targetOperation childData
          formalItemEvidence := .cut mappedChildSites
      let formalSites : ItemsSites
          targetOperation childData
          formalEvidence := .cons formalItemSites (.nil tailEvidence)
      have formalCoherence : formalSource =
          (argumentItemsEdit formalSites values
            (normalizationOperation targetArguments) childFrame PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 := by
        unfold formalSource formalSites argumentItemsEdit formalItemSites
          argumentItemEdit
        exact congrArg (fun source => ItemSeq.cons (.cut source) .nil)
          mappedChildCoherence
      refine ⟨[], formalSource, formalResult, formalEvidence, formalSites,
        formalCoherence, ?_⟩
      intro patternEq
      cases patternEq
      obtain ⟨childStaged, childHosted, childScope,
          ⟨childPresentation⟩⟩ :=
        childSemantic rfl
      let staged := Region.singleton (.cut childStaged)
      have liftHosted : ∀ (childBefore childAfter : Region itemCommon),
          HostedStrict childBefore childAfter →
            HostedStrict (Region.singleton (.cut childBefore))
              (Region.singleton (.cut childAfter)) := by
        intro childBefore childAfter childTransformation
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let appendNil : WireRenaming itemCommon (itemCommon ++ []) :=
          ⟨fun wire => wire.appendLeft []⟩
        let materialRename := Region.adjoinMaterialWire outer hostLocals []
        let childRename := WireRenaming.comp materialRename
          (WireRenaming.comp (rename.appendRight []) appendNil)
        let retained := hostItems.renameWires
          (Region.adjoinHostWire outer hostLocals [])
        let inner : DiagramContext outer (outer ++ (hostLocals ++ [])) :=
          .cut (hostLocals ++ []) retained .nil .hole
        have childRename_eq (region : Region itemCommon) :
            Region.renameWires materialRename
                (Region.renameWires (rename.appendRight [])
                  (Region.renameWires appendNil region)) =
              Region.renameWires childRename region := by
          rw [Region.renameWires_comp, Region.renameWires_comp]
          apply congrArg (fun map => Region.renameWires map region)
          apply WireRenaming.ext
          intro signature wire
          rfl
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childBefore)).renameWires rename)
        let sourceAfter := inner.fill
          (childBefore.renameWires childRename)
        change Occurrence sourceBefore source at occurrence
        have sourceEq : sourceBefore = sourceAfter := by
          simp only [inner, retained, childRename, materialRename, appendNil,
            sourceBefore, sourceAfter, DiagramContext.fill,
            Region.renameWires, Region.singleton, Region.ofItems,
            Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have sourceAfterCanonical : sourceAfter.Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let outerOccurrence : Occurrence sourceAfter source :=
          EqualityNormalization.presentationOccurrence occurrence
            sourceAfterCanonical sourceNonempty (by
              rw [← sourceEq]
              exact RegionIso.refl _)
        let childOccurrence := EqualityNormalization.Occurrence.nest
          outerOccurrence
        let targetBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childAfter)).renameWires rename)
        let targetAfter := inner.fill
          (childAfter.renameWires childRename)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [inner, retained, childRename, materialRename,
            appendNil, targetBefore, targetAfter, DiagramContext.fill,
            Region.renameWires, Region.singleton, Region.ofItems,
            Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have childTargetCanonical :
            (childOccurrence.context.fill
              (childAfter.renameWires childRename)).Canonical := by
          simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              targetReplacement.1
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (childAfter.renameWires childRename)) := by
          intro signature wire
          simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              targetAfterExternalTwoEnded wire
        let childOuter := outer ++ (hostLocals ++ [])
        let childEmptyEquiv := WireEquiv.appendNil childOuter
        let childAppend : WireRenaming childOuter (childOuter ++ []) :=
          childEmptyEquiv.symm.toRenaming
        let hostedChildRename := WireRenaming.comp childAppend childRename
        let emptyHostIso (region : Region itemCommon) :
            RegionIso (WireEquiv.refl childOuter)
              (region.renameWires childRename)
              (Region.adjoinAt [] .nil
                (region.renameWires hostedChildRename)) := by
          let directToCollapsed := RegionIso.renameWires region childRename
            (WireRenaming.comp childEmptyEquiv.toRenaming
              hostedChildRename)
            (WireEquiv.refl childOuter) (by
              intro signature wire
              exact (childEmptyEquiv.right_inv (childRename wire)).symm)
          let collapsedFromHosted :=
            (RegionIso.renameWiresComp region hostedChildRename
              childEmptyEquiv.toRenaming).symm
          exact (directToCollapsed.trans collapsedFromHosted).trans
            (RegionIso.adjoinAtNil
              (region.renameWires hostedChildRename))
        let sourceHosted := Region.adjoinAt [] .nil
          (childBefore.renameWires hostedChildRename)
        let sourcePresentation : RegionIso (WireEquiv.refl childOuter)
            (childBefore.renameWires childRename) sourceHosted :=
          emptyHostIso childBefore
        have sourceHostedCanonical : sourceHosted.Canonical :=
          sourcePresentation.canonical_iff.mp
            (childOccurrence.context.holeCanonical _
              childOccurrence.sourceCanonical)
        have sourceHostedNonempty : ∀ {signature}
            (wire : Var childOuter signature),
            (childBefore.renameWires childRename).incidencePaths
                wire.index.val ≠ [] ↔
              sourceHosted.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := sourcePresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        let presentedChildOccurrence : Occurrence sourceHosted source :=
          EqualityNormalization.presentationOccurrence childOccurrence
            sourceHostedCanonical sourceHostedNonempty sourcePresentation
        let targetHosted := Region.adjoinAt [] .nil
          (childAfter.renameWires hostedChildRename)
        let targetPresentation : RegionIso (WireEquiv.refl childOuter)
            (childAfter.renameWires childRename) targetHosted :=
          emptyHostIso childAfter
        have targetHostedCanonical : targetHosted.Canonical :=
          targetPresentation.canonical_iff.mp
            (childOccurrence.context.holeCanonical _ childTargetCanonical)
        have targetHostedNonempty : ∀ {signature}
            (wire : Var childOuter signature),
            (childAfter.renameWires childRename).incidencePaths
                wire.index.val ≠ [] ↔
              targetHosted.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          have lengthEq := targetPresentation.incidencePaths_length_eq wire
          exact ⟨fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [← lengthEq], fun nonempty => by
            rw [← List.length_pos_iff] at nonempty ⊢
            rwa [lengthEq]⟩
        have targetHostedReplacement :=
          childOccurrence.context.replaceCanonical
            (childAfter.renameWires childRename) targetHosted
            childTargetCanonical targetHostedCanonical targetHostedNonempty
        let childTargetEndpoint := childOccurrence.interface.withBody
          (childOccurrence.context.fill
            (childAfter.renameWires childRename))
          childTargetCanonical childTargetExternalTwoEnded
        have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill targetHosted) :=
          childTargetEndpoint.externalTwoEnded_of_nonempty_iff _
            targetHostedReplacement.2
        have presentedTargetCanonical :
            (presentedChildOccurrence.context.fill targetHosted).Canonical := by
          exact targetHostedReplacement.1
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedChildOccurrence.interface.boundaryWire
            (presentedChildOccurrence.context.fill targetHosted) := by
          intro signature wire
          exact targetHostedExternalTwoEnded wire
        have childStrict := childTransformation childOuter [] hostedChildRename .nil
          presentedChildOccurrence presentedTargetCanonical
            presentedTargetExternalTwoEnded
        let hostedToDirect : OpenDiagramIso
            (presentedChildOccurrence.interface.withBody
              (presentedChildOccurrence.context.fill targetHosted)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                (childAfter.renameWires childRename))
              childTargetCanonical childTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical
            childTargetCanonical presentedTargetExternalTwoEnded
            childTargetExternalTwoEnded
            (DiagramContext.fillIso childOccurrence.context
              targetPresentation.symm)
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          rw [← targetEq]
          exact RegionIso.refl _
        have outerFinalIso : OpenDiagramIso
            (outerOccurrence.interface.withBody
              (outerOccurrence.context.fill targetAfter)
              targetReplacement.1 targetAfterExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso targetReplacement.1 targetCanonical
            targetAfterExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have directToOuter : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                (childAfter.renameWires childRename))
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) := by
          simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerFinalIso
        let finalIso := hostedToDirect.trans directToOuter
        exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
            finalIso,
          transGen_iso finalIso childStrict.2
            (OpenDiagramIso.refl source)⟩
      have hosted : HostedStrict
          (Region.singleton (.cut childResult)) staged := by
        simpa only [staged] using
          liftHosted childResult childStaged childHosted
      let stagedCollapse : RegionIso commonEquiv
          (childStaged.renameWires commonRename) childStaged := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires childStaged commonRename WireRenaming.id
            commonEquiv (by
              intro signature wire
              exact commonEquiv.right_inv wire)
      let resultForward : RegionIso commonEquiv.symm childFormalResult
          (childFormalResult.renameWires commonRename) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires childFormalResult WireRenaming.id
            commonRename commonEquiv.symm (by
              intro signature wire
              rfl)
      let renamedChildPresentationRaw :=
        (stagedCollapse.trans childPresentation).trans resultForward
      have renamedAmbientEq :
          ((commonEquiv.trans (WireEquiv.refl itemCommon)).trans
            commonEquiv.symm) = WireEquiv.refl (itemCommon ++ []) := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.left_inv wire
      let renamedChildPresentation :
          RegionIso (WireEquiv.refl (itemCommon ++ []))
            (childStaged.renameWires commonRename)
            (childFormalResult.renameWires commonRename) :=
        renamedChildPresentationRaw.castAmbient renamedAmbientEq
      let childIntoMapped : RegionIso (WireEquiv.refl (itemCommon ++ []))
          (childStaged.renameWires commonRename) mappedChildResult :=
        renamedChildPresentation.trans mappedChildPresentation
      let itemIntoMapped :=
        RegionIso.singletonCutCongr childIntoMapped
      let stagedIntoMapped : RegionIso commonEquiv.symm staged
          formalItemResult := by
        let renamed := RegionIso.renameWires staged WireRenaming.id
          commonRename commonEquiv.symm (by
            intro signature wire
            rfl)
        rw [Region.renameWires_id] at renamed
        let mappedStaged := Region.singleton
          (.cut (childStaged.renameWires commonRename))
        have targetEq : staged.renameWires commonRename = mappedStaged := by
          simp only [staged, mappedStaged, Region.singleton_renameWires,
            Item.renameWires]
        rw [targetEq] at renamed
        exact renamed.trans itemIntoMapped
      let intoFormal : RegionIso commonEquiv.symm staged formalResult :=
        stagedIntoMapped.trans
          ((RegionIso.conjoinBlank formalItemResult).symm)
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by
              intro signature wire
              rfl)
      let closed := (intoFormal.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq :
          ((commonEquiv.symm.trans commonEquiv).trans
            (WireEquiv.refl itemCommon)) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      exact ⟨staged, hosted, sideCut childScope,
        ⟨closed.castAmbient ambientEq⟩⟩
  obtain ⟨retained, formalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, semantic⟩ :=
    foldedFamilyWithPattern
  refine ⟨retained, formalSource, formalResult, formalEvidence,
    formalSites, formalCoherence, ?_⟩
  exact semantic rfl

/-- Accumulate the hosted transformation and its literal formal target through
one authoritative traversal.  Endpoint validity is deliberately outside this
interface: callers provide it only when they apply the returned `HostedStrict`.
-/
theorem accumulateHostedTarget
    {targetArguments patternWires outer before after targetInserted
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetBaseOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram patternWires}
    {originalFrame : Transform.Frame patternWires
      (outer ++ (before ++ after)) originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires}
    {result : Region (outer ++ (before ++ after))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    (targetValues : Vars pattern.external targetArguments)
    (targetData : targetBaseOperation.Data
      (Transform.Frame.replace outer before after targetInserted
        targetArguments))
    (targetSiteNatural : ∀
      {siteCommon siteMappedCommon siteSourceWires siteMappedSourceWires
        siteTargetWires siteMappedTargetWires : List Sig}
      {siteFrame : Transform.Frame targetArguments siteCommon siteSourceWires
        siteTargetWires}
      {siteMappedFrame : Transform.Frame targetArguments siteMappedCommon
        siteMappedSourceWires siteMappedTargetWires}
      {siteData : targetBaseOperation.Data siteFrame}
      {siteMappedData : targetBaseOperation.Data siteMappedFrame}
      (siteCommonRename : WireRenaming siteCommon siteMappedCommon)
      (siteTargetRename : WireRenaming siteTargetWires
        siteMappedTargetWires)
      (_siteTargetKeepCommutes : ∀ {wireSignature}
        (wire : Var siteCommon wireSignature),
        siteTargetRename (siteFrame.targetKeep wire) =
          siteMappedFrame.targetKeep (siteCommonRename wire))
      (ports : Vars siteCommon targetArguments)
      (site : (recordingOperation targetBaseOperation
        pattern.external).SiteData siteFrame siteData ports),
      ∃ mappedSite : (recordingOperation targetBaseOperation
          pattern.external).SiteData siteMappedFrame siteMappedData
          (ports.map fun wire => siteCommonRename wire),
        Nonempty (RegionIso (WireEquiv.refl siteMappedTargetWires)
          (((recordingOperation targetBaseOperation pattern.external).site
            siteFrame siteData ports site).renameWires siteTargetRename)
          ((recordingOperation targetBaseOperation pattern.external).site
            siteMappedFrame siteMappedData
            (ports.map fun wire => siteCommonRename wire) mappedSite)))
    (selectedCase : ∀
      {itemCommon itemSourceWires itemTargetWires : List Sig}
      {itemFrame : Transform.Frame patternWires itemCommon
        itemSourceWires itemTargetWires}
      {itemOperation : Transform.Operation patternWires}
      {itemData : itemOperation.Data itemFrame}
      (application : Vars itemCommon patternWires)
      (siteData : itemOperation.SiteData itemFrame itemData application)
      {selectedTargetSourceWires selectedTargetWires : List Sig}
      (selectedTargetFrame : Transform.Frame targetArguments itemCommon
        selectedTargetSourceWires selectedTargetWires)
      (selectedTargetData : targetBaseOperation.Data selectedTargetFrame),
      TargetItem
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := pattern) (retain := itemFrame.sourceKeep)
          (selected := itemFrame.selected) application)
        (ItemSites.selectedAtom (operation := itemOperation)
          (pattern := pattern) (frame := itemFrame) application siteData)
        targetValues selectedTargetFrame selectedTargetData
        (fun retained _formalSource formalResult _formalEvidence _formalSites
            _coherence =>
          ∃ staged : Region itemCommon,
            HostedStrict
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult)))) :
    TargetItems
      (targetPattern := targetPattern)
      (targetOperation := targetBaseOperation)
      evidence sites targetValues
      (Transform.Frame.replace outer before after targetInserted
        targetArguments) targetData
      (fun retained _formalSource formalResult _formalEvidence _formalSites
          _coherence =>
        ∃ staged : Region (outer ++ (before ++ after)),
          HostedStrict result staged ∧
            Nonempty (RegionIso
              (WireEquiv.refl (outer ++ (before ++ after))) staged
              (Region.adjoinAt retained .nil formalResult))) := by
  have selectedWithUnit : ∀
      {itemCommon itemSourceWires itemTargetWires : List Sig}
      {itemFrame : Transform.Frame patternWires itemCommon
        itemSourceWires itemTargetWires}
      {itemOperation : Transform.Operation patternWires}
      {itemData : itemOperation.Data itemFrame}
      (application : Vars itemCommon patternWires)
      (siteData : itemOperation.SiteData itemFrame itemData application)
      {selectedTargetSourceWires selectedTargetWires : List Sig}
      (selectedTargetFrame : Transform.Frame targetArguments itemCommon
        selectedTargetSourceWires selectedTargetWires)
      (selectedTargetData : targetBaseOperation.Data selectedTargetFrame),
      TargetItem
        (targetPattern := targetPattern)
        (targetOperation := targetBaseOperation)
        (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
          (pattern := pattern) (retain := itemFrame.sourceKeep)
          (selected := itemFrame.selected) application)
        (ItemSites.selectedAtom (operation := itemOperation)
          (pattern := pattern) (frame := itemFrame) application siteData)
        targetValues selectedTargetFrame selectedTargetData
        (fun retained _formalSource formalResult _formalEvidence _formalSites
            _coherence =>
          ∃ staged : Region itemCommon,
            HostedStrict
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              True ∧
                Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                  (Region.adjoinAt retained .nil formalResult))) := by
    intro itemCommon itemSourceWires itemTargetWires itemFrame itemOperation
      itemData application siteData selectedTargetSourceWires
      selectedTargetWires selectedTargetFrame selectedTargetData
    obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
        coherence, staged, hosted, presentation⟩ :=
      selectedCase application siteData selectedTargetFrame selectedTargetData
    exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      coherence, staged, hosted, True.intro, presentation⟩
  obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      coherence, staged, hosted, _unit, presentation⟩ :=
    accumulateHostedTargetWith evidence sites targetValues targetData
      (fun {_} _ _ => True)
      (fun _ => True.intro)
      (fun _ _ _ _ => True.intro)
      (fun _ _ => True.intro)
      (fun _ => True.intro)
      targetSiteNatural selectedWithUnit
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    coherence, staged, hosted, presentation⟩

/-- Accumulate every selected application in one authoritative item sequence
into the single literal positional-Formal edit consumed at the binder home. -/
theorem accumulateAtomFormal
    {patternWires atomArguments common originalSourceWires
      originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel (positionalAtomWires atomArguments) :: retained)),
        ∃ formalResult : Region (common ++ retained),
          ∃ formalEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalAtomPattern atomArguments)
                (Leaf.Formal.rootFrame common [] retained []
                  atomArguments).sourceKeep
                (Leaf.Formal.rootFrame common [] retained []
                  atomArguments).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation (Leaf.Formal.operation [] atomArguments)
                  pattern.external) PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (positionalAtomSelection head ports)
                    (normalizationOperation (positionalAtomWires atomArguments))
                    (Leaf.Formal.rootFrame common [] retained []
                      atomArguments) PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1,
                let output := itemsEdit
                  (operation := recordingOperation
                    (Leaf.Formal.operation [] atomArguments) pattern.external)
                  PUnit.unit formalEvidence formalSites
                ∃ outputCanonical :
                  (occurrence.context.fill
                    (Region.adjoinAt retained .nil output.endpoint)).Canonical,
                ∃ outputExternalTwoEnded :
                    OpenDiagram.ExternalTwoEnded
                      occurrence.interface.boundaryWire
                      (occurrence.context.fill
                        (Region.adjoinAt retained .nil output.endpoint)),
                  EqualityNormalization.StrictEquates occurrence
                    (Region.adjoinAt retained .nil output.endpoint)
                    outputCanonical outputExternalTwoEnded := by
  let initialFrame : Transform.Frame (positionalAtomWires atomArguments)
      common (.rel (positionalAtomWires atomArguments) :: common) common :=
    Transform.Frame.replace [] [] common []
      (positionalAtomWires atomArguments)
  have folded : TargetItems
      (targetPattern := positionalAtomPattern atomArguments)
      (targetOperation := Leaf.Formal.operation [] atomArguments)
      evidence sites (positionalAtomSelection head ports) initialFrame
        PUnit.unit
        (fun retained _formalSource formalResult formalEvidence formalSites
            _coherence =>
          ∃ staged : Region common,
            HostedStrict result staged ∧
              ScopePreservation result staged ∧
                Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult))) :=
    accumulateHostedTargetWith evidence sites
      (positionalAtomSelection head ports)
      (outer := []) (before := []) (after := common)
      PUnit.unit ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      formalRecordingSiteNatural
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemOperation} {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame
          selectedData => by
        cases selectedData
        exact atomSelectedTargetItem body_eq application siteData selectedFrame)
  obtain ⟨retained, rawFormalSource, rawFormalResult, rawFormalEvidence,
      rawFormalSites, rawCoherence, rawStaged, rawHosted, rawScope,
      ⟨rawPresentation⟩⟩ := folded
  let canonicalFrame := Leaf.Formal.rootFrame common [] retained []
    atomArguments
  let move := WireEquiv.rotate [] common
    [.rel (positionalAtomWires atomArguments)]
  let forward := move.append (WireEquiv.refl retained)
  let reassociate : WireEquiv
      ((common ++ [.rel (positionalAtomWires atomArguments)]) ++ retained)
      (common ++ ([] ++ .rel (positionalAtomWires atomArguments) :: retained)) :=
    WireEquiv.ofEq (by simp)
  let sourceEquiv := forward.symm.trans reassociate
  let sourceRename := sourceEquiv.toRenaming
  let commonRename : WireRenaming (common ++ retained)
      (common ++ retained) := WireRenaming.id
  have sourceRename_common {wireSignature}
      (wire : Var common wireSignature) :
      sourceRename
          ((Var.appendRight [.rel (positionalAtomWires atomArguments)] wire).appendLeft
            retained) =
        wire.appendLeft
          (.rel (positionalAtomWires atomArguments) :: retained) := by
    let targetWire :=
      (wire.appendLeft [.rel (positionalAtomWires atomArguments)]).appendLeft
        retained
    have forwardEq : forward targetWire =
        (Var.appendRight [.rel (positionalAtomWires atomArguments)] wire).appendLeft
          retained := by
      calc
        forward targetWire =
            (move
              (wire.appendLeft
                [.rel (positionalAtomWires atomArguments)])).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (wire.appendLeft
              [.rel (positionalAtomWires atomArguments)])
        _ = (Var.appendRight
              [.rel (positionalAtomWires atomArguments)] wire).appendLeft
            retained := by
          change
            ((WireEquiv.rotate [] common
                [.rel (positionalAtomWires atomArguments)])
              ((Var.appendRight [] wire).appendLeft
                [.rel (positionalAtomWires atomArguments)])).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_middle]
          rfl
    calc
      sourceRename
          ((Var.appendRight
              [.rel (positionalAtomWires atomArguments)] wire).appendLeft
            retained) =
          reassociate
            (forward.symm
              ((Var.appendRight
                  [.rel (positionalAtomWires atomArguments)] wire).appendLeft
                retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = wire.appendLeft
          (.rel (positionalAtomWires atomArguments) :: retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        simp [targetWire]
  have sourceRename_retained {wireSignature}
      (wire : Var retained wireSignature) :
      sourceRename (Var.appendRight
          (.rel (positionalAtomWires atomArguments) :: common) wire) =
        Var.appendRight common (.there wire) := by
    let targetWire := Var.appendRight
      (common ++ [.rel (positionalAtomWires atomArguments)]) wire
    have forwardEq : forward targetWire = Var.appendRight
        (.rel (positionalAtomWires atomArguments) :: common) wire := by
      change
        (move.append (WireEquiv.refl retained))
            (Var.appendRight
              ([] ++ common ++
                [.rel (positionalAtomWires atomArguments)]) wire) = _
      rw [WireEquiv.append_apply_right]
      rfl
    calc
      sourceRename
          (Var.appendRight
            (.rel (positionalAtomWires atomArguments) :: common) wire) =
          reassociate
            (forward.symm
              (Var.appendRight
                (.rel (positionalAtomWires atomArguments) :: common) wire)) :=
        rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common (.there wire) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        change targetWire.index.val =
          (Var.appendRight common (.there wire)).index.val
        calc
          targetWire.index.val =
              (common ++
                [Sig.rel (positionalAtomWires atomArguments)]).length +
                wire.index.val :=
            Var.index_appendRight
              (common ++
                [Sig.rel (positionalAtomWires atomArguments)]) wire
          _ = common.length + (Var.there wire).index.val := by
            simp only [List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Var.index, Fin.val_succ]
            omega
          _ = (Var.appendRight common (.there wire)).index.val :=
            (Var.index_appendRight common (.there wire)).symm
  have sourceRename_selected :
      sourceRename ((.here : Var
          (.rel (positionalAtomWires atomArguments) :: common)
          (.rel (positionalAtomWires atomArguments))).appendLeft retained) =
        Var.appendRight common
          ((.here : Var [.rel (positionalAtomWires atomArguments)]
            (.rel (positionalAtomWires atomArguments))).appendLeft retained) := by
    let targetWire := (Var.appendRight common (.here : Var
      [.rel (positionalAtomWires atomArguments)]
      (.rel (positionalAtomWires atomArguments)))).appendLeft retained
    have forwardEq : forward targetWire =
        ((.here : Var
          (.rel (positionalAtomWires atomArguments) :: common)
          (.rel (positionalAtomWires atomArguments))).appendLeft retained) := by
      calc
        forward targetWire =
            (move
              (Var.appendRight common
                (.here : Var [.rel (positionalAtomWires atomArguments)]
                  (.rel (positionalAtomWires atomArguments))))).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (Var.appendRight common
              (.here : Var [.rel (positionalAtomWires atomArguments)]
                (.rel (positionalAtomWires atomArguments))))
        _ = ((.here : Var
              (.rel (positionalAtomWires atomArguments) :: common)
              (.rel (positionalAtomWires atomArguments))).appendLeft
            retained) := by
          change
            ((WireEquiv.rotate [] common
                [.rel (positionalAtomWires atomArguments)])
              (Var.appendRight ([] ++ common)
                (.here : Var [.rel (positionalAtomWires atomArguments)]
                  (.rel (positionalAtomWires atomArguments))))).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_suffix]
          rfl
    calc
      sourceRename
          ((.here : Var
            (.rel (positionalAtomWires atomArguments) :: common)
            (.rel (positionalAtomWires atomArguments))).appendLeft retained) =
          reassociate
            (forward.symm
              ((.here : Var
                (.rel (positionalAtomWires atomArguments) :: common)
                (.rel (positionalAtomWires atomArguments))).appendLeft
                  retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common
          ((.here : Var [.rel (positionalAtomWires atomArguments)]
            (.rel (positionalAtomWires atomArguments))).appendLeft retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        let binder := (.here :
          Var [.rel (positionalAtomWires atomArguments)]
            (.rel (positionalAtomWires atomArguments)))
        change targetWire.index.val =
          (Var.appendRight common (binder.appendLeft retained)).index.val
        calc
          targetWire.index.val =
              (Var.appendRight common binder).index.val :=
            Var.index_appendLeft (Var.appendRight common binder) retained
          _ = common.length + binder.index.val :=
            Var.index_appendRight common binder
          _ = common.length + (binder.appendLeft retained).index.val := by
            rw [Var.index_appendLeft]
          _ = (Var.appendRight common
                (binder.appendLeft retained)).index.val :=
            (Var.index_appendRight common
              (binder.appendLeft retained)).symm
  have keepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      sourceRename ((initialFrame.append retained).sourceKeep wire) =
        canonicalFrame.sourceKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        sourceRename ((initialFrame.append retained).sourceKeep wire) =
          canonicalFrame.sourceKeep (commonRename wire))
    · intro inheritedSignature inherited
      rw [show (initialFrame.append retained).sourceKeep
          (inherited.appendLeft retained) =
          (Var.appendRight [.rel (positionalAtomWires atomArguments)] inherited).appendLeft
            retained by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_common]
      simp [commonRename, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap,
        Var.appendRight]
      unfold positionalAtomWires
      rfl
    · intro retainedSignature retainedWire
      rw [show (initialFrame.append retained).sourceKeep
          (Var.appendRight common retainedWire) =
          Var.appendRight
            (.rel (positionalAtomWires atomArguments) :: common)
            retainedWire by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_retained]
      simp [commonRename, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Region.adjoinMaterialWire, Var.appendMap,
        Var.appendRight]
      rfl
  have targetKeepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      commonRename ((initialFrame.append retained).targetKeep wire) =
        canonicalFrame.targetKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        commonRename ((initialFrame.append retained).targetKeep wire) =
          canonicalFrame.targetKeep (commonRename wire))
    · intro inheritedSignature inherited
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
    · intro retainedSignature retainedWire
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
  have selectedCommutes :
      sourceRename (initialFrame.append retained).selected =
        canonicalFrame.selected := by
    rw [show (initialFrame.append retained).selected =
        ((.here : Var
          (.rel (positionalAtomWires atomArguments) :: common)
          (.rel (positionalAtomWires atomArguments))).appendLeft retained) by rfl]
    rw [sourceRename_selected]
    simp [canonicalFrame,
      Leaf.Formal.rootFrame, Transform.Frame.replace,
      Transform.Frame.append, Transform.Frame.insertedHead,
      Var.appendLeft, Var.appendRight]
    rfl
  obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
      formalSourceEq, formalArgumentEq, ⟨formalPresentation⟩,
      ⟨formalEndpointPresentation⟩⟩ :=
    targetItemsReindex rawFormalEvidence rawFormalSites
      (positionalAtomSelection head ports) commonRename
      sourceRename commonRename keepCommutes targetKeepCommutes
      selectedCommutes formalRecordingSiteNatural
  have formalCoherence : formalSource =
      (argumentItemsEdit formalSites (positionalAtomSelection head ports)
        (normalizationOperation (positionalAtomWires atomArguments))
        canonicalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    calc
      formalSource = rawFormalSource.renameWires sourceRename :=
        formalSourceEq.symm
      _ = (argumentItemsEdit rawFormalSites
            (positionalAtomSelection head ports)
            (normalizationOperation (positionalAtomWires atomArguments))
            (initialFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
        congrArg (fun items => items.renameWires sourceRename) rawCoherence
      _ = _ := formalArgumentEq
  let output := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit formalEvidence formalSites
  let exactOutput := Region.adjoinAt retained .nil output.endpoint
  let rawResultRename : RegionIso (WireEquiv.refl (common ++ retained))
      rawFormalResult (rawFormalResult.renameWires commonRename) := by
    simpa only [commonRename] using
      RegionIso.ofEq (Region.renameWires_id rawFormalResult).symm
  have targetKeepIdentity : canonicalFrame.targetKeep = WireRenaming.id :=
    formalRootFrame_targetKeep common retained atomArguments
  obtain ⟨leafHosted, leafScope⟩ :=
    leafItemsEndpoint formalEvidence formalSites targetKeepIdentity
      (fun siteTargetKeepEq application site =>
        positionalAtomLeafEndpoint atomArguments siteTargetKeepEq
          application site)
  let formalStart := Region.adjoinAt retained .nil formalResult
  let formalPresentationIso : RegionIso (WireEquiv.refl common)
      rawStaged formalStart :=
    (rawPresentation.trans
      (RegionIso.adjoinAt retained .nil rawResultRename)).trans
      (RegionIso.adjoinAt retained .nil formalPresentation)
  have liftedLeafHosted : HostedStrict formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      HostedStrict.adjoinAt retained formalResult output.endpoint leafHosted
  have liftedLeafScope : ScopePreservation formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      adjoinAt_preserves_scope retained .nil formalResult output.endpoint
        leafScope
  let emptyEquiv := WireEquiv.appendNil common
  let emptyRename : WireRenaming common (common ++ []) :=
    emptyEquiv.symm.toRenaming
  let emptyHostIso (region : Region common) :
      RegionIso (WireEquiv.refl common) region
        (Region.adjoinAt [] .nil (region.renameWires emptyRename)) := by
    let directToCollapsed := RegionIso.renameWires region WireRenaming.id
      (WireRenaming.comp emptyEquiv.toRenaming emptyRename)
      (WireEquiv.refl common) (by
        intro signature wire
        exact (emptyEquiv.right_inv wire).symm)
    let collapsedFromHosted :=
      (RegionIso.renameWiresComp region emptyRename
        emptyEquiv.toRenaming).symm
    let chained := (directToCollapsed.trans collapsedFromHosted).trans
      (RegionIso.adjoinAtNil (region.renameWires emptyRename))
    have ambientEq :
        (((WireEquiv.refl common).trans
          (WireEquiv.refl common).symm).trans
            (WireEquiv.refl common)) = WireEquiv.refl common := by
      apply WireEquiv.ext
      intro signature wire
      rfl
    simpa only [Region.renameWires_id] using chained.castAmbient ambientEq
  let sourceHosted := Region.adjoinAt [] .nil
    (result.renameWires emptyRename)
  let targetHosted := Region.adjoinAt [] .nil
    (rawStaged.renameWires emptyRename)
  let sourceHostedIso : RegionIso (WireEquiv.refl common)
      result sourceHosted := emptyHostIso result
  let targetHostedIso : RegionIso (WireEquiv.refl common)
      rawStaged targetHosted := emptyHostIso rawStaged
  have sourceHostedCanonical : sourceHosted.Canonical :=
    sourceHostedIso.canonical_iff.mp
      (occurrence.context.holeCanonical result occurrence.sourceCanonical)
  have sourceHostedNonempty : ∀ {signature} (wire : Var common signature),
      result.incidencePaths wire.index.val ≠ [] ↔
        sourceHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourceHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let rootOccurrence : Occurrence sourceHosted host :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceHostedCanonical sourceHostedNonempty sourceHostedIso
  have hostedScope : ScopePreservation sourceHosted targetHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso sourceHostedIso.symm)
      (ScopePreservation.trans rawScope
        (ScopePreservation.ofIso targetHostedIso))
  have targetHostedCanonical : targetHosted.Canonical :=
    hostedScope.canonical sourceHostedCanonical
  have targetHostedReplacement := rootOccurrence.context.replaceCanonical
    sourceHosted targetHosted rootOccurrence.sourceCanonical
      targetHostedCanonical hostedScope.incidenceNonempty
  let sourceHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill sourceHosted) rootOccurrence.sourceCanonical
      rootOccurrence.sourceExternalTwoEnded
  have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill targetHosted) :=
    sourceHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      targetHostedReplacement.2
  have hostedStrict := rawHosted common [] emptyRename .nil
    rootOccurrence targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalHosted := Region.adjoinAt [] .nil
    ((formalStart : Region common).renameWires emptyRename)
  let exactHosted := Region.adjoinAt [] .nil
    (exactOutput.renameWires emptyRename)
  let formalHostedIso : RegionIso (WireEquiv.refl common)
      targetHosted formalHosted :=
    (targetHostedIso.symm.trans formalPresentationIso).trans
      (emptyHostIso formalStart)
  have formalHostedCanonical : formalHosted.Canonical :=
    formalHostedIso.canonical_iff.mp targetHostedCanonical
  have formalHostedNonempty : ∀ {signature} (wire : Var common signature),
      targetHosted.incidencePaths wire.index.val ≠ [] ↔
        formalHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := formalHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have formalReplacement := rootOccurrence.context.replaceCanonical
    targetHosted formalHosted targetHostedReplacement.1
      formalHostedCanonical formalHostedNonempty
  let targetHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill targetHosted) targetHostedReplacement.1
      targetHostedExternalTwoEnded
  have formalHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill formalHosted) :=
    targetHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      formalReplacement.2
  let targetHostedOccurrence : Occurrence targetHosted targetHostedEndpoint :=
    exactOccurrence rootOccurrence.interface rootOccurrence.context
      targetHosted targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalOccurrence : Occurrence formalHosted targetHostedEndpoint :=
    EqualityNormalization.presentationOccurrence targetHostedOccurrence
      formalHostedCanonical formalHostedNonempty formalHostedIso
  let formalEmptyIso := emptyHostIso formalStart
  let exactEmptyIso := emptyHostIso exactOutput
  have hostedLeafScope : ScopePreservation formalHosted exactHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso formalEmptyIso.symm)
      (ScopePreservation.trans liftedLeafScope
        (ScopePreservation.ofIso exactEmptyIso))
  have exactHostedCanonical : exactHosted.Canonical :=
    hostedLeafScope.canonical formalHostedCanonical
  have exactHostedReplacement := formalOccurrence.context.replaceCanonical
    formalHosted exactHosted formalOccurrence.sourceCanonical
      exactHostedCanonical hostedLeafScope.incidenceNonempty
  let formalHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill formalHosted)
      formalOccurrence.sourceCanonical formalOccurrence.sourceExternalTwoEnded
  have exactHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      formalOccurrence.interface.boundaryWire
      (formalOccurrence.context.fill exactHosted) :=
    formalHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactHostedReplacement.2
  have leafStrict := liftedLeafHosted common [] emptyRename .nil
    formalOccurrence exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactLocalCanonical : exactOutput.Canonical :=
    exactEmptyIso.canonical_iff.mpr exactHostedCanonical
  have exactNonempty : ∀ {signature} (wire : Var common signature),
      exactHosted.incidencePaths wire.index.val ≠ [] ↔
        exactOutput.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := exactEmptyIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq]⟩
  have exactReplacement := formalOccurrence.context.replaceCanonical
    exactHosted exactOutput exactHostedReplacement.1 exactLocalCanonical
      exactNonempty
  let exactHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill exactHosted) exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill exactOutput) :=
    exactHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactReplacement.2
  let exactTargetIso : OpenDiagramIso
      (formalOccurrence.interface.withBody
        (formalOccurrence.context.fill exactHosted)
        exactHostedReplacement.1 exactHostedExternalTwoEnded)
      (rootOccurrence.interface.withBody
        (rootOccurrence.context.fill exactOutput)
        exactReplacement.1 exactExternalTwoEnded) :=
    OpenDiagram.withBody_iso exactHostedReplacement.1 exactReplacement.1
      exactHostedExternalTwoEnded exactExternalTwoEnded
      (DiagramContext.fillIso rootOccurrence.context exactEmptyIso.symm)
  have presentedLeafStrict : EqualityNormalization.StrictEquates
      formalOccurrence exactOutput exactReplacement.1 exactExternalTwoEnded :=
    EqualityNormalization.StrictEquates.targetIso leafStrict exactTargetIso
  have presentedStrict : EqualityNormalization.StrictEquates rootOccurrence
      exactOutput exactReplacement.1 exactExternalTwoEnded :=
    ⟨hostedStrict.1.trans presentedLeafStrict.1,
      presentedLeafStrict.2.trans hostedStrict.2⟩
  have strict : EqualityNormalization.StrictEquates occurrence exactOutput
      exactReplacement.1 exactExternalTwoEnded := by
    simpa only [EqualityNormalization.StrictEquates, rootOccurrence,
      EqualityNormalization.presentationOccurrence] using presentedStrict
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, exactReplacement.1, exactExternalTwoEnded, strict⟩

/-- Accumulate every selected application of an authoritative identity-headed
pattern into one literal IdentityLeaf edit consumed at the binder home. -/
theorem accumulateIdentity
    {patternWires common originalSourceWires originalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel (List.replicate arity signature) :: retained)),
        ∃ formalResult : Region (common ++ retained),
          ∃ formalEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalIdentityPattern signature arity)
                (Leaf.Identity.rootFrame common [] retained signature arity).sourceKeep
                (Leaf.Identity.rootFrame common [] retained signature arity).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation
                  (Leaf.Identity.operation signature arity) pattern.external)
                PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (Leaf.Identity.Vars.fromFn ports)
                    (normalizationOperation
                      (List.replicate arity signature))
                    (Leaf.Identity.rootFrame common [] retained signature arity)
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1,
              let primitiveSites := recordingItemsSitesTarget formalSites
              let output := itemsEdit
                (operation := Leaf.Identity.operation signature arity)
                PUnit.unit formalEvidence primitiveSites
              ∃ outputCanonical :
                  (occurrence.context.fill
                    (Region.adjoinAt retained .nil output.endpoint)).Canonical,
                ∃ outputExternalTwoEnded :
                    OpenDiagram.ExternalTwoEnded
                      occurrence.interface.boundaryWire
                      (occurrence.context.fill
                        (Region.adjoinAt retained .nil output.endpoint)),
                  EqualityNormalization.StrictEquates occurrence
                    (Region.adjoinAt retained .nil output.endpoint)
                    outputCanonical outputExternalTwoEnded := by
  let initialFrame : Transform.Frame (List.replicate arity signature)
      common (.rel (List.replicate arity signature) :: common) common :=
    Transform.Frame.replace [] [] common []
      (List.replicate arity signature)
  have folded : TargetItems
      (targetPattern := positionalIdentityPattern signature arity)
      (targetOperation := Leaf.Identity.operation signature arity)
      evidence sites (Leaf.Identity.Vars.fromFn ports) initialFrame PUnit.unit
        (fun retained _formalSource formalResult formalEvidence formalSites
            _coherence =>
          ∃ staged : Region common,
            HostedStrict result staged ∧
              ScopePreservation result staged ∧
                Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult))) :=
    accumulateHostedTargetWith evidence sites
      (Leaf.Identity.Vars.fromFn ports)
      (outer := []) (before := []) (after := common)
      PUnit.unit ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      identityRecordingSiteNatural
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemOperation} {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame
          selectedData => by
        exact identitySelectedTargetItem body_eq application siteData
          selectedFrame)
  obtain ⟨retained, rawFormalSource, rawFormalResult, rawFormalEvidence,
      rawFormalSites, rawCoherence, rawStaged, rawHosted, rawScope,
      ⟨rawPresentation⟩⟩ := folded
  let canonicalFrame := Leaf.Identity.rootFrame common [] retained signature
    arity
  let move := WireEquiv.rotate [] common
    [.rel (List.replicate arity signature)]
  let forward := move.append (WireEquiv.refl retained)
  let reassociate : WireEquiv
      ((common ++ [.rel (List.replicate arity signature)]) ++ retained)
      (common ++ ([] ++ .rel (List.replicate arity signature) :: retained)) :=
    WireEquiv.ofEq (by simp)
  let sourceEquiv := forward.symm.trans reassociate
  let sourceRename := sourceEquiv.toRenaming
  let commonRename : WireRenaming (common ++ retained)
      (common ++ retained) := WireRenaming.id
  have sourceRename_common {wireSignature}
      (wire : Var common wireSignature) :
      sourceRename
          ((Var.appendRight
              [.rel (List.replicate arity signature)] wire).appendLeft
            retained) =
        wire.appendLeft
          (.rel (List.replicate arity signature) :: retained) := by
    let targetWire :=
      (wire.appendLeft [.rel (List.replicate arity signature)]).appendLeft
        retained
    have forwardEq : forward targetWire =
        (Var.appendRight [.rel (List.replicate arity signature)] wire).appendLeft
          retained := by
      calc
        forward targetWire =
            (move
              (wire.appendLeft
                [.rel (List.replicate arity signature)])).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (wire.appendLeft [.rel (List.replicate arity signature)])
        _ = (Var.appendRight
              [.rel (List.replicate arity signature)] wire).appendLeft
            retained := by
          change
            ((WireEquiv.rotate [] common
                [.rel (List.replicate arity signature)])
              ((Var.appendRight [] wire).appendLeft
                [.rel (List.replicate arity signature)])).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_middle]
          rfl
    calc
      sourceRename
          ((Var.appendRight
              [.rel (List.replicate arity signature)] wire).appendLeft
            retained) =
          reassociate
            (forward.symm
              ((Var.appendRight
                  [.rel (List.replicate arity signature)] wire).appendLeft
                retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = wire.appendLeft
          (.rel (List.replicate arity signature) :: retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        simp [targetWire]
  have sourceRename_retained {wireSignature}
      (wire : Var retained wireSignature) :
      sourceRename (Var.appendRight
          (.rel (List.replicate arity signature) :: common) wire) =
        Var.appendRight common (.there wire) := by
    let targetWire := Var.appendRight
      (common ++ [.rel (List.replicate arity signature)]) wire
    have forwardEq : forward targetWire = Var.appendRight
        (.rel (List.replicate arity signature) :: common) wire := by
      change
        (move.append (WireEquiv.refl retained))
            (Var.appendRight
              ([] ++ common ++
                [.rel (List.replicate arity signature)]) wire) = _
      rw [WireEquiv.append_apply_right]
      rfl
    calc
      sourceRename
          (Var.appendRight
            (.rel (List.replicate arity signature) :: common) wire) =
          reassociate
            (forward.symm
              (Var.appendRight
                (.rel (List.replicate arity signature) :: common) wire)) :=
        rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common (.there wire) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        change targetWire.index.val =
          (Var.appendRight common (.there wire)).index.val
        calc
          targetWire.index.val =
              (common ++
                [Sig.rel (List.replicate arity signature)]).length +
                wire.index.val :=
            Var.index_appendRight
              (common ++
                [Sig.rel (List.replicate arity signature)]) wire
          _ = common.length + (Var.there wire).index.val := by
            simp only [List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Var.index, Fin.val_succ]
            omega
          _ = (Var.appendRight common (.there wire)).index.val :=
            (Var.index_appendRight common (.there wire)).symm
  have sourceRename_selected :
      sourceRename ((.here : Var
          (.rel (List.replicate arity signature) :: common)
          (.rel (List.replicate arity signature))).appendLeft retained) =
        Var.appendRight common
          ((.here : Var [.rel (List.replicate arity signature)]
            (.rel (List.replicate arity signature))).appendLeft retained) := by
    let targetWire := (Var.appendRight common (.here : Var
      [.rel (List.replicate arity signature)]
      (.rel (List.replicate arity signature)))).appendLeft retained
    have forwardEq : forward targetWire =
        ((.here : Var
          (.rel (List.replicate arity signature) :: common)
          (.rel (List.replicate arity signature))).appendLeft retained) := by
      calc
        forward targetWire =
            (move
              (Var.appendRight common
                (.here : Var [.rel (List.replicate arity signature)]
                  (.rel (List.replicate arity signature))))).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (Var.appendRight common
              (.here : Var [.rel (List.replicate arity signature)]
                (.rel (List.replicate arity signature))))
        _ = ((.here : Var
              (.rel (List.replicate arity signature) :: common)
              (.rel (List.replicate arity signature))).appendLeft
            retained) := by
          change
            ((WireEquiv.rotate [] common
                [.rel (List.replicate arity signature)])
              (Var.appendRight ([] ++ common)
                (.here : Var [.rel (List.replicate arity signature)]
                  (.rel (List.replicate arity signature))))).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_suffix]
          rfl
    calc
      sourceRename
          ((.here : Var
            (.rel (List.replicate arity signature) :: common)
            (.rel (List.replicate arity signature))).appendLeft retained) =
          reassociate
            (forward.symm
              ((.here : Var
                (.rel (List.replicate arity signature) :: common)
                (.rel (List.replicate arity signature))).appendLeft
                  retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common
          ((.here : Var [.rel (List.replicate arity signature)]
            (.rel (List.replicate arity signature))).appendLeft retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        let binder := (.here :
          Var [.rel (List.replicate arity signature)]
            (.rel (List.replicate arity signature)))
        change targetWire.index.val =
          (Var.appendRight common (binder.appendLeft retained)).index.val
        calc
          targetWire.index.val =
              (Var.appendRight common binder).index.val :=
            Var.index_appendLeft (Var.appendRight common binder) retained
          _ = common.length + binder.index.val :=
            Var.index_appendRight common binder
          _ = common.length + (binder.appendLeft retained).index.val := by
            rw [Var.index_appendLeft]
          _ = (Var.appendRight common
                (binder.appendLeft retained)).index.val :=
            (Var.index_appendRight common
              (binder.appendLeft retained)).symm
  have keepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      sourceRename ((initialFrame.append retained).sourceKeep wire) =
        canonicalFrame.sourceKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        sourceRename ((initialFrame.append retained).sourceKeep wire) =
          canonicalFrame.sourceKeep (commonRename wire))
    · intro inheritedSignature inherited
      rw [show (initialFrame.append retained).sourceKeep
          (inherited.appendLeft retained) =
          (Var.appendRight
            [.rel (List.replicate arity signature)] inherited).appendLeft
            retained by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_common]
      simp [commonRename, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
    · intro retainedSignature retainedWire
      rw [show (initialFrame.append retained).sourceKeep
          (Var.appendRight common retainedWire) =
          Var.appendRight
            (.rel (List.replicate arity signature) :: common)
            retainedWire by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_retained]
      simp [commonRename, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
  have targetKeepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      commonRename ((initialFrame.append retained).targetKeep wire) =
        canonicalFrame.targetKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        commonRename ((initialFrame.append retained).targetKeep wire) =
          canonicalFrame.targetKeep (commonRename wire))
    · intro inheritedSignature inherited
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
    · intro retainedSignature retainedWire
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
  have selectedCommutes :
      sourceRename (initialFrame.append retained).selected =
        canonicalFrame.selected := by
    rw [show (initialFrame.append retained).selected =
        ((.here : Var
          (.rel (List.replicate arity signature) :: common)
          (.rel (List.replicate arity signature))).appendLeft retained) by rfl]
    rw [sourceRename_selected]
    simp [canonicalFrame,
      Leaf.Identity.rootFrame, Transform.Frame.replace,
      Transform.Frame.append, Transform.Frame.insertedHead,
      Var.appendLeft, Var.appendRight]
  obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
      formalSourceEq, formalArgumentEq, ⟨formalPresentation⟩,
      ⟨formalEndpointPresentation⟩⟩ :=
    targetItemsReindex rawFormalEvidence rawFormalSites
      (Leaf.Identity.Vars.fromFn ports) commonRename
      sourceRename commonRename keepCommutes targetKeepCommutes
      selectedCommutes identityRecordingSiteNatural
  have formalCoherence : formalSource =
      (argumentItemsEdit formalSites (Leaf.Identity.Vars.fromFn ports)
        (normalizationOperation (List.replicate arity signature))
        canonicalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    calc
      formalSource = rawFormalSource.renameWires sourceRename :=
        formalSourceEq.symm
      _ = (argumentItemsEdit rawFormalSites
            (Leaf.Identity.Vars.fromFn ports)
            (normalizationOperation (List.replicate arity signature))
            (initialFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
        congrArg (fun items => items.renameWires sourceRename) rawCoherence
      _ = _ := formalArgumentEq
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Identity.operation signature arity) pattern.external)
    PUnit.unit formalEvidence formalSites
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit formalEvidence primitiveSites
  have recordedEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq formalSites
  let exactOutput := Region.adjoinAt retained .nil output.endpoint
  let rawResultRename : RegionIso (WireEquiv.refl (common ++ retained))
      rawFormalResult (rawFormalResult.renameWires commonRename) := by
    simpa only [commonRename] using
      RegionIso.ofEq (Region.renameWires_id rawFormalResult).symm
  have targetKeepIdentity : canonicalFrame.targetKeep = WireRenaming.id := by
    simpa only [canonicalFrame] using
      formalRootFrame_targetKeep common retained
        (List.replicate arity signature)
  obtain ⟨recordedLeafHosted, recordedLeafScope⟩ :=
    leafItemsEndpoint formalEvidence formalSites targetKeepIdentity
      (fun siteTargetKeepEq application site =>
        positionalIdentityLeafEndpoint signature arity siteTargetKeepEq
          application site)
  have leafHosted : HostedStrict formalResult output.endpoint := by
    rw [← recordedEndpointEq]
    exact recordedLeafHosted
  have leafScope : ScopePreservation formalResult output.endpoint := by
    rw [← recordedEndpointEq]
    exact recordedLeafScope
  let formalStart := Region.adjoinAt retained .nil formalResult
  let formalPresentationIso : RegionIso (WireEquiv.refl common)
      rawStaged formalStart :=
    (rawPresentation.trans
      (RegionIso.adjoinAt retained .nil rawResultRename)).trans
      (RegionIso.adjoinAt retained .nil formalPresentation)
  have liftedLeafHosted : HostedStrict formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      HostedStrict.adjoinAt retained formalResult output.endpoint leafHosted
  have liftedLeafScope : ScopePreservation formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      adjoinAt_preserves_scope retained .nil formalResult output.endpoint
        leafScope
  let emptyEquiv := WireEquiv.appendNil common
  let emptyRename : WireRenaming common (common ++ []) :=
    emptyEquiv.symm.toRenaming
  let emptyHostIso (region : Region common) :
      RegionIso (WireEquiv.refl common) region
        (Region.adjoinAt [] .nil (region.renameWires emptyRename)) := by
    let directToCollapsed := RegionIso.renameWires region WireRenaming.id
      (WireRenaming.comp emptyEquiv.toRenaming emptyRename)
      (WireEquiv.refl common) (by
        intro signature wire
        exact (emptyEquiv.right_inv wire).symm)
    let collapsedFromHosted :=
      (RegionIso.renameWiresComp region emptyRename
        emptyEquiv.toRenaming).symm
    let chained := (directToCollapsed.trans collapsedFromHosted).trans
      (RegionIso.adjoinAtNil (region.renameWires emptyRename))
    have ambientEq :
        (((WireEquiv.refl common).trans
          (WireEquiv.refl common).symm).trans
            (WireEquiv.refl common)) = WireEquiv.refl common := by
      apply WireEquiv.ext
      intro signature wire
      rfl
    simpa only [Region.renameWires_id] using chained.castAmbient ambientEq
  let sourceHosted := Region.adjoinAt [] .nil
    (result.renameWires emptyRename)
  let targetHosted := Region.adjoinAt [] .nil
    (rawStaged.renameWires emptyRename)
  let sourceHostedIso : RegionIso (WireEquiv.refl common)
      result sourceHosted := emptyHostIso result
  let targetHostedIso : RegionIso (WireEquiv.refl common)
      rawStaged targetHosted := emptyHostIso rawStaged
  have sourceHostedCanonical : sourceHosted.Canonical :=
    sourceHostedIso.canonical_iff.mp
      (occurrence.context.holeCanonical result occurrence.sourceCanonical)
  have sourceHostedNonempty : ∀ {signature} (wire : Var common signature),
      result.incidencePaths wire.index.val ≠ [] ↔
        sourceHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourceHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let rootOccurrence : Occurrence sourceHosted host :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceHostedCanonical sourceHostedNonempty sourceHostedIso
  have hostedScope : ScopePreservation sourceHosted targetHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso sourceHostedIso.symm)
      (ScopePreservation.trans rawScope
        (ScopePreservation.ofIso targetHostedIso))
  have targetHostedCanonical : targetHosted.Canonical :=
    hostedScope.canonical sourceHostedCanonical
  have targetHostedReplacement := rootOccurrence.context.replaceCanonical
    sourceHosted targetHosted rootOccurrence.sourceCanonical
      targetHostedCanonical hostedScope.incidenceNonempty
  let sourceHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill sourceHosted) rootOccurrence.sourceCanonical
      rootOccurrence.sourceExternalTwoEnded
  have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill targetHosted) :=
    sourceHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      targetHostedReplacement.2
  have hostedStrict := rawHosted common [] emptyRename .nil
    rootOccurrence targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalHosted := Region.adjoinAt [] .nil
    ((formalStart : Region common).renameWires emptyRename)
  let exactHosted := Region.adjoinAt [] .nil
    (exactOutput.renameWires emptyRename)
  let formalHostedIso : RegionIso (WireEquiv.refl common)
      targetHosted formalHosted :=
    (targetHostedIso.symm.trans formalPresentationIso).trans
      (emptyHostIso formalStart)
  have formalHostedCanonical : formalHosted.Canonical :=
    formalHostedIso.canonical_iff.mp targetHostedCanonical
  have formalHostedNonempty : ∀ {signature} (wire : Var common signature),
      targetHosted.incidencePaths wire.index.val ≠ [] ↔
        formalHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := formalHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have formalReplacement := rootOccurrence.context.replaceCanonical
    targetHosted formalHosted targetHostedReplacement.1
      formalHostedCanonical formalHostedNonempty
  let targetHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill targetHosted) targetHostedReplacement.1
      targetHostedExternalTwoEnded
  have formalHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill formalHosted) :=
    targetHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      formalReplacement.2
  let targetHostedOccurrence : Occurrence targetHosted targetHostedEndpoint :=
    exactOccurrence rootOccurrence.interface rootOccurrence.context
      targetHosted targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalOccurrence : Occurrence formalHosted targetHostedEndpoint :=
    EqualityNormalization.presentationOccurrence targetHostedOccurrence
      formalHostedCanonical formalHostedNonempty formalHostedIso
  let formalEmptyIso := emptyHostIso formalStart
  let exactEmptyIso := emptyHostIso exactOutput
  have hostedLeafScope : ScopePreservation formalHosted exactHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso formalEmptyIso.symm)
      (ScopePreservation.trans liftedLeafScope
        (ScopePreservation.ofIso exactEmptyIso))
  have exactHostedCanonical : exactHosted.Canonical :=
    hostedLeafScope.canonical formalHostedCanonical
  have exactHostedReplacement := formalOccurrence.context.replaceCanonical
    formalHosted exactHosted formalOccurrence.sourceCanonical
      exactHostedCanonical hostedLeafScope.incidenceNonempty
  let formalHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill formalHosted)
      formalOccurrence.sourceCanonical formalOccurrence.sourceExternalTwoEnded
  have exactHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      formalOccurrence.interface.boundaryWire
      (formalOccurrence.context.fill exactHosted) :=
    formalHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactHostedReplacement.2
  have leafStrict := liftedLeafHosted common [] emptyRename .nil
    formalOccurrence exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactLocalCanonical : exactOutput.Canonical :=
    exactEmptyIso.canonical_iff.mpr exactHostedCanonical
  have exactNonempty : ∀ {signature} (wire : Var common signature),
      exactHosted.incidencePaths wire.index.val ≠ [] ↔
        exactOutput.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := exactEmptyIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq]⟩
  have exactReplacement := formalOccurrence.context.replaceCanonical
    exactHosted exactOutput exactHostedReplacement.1 exactLocalCanonical
      exactNonempty
  let exactHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill exactHosted) exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill exactOutput) :=
    exactHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactReplacement.2
  let exactTargetIso : OpenDiagramIso
      (formalOccurrence.interface.withBody
        (formalOccurrence.context.fill exactHosted)
        exactHostedReplacement.1 exactHostedExternalTwoEnded)
      (rootOccurrence.interface.withBody
        (rootOccurrence.context.fill exactOutput)
        exactReplacement.1 exactExternalTwoEnded) :=
    OpenDiagram.withBody_iso exactHostedReplacement.1 exactReplacement.1
      exactHostedExternalTwoEnded exactExternalTwoEnded
      (DiagramContext.fillIso rootOccurrence.context exactEmptyIso.symm)
  have presentedLeafStrict : EqualityNormalization.StrictEquates
      formalOccurrence exactOutput exactReplacement.1 exactExternalTwoEnded :=
    EqualityNormalization.StrictEquates.targetIso leafStrict exactTargetIso
  have presentedStrict : EqualityNormalization.StrictEquates rootOccurrence
      exactOutput exactReplacement.1 exactExternalTwoEnded :=
    ⟨hostedStrict.1.trans presentedLeafStrict.1,
      presentedLeafStrict.2.trans hostedStrict.2⟩
  have strict : EqualityNormalization.StrictEquates occurrence exactOutput
      exactReplacement.1 exactExternalTwoEnded := by
    simpa only [EqualityNormalization.StrictEquates, rootOccurrence,
      EqualityNormalization.presentationOccurrence] using presentedStrict
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, exactReplacement.1, exactExternalTwoEnded, strict⟩

/-- Extend a positional selected-wire argument tuple to the authoritative
boundary tuple, then contract the positional prefix.  This is the common
argument-normalization continuation used by both leaf compilers. -/
theorem argumentNormalizationTelescope
    {recordedArguments external common retained boundary : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (positionalValues : Vars external recordedArguments)
    (externalNonempty : external ≠ [])
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    {positionalPending endpoint : Region common}
    (positionalEq : positionalPending =
      argumentNormalizedRegion recordedSites positionalValues)
    (positionalCanonical : (context.fill positionalPending).Canonical)
    (positionalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending))
    (authoritativeCanonical :
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (authoritativeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint))
    (polarity : Polarity) (polarityEq : context.polarity = polarity)
    (continuation : Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)) endpoint
      authoritativeCanonical authoritativeExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded) :
    Telescope polarity interface context positionalPending endpoint
      positionalCanonical positionalExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded := by
  let authoritativeValues := EqualityNormalization.formalPorts external
  let extendedValues := Theory.Vars.extend positionalValues authoritativeValues
  let extendedPending := argumentNormalizedRegion recordedSites extendedValues
  have extendedValidity := argumentExtendedValidity recordedSites
    positionalValues interface context authoritativeCanonical
      authoritativeExternalTwoEnded
  have contractTelescope : Telescope polarity interface context
      extendedPending endpoint extendedValidity.1 extendedValidity.2
      endpointCanonical endpointExternalTwoEnded := by
    simpa only [extendedPending, extendedValues, authoritativeValues] using
      argumentVarsContractTelescope recordedSites positionalValues interface
        context authoritativeCanonical authoritativeExternalTwoEnded
        endpointCanonical endpointExternalTwoEnded polarity polarityEq
        continuation
  have positionalNormalizedCanonical :
      (context.fill
        (argumentNormalizedRegion recordedSites positionalValues)).Canonical :=
    positionalEq ▸ positionalCanonical
  have positionalNormalizedExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (argumentNormalizedRegion recordedSites positionalValues)) :=
    positionalEq ▸ positionalExternalTwoEnded
  have positionalSourceCanonical :
      (context.fill (polaritySource polarity positionalPending endpoint)).Canonical := by
    cases polarity
    · exact positionalCanonical
    · exact endpointCanonical
  have positionalSourceExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (polaritySource polarity positionalPending endpoint)) := by
    intro signature wire
    cases polarity
    · exact positionalExternalTwoEnded wire
    · exact endpointExternalTwoEnded wire
  let positionalSource := interface.withBody
    (context.fill (polaritySource polarity positionalPending endpoint))
    positionalSourceCanonical positionalSourceExternal
  have normalizedSourceCanonical :
      (context.fill (polaritySource polarity
        (argumentNormalizedRegion recordedSites positionalValues)
        endpoint)).Canonical := by
    cases polarity
    · exact positionalNormalizedCanonical
    · exact endpointCanonical
  have normalizedSourceExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (polaritySource polarity
        (argumentNormalizedRegion recordedSites positionalValues)
        endpoint)) := by
    intro signature wire
    cases polarity
    · exact positionalNormalizedExternal wire
    · exact endpointExternalTwoEnded wire
  let normalizedOccurrence : Occurrence
      (polaritySource polarity
        (argumentNormalizedRegion recordedSites positionalValues) endpoint)
      positionalSource := {
    interface := interface
    context := context
    sourceCanonical := normalizedSourceCanonical
    sourceExternalTwoEnded := normalizedSourceExternal
    host_iso := by
      cases polarity with
      | positive =>
          simpa only [positionalSource, polaritySource] using
            OpenDiagram.withBody_iso positionalCanonical
              positionalNormalizedCanonical positionalExternalTwoEnded
              positionalNormalizedExternal
              (DiagramContext.fillIso context (RegionIso.ofEq positionalEq))
      | negative =>
          simpa only [positionalSource, polaritySource] using
            OpenDiagramIso.refl
              (interface.withBody (context.fill endpoint) endpointCanonical
                endpointExternalTwoEnded)
  }
  let projectionRequest : Telescope.Request
      (argumentNormalizedRegion recordedSites positionalValues)
      extendedPending := {
    boundary := boundary
    source := positionalSource
    endpoint := endpoint
    polarity := polarity
    occurrence := normalizedOccurrence
    instantiatedCanonical := positionalNormalizedCanonical
    instantiatedExternalTwoEnded := positionalNormalizedExternal
    pendingCanonical := extendedValidity.1
    pendingExternalTwoEnded := extendedValidity.2
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := contractTelescope
  }
  have projectionCompiled : projectionRequest.Result := by
    obtain ⟨authoritativeSignature, authoritativeRest, authoritativeHead,
        authoritativeTail, authoritativeArgumentsEq,
        authoritativeValuesEq⟩ :=
      EqualityNormalization.formalPorts_cons_of_nonempty externalNonempty
    let extendedCons := Theory.Vars.extend positionalValues
      (Theory.Vars.cons authoritativeHead authoritativeTail)
    have extendedArgumentsEq :
        recordedArguments ++ external =
          recordedArguments ++ (authoritativeSignature :: authoritativeRest) :=
      congrArg (List.append recordedArguments) authoritativeArgumentsEq
    have extendedValuesEq : HEq extendedValues extendedCons := by
      exact varsExtendHEqRight positionalValues authoritativeValues
        (Theory.Vars.cons authoritativeHead authoritativeTail)
        authoritativeArgumentsEq authoritativeValuesEq
    let pendingIso := argumentNormalizationPresentation recordedSites
      extendedValues extendedCons extendedArgumentsEq extendedValuesEq
    exact argumentVarsProjectionCompiles (boundary := boundary) recordedSites
      positionalValues authoritativeHead authoritativeTail projectionRequest
      pendingIso authoritativeCanonical authoritativeExternalTwoEnded
  have optional : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last → Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail _ step induction => exact .tail induction step
  cases polarity with
  | positive =>
      have exactCompiled : Relation.TransGen Step
          (interface.withBody (context.fill positionalPending)
            positionalCanonical positionalExternalTwoEnded)
          (interface.withBody (context.fill endpoint)
            endpointCanonical endpointExternalTwoEnded) := by
        simpa [projectionRequest, normalizedOccurrence, positionalSource,
          exactOccurrence, polaritySource, polarityTarget] using
            projectionCompiled
      exact ⟨polarityEq, optional exactCompiled⟩
  | negative =>
      let targetIso : OpenDiagramIso
          (interface.withBody
            (context.fill
              (argumentNormalizedRegion recordedSites positionalValues))
            positionalNormalizedCanonical positionalNormalizedExternal)
          (interface.withBody (context.fill positionalPending)
            positionalCanonical positionalExternalTwoEnded) :=
        OpenDiagram.withBody_iso positionalNormalizedCanonical
          positionalCanonical positionalNormalizedExternal
          positionalExternalTwoEnded
          (DiagramContext.fillIso context (RegionIso.ofEq positionalEq.symm))
      have exactCompiled : Relation.TransGen Step
          (interface.withBody (context.fill endpoint)
            endpointCanonical endpointExternalTwoEnded)
          (interface.withBody
            (context.fill
              (argumentNormalizedRegion recordedSites positionalValues))
            positionalNormalizedCanonical positionalNormalizedExternal) := by
        simpa [projectionRequest, normalizedOccurrence, positionalSource,
          exactOccurrence, polaritySource, polarityTarget] using
            projectionCompiled
      exact ⟨polarityEq, optional (transGen_iso
        (OpenDiagramIso.refl _) exactCompiled targetIso)⟩

/-- Argument normalization including the structurally empty boundary case,
where the positional and authoritative tuples are both empty and no argument
step is required. -/
theorem argumentNormalizationTelescopeAll
    {recordedArguments external common retained boundary : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (positionalValues : Vars external recordedArguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    {positionalPending endpoint : Region common}
    (positionalEq : positionalPending =
      argumentNormalizedRegion recordedSites positionalValues)
    (positionalCanonical : (context.fill positionalPending).Canonical)
    (positionalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending))
    (authoritativeCanonical :
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (authoritativeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint))
    (polarity : Polarity) (polarityEq : context.polarity = polarity)
    (continuation : Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)) endpoint
      authoritativeCanonical authoritativeExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded) :
    Telescope polarity interface context positionalPending endpoint
      positionalCanonical positionalExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded := by
  cases external with
  | nil =>
      cases positionalValues with
      | nil =>
          simpa only [positionalEq, EqualityNormalization.formalPorts,
            Erasure.Exposure.identityBoundary] using continuation
      | cons head tail => exact nomatch head
  | cons signature rest =>
      exact argumentNormalizationTelescope recordedSites positionalValues
        (by simp) interface context positionalEq positionalCanonical
        positionalExternalTwoEnded authoritativeCanonical
        authoritativeExternalTwoEnded endpointCanonical
        endpointExternalTwoEnded polarity polarityEq continuation


/-- The direct singleton-atom branch: accumulate every authoritative selected
site into one literal Formal edit, prepare its exact deterministic endpoint,
and run the single directed FormalApplication primitive at the binder home. -/
theorem atomFormal
    {patternWires atomArguments common originalSourceWires
      originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (resultCanonical : (context.fill result).Canonical)
    (resultExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill result)) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel pattern.external :: retained)),
        let pending : Region common :=
          .mk (.rel pattern.external :: retained)
            formalSource
        ∀ (polarity : Polarity)
          (_polarityEq : context.polarity = polarity)
          {endpoint : Region common}
          (pendingCanonical : (context.fill pending).Canonical)
          (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill pending))
          (endpointCanonical : (context.fill endpoint).Canonical)
          (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill endpoint))
          (_continuation : Telescope polarity interface context
            pending endpoint pendingCanonical pendingExternalTwoEnded
            endpointCanonical endpointExternalTwoEnded),
          Telescope.Compiles polarity
            (exactOccurrence interface context
              (polaritySource polarity result endpoint)
              (match polarity with
              | .positive => resultCanonical
              | .negative => endpointCanonical)
              (match polarity with
              | .positive => resultExternalTwoEnded
              | .negative => endpointExternalTwoEnded))
            resultCanonical resultExternalTwoEnded endpointCanonical
            endpointExternalTwoEnded := by
  let instantiatedEndpoint := interface.withBody (context.fill result)
    resultCanonical resultExternalTwoEnded
  let accumulatorOccurrence : Occurrence result instantiatedEndpoint :=
    exactOccurrence interface context result resultCanonical
      resultExternalTwoEnded
  obtain ⟨retained, positionalFormalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, outputCanonical, outputExternalTwoEnded,
      strict⟩ :=
    accumulateAtomFormal body_eq evidence sites accumulatorOccurrence
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit formalEvidence formalSites
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Formal.operation [] atomArguments)
    PUnit.unit formalEvidence primitiveSites
  have primitiveNoPin : output.edit.NoSelectedPin := by
    exact itemsEdit_noSelectedPin primitiveSites
  have outputEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq formalSites
  have exactOutputEq : Region.adjoinAt retained .nil recordedOutput.endpoint =
      Region.adjoinAt retained .nil output.endpoint :=
    congrArg (Region.adjoinAt retained .nil) outputEndpointEq
  have primitiveOutputCanonical :
      (accumulatorOccurrence.context.fill
        (Region.adjoinAt retained .nil output.endpoint)).Canonical := by
    rw [← exactOutputEq]
    exact outputCanonical
  have primitiveOutputExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      accumulatorOccurrence.interface.boundaryWire
      (accumulatorOccurrence.context.fill
        (Region.adjoinAt retained .nil output.endpoint)) := by
    intro signature wire
    rw [← exactOutputEq]
    exact outputExternalTwoEnded wire
  have primitiveStrict : EqualityNormalization.StrictEquates
      accumulatorOccurrence (Region.adjoinAt retained .nil output.endpoint)
      primitiveOutputCanonical primitiveOutputExternalTwoEnded := by
    let endpointIso : OpenDiagramIso
        (accumulatorOccurrence.interface.withBody
          (accumulatorOccurrence.context.fill
            (Region.adjoinAt retained .nil recordedOutput.endpoint))
          outputCanonical outputExternalTwoEnded)
        (accumulatorOccurrence.interface.withBody
          (accumulatorOccurrence.context.fill
            (Region.adjoinAt retained .nil output.endpoint))
          primitiveOutputCanonical primitiveOutputExternalTwoEnded) :=
      OpenDiagram.withBody_iso outputCanonical primitiveOutputCanonical
        outputExternalTwoEnded primitiveOutputExternalTwoEnded
        (DiagramContext.fillIso accumulatorOccurrence.context
          (RegionIso.ofEq exactOutputEq))
    exact EqualityNormalization.StrictEquates.targetIso strict endpointIso
  let prepared := Region.adjoinAt retained .nil output.endpoint
  let positionalValues := positionalAtomSelection head ports
  let authoritativeValues := EqualityNormalization.formalPorts pattern.external
  let authoritativePending := argumentNormalizedRegion
    (common := common) (retained := retained) formalSites authoritativeValues
  let pending : Region common := authoritativePending
  refine ⟨retained, authoritativePending.items, ?_⟩
  dsimp only
  intro polarity polarityEq endpoint pendingCanonical
    pendingExternalTwoEnded endpointCanonical endpointExternalTwoEnded
    continuation
  let positionalPending : Region common :=
    .mk (.rel (positionalAtomWires atomArguments) :: retained)
      positionalFormalSource
  have authoritativeFilledCanonical :
      (context.fill authoritativePending).Canonical := by
    change (context.fill authoritativePending).Canonical at pendingCanonical
    exact pendingCanonical
  have authoritativeFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill authoritativePending) := by
    change OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill authoritativePending) at pendingExternalTwoEnded
    exact pendingExternalTwoEnded
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    context.holeCanonical authoritativePending authoritativeFilledCanonical
  let authoritativeFrame : Transform.Frame pattern.external
      (common ++ retained)
      (common ++ (.rel pattern.external :: retained))
      (common ++ (.rel pattern.external :: retained)) :=
    Transform.Frame.replace common [] retained [.rel pattern.external]
      pattern.external
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths formalSites
    authoritativeValues (normalizationOperation pattern.external)
    authoritativeFrame PUnit.unit (fun _ _ _ => PUnit.unit)
    authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant
      (Leaf.Formal.rootFrame common [] retained [] atomArguments) := by
    exact Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := formalSites.source_selectedPaths formalInvariant 0
  have selectedRooted : RegionPath.RootedTwo
      (positionalFormalSource.incidencePaths common.length 0) := by
    have authoritativeRoot := authoritativeLocalCanonical.1 (0 : Fin
      (.rel pattern.external :: retained).length)
    have pathEq : positionalFormalSource.incidencePaths common.length 0 =
        authoritativePending.items.incidencePaths common.length 0 := by
      calc
        positionalFormalSource.incidencePaths common.length 0 =
            formalSites.selectedPaths 0 := by
              simpa [Leaf.Formal.rootFrame, Transform.Frame.replace,
                Transform.Frame.insertedHead] using formalPaths
        _ = authoritativePending.items.incidencePaths common.length 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegion,
            authoritativeFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using authoritativePaths
    simpa only [pathEq] using authoritativeRoot
  have preparedLocalCanonical : prepared.Canonical :=
    context.holeCanonical prepared primitiveOutputCanonical
  let rawPrepared := Region.adjoinAt retained .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedLocalCanonical
  have positionalLocalValidity := Leaf.Formal.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical : (context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact primitiveOutputCanonical
  have positionalReplacement := context.replaceCanonical rawPrepared
    positionalPending rawPreparedFilledCanonical positionalLocalValidity.1 (by
      intro signature wire
      have paths := positionalLocalValidity.2 wire
      exact ⟨fun nonempty => by
          dsimp only [positionalPending]
          simp only [positionalAtomWires]
          rw [← paths]
          exact nonempty,
        fun nonempty => by
          dsimp only [positionalPending] at nonempty ⊢
          simp only [positionalAtomWires] at nonempty ⊢
          rw [paths]
          exact nonempty⟩)
  have positionalFilledCanonical :
      (context.fill positionalPending).Canonical := positionalReplacement.1
  have positionalFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending) := by
    have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire (context.fill rawPrepared) := by
      dsimp only [rawPrepared]
      rw [output.run_eq]
      exact primitiveOutputExternalTwoEnded
    let preparedEndpoint := interface.withBody (context.fill rawPrepared)
      rawPreparedFilledCanonical rawPreparedFilledExternal
    intro signature wire
    exact preparedEndpoint.externalTwoEnded_of_nonempty_iff _
      positionalReplacement.2 wire
  have positionalEq : positionalPending =
      argumentNormalizedRegion (common := common) (retained := retained)
        formalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (positionalAtomWires atomArguments) (common ++ retained)
        (common ++ (.rel (positionalAtomWires atomArguments) :: retained))
        (common ++ (.rel (positionalAtomWires atomArguments) :: retained)) :=
      { sourceKeep := Transform.Frame.keep common []
          [.rel (positionalAtomWires atomArguments)] retained
        targetKeep := Transform.Frame.keep common []
          [.rel (positionalAtomWires atomArguments)] retained
        selected := Transform.Frame.insertedHead common [] retained
          (.rel (positionalAtomWires atomArguments)) }
    have sourceIndependent := argumentItemsEdit_source_independent formalSites
      positionalValues
      (normalizationOperation (positionalAtomWires atomArguments))
      (Leaf.Formal.rootFrame common [] retained [] atomArguments)
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (positionalAtomWires atomArguments))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by
        intro wireSignature wire
        rfl)
      (by rfl)
    have normalizedCoherence : positionalFormalSource =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (positionalAtomWires atomArguments))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      formalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (.rel (positionalAtomWires atomArguments) :: retained))
      normalizedCoherence
  have normalizationTelescope : Telescope polarity interface context
      positionalPending endpoint positionalFilledCanonical
      positionalFilledExternal endpointCanonical endpointExternalTwoEnded := by
    exact argumentNormalizationTelescopeAll formalSites positionalValues
      interface context positionalEq positionalFilledCanonical
      positionalFilledExternal authoritativeFilledCanonical
      authoritativeFilledExternal endpointCanonical endpointExternalTwoEnded
      polarity polarityEq (by
        simpa only [authoritativeValues, authoritativePending] using continuation)
  let request : Telescope.Request result positionalPending := {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity result endpoint))
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    endpoint := endpoint
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity result endpoint)
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    instantiatedCanonical := resultCanonical
    instantiatedExternalTwoEnded := resultExternalTwoEnded
    pendingCanonical := positionalFilledCanonical
    pendingExternalTwoEnded := positionalFilledExternal
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  have equates := primitiveStrict.toEquates
  have preparationTelescope : Telescope polarity interface context result
      prepared resultCanonical resultExternalTwoEnded primitiveOutputCanonical
        primitiveOutputExternalTwoEnded := by
    cases polarity with
    | positive =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.1⟩
    | negative =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.2⟩
  let preparation : request.Preparation prepared := {
    prepared := prepared
    preparedCanonical := primitiveOutputCanonical
    preparedExternalTwoEnded := primitiveOutputExternalTwoEnded
    rawPreparedCanonical := primitiveOutputCanonical
    rawPreparedExternalTwoEnded := primitiveOutputExternalTwoEnded
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [request, exactOccurrence] using preparationTelescope
  }
  exact itemsFormal (before := []) (after := atomArguments)
    (localBefore := []) (localAfter := retained) formalEvidence primitiveSites
      request (by
        simpa only [prepared, output, positionalAtomWires] using
          preparation)

/-- The direct authoritative identity branch: accumulate every selected site
into one literal IdentityLeaf edit, prepare its deterministic endpoint, and
run the single directed primitive at the binder home. -/
theorem identityLeaf
    {patternWires common originalSourceWires originalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (resultCanonical : (context.fill result).Canonical)
    (resultExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill result)) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel pattern.external :: retained)),
        let pending : Region common :=
          .mk (.rel pattern.external :: retained)
            formalSource
        ∀ (polarity : Polarity)
          (_polarityEq : context.polarity = polarity)
          {endpoint : Region common}
          (pendingCanonical : (context.fill pending).Canonical)
          (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill pending))
          (endpointCanonical : (context.fill endpoint).Canonical)
          (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill endpoint))
          (_continuation : Telescope polarity interface context
            pending endpoint pendingCanonical pendingExternalTwoEnded
            endpointCanonical endpointExternalTwoEnded),
          Telescope.Compiles polarity
            (exactOccurrence interface context
              (polaritySource polarity result endpoint)
              (match polarity with
              | .positive => resultCanonical
              | .negative => endpointCanonical)
              (match polarity with
              | .positive => resultExternalTwoEnded
              | .negative => endpointExternalTwoEnded))
            resultCanonical resultExternalTwoEnded endpointCanonical
            endpointExternalTwoEnded := by
  let instantiatedEndpoint := interface.withBody (context.fill result)
    resultCanonical resultExternalTwoEnded
  let accumulatorOccurrence : Occurrence result instantiatedEndpoint :=
    exactOccurrence interface context result resultCanonical
      resultExternalTwoEnded
  obtain ⟨retained, formalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, outputCanonical, outputExternalTwoEnded,
      strict⟩ :=
    accumulateIdentity body_eq evidence sites accumulatorOccurrence
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit formalEvidence primitiveSites
  have primitiveNoPin : output.edit.NoSelectedPin :=
    itemsEdit_noSelectedPin primitiveSites
  let prepared := Region.adjoinAt retained .nil output.endpoint
  let positionalValues := Leaf.Identity.Vars.fromFn ports
  let authoritativeValues := EqualityNormalization.formalPorts pattern.external
  let authoritativePending := argumentNormalizedRegion
    (common := common) (retained := retained) formalSites authoritativeValues
  let pending : Region common := authoritativePending
  refine ⟨retained, authoritativePending.items, ?_⟩
  dsimp only
  intro polarity polarityEq endpoint pendingCanonical
    pendingExternalTwoEnded endpointCanonical endpointExternalTwoEnded
    continuation
  let positionalPending : Region common :=
    .mk (.rel (List.replicate arity signature) :: retained) formalSource
  have authoritativeFilledCanonical :
      (context.fill authoritativePending).Canonical := by
    change (context.fill authoritativePending).Canonical at pendingCanonical
    exact pendingCanonical
  have authoritativeFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill authoritativePending) := by
    change OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill authoritativePending) at pendingExternalTwoEnded
    exact pendingExternalTwoEnded
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    context.holeCanonical authoritativePending authoritativeFilledCanonical
  let authoritativeFrame : Transform.Frame pattern.external
      (common ++ retained)
      (common ++ (.rel pattern.external :: retained))
      (common ++ (.rel pattern.external :: retained)) :=
    Transform.Frame.replace common [] retained [.rel pattern.external]
      pattern.external
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths formalSites
    authoritativeValues (normalizationOperation pattern.external)
    authoritativeFrame PUnit.unit (fun _ _ _ => PUnit.unit)
    authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant
      (Leaf.Identity.rootFrame common [] retained signature arity) :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := formalSites.source_selectedPaths formalInvariant 0
  have selectedRooted : RegionPath.RootedTwo
      (formalSource.incidencePaths common.length 0) := by
    have authoritativeRoot := authoritativeLocalCanonical.1 (0 : Fin
      (.rel pattern.external :: retained).length)
    have pathEq : formalSource.incidencePaths common.length 0 =
        authoritativePending.items.incidencePaths common.length 0 := by
      calc
        formalSource.incidencePaths common.length 0 =
            formalSites.selectedPaths 0 := by
          simpa [Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using formalPaths
        _ = authoritativePending.items.incidencePaths common.length 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegion,
            authoritativeFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using authoritativePaths
    simpa only [pathEq] using authoritativeRoot
  have preparedLocalCanonical : prepared.Canonical :=
    context.holeCanonical prepared outputCanonical
  let rawPrepared := Region.adjoinAt retained .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedLocalCanonical
  have positionalLocalValidity := Leaf.Identity.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical : (context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact outputCanonical
  have positionalReplacement := context.replaceCanonical rawPrepared
    positionalPending rawPreparedFilledCanonical positionalLocalValidity.1 (by
      intro wireSignature wire
      have paths := positionalLocalValidity.2 wire
      exact ⟨fun nonempty => by
          dsimp only [positionalPending]
          rw [← paths]
          exact nonempty,
        fun nonempty => by
          dsimp only [positionalPending] at nonempty ⊢
          rw [paths]
          exact nonempty⟩)
  have positionalFilledCanonical :
      (context.fill positionalPending).Canonical := positionalReplacement.1
  have positionalFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending) := by
    have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire (context.fill rawPrepared) := by
      dsimp only [rawPrepared]
      rw [output.run_eq]
      exact outputExternalTwoEnded
    let preparedEndpoint := interface.withBody (context.fill rawPrepared)
      rawPreparedFilledCanonical rawPreparedFilledExternal
    intro wireSignature wire
    exact preparedEndpoint.externalTwoEnded_of_nonempty_iff _
      positionalReplacement.2 wire
  have positionalEq : positionalPending =
      argumentNormalizedRegion (common := common) (retained := retained)
        formalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (List.replicate arity signature) (common ++ retained)
        (common ++ (.rel (List.replicate arity signature) :: retained))
        (common ++ (.rel (List.replicate arity signature) :: retained)) :=
      { sourceKeep := Transform.Frame.keep common []
          [.rel (List.replicate arity signature)] retained
        targetKeep := Transform.Frame.keep common []
          [.rel (List.replicate arity signature)] retained
        selected := Transform.Frame.insertedHead common [] retained
          (.rel (List.replicate arity signature)) }
    have sourceIndependent := argumentItemsEdit_source_independent formalSites
      positionalValues
      (normalizationOperation (List.replicate arity signature))
      (Leaf.Identity.rootFrame common [] retained signature arity)
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (List.replicate arity signature))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by intro wireSignature wire; rfl) (by rfl)
    have normalizedCoherence : formalSource =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (List.replicate arity signature))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      formalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (.rel (List.replicate arity signature) :: retained))
      normalizedCoherence
  have normalizationTelescope : Telescope polarity interface context
      positionalPending endpoint positionalFilledCanonical
      positionalFilledExternal endpointCanonical endpointExternalTwoEnded := by
    exact argumentNormalizationTelescopeAll formalSites positionalValues
      interface context positionalEq positionalFilledCanonical
      positionalFilledExternal authoritativeFilledCanonical
      authoritativeFilledExternal endpointCanonical endpointExternalTwoEnded
      polarity polarityEq (by
        simpa only [authoritativeValues, authoritativePending] using continuation)
  let request : Telescope.Request result positionalPending := {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity result endpoint))
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    endpoint := endpoint
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity result endpoint)
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    instantiatedCanonical := resultCanonical
    instantiatedExternalTwoEnded := resultExternalTwoEnded
    pendingCanonical := positionalFilledCanonical
    pendingExternalTwoEnded := positionalFilledExternal
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  have equates := strict.toEquates
  have preparationTelescope : Telescope polarity interface context result
      prepared resultCanonical resultExternalTwoEnded outputCanonical
        outputExternalTwoEnded := by
    cases polarity with
    | positive =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.1⟩
    | negative =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.2⟩
  let preparation : request.Preparation prepared := {
    prepared := prepared
    preparedCanonical := outputCanonical
    preparedExternalTwoEnded := outputExternalTwoEnded
    rawPreparedCanonical := outputCanonical
    rawPreparedExternalTwoEnded := outputExternalTwoEnded
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [request, exactOccurrence] using preparationTelescope
  }
  exact itemsIdentity (signature := signature) (arity := arity)
    (localBefore := []) (localAfter := retained) formalEvidence primitiveSites
      request (by
        simpa only [prepared, output, positionalPending] using preparation)

/-- Canonicality of the endpoint selected by an occurrence polarity. -/
theorem polaritySourceCanonicalAt
    {outer holeWires : List Sig}
    (polarity : Polarity)
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (beforeCanonical : (context.fill before).Canonical)
    (afterCanonical : (context.fill after).Canonical) :
    (context.fill (polaritySource polarity before after)).Canonical := by
  cases polarity
  · exact beforeCanonical
  · exact afterCanonical

/-- External two-endedness of the endpoint selected by an occurrence
polarity. -/
theorem polaritySourceExternalTwoEndedAt
    {boundary holeWires : List Sig}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (before after : Region holeWires)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before))
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after)) :
    OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill (polaritySource polarity before after)) := by
  cases polarity
  · exact beforeExternalTwoEnded
  · exact afterExternalTwoEnded

/-- Compile authoritative comprehension evidence directly into the exact
occurrence-indexed step chain requested by the caller.  The pattern and its
`Instantiates` witness determine every structural branch and all selected
sites; the caller supplies only the actual telescope request whose pending
endpoint is the quantified region. -/
theorem compile
    {arguments before after outer : List Sig}
    (pattern : OpenDiagram arguments)
    {quantified specialized : Region outer}
    (instantiates :
      _root_.VisualProof.Rule.Comprehension.Instantiates pattern before after
        quantified specialized)
    (request : Telescope.Request specialized quantified) :
    request.Result := by
  have compileSupportPattern :
      ∀ {materialWires structuralOuter structuralBefore structuralAfter :
          List Sig}
        (material : Region materialWires)
        (materialCanonical : material.Canonical)
        {items : ItemSeq
          (structuralOuter ++
            (structuralBefore ++ .rel materialWires :: structuralAfter))}
        {result : Region
          (structuralOuter ++ (structuralBefore ++ structuralAfter))}
        (evidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (Erasure.Exposure.supportPattern material materialCanonical)
            (_root_.VisualProof.Rule.Comprehension.retain structuralOuter
              structuralBefore structuralAfter materialWires)
            (_root_.VisualProof.Rule.Comprehension.selected structuralOuter
              structuralBefore structuralAfter materialWires)
            items result)
        (structuralRequest : Telescope.Request
          (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
          (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
            items)),
        structuralRequest.Result := by
    intro materialWires structuralOuter structuralBefore structuralAfter
      material materialCanonical items result evidence structuralRequest
    cases materialWires with
    | nil =>
        cases material with
        | mk materialLocals materialItems =>
            cases materialLocals with
            | nil =>
                cases materialItems with
                | nil =>
                    have patternEq :
                        Erasure.Exposure.supportPattern
                          (Region.mk [] ItemSeq.nil)
                            materialCanonical =
                          _root_.VisualProof.Rule.Completeness.Comprehension.Compiler.blankPattern := by
                      apply EqualityNormalization.OpenDiagram.eq_of_data
                      · rfl
                      · rfl
                      · rfl
                    rw [patternEq] at evidence
                    exact
                      _root_.VisualProof.Rule.Completeness.Comprehension.Compiler.itemsEnds
                        evidence structuralRequest
                | cons materialHead materialTail =>
                    sorry
            | cons materialLocal materialLocals =>
                sorry
    | cons materialWire materialWires =>
        sorry
  cases instantiates with
  | @mk items result evidence =>
      let sites := normalizationSites
        (frame := normalizationFrame outer before after arguments) evidence
      let originalEndpoint := request.occurrence.interface.withBody
        (request.occurrence.context.fill
          (Region.adjoinAt (before ++ after) .nil result))
        request.instantiatedCanonical request.instantiatedExternalTwoEnded
      let normalizationOccurrence : Occurrence
          (Region.adjoinAt (before ++ after) .nil result)
          originalEndpoint :=
        exactOccurrence request.occurrence.interface
          request.occurrence.context
          (Region.adjoinAt (before ++ after) .nil result)
          request.instantiatedCanonical request.instantiatedExternalTwoEnded
      obtain ⟨normalized, normalizedEvidence, normalizedCanonical,
          normalizedExternalTwoEnded, normalizedIsomorphic, forward,
          reverse⟩ :=
        EqualityNormalization.normalizeItemsEquates pattern evidence sites
          normalizationOccurrence
      obtain ⟨normalizedIso⟩ := normalizedIsomorphic
      let normalizedInstantiated : Region outer :=
        Region.adjoinAt (before ++ after) .nil normalized
      let normalizedEndpoint := request.occurrence.interface.withBody
        (request.occurrence.context.fill normalizedInstantiated)
        normalizedCanonical normalizedExternalTwoEnded
      let phaseTarget :=
        if EqualityNormalization.itemsHaveSelection sites = false then
          originalEndpoint
        else
          normalizedEndpoint
      have normalizedSourceCanonical :
          (request.occurrence.context.fill
            (polaritySource request.polarity normalizedInstantiated
              request.endpoint)).Canonical := by
        exact polaritySourceCanonicalAt request.polarity
          request.occurrence.context normalizedInstantiated request.endpoint
          normalizedCanonical request.endpointCanonical
      have normalizedSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          request.occurrence.interface.boundaryWire
          (request.occurrence.context.fill
            (polaritySource request.polarity normalizedInstantiated
              request.endpoint)) := by
        exact polaritySourceExternalTwoEndedAt request.polarity
          request.occurrence.interface request.occurrence.context
          normalizedInstantiated request.endpoint normalizedExternalTwoEnded
          request.endpointExternalTwoEnded
      let normalizedRequest : Telescope.Request normalizedInstantiated
          (.mk (before ++ .rel arguments :: after) items) := {
        boundary := request.boundary
        source := request.occurrence.interface.withBody
          (request.occurrence.context.fill
            (polaritySource request.polarity normalizedInstantiated
              request.endpoint))
          normalizedSourceCanonical normalizedSourceExternalTwoEnded
        endpoint := request.endpoint
        polarity := request.polarity
        occurrence := exactOccurrence request.occurrence.interface
          request.occurrence.context
          (polaritySource request.polarity normalizedInstantiated
            request.endpoint)
          normalizedSourceCanonical normalizedSourceExternalTwoEnded
        instantiatedCanonical := normalizedCanonical
        instantiatedExternalTwoEnded := normalizedExternalTwoEnded
        pendingCanonical := request.pendingCanonical
        pendingExternalTwoEnded := request.pendingExternalTwoEnded
        endpointCanonical := request.endpointCanonical
        endpointExternalTwoEnded := request.endpointExternalTwoEnded
        continuation := request.continuation
      }
      let material :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (EqualityNormalization.formalPorts arguments)
      have materialCanonical : material.Canonical := by
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
          pattern (EqualityNormalization.formalPorts arguments)
      have supportEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (Erasure.Exposure.supportPattern material materialCanonical)
            (_root_.VisualProof.Rule.Comprehension.retain outer before after
              arguments)
            (_root_.VisualProof.Rule.Comprehension.selected outer before after
              arguments)
            items normalized := by
        rw [EqualityNormalization.supportPattern_eq_identityBoundary pattern
          materialCanonical]
        exact normalizedEvidence
      have core : normalizedRequest.Result :=
        compileSupportPattern material materialCanonical supportEvidence
          normalizedRequest
      cases polarityEq : request.polarity with
      | positive =>
          have coreSteps : Relation.TransGen Step normalizedEndpoint
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded) := by
            simpa only [normalizedRequest, Telescope.Request.Result,
              Telescope.Compiles, polarityEq, polaritySource, polarityTarget,
              exactOccurrence, normalizedEndpoint] using core
          have phaseIso : OpenDiagramIso phaseTarget normalizedEndpoint := by
            simpa only [phaseTarget, normalizedEndpoint] using normalizedIso
          have forwardSteps : Relation.ReflTransGen Step originalEndpoint
              phaseTarget := by
            simpa only [phaseTarget, normalizedEndpoint] using forward
          have exact : Relation.TransGen Step originalEndpoint
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded) :=
            forwardSteps.transGen
              (transGen_iso phaseIso.symm coreSteps (OpenDiagramIso.refl _))
          have sourceIso : OpenDiagramIso originalEndpoint request.source := by
            simpa only [originalEndpoint, polarityEq, polaritySource] using
              request.occurrence.host_iso.symm
          have presented :=
            transGen_iso sourceIso exact (OpenDiagramIso.refl _)
          simpa only [Telescope.Request.Result, Telescope.Compiles,
            polarityEq, polarityTarget] using presented
      | negative =>
          have coreSteps : Relation.TransGen Step
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded)
              normalizedEndpoint := by
            simpa only [normalizedRequest, Telescope.Request.Result,
              Telescope.Compiles, polarityEq, polaritySource, polarityTarget,
              exactOccurrence, normalizedEndpoint] using core
          have phaseIso : OpenDiagramIso phaseTarget normalizedEndpoint := by
            simpa only [phaseTarget, normalizedEndpoint] using normalizedIso
          have reverseSteps : Relation.ReflTransGen Step phaseTarget
              originalEndpoint := by
            simpa only [phaseTarget, normalizedEndpoint] using reverse
          have exact : Relation.TransGen Step
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded)
              originalEndpoint :=
            (transGen_iso (OpenDiagramIso.refl _) coreSteps phaseIso.symm)
              |>.reflTransGen reverseSteps
          have sourceIso : OpenDiagramIso
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded)
              request.source := by
            simpa only [polarityEq, polaritySource] using
              request.occurrence.host_iso.symm
          have presented :=
            transGen_iso sourceIso exact (OpenDiagramIso.refl _)
          simpa only [Telescope.Request.Result, Telescope.Compiles,
            polarityEq, polarityTarget, originalEndpoint] using presented

end PatternCompiler

end Compiler

end VisualProof.Rule.Completeness.Comprehension
