import VisualProof.Rule.Completeness.Comprehension.Telescope
import VisualProof.Rule.Completeness.Erasure.Exposure
import VisualProof.Diagram.Scope.Isomorphism
import VisualProof.Diagram.Isomorphism.Algebra

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

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


end VisualProof.Rule.Completeness.Comprehension
