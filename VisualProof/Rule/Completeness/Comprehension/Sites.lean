import VisualProof.Rule.Completeness.Comprehension.Telescope
import VisualProof.Diagram.Scope.Isomorphism
import VisualProof.Diagram.Isomorphism.Algebra

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- An existing transform edit together with the exact staged region computed
by its authoritative `run`; no edit leaves the structural fold unaccounted. -/
structure ExactEdit
    {targetWires : List Sig}
    (Edit : Type)
    (run : Edit → Region targetWires) where
  edit : Edit
  endpoint : Region targetWires
  run_eq : run edit = endpoint

def ExactEdit.refl
    {targetWires : List Sig}
    {Edit : Type}
    {run : Edit → Region targetWires}
    (edit : Edit) : ExactEdit Edit run where
  edit := edit
  endpoint := run edit
  run_eq := rfl


/-! These witnesses live in `Type` only to make the demand for
`Operation.SiteData` explicit and to expose their genuine recursive shape to
Lean's termination checker. The authoritative `Instantiation` proof is the
index of every constructor; the witnesses carry no alternate source, result,
transform, or validity authority. In particular, no proposition is eliminated
to manufacture Type-valued site data. -/

mutual
  /-- Demand-driven selected-site evidence for one actual recursive region
result. It asks for site data only where the authoritative evidence contains a
selected application. -/
  inductive RegionSites (operation : Transform.Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      {pattern : OpenDiagram arguments} →
      {frame : Transform.Frame arguments common sourceWires targetWires} →
      (data : operation.Data frame) →
      {source : Region sourceWires} → {result : Region common} →
      VisualProof.Rule.Comprehension.Instantiation.RegionResult
        pattern frame.sourceKeep frame.selected source result → Type
    | mk
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {locals : List Sig}
        {items : ItemSeq (sourceWires ++ locals)}
        {result : Region (common ++ locals)}
        {evidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            pattern (frame.sourceKeep.appendRight locals)
            (frame.selected.appendLeft locals) items result}
        (sites : ItemsSites operation
          (operation.appendData frame data locals) evidence) :
        RegionSites operation data
          (VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            evidence)

  /-- Demand-driven selected-site evidence for an actual item sequence. -/
  inductive ItemsSites (operation : Transform.Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      {pattern : OpenDiagram arguments} →
      {frame : Transform.Frame arguments common sourceWires targetWires} →
      (data : operation.Data frame) →
      {source : ItemSeq sourceWires} → {result : Region common} →
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result → Type
    | nil
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (evidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            pattern frame.sourceKeep frame.selected
            (.nil : ItemSeq sourceWires) (Region.blank common)) :
        ItemsSites operation data evidence
    | cons
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {item : Item sourceWires} {tail : ItemSeq sourceWires}
        {itemResult tailResult : Region common}
        {itemEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemResult
            pattern frame.sourceKeep frame.selected item itemResult}
        {tailEvidence :
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            pattern frame.sourceKeep frame.selected tail tailResult}
        (itemSites : ItemSites operation data itemEvidence)
        (tailSites : ItemsSites operation data tailEvidence) :
        ItemsSites operation data
          (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemEvidence tailEvidence)

  /-- Demand-driven selected-site evidence for one actual item. Nonselected
atoms and identities need no operation site data. -/
  inductive ItemSites (operation : Transform.Operation arguments) :
      {common sourceWires targetWires : List Sig} →
      {pattern : OpenDiagram arguments} →
      {frame : Transform.Frame arguments common sourceWires targetWires} →
      (data : operation.Data frame) →
      {source : Item sourceWires} → {result : Region common} →
      VisualProof.Rule.Comprehension.Instantiation.ItemResult
        pattern frame.sourceKeep frame.selected source result → Type
    | atom
        {common sourceWires targetWires atomArguments : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (head : Var common (.rel atomArguments))
        (ports : Vars common atomArguments) :
        ItemSites operation data
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            head ports)
    | selectedAtom
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (ports : Vars common arguments)
        (siteData : operation.SiteData frame data ports) :
        ItemSites operation data
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            ports)
    | identity
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var common signature) :
        ItemSites operation data
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            signature arity ports)
    | cut
        {common sourceWires targetWires : List Sig}
        {pattern : OpenDiagram arguments}
        {frame : Transform.Frame arguments common sourceWires targetWires}
        {data : operation.Data frame}
        {body : Region sourceWires} {result : Region common}
        {evidence :
          VisualProof.Rule.Comprehension.Instantiation.RegionResult
            pattern frame.sourceKeep frame.selected body result}
        (sites : RegionSites operation data evidence) :
        ItemSites operation data
          (VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            evidence)
end


/-! `RegionResult`, `ItemsResult`, and `ItemResult` describe the simultaneous
layout of every selected site for one `Transform` primitive. Their recursive
shape therefore builds one exact edit; it does not introduce recursive
calculus steps or duplicate the surrounding telescope request. -/

mutual
  /-- Fold authoritative region evidence and its demand-driven sites into one
existing transform edit at its exact `run` endpoint. -/
  def regionEdit
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : Region sourceWires}
      {result : Region common}
      (evidence : VisualProof.Rule.Comprehension.Instantiation.RegionResult
        pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      ExactEdit
        (Transform.RegionEdit operation frame data source)
        (fun edit => edit.run) :=
    match sites with
    | .mk childSites =>
        let childOutput := itemsEdit
          (operation.appendData frame data _) _ childSites
        {
          edit := .mk childOutput.edit
          endpoint := Region.adjoinAt _ .nil childOutput.endpoint
          run_eq := by
            simp only [Transform.RegionEdit.run]
            rw [childOutput.run_eq]
        }
  termination_by structural sites

  /-- Fold one authoritative item sequence into the same all-sites edit. -/
  def itemsEdit
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : ItemSeq sourceWires}
      {result : Region common}
      (evidence : VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      ExactEdit
        (Transform.ItemsEdit operation frame data source)
        (fun edit => edit.run) :=
    match sites with
    | .nil _ => ExactEdit.refl .nil
    | .cons itemSites tailSites =>
        let itemOutput := itemEdit data _ itemSites
        let tailOutput := itemsEdit data _ tailSites
        {
          edit := .cons itemOutput.edit tailOutput.edit
          endpoint := itemOutput.endpoint.conjoin tailOutput.endpoint
          run_eq := by
            simp only [Transform.ItemsEdit.run]
            rw [itemOutput.run_eq, tailOutput.run_eq]
        }
  termination_by structural sites

  /-- Fold one authoritative item. Only its selected-atom branch consumes
operation-specific site data. -/
  def itemEdit
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      (data : operation.Data frame)
      {source : Item sourceWires}
      {result : Region common}
      (evidence : VisualProof.Rule.Comprehension.Instantiation.ItemResult
        pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      ExactEdit
        (Transform.ItemEdit operation frame data source)
        (fun edit => edit.run) :=
    match sites with
    | .atom head ports => ExactEdit.refl (.atom head ports)
    | .selectedAtom ports siteData =>
        ExactEdit.refl (.selectedAtom ports siteData)
    | .identity signature arity ports =>
        ExactEdit.refl (.identity signature arity ports)
    | .cut childSites =>
        let childOutput := regionEdit data _ childSites
        {
          edit := .cut childOutput.edit
          endpoint := Region.singleton (.cut childOutput.endpoint)
          run_eq := by
            simp only [Transform.ItemEdit.run]
            rw [childOutput.run_eq]
        }
  termination_by structural sites
end


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
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
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


mutual
  theorem regionEdit_noSelectedPin
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame} {pattern : OpenDiagram arguments}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
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

/-- Derive one authoritative cut-pattern layer through the single CutShape
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
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
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
      exact branch.derive

/-- Derive one authoritative pattern-local wire through the single Arity
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
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
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
      exact branch.derive

/-- Derive one authoritative conjunction layer through the single
ParallelShape primitive at the binder home. Recursive child derivation has
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
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
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
      exact branch.derive


/-- Derive one complete selected-application layer through formal
application. Boundary and equality derivation prepare the authoritative
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
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
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
          exact branch.derive

/-- Derive one complete selected-application layer through identity leaf.
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
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
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
      exact branch.derive


end VisualProof.Rule.Completeness.Comprehension
