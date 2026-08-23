import VisualProof.Rule.Completeness.Comprehension.Normalization.Instantiation

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace EqualityNormalization

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

theorem StrictEquates.toEquates
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
theorem StrictEquates.refl
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
theorem Equates.trans
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
def allPins (source : List Sig)
    (rename : WireRenaming source target) : ItemSeq target :=
  ItemSeq.pinWires source rename (fun _ => true)

/-- Add one pin for every selected source wire at an exact occurrence. -/
theorem pinAllExact
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
theorem pinAllNonempty
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
theorem pinAllTwiceNonempty
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

theorem pinAllTwiceOfNonempty
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

theorem allPins_renameWires
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

theorem allPins_mem_nil
    (source : List Sig) (rename : WireRenaming source target)
    (wire : Var source signature) (itemIndex : Nat) :
    [] ∈ (allPins source rename).incidencePaths
      (rename wire).index.val itemIndex := by
  exact ItemSeq.pinWires_mem_nil source rename (fun _ => true) wire
    itemIndex rfl

/-- Two complete pin batches root every selected wire at the current region. -/
theorem allPins_twice_rooted
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

theorem allPins_twice_childrenCanonical
    (source : List Sig) (rename : WireRenaming source target) :
    ((allPins source rename).append
      (allPins source rename)).ChildrenCanonical := by
  exact (ItemSeq.childrenCanonical_append _ _).mpr
    ⟨ItemSeq.pinWires_childrenCanonical source rename (fun _ => true),
      ItemSeq.pinWires_childrenCanonical source rename (fun _ => true)⟩
def appendAdjoinedPins
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
noncomputable def adjoinPinsIso
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

theorem ItemSeq.incidencePaths_append_nonempty_iff
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

theorem ItemSeq.incidencePaths_rotate_nonempty_iff
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

theorem contextPins_incidence_nonempty
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


end EqualityNormalization

end VisualProof.Rule.Completeness.Comprehension
