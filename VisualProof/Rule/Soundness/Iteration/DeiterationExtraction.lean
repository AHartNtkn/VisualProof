import VisualProof.Rule.Soundness.Iteration.DeiterationTransport

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

def deiterationRetainedLayout
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FragmentLayout
      (input.val.removeRaw selection (deiterationDomains input selection))
      (deiterationRetainedSelection input selection witness) := {}

def deiterationOriginalLayout
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FragmentLayout input.val witness.justifier := {}

def deiterationRetainedExtract
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) : OpenConcreteDiagram :=
  input.val.removeRaw selection (deiterationDomains input selection)
    |>.extractOpenRaw (deiterationRetainedSelection input selection witness)
      (deiterationRetainedLayout input selection witness)

def deiterationOriginalExtract
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) : OpenConcreteDiagram :=
  input.val.extractOpenRaw witness.justifier
    (deiterationOriginalLayout input selection witness)

private theorem listGet_origin_of_map_eq
    {source : List α} {target : List β} (origin : α → β)
    (equality : source.map origin = target) (index : Fin source.length) :
    origin (source.get index) =
      target.get (Fin.cast (by
        simpa using congrArg List.length equality) index) := by
  let mappedIndex : Fin (source.map origin).length :=
    Fin.cast (by simp) index
  have transported := List.get_of_eq equality mappedIndex
  simpa using transported

private theorem indexOf?_map_injective
    [DecidableEq α] [DecidableEq β]
    (origin : α → β) (injective : Function.Injective origin)
    (values : List α) (nodup : values.Nodup) (value : α) :
    indexOf? (values.map origin) (origin value) =
      Option.map (Fin.cast (by simp)) (indexOf? values value) := by
  cases found : indexOf? values value with
  | some index =>
      have getEq := indexOf?_sound found
      have mappedGet : (values.map origin).get
          (Fin.cast (by simp) index) = origin value := by
        exact (listGet_origin_of_map_eq origin rfl index).symm.trans
          (congrArg origin getEq)
      have mappedFound := indexOf?_get_eq_some_of_nodup
        (nodup.map origin (fun first second distinct equality =>
          distinct (injective equality))) (Fin.cast (by simp) index)
      rw [mappedGet] at mappedFound
      simpa [found] using mappedFound
  | none =>
      simp only [Option.map_none]
      cases mappedFound : indexOf? (values.map origin) (origin value) with
      | none => rfl
      | some index =>
          have mappedGet := indexOf?_sound mappedFound
          have member := List.get_mem (values.map origin) index
          obtain ⟨original, originalMember, originalMap⟩ :=
            List.mem_map.mp member
          have valueEq : original = value := injective
            (originalMap.trans mappedGet)
          subst original
          obtain ⟨presentIndex, present⟩ := indexOf?_complete originalMember
          rw [found] at present
          contradiction

private theorem indexOf?_of_map_eq
    [DecidableEq α] [DecidableEq β]
    (origin : α → β) (injective : Function.Injective origin)
    (source : List α) (sourceNodup : source.Nodup) (target : List β)
    (equality : source.map origin = target) (value : α) :
    indexOf? target (origin value) =
      Option.map
        (Fin.cast (by simpa using congrArg List.length equality))
        (indexOf? source value) := by
  subst target
  exact indexOf?_map_injective origin injective source sourceNodup value

theorem deiterationRetainedLayout_externalBinders_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedLayout input selection witness).externalBinders.map
        (deiterationDomains input selection).regions.origin =
      (deiterationOriginalLayout input selection witness).externalBinders := by
  rw [(deiterationRetainedLayout input selection witness).externalBinders_exact,
    (deiterationOriginalLayout input selection witness).externalBinders_exact]
  exact deiterationRetained_externalBinders_origin input selection witness

def deiterationExternalLengthEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedLayout input selection witness).externalBinders.length =
      (deiterationOriginalLayout input selection witness).externalBinders.length :=
  by
    simpa using congrArg List.length
      (deiterationRetainedLayout_externalBinders_origin input selection witness)

def deiterationRegionLengthEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).selectedRegions.length =
      witness.justifier.selectedRegions.length :=
  by
    simpa using congrArg List.length
      (deiterationRetained_selectedRegions_origin input selection witness)

def deiterationNodeLengthEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).selectedNodes.length =
      witness.justifier.selectedNodes.length :=
  by
    simpa using congrArg List.length
      (deiterationRetained_selectedNodes_origin input selection witness)

def deiterationInternalWireLengthEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).internalWires.length =
      witness.justifier.internalWires.length :=
  by
    simpa using congrArg List.length
      (deiterationRetained_internalWires_origin input selection witness)

def deiterationTouchingWireLengthEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedSelection input selection witness).touchingWires.length =
      witness.justifier.touchingWires.length :=
  by
    simpa using congrArg List.length
      (deiterationRetained_touchingWires_origin input selection witness)

def deiterationExtractRegionCountEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedExtract input selection witness).diagram.regionCount =
      (deiterationOriginalExtract input selection witness).diagram.regionCount := by
  simp only [deiterationRetainedExtract, deiterationOriginalExtract,
    ConcreteDiagram.extractOpenRaw, ConcreteDiagram.extractDiagramRaw,
    FragmentLayout.regionCount, FragmentLayout.proxyCount,
    FragmentLayout.materialRegionCount]
  rw [deiterationExternalLengthEq input selection witness,
    deiterationRegionLengthEq input selection witness]

def deiterationExtractNodeCountEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedExtract input selection witness).diagram.nodeCount =
      (deiterationOriginalExtract input selection witness).diagram.nodeCount :=
  deiterationNodeLengthEq input selection witness

def deiterationExtractWireCountEq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedExtract input selection witness).diagram.wireCount =
      (deiterationOriginalExtract input selection witness).diagram.wireCount := by
  simp only [deiterationRetainedExtract, deiterationOriginalExtract,
    ConcreteDiagram.extractOpenRaw, ConcreteDiagram.extractDiagramRaw,
    FragmentLayout.wireCount, FragmentLayout.internalWireCount,
    FragmentLayout.boundaryWireCount]
  rw [deiterationInternalWireLengthEq input selection witness,
    deiterationTouchingWireLengthEq input selection witness]

def deiterationExtractRegionEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (Fin (deiterationRetainedExtract input selection witness).diagram.regionCount)
      (Fin (deiterationOriginalExtract input selection witness).diagram.regionCount) :=
  FiniteEquiv.finCast (deiterationExtractRegionCountEq input selection witness)

def deiterationExtractNodeEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (Fin (deiterationRetainedExtract input selection witness).diagram.nodeCount)
      (Fin (deiterationOriginalExtract input selection witness).diagram.nodeCount) :=
  FiniteEquiv.finCast (deiterationExtractNodeCountEq input selection witness)

def deiterationExtractWireEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    FiniteEquiv
      (Fin (deiterationRetainedExtract input selection witness).diagram.wireCount)
      (Fin (deiterationOriginalExtract input selection witness).diagram.wireCount) :=
  FiniteEquiv.finCast (deiterationExtractWireCountEq input selection witness)

theorem deiterationRetained_selectedRegion_get_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedSelection input selection witness
      |>.selectedRegions.length)) :
    (deiterationDomains input selection).regions.origin
        ((deiterationRetainedSelection input selection witness
          |>.selectedRegions).get index) =
      witness.justifier.selectedRegions.get
        (Fin.cast (deiterationRegionLengthEq input selection witness) index) := by
  exact listGet_origin_of_map_eq _
    (deiterationRetained_selectedRegions_origin input selection witness) index

theorem deiterationRetained_selectedNode_get_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedSelection input selection witness
      |>.selectedNodes.length)) :
    (deiterationDomains input selection).nodes.origin
        ((deiterationRetainedSelection input selection witness
          |>.selectedNodes).get index) =
      witness.justifier.selectedNodes.get
        (Fin.cast (deiterationNodeLengthEq input selection witness) index) := by
  exact listGet_origin_of_map_eq _
    (deiterationRetained_selectedNodes_origin input selection witness) index

theorem deiterationRetained_internalWire_get_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedSelection input selection witness
      |>.internalWires.length)) :
    (deiterationDomains input selection).wires.origin
        ((deiterationRetainedSelection input selection witness
          |>.internalWires).get index) =
      witness.justifier.internalWires.get
        (Fin.cast (deiterationInternalWireLengthEq input selection witness)
          index) := by
  exact listGet_origin_of_map_eq _
    (deiterationRetained_internalWires_origin input selection witness) index

theorem deiterationRetained_touchingWire_get_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedSelection input selection witness
      |>.touchingWires.length)) :
    (deiterationDomains input selection).wires.origin
        ((deiterationRetainedSelection input selection witness
          |>.touchingWires).get index) =
      witness.justifier.touchingWires.get
        (Fin.cast (deiterationTouchingWireLengthEq input selection witness)
          index) := by
  exact listGet_origin_of_map_eq _
    (deiterationRetained_touchingWires_origin input selection witness) index

theorem deiterationRetained_externalBinder_get_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.externalBinders.length)) :
    (deiterationDomains input selection).regions.origin
        ((deiterationRetainedLayout input selection witness
          |>.externalBinders).get index) =
      (deiterationOriginalLayout input selection witness).externalBinders.get
        (Fin.cast (deiterationExternalLengthEq input selection witness)
          index) := by
  exact listGet_origin_of_map_eq _
    (deiterationRetainedLayout_externalBinders_origin input selection witness)
    index

theorem deiterationExtractRegionEquiv_root
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    deiterationExtractRegionEquiv input selection witness
        (deiterationRetainedLayout input selection witness).root =
      (deiterationOriginalLayout input selection witness).root := by
  apply Fin.ext
  rfl

theorem deiterationExtractRegionEquiv_proxy
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.proxyCount)) :
    deiterationExtractRegionEquiv input selection witness
        ((deiterationRetainedLayout input selection witness).proxy index) =
      (deiterationOriginalLayout input selection witness).proxy
        (Fin.cast (deiterationExternalLengthEq input selection witness)
          index) := by
  apply Fin.ext
  rfl

theorem deiterationExtractRegionEquiv_materialRegion
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.materialRegionCount)) :
    deiterationExtractRegionEquiv input selection witness
        ((deiterationRetainedLayout input selection witness).materialRegion
          index) =
      (deiterationOriginalLayout input selection witness).materialRegion
        (Fin.cast (deiterationRegionLengthEq input selection witness)
          index) := by
  apply Fin.ext
  simp only [deiterationExtractRegionEquiv, FiniteEquiv.finCast,
    FragmentLayout.materialRegion]
  change 1 +
      (deiterationRetainedLayout input selection witness).proxyCount +
        index.val =
    1 + (deiterationOriginalLayout input selection witness).proxyCount +
      index.val
  rw [show (deiterationRetainedLayout input selection witness).proxyCount =
      (deiterationOriginalLayout input selection witness).proxyCount from
    deiterationExternalLengthEq input selection witness]

theorem deiterationExtractRegionEquiv_bodyContainer
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    deiterationExtractRegionEquiv input selection witness
        (deiterationRetainedLayout input selection witness).bodyContainer =
      (deiterationOriginalLayout input selection witness).bodyContainer := by
  let source := deiterationRetainedLayout input selection witness
  let target := deiterationOriginalLayout input selection witness
  have countEq : source.proxyCount = target.proxyCount :=
    deiterationExternalLengthEq input selection witness
  by_cases empty : source.proxyCount = 0
  · have targetEmpty : target.proxyCount = 0 := by omega
    rw [source.bodyContainer_eq_root_of_proxyCount_eq_zero empty,
      target.bodyContainer_eq_root_of_proxyCount_eq_zero targetEmpty]
    exact deiterationExtractRegionEquiv_root input selection witness
  · have targetNonempty : target.proxyCount ≠ 0 := by omega
    rw [source.bodyContainer_eq_terminal_of_proxyCount_ne_zero empty,
      target.bodyContainer_eq_terminal_of_proxyCount_ne_zero targetNonempty]
    apply Fin.ext
    simp only [deiterationExtractRegionEquiv, FiniteEquiv.finCast,
      Fin.val_cast, FragmentLayout.proxy]
    omega

theorem deiterationExtractWireEquiv_internalWire
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.internalWireCount)) :
    deiterationExtractWireEquiv input selection witness
        ((deiterationRetainedLayout input selection witness).internalWire
          index) =
      (deiterationOriginalLayout input selection witness).internalWire
        (Fin.cast (deiterationInternalWireLengthEq input selection witness)
          index) := by
  apply Fin.ext
  rfl

theorem deiterationExtractWireEquiv_boundaryWire
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.boundaryWireCount)) :
    deiterationExtractWireEquiv input selection witness
        ((deiterationRetainedLayout input selection witness).boundaryWire
          index) =
      (deiterationOriginalLayout input selection witness).boundaryWire
        (Fin.cast (deiterationTouchingWireLengthEq input selection witness)
          index) := by
  apply Fin.ext
  simp only [deiterationExtractWireEquiv, FiniteEquiv.finCast,
    FragmentLayout.boundaryWire, Fin.natAdd]
  change (deiterationRetainedLayout input selection witness).internalWireCount +
      index.val =
    (deiterationOriginalLayout input selection witness).internalWireCount +
      index.val
  rw [show (deiterationRetainedLayout input selection witness).internalWireCount =
      (deiterationOriginalLayout input selection witness).internalWireCount from
    deiterationInternalWireLengthEq input selection witness]

theorem deiterationExtractNodeEquiv_index
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.nodeCount)) :
    deiterationExtractNodeEquiv input selection witness index =
      Fin.cast (deiterationNodeLengthEq input selection witness) index := rfl

private theorem deiteration_selectedRegions_indexOf_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : (deiterationDomains input selection).regions.Carrier) :
    indexOf? witness.justifier.selectedRegions
        ((deiterationDomains input selection).regions.origin region) =
      Option.map
        (Fin.cast (deiterationRegionLengthEq input selection witness))
        (indexOf?
          (deiterationRetainedSelection input selection witness
            |>.selectedRegions) region) := by
  exact indexOf?_of_map_eq _
    (deiterationDomains input selection).regions.origin_injective
    (deiterationRetainedSelection input selection witness).selectedRegions
    (deiterationRetainedSelection input selection witness
      |>.selectedRegions_nodup)
    witness.justifier.selectedRegions
    (deiterationRetained_selectedRegions_origin input selection witness) region

private theorem deiteration_externalBinders_indexOf_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (binder : (deiterationDomains input selection).regions.Carrier) :
    indexOf? (deiterationOriginalLayout input selection witness).externalBinders
        ((deiterationDomains input selection).regions.origin binder) =
      Option.map
        (Fin.cast (deiterationExternalLengthEq input selection witness))
        (indexOf?
          (deiterationRetainedLayout input selection witness).externalBinders
          binder) := by
  exact indexOf?_of_map_eq _
    (deiterationDomains input selection).regions.origin_injective
    (deiterationRetainedLayout input selection witness).externalBinders
    (deiterationRetainedLayout input selection witness
      |>.externalBinders_nodup)
    (deiterationOriginalLayout input selection witness).externalBinders
    (deiterationRetainedLayout_externalBinders_origin input selection witness)
    binder

private theorem deiteration_selectedNodes_indexOf_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : (deiterationDomains input selection).nodes.Carrier) :
    indexOf? witness.justifier.selectedNodes
        ((deiterationDomains input selection).nodes.origin node) =
      Option.map
        (Fin.cast (deiterationNodeLengthEq input selection witness))
        (indexOf?
          (deiterationRetainedSelection input selection witness
            |>.selectedNodes) node) := by
  exact indexOf?_of_map_eq _
    (deiterationDomains input selection).nodes.origin_injective
    (deiterationRetainedSelection input selection witness).selectedNodes
    (deiterationRetainedSelection input selection witness
      |>.selectedNodes_nodup)
    witness.justifier.selectedNodes
    (deiterationRetained_selectedNodes_origin input selection witness) node

theorem deiteration_fragmentParent_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (parent : (deiterationDomains input selection).regions.Carrier) :
    deiterationExtractRegionEquiv input selection witness
        ((input.val.removeRaw selection (deiterationDomains input selection))
          |>.fragmentParent
            (deiterationRetainedLayout input selection witness) parent) =
      input.val.fragmentParent
        (deiterationOriginalLayout input selection witness)
        ((deiterationDomains input selection).regions.origin parent) := by
  have anchorOrigin : (deiterationDomains input selection).regions.origin
        (deiterationRetainedSelection input selection witness).val.anchor =
      witness.justifier.val.anchor := by
    exact (deiterationDomains input selection).regions.origin_index
      witness.justifier.val.anchor
      (deiterationJustifierAnchor_survives input selection witness)
  unfold ConcreteDiagram.fragmentParent
  split
  · rename_i sourceAnchor
    have targetAnchor :
        (deiterationDomains input selection).regions.origin parent =
          witness.justifier.val.anchor := by rw [sourceAnchor, anchorOrigin]
    rw [if_pos targetAnchor]
    exact deiterationExtractRegionEquiv_bodyContainer input selection witness
  · rename_i sourceNotAnchor
    have targetNotAnchor :
        (deiterationDomains input selection).regions.origin parent ≠
          witness.justifier.val.anchor := by
      intro targetAnchor
      apply sourceNotAnchor
      apply (deiterationDomains input selection).regions.origin_injective
      rw [targetAnchor, anchorOrigin]
    rw [if_neg targetNotAnchor]
    rw [deiteration_selectedRegions_indexOf_origin input selection witness]
    cases found : indexOf?
        (deiterationRetainedSelection input selection witness).selectedRegions
        parent with
    | none =>
        simp only [Option.map_none]
        exact deiterationExtractRegionEquiv_bodyContainer input selection
          witness
    | some index =>
        simp only [Option.map_some]
        exact deiterationExtractRegionEquiv_materialRegion input selection
          witness index

theorem deiteration_fragmentBinder_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (binder : (deiterationDomains input selection).regions.Carrier) :
    deiterationExtractRegionEquiv input selection witness
        ((input.val.removeRaw selection (deiterationDomains input selection))
          |>.fragmentBinder
            (deiterationRetainedLayout input selection witness) binder) =
      input.val.fragmentBinder
        (deiterationOriginalLayout input selection witness)
        ((deiterationDomains input selection).regions.origin binder) := by
  unfold ConcreteDiagram.fragmentBinder
  rw [deiteration_selectedRegions_indexOf_origin input selection witness]
  cases selected : indexOf?
      (deiterationRetainedSelection input selection witness).selectedRegions
      binder with
  | some index =>
      simp only [Option.map_some]
      exact deiterationExtractRegionEquiv_materialRegion input selection
        witness index
  | none =>
      simp only [Option.map_none]
      rw [deiteration_externalBinders_indexOf_origin input selection witness]
      cases external : indexOf?
          (deiterationRetainedLayout input selection witness).externalBinders
          binder with
      | some index =>
          simp only [Option.map_some]
          exact deiterationExtractRegionEquiv_proxy input selection witness index
      | none =>
          simp only [Option.map_none]
          exact deiterationExtractRegionEquiv_bodyContainer input selection
            witness

private theorem deiteration_removeRaw_binderArity_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (domains : FrameDomains input.val selection)
    (binder : domains.regions.Carrier) :
    (input.val.removeRaw selection domains).binderArity? binder =
      input.val.binderArity? (domains.regions.origin binder) := by
  have reindexed := ConcreteDiagram.removeRaw_region_reindexed input selection
    domains binder
  cases originalKind : input.val.regions (domains.regions.origin binder) with
  | sheet =>
      rw [originalKind] at reindexed
      have removedKind :
          (input.val.removeRaw selection domains).regions binder = .sheet := by
        simpa [SurvivorDomain.reindexRegion?] using
          (Option.some.inj reindexed).symm
      unfold ConcreteDiagram.binderArity?
      rw [removedKind, originalKind]
  | cut parent =>
      have parentSurvives := domains.parent_survives input selection
        (domains.regions.origin_survives binder)
        ((congrArg CRegion.parent? originalKind).trans rfl)
      rw [originalKind] at reindexed
      simp only [SurvivorDomain.reindexRegion?] at reindexed
      rw [domains.regions.index?_index parent parentSurvives] at reindexed
      have removedKind :
          (input.val.removeRaw selection domains).regions binder =
            .cut (domains.regions.index parent parentSurvives) :=
        (Option.some.inj reindexed).symm
      unfold ConcreteDiagram.binderArity?
      rw [removedKind, originalKind]
  | bubble parent arity =>
      have parentSurvives := domains.parent_survives input selection
        (domains.regions.origin_survives binder)
        ((congrArg CRegion.parent? originalKind).trans rfl)
      rw [originalKind] at reindexed
      simp only [SurvivorDomain.reindexRegion?] at reindexed
      rw [domains.regions.index?_index parent parentSurvives] at reindexed
      have removedKind :
          (input.val.removeRaw selection domains).regions binder =
            .bubble (domains.regions.index parent parentSurvives) arity :=
        (Option.some.inj reindexed).symm
      unfold ConcreteDiagram.binderArity?
      rw [removedKind, originalKind]

theorem deiterationExtract_materialRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.materialRegionCount)) :
    ((deiterationRetainedExtract input selection witness).diagram.regions
        ((deiterationRetainedLayout input selection witness).materialRegion
          index)).rename
      (deiterationExtractRegionEquiv input selection witness) =
    (deiterationOriginalExtract input selection witness).diagram.regions
      ((deiterationOriginalLayout input selection witness).materialRegion
        (Fin.cast (deiterationRegionLengthEq input selection witness)
          index)) := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  let sourceLayout := deiterationRetainedLayout input selection witness
  let targetLayout := deiterationOriginalLayout input selection witness
  let mappedRegion := retained.selectedRegions.get index
  let originalRegion := domains.regions.origin mappedRegion
  unfold deiterationRetainedExtract deiterationOriginalExtract
  simp only [ConcreteDiagram.extractOpenRaw]
  have originalGet : originalRegion = witness.justifier.selectedRegions.get
      (Fin.cast (deiterationRegionLengthEq input selection witness) index) :=
    deiterationRetained_selectedRegion_get_origin input selection witness index
  have reindexed := ConcreteDiagram.removeRaw_region_reindexed input selection
    domains mappedRegion
  cases originalKind : input.val.regions originalRegion with
  | sheet =>
      have targetKind : input.val.regions
          (witness.justifier.selectedRegions.get
            (Fin.cast (deiterationRegionLengthEq input selection witness)
              index)) = .sheet := by
        rw [← originalGet]
        exact originalKind
      have removedKind :
          (input.val.removeRaw selection domains).regions mappedRegion =
            .sheet := by
        rw [originalKind] at reindexed
        simpa [SurvivorDomain.reindexRegion?] using
          (Option.some.inj reindexed).symm
      rw [ConcreteDiagram.extractDiagramRaw_materialRegion_sheet _ retained
          sourceLayout index removedKind,
        ConcreteDiagram.extractDiagramRaw_materialRegion_sheet _
          witness.justifier targetLayout
          (Fin.cast (deiterationRegionLengthEq input selection witness) index)
          targetKind]
      simp only [CRegion.rename]
      exact congrArg CRegion.cut
        (deiterationExtractRegionEquiv_bodyContainer input selection witness)
  | cut parent =>
      have targetKind : input.val.regions
          (witness.justifier.selectedRegions.get
            (Fin.cast (deiterationRegionLengthEq input selection witness)
              index)) = .cut parent := by
        rw [← originalGet]
        exact originalKind
      have parentSurvives := domains.parent_survives input selection
        (domains.regions.origin_survives mappedRegion)
        ((congrArg CRegion.parent? originalKind).trans rfl)
      have removedKind :
          (input.val.removeRaw selection domains).regions mappedRegion =
            .cut (domains.regions.index parent parentSurvives) := by
        rw [originalKind] at reindexed
        simp only [SurvivorDomain.reindexRegion?] at reindexed
        rw [domains.regions.index?_index parent parentSurvives] at reindexed
        exact (Option.some.inj reindexed).symm
      rw [ConcreteDiagram.extractDiagramRaw_materialRegion_cut _ retained
          sourceLayout index _ removedKind,
        ConcreteDiagram.extractDiagramRaw_materialRegion_cut _
          witness.justifier targetLayout
          (Fin.cast (deiterationRegionLengthEq input selection witness) index)
          parent targetKind]
      simp only [CRegion.rename]
      exact congrArg CRegion.cut
        (deiteration_fragmentParent_origin input selection witness
          (domains.regions.index parent parentSurvives) |>.trans (by
            rw [domains.regions.origin_index]))
  | bubble parent arity =>
      have targetKind : input.val.regions
          (witness.justifier.selectedRegions.get
            (Fin.cast (deiterationRegionLengthEq input selection witness)
              index)) = .bubble parent arity := by
        rw [← originalGet]
        exact originalKind
      have parentSurvives := domains.parent_survives input selection
        (domains.regions.origin_survives mappedRegion)
        ((congrArg CRegion.parent? originalKind).trans rfl)
      have removedKind :
          (input.val.removeRaw selection domains).regions mappedRegion =
            .bubble (domains.regions.index parent parentSurvives) arity := by
        rw [originalKind] at reindexed
        simp only [SurvivorDomain.reindexRegion?] at reindexed
        rw [domains.regions.index?_index parent parentSurvives] at reindexed
        exact (Option.some.inj reindexed).symm
      rw [ConcreteDiagram.extractDiagramRaw_materialRegion_bubble _ retained
          sourceLayout index _ arity removedKind,
        ConcreteDiagram.extractDiagramRaw_materialRegion_bubble _
          witness.justifier targetLayout
          (Fin.cast (deiterationRegionLengthEq input selection witness) index)
          parent arity targetKind]
      simp only [CRegion.rename]
      congr 1
      exact deiteration_fragmentParent_origin input selection witness
        (domains.regions.index parent parentSurvives) |>.trans (by
          rw [domains.regions.origin_index])

theorem deiterationExtract_proxyRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.proxyCount)) :
    ((deiterationRetainedExtract input selection witness).diagram.regions
        ((deiterationRetainedLayout input selection witness).proxy index)).rename
      (deiterationExtractRegionEquiv input selection witness) =
    (deiterationOriginalExtract input selection witness).diagram.regions
      ((deiterationOriginalLayout input selection witness).proxy
        (Fin.cast (deiterationExternalLengthEq input selection witness)
          index)) := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  let targetIndex :=
    Fin.cast (deiterationExternalLengthEq input selection witness) index
  unfold deiterationRetainedExtract deiterationOriginalExtract
  simp only [ConcreteDiagram.extractOpenRaw]
  rw [ConcreteDiagram.extractDiagramRaw_proxy_region _ retained
      (deiterationRetainedLayout input selection witness) index,
    ConcreteDiagram.extractDiagramRaw_proxy_region _ witness.justifier
      (deiterationOriginalLayout input selection witness)
      (Fin.cast (deiterationExternalLengthEq input selection witness) index)]
  simp only [CRegion.rename]
  congr 1
  · change deiterationExtractRegionEquiv input selection witness
        (if _hzero : index.val = 0 then
          (deiterationRetainedLayout input selection witness).root
        else (deiterationRetainedLayout input selection witness).proxy
          ⟨index.val - 1, by omega⟩) =
      (if _hzero : targetIndex.val = 0 then
        (deiterationOriginalLayout input selection witness).root
      else (deiterationOriginalLayout input selection witness).proxy
        ⟨targetIndex.val - 1, by
          change targetIndex.val - 1 <
            (deiterationOriginalLayout input selection witness
              |>.externalBinders.length)
          omega⟩)
    by_cases zero : index.val = 0
    · have targetZero : targetIndex.val = 0 := by
        simpa [targetIndex] using zero
      simp only [zero, targetZero, dite_true]
      exact deiterationExtractRegionEquiv_root input selection witness
    · have targetNonzero : targetIndex.val ≠ 0 := by
        simpa [targetIndex] using zero
      simp only [zero, targetNonzero, dite_false]
      simpa [targetIndex] using
        (deiterationExtractRegionEquiv_proxy input selection witness
          ⟨index.val - 1, by omega⟩)
  · change ((input.val.removeRaw selection domains).binderArity?
          ((deiterationRetainedLayout input selection witness
            |>.externalBinders).get index)).getD 0 =
      (input.val.binderArity?
        ((deiterationOriginalLayout input selection witness
          |>.externalBinders).get targetIndex)).getD 0
    rw [deiteration_removeRaw_binderArity_origin input selection domains,
      deiterationRetained_externalBinder_get_origin input selection witness]

theorem deiterationExtract_regions_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin
      (deiterationRetainedExtract input selection witness).diagram.regionCount) :
    ((deiterationRetainedExtract input selection witness).diagram.regions
        region).rename
      (deiterationExtractRegionEquiv input selection witness) =
    (deiterationOriginalExtract input selection witness).diagram.regions
      (deiterationExtractRegionEquiv input selection witness region) := by
  let sourceLayout := deiterationRetainedLayout input selection witness
  revert region
  change ∀ region : Fin sourceLayout.regionCount,
      ((deiterationRetainedExtract input selection witness).diagram.regions
          region).rename
        (deiterationExtractRegionEquiv input selection witness) =
      (deiterationOriginalExtract input selection witness).diagram.regions
        (deiterationExtractRegionEquiv input selection witness region)
  intro region
  by_cases rootCase : region.val = 0
  · have sourceRoot : region = sourceLayout.root := by
      apply Fin.ext
      simpa [FragmentLayout.root] using rootCase
    rw [sourceRoot, deiterationExtractRegionEquiv_root input selection witness]
    unfold deiterationRetainedExtract deiterationOriginalExtract
    simp only [ConcreteDiagram.extractOpenRaw]
    rw [ConcreteDiagram.extractDiagramRaw_root_region _ _ sourceLayout,
      ConcreteDiagram.extractDiagramRaw_root_region _ _
        (deiterationOriginalLayout input selection witness)]
    rfl
  · by_cases proxyCase : region.val - 1 < sourceLayout.proxyCount
    · let proxy : Fin sourceLayout.proxyCount := ⟨region.val - 1, proxyCase⟩
      have sourceEq : region = sourceLayout.proxy proxy := by
        apply Fin.ext
        simp only [FragmentLayout.proxy, proxy]
        omega
      rw [sourceEq,
        deiterationExtractRegionEquiv_proxy input selection witness]
      exact deiterationExtract_proxyRegion_eq input selection witness proxy
    · have materialBound : region.val - 1 - sourceLayout.proxyCount <
          sourceLayout.materialRegionCount := by
        have regionBound := region.isLt
        simp only [FragmentLayout.regionCount] at regionBound
        omega
      let material : Fin sourceLayout.materialRegionCount :=
        ⟨region.val - 1 - sourceLayout.proxyCount, materialBound⟩
      have sourceEq : region = sourceLayout.materialRegion material := by
        apply Fin.ext
        simp only [FragmentLayout.materialRegion, material]
        omega
      rw [sourceEq,
        deiterationExtractRegionEquiv_materialRegion input selection witness]
      exact deiterationExtract_materialRegion_eq input selection witness material

theorem deiterationExtract_nodes_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin
      (deiterationRetainedExtract input selection witness).diagram.nodeCount) :
    ((deiterationRetainedExtract input selection witness).diagram.nodes
        index).rename
      (deiterationExtractRegionEquiv input selection witness) =
    (deiterationOriginalExtract input selection witness).diagram.nodes
      (deiterationExtractNodeEquiv input selection witness index) := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  let sourceLayout := deiterationRetainedLayout input selection witness
  let targetLayout := deiterationOriginalLayout input selection witness
  let targetIndex := Fin.cast
    (deiterationNodeLengthEq input selection witness) index
  let mappedNode := retained.selectedNodes.get index
  let originalNode := domains.nodes.origin mappedNode
  have originalGet : originalNode = witness.justifier.selectedNodes.get
      targetIndex :=
    deiterationRetained_selectedNode_get_origin input selection witness index
  have nodeSurvives := domains.nodes.origin_survives mappedNode
  have nodeIndex : domains.nodes.index originalNode nodeSurvives = mappedNode :=
    domains.nodes.index_origin mappedNode
  unfold deiterationRetainedExtract deiterationOriginalExtract
  simp only [ConcreteDiagram.extractOpenRaw]
  rw [deiterationExtractNodeEquiv_index input selection witness index]
  cases originalKind : input.val.nodes originalNode with
  | term region freePorts term =>
      have ownerSurvives : domains.regions.survives region = true := by
        have core := domains.nodeRegion_survives nodeSurvives
        rw [originalKind] at core
        exact core
      have removedKind := ConcreteDiagram.removeRaw_term input selection domains
        nodeSurvives originalKind
      rw [nodeIndex] at removedKind
      have targetKind : input.val.nodes
          (witness.justifier.selectedNodes.get targetIndex) =
            .term region freePorts term := by
        rw [← originalGet]
        exact originalKind
      rw [ConcreteDiagram.extractDiagramRaw_node_term _ retained sourceLayout
          index _ _ _ removedKind,
        ConcreteDiagram.extractDiagramRaw_node_term _ witness.justifier
          targetLayout targetIndex region freePorts term targetKind]
      simp only [CNode.rename]
      congr 1
      exact deiteration_fragmentParent_origin input selection witness
        (domains.regions.index region ownerSurvives) |>.trans (by
          rw [domains.regions.origin_index])
  | atom region binder =>
      have ownerSurvives : domains.regions.survives region = true := by
        have core := domains.nodeRegion_survives nodeSurvives
        rw [originalKind] at core
        exact core
      have binderSurvives := domains.atomBinder_survives input selection
        nodeSurvives originalKind
      have removedKind := ConcreteDiagram.removeRaw_atom input selection domains
        nodeSurvives originalKind
      rw [nodeIndex] at removedKind
      have targetKind : input.val.nodes
          (witness.justifier.selectedNodes.get targetIndex) =
            .atom region binder := by
        rw [← originalGet]
        exact originalKind
      rw [ConcreteDiagram.extractDiagramRaw_node_atom _ retained sourceLayout
          index _ _ removedKind,
        ConcreteDiagram.extractDiagramRaw_node_atom _ witness.justifier
          targetLayout targetIndex region binder targetKind]
      simp only [CNode.rename]
      congr 1
      · exact deiteration_fragmentParent_origin input selection witness
          (domains.regions.index region ownerSurvives) |>.trans (by
            rw [domains.regions.origin_index])
      · exact deiteration_fragmentBinder_origin input selection witness
          (domains.regions.index binder binderSurvives) |>.trans (by
            rw [domains.regions.origin_index])
  | named region definition arity =>
      have ownerSurvives : domains.regions.survives region = true := by
        have core := domains.nodeRegion_survives nodeSurvives
        rw [originalKind] at core
        exact core
      have removedKind := ConcreteDiagram.removeRaw_named input selection domains
        nodeSurvives originalKind
      rw [nodeIndex] at removedKind
      have targetKind : input.val.nodes
          (witness.justifier.selectedNodes.get targetIndex) =
            .named region definition arity := by
        rw [← originalGet]
        exact originalKind
      rw [ConcreteDiagram.extractDiagramRaw_node_named _ retained sourceLayout
          index _ _ _ removedKind,
        ConcreteDiagram.extractDiagramRaw_node_named _ witness.justifier
          targetLayout targetIndex region definition arity targetKind]
      simp only [CNode.rename]
      congr 1
      exact deiteration_fragmentParent_origin input selection witness
        (domains.regions.index region ownerSurvives) |>.trans (by
          rw [domains.regions.origin_index])

theorem deiterationExtract_internalWire_scope_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.internalWireCount)) :
    deiterationExtractRegionEquiv input selection witness
        ((deiterationRetainedExtract input selection witness).diagram.wires
          ((deiterationRetainedLayout input selection witness).internalWire
            index)).scope =
      ((deiterationOriginalExtract input selection witness).diagram.wires
        ((deiterationOriginalLayout input selection witness).internalWire
          (Fin.cast
            (deiterationInternalWireLengthEq input selection witness)
            index))).scope := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  let sourceLayout := deiterationRetainedLayout input selection witness
  let targetLayout := deiterationOriginalLayout input selection witness
  let targetIndex := Fin.cast
    (deiterationInternalWireLengthEq input selection witness) index
  let mappedWire := retained.internalWires.get index
  let originalWire := domains.wires.origin mappedWire
  have originalGet : originalWire = witness.justifier.internalWires.get
      targetIndex :=
    deiterationRetained_internalWire_get_origin input selection witness index
  have wireSurvives := domains.wires.origin_survives mappedWire
  unfold deiterationRetainedExtract deiterationOriginalExtract
  simp only [ConcreteDiagram.extractOpenRaw]
  rw [ConcreteDiagram.extractDiagramRaw_internalWire_scope_exact _ retained
      sourceLayout index,
    ConcreteDiagram.extractDiagramRaw_internalWire_scope_exact _ witness.justifier
      (deiterationOriginalLayout input selection witness)
      (Fin.cast (deiterationInternalWireLengthEq input selection witness) index),
    ConcreteDiagram.removeRaw_wire_scope]
  have wireGet := deiterationRetained_internalWire_get_origin input selection
    witness index
  calc
    deiterationExtractRegionEquiv input selection witness
        ((input.val.removeRaw selection domains).fragmentParent sourceLayout
          (domains.regions.index (input.val.wires originalWire).scope
            (domains.wireScope_survives wireSurvives))) =
      input.val.fragmentParent
        (deiterationOriginalLayout input selection witness)
        (domains.regions.origin
          (domains.regions.index (input.val.wires originalWire).scope
            (domains.wireScope_survives wireSurvives))) :=
      deiteration_fragmentParent_origin input selection witness _
    _ = input.val.fragmentParent
        (deiterationOriginalLayout input selection witness)
        (input.val.wires originalWire).scope := by
      rw [domains.regions.origin_index]
    _ = input.val.fragmentParent
        (deiterationOriginalLayout input selection witness)
        (input.val.wires (witness.justifier.internalWires.get
          (Fin.cast (deiterationInternalWireLengthEq input selection witness)
            index))).scope := congrArg
      (input.val.fragmentParent
        (deiterationOriginalLayout input selection witness))
      (congrArg (fun wire => (input.val.wires wire).scope) wireGet)

theorem deiterationExtract_boundaryWire_scope_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (index : Fin (deiterationRetainedLayout input selection witness
      |>.boundaryWireCount)) :
    deiterationExtractRegionEquiv input selection witness
        ((deiterationRetainedExtract input selection witness).diagram.wires
          ((deiterationRetainedLayout input selection witness).boundaryWire
            index)).scope =
      ((deiterationOriginalExtract input selection witness).diagram.wires
        ((deiterationOriginalLayout input selection witness).boundaryWire
          (Fin.cast
            (deiterationTouchingWireLengthEq input selection witness)
            index))).scope := by
  unfold deiterationRetainedExtract deiterationOriginalExtract
  simp only [ConcreteDiagram.extractOpenRaw]
  rw [ConcreteDiagram.extractDiagramRaw_boundaryWire_scope,
    ConcreteDiagram.extractDiagramRaw_boundaryWire_scope]
  exact deiterationExtractRegionEquiv_root input selection witness

theorem deiterationExtract_wire_scope_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationRetainedExtract input selection witness).diagram.wireCount) :
    deiterationExtractRegionEquiv input selection witness
        ((deiterationRetainedExtract input selection witness).diagram.wires
          wire).scope =
      ((deiterationOriginalExtract input selection witness).diagram.wires
        (deiterationExtractWireEquiv input selection witness wire)).scope := by
  let sourceLayout := deiterationRetainedLayout input selection witness
  by_cases internal : wire.val < sourceLayout.internalWireCount
  · let index : Fin sourceLayout.internalWireCount := ⟨wire.val, internal⟩
    have sourceEq : wire = sourceLayout.internalWire index := by
      apply Fin.ext
      rfl
    rw [sourceEq,
      deiterationExtractWireEquiv_internalWire input selection witness]
    exact deiterationExtract_internalWire_scope_eq input selection witness index
  · have boundaryBound : wire.val - sourceLayout.internalWireCount <
        sourceLayout.boundaryWireCount := by
      have wireBound := wire.isLt
      change wire.val < sourceLayout.wireCount at wireBound
      unfold FragmentLayout.wireCount at wireBound
      omega
    let index : Fin sourceLayout.boundaryWireCount :=
      ⟨wire.val - sourceLayout.internalWireCount, boundaryBound⟩
    have sourceEq : wire = sourceLayout.boundaryWire index := by
      apply Fin.ext
      simp only [FragmentLayout.boundaryWire_val, index]
      omega
    rw [sourceEq,
      deiterationExtractWireEquiv_boundaryWire input selection witness]
    exact deiterationExtract_boundaryWire_scope_eq input selection witness index

theorem deiterationExtract_wireOrigin_origin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationRetainedExtract input selection witness).diagram.wireCount) :
    (deiterationDomains input selection).wires.origin
        (ConcreteDiagram.fragmentWireOrigin
          (deiterationRetainedSelection input selection witness)
          (deiterationRetainedLayout input selection witness) wire) =
      ConcreteDiagram.fragmentWireOrigin witness.justifier
        (deiterationOriginalLayout input selection witness)
        (deiterationExtractWireEquiv input selection witness wire) := by
  let sourceLayout := deiterationRetainedLayout input selection witness
  by_cases internal : wire.val < sourceLayout.internalWireCount
  · let index : Fin sourceLayout.internalWireCount := ⟨wire.val, internal⟩
    have sourceEq : wire = sourceLayout.internalWire index := by
      apply Fin.ext
      rfl
    rw [sourceEq,
      deiterationExtractWireEquiv_internalWire input selection witness]
    dsimp only [sourceLayout]
    simpa [ConcreteDiagram.fragmentWireOrigin,
      FragmentLayout.internalWire] using
        deiterationRetained_internalWire_get_origin input selection witness index
  · have boundaryBound : wire.val - sourceLayout.internalWireCount <
        sourceLayout.boundaryWireCount := by
      have wireBound := wire.isLt
      change wire.val < sourceLayout.wireCount at wireBound
      unfold FragmentLayout.wireCount at wireBound
      omega
    let index : Fin sourceLayout.boundaryWireCount :=
      ⟨wire.val - sourceLayout.internalWireCount, boundaryBound⟩
    have sourceEq : wire = sourceLayout.boundaryWire index := by
      apply Fin.ext
      simp only [FragmentLayout.boundaryWire_val, index]
      omega
    rw [sourceEq,
      deiterationExtractWireEquiv_boundaryWire input selection witness]
    dsimp only [sourceLayout]
    simpa [ConcreteDiagram.fragmentWireOrigin,
      FragmentLayout.boundaryWire] using
        deiterationRetained_touchingWire_get_origin input selection witness index

theorem deiterationExtract_endpoint_mem_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationRetainedExtract input selection witness).diagram.wireCount)
    (endpoint : CEndpoint
      (deiterationOriginalExtract input selection witness).diagram.nodeCount) :
    endpoint ∈
        ((deiterationRetainedExtract input selection witness).diagram.wires
          wire).endpoints.map
            (CEndpoint.rename
              (deiterationExtractNodeEquiv input selection witness)) ↔
      endpoint ∈
        ((deiterationOriginalExtract input selection witness).diagram.wires
          (deiterationExtractWireEquiv input selection witness wire)).endpoints := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  let sourceLayout := deiterationRetainedLayout input selection witness
  let targetLayout := deiterationOriginalLayout input selection witness
  let sourceWire := ConcreteDiagram.fragmentWireOrigin retained sourceLayout wire
  let targetWire := ConcreteDiagram.fragmentWireOrigin witness.justifier
    targetLayout (deiterationExtractWireEquiv input selection witness wire)
  have wireOrigin : domains.wires.origin sourceWire = targetWire :=
    deiterationExtract_wireOrigin_origin input selection witness wire
  constructor
  · intro member
    obtain ⟨sourceEndpoint, sourceMember, renamed⟩ := List.mem_map.mp member
    obtain ⟨mappedOriginal, mappedMember, sourceFragment⟩ :=
      (ConcreteDiagram.mem_extractDiagramRaw_wire_endpoints_iff
        (input.val.removeRaw selection domains) retained sourceLayout wire
        sourceEndpoint).1 sourceMember
    obtain ⟨original, originalMember, reindexed⟩ :=
      (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff input selection domains
        sourceWire mappedOriginal).1 mappedMember
    apply (ConcreteDiagram.mem_extractDiagramRaw_wire_endpoints_iff input.val
      witness.justifier targetLayout
      (deiterationExtractWireEquiv input selection witness wire) endpoint).2
    refine ⟨original, ?_, ?_⟩
    · change original ∈ (input.val.wires targetWire).endpoints
      rw [← wireOrigin]
      exact originalMember
    · have mappedOrigin := ConcreteDiagram.fragmentEndpoint?_origin retained
        sourceFragment
      have originalOrigin := ConcreteDiagram.reindexEndpoint?_origin domains
        reindexed
      have selectedGet := deiterationRetained_selectedNode_get_origin input
        selection witness sourceEndpoint.node
      have originalEq : original = {
          node := witness.justifier.selectedNodes.get
            (deiterationExtractNodeEquiv input selection witness
              sourceEndpoint.node)
          port := sourceEndpoint.port
        } := by
        rw [originalOrigin, mappedOrigin]
        cases sourceEndpoint
        simp only [CEndpoint.node, CEndpoint.port,
          deiterationExtractNodeEquiv_index]
        rw [selectedGet]
      rw [originalEq]
      have canonical := ConcreteDiagram.fragmentEndpoint_selectedNode
        witness.justifier
        (deiterationExtractNodeEquiv input selection witness
          sourceEndpoint.node) sourceEndpoint.port
      exact canonical.trans (congrArg some renamed)
  · intro member
    obtain ⟨original, originalMember, targetFragment⟩ :=
      (ConcreteDiagram.mem_extractDiagramRaw_wire_endpoints_iff input.val
        witness.justifier targetLayout
        (deiterationExtractWireEquiv input selection witness wire) endpoint).1
        member
    have originalOrigin := ConcreteDiagram.fragmentEndpoint?_origin
      witness.justifier targetFragment
    let sourceNode : Fin retained.selectedNodes.length :=
      (deiterationExtractNodeEquiv input selection witness).symm endpoint.node
    let mappedEndpoint : CEndpoint domains.nodes.count := {
      node := retained.selectedNodes.get sourceNode
      port := endpoint.port
    }
    have selectedGet := deiterationRetained_selectedNode_get_origin input
      selection witness sourceNode
    have targetNodeEq :
        Fin.cast (deiterationNodeLengthEq input selection witness) sourceNode =
          endpoint.node :=
      (deiterationExtractNodeEquiv input selection witness).apply_symm_apply
        endpoint.node
    have originalEq : original = {
        node := domains.nodes.origin mappedEndpoint.node
        port := mappedEndpoint.port
      } := by
      rw [originalOrigin]
      cases endpoint
      simp only [CEndpoint.node, CEndpoint.port, mappedEndpoint]
      rw [selectedGet, targetNodeEq]
    have mappedNodeSurvives := domains.nodes.origin_survives mappedEndpoint.node
    have reindexed : domains.nodes.reindexEndpoint? original =
        some mappedEndpoint := by
      rw [originalEq]
      unfold SurvivorDomain.reindexEndpoint?
      rw [domains.nodes.index?_origin]
      rfl
    have removedMember : mappedEndpoint ∈
        ((input.val.removeRaw selection domains).wires sourceWire).endpoints := by
      apply (ConcreteDiagram.mem_removeRaw_wire_endpoints_iff input selection
        domains sourceWire mappedEndpoint).2
      refine ⟨original, ?_, reindexed⟩
      rw [wireOrigin]
      exact originalMember
    let sourceEndpoint : CEndpoint retained.selectedNodes.length := {
      node := sourceNode
      port := endpoint.port
    }
    have sourceFragment := ConcreteDiagram.fragmentEndpoint_selectedNode
      retained sourceNode endpoint.port
    have sourceMember : sourceEndpoint ∈
        ((deiterationRetainedExtract input selection witness).diagram.wires
          wire).endpoints := by
      apply (ConcreteDiagram.mem_extractDiagramRaw_wire_endpoints_iff
        (input.val.removeRaw selection domains) retained sourceLayout wire
        sourceEndpoint).2
      exact ⟨mappedEndpoint, removedMember, sourceFragment⟩
    apply List.mem_map.mpr
    refine ⟨sourceEndpoint, sourceMember, ?_⟩
    cases endpoint
    dsimp only [sourceEndpoint]
    unfold CEndpoint.rename
    congr

private theorem perm_of_nodup_and_mem_iff
    {values other : List α} [BEq α] [LawfulBEq α]
    (valuesNodup : values.Nodup) (otherNodup : other.Nodup)
    (members : ∀ value, value ∈ values ↔ value ∈ other) :
    values.Perm other := by
  rw [List.perm_iff_count]
  intro value
  rw [valuesNodup.count, otherNodup.count]
  by_cases member : value ∈ values
  · have otherMember : value ∈ other := (members value).1 member
    simp [member, otherMember]
  · have otherNotMember : value ∉ other :=
      fun present => member ((members value).2 present)
    simp [member, otherNotMember]

theorem deiterationExtract_wire_endpoints_perm
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationRetainedExtract input selection witness).diagram.wireCount) :
    (((deiterationRetainedExtract input selection witness).diagram.wires
        wire).endpoints.map
          (CEndpoint.rename
            (deiterationExtractNodeEquiv input selection witness))).Perm
      ((deiterationOriginalExtract input selection witness).diagram.wires
        (deiterationExtractWireEquiv input selection witness wire)).endpoints := by
  let domains := deiterationDomains input selection
  let removed : CheckedDiagram signature :=
    ⟨input.val.removeRaw selection domains,
      ConcreteDiagram.removeRaw_wellFormed input selection domains⟩
  have sourceNodup :
      ((deiterationRetainedExtract input selection witness).diagram.wires
        wire).endpoints.Nodup := by
    exact ConcreteDiagram.extractDiagramRaw_endpoints_are_nodup removed
      (deiterationRetainedSelection input selection witness)
      (deiterationRetainedLayout input selection witness) wire
  have mappedNodup :
      (((deiterationRetainedExtract input selection witness).diagram.wires
        wire).endpoints.map
          (CEndpoint.rename
            (deiterationExtractNodeEquiv input selection witness))).Nodup :=
    sourceNodup.map _ (fun first second distinct equality =>
      distinct (CEndpoint.rename_injective
        (deiterationExtractNodeEquiv input selection witness) equality))
  have targetNodup :
      ((deiterationOriginalExtract input selection witness).diagram.wires
        (deiterationExtractWireEquiv input selection witness wire)).endpoints.Nodup :=
    ConcreteDiagram.extractDiagramRaw_endpoints_are_nodup input
      witness.justifier (deiterationOriginalLayout input selection witness)
      (deiterationExtractWireEquiv input selection witness wire)
  exact perm_of_nodup_and_mem_iff mappedNodup targetNodup
    (deiterationExtract_endpoint_mem_iff input selection witness wire)

theorem deiterationExtract_boundary_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationRetainedExtract input selection witness).boundary.map
        (deiterationExtractWireEquiv input selection witness) =
      (deiterationOriginalExtract input selection witness).boundary := by
  unfold deiterationRetainedExtract deiterationOriginalExtract
  simp only [ConcreteDiagram.extractOpenRaw,
    ConcreteDiagram.extractBoundaryRaw, List.map_ofFn]
  apply List.ext_get
  · simpa [FragmentLayout.boundaryWireCount] using
      deiterationTouchingWireLengthEq input selection witness
  · intro position sourceBound targetBound
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact deiterationExtractWireEquiv_boundaryWire input selection witness
      ⟨position, by
        change position <
          (deiterationRetainedLayout input selection witness
            |>.boundaryWireCount)
        simpa using sourceBound⟩

def deiterationExtractOccurrenceEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    OpenOccurrenceEquiv
      (deiterationRetainedExtract input selection witness)
      (deiterationOriginalExtract input selection witness) where
  diagram := {
    regionCount_eq := deiterationExtractRegionCountEq input selection witness
    nodeCount_eq := deiterationExtractNodeCountEq input selection witness
    wireCount_eq := deiterationExtractWireCountEq input selection witness
    regions := deiterationExtractRegionEquiv input selection witness
    nodes := deiterationExtractNodeEquiv input selection witness
    wires := deiterationExtractWireEquiv input selection witness
    root_eq := deiterationExtractRegionEquiv_root input selection witness
    regions_eq := deiterationExtract_regions_eq input selection witness
    nodes_correspond := fun node => CNode.CertifiedCorresponds.ofRenameEq
      (deiterationExtractRegionEquiv input selection witness)
      (deiterationExtract_nodes_eq input selection witness node)
    wire_scope_eq := deiterationExtract_wire_scope_eq input selection witness
    wire_endpoints_perm :=
      deiterationExtract_wire_endpoints_perm input selection witness
  }
  boundary := deiterationExtract_boundary_eq input selection witness

private theorem selectedFragment_eq_extractOpenRaw
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection) :
    selectedFragment input selection =
      input.val.extractOpenRaw selection layout := by
  have pinned := pinnedSelectedFragment_eq_extractOpenRaw input selection
    selection.touchingWires.length (fun index => index) layout
  change pinnedSelectedFragment input selection selection.touchingWires.length
      (fun index => index) = input.val.extractOpenRaw selection layout
  exact pinned

theorem deiterationRetained_selectedFragment_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    selectedFragment
        ⟨input.val.removeRaw selection (deiterationDomains input selection),
          ConcreteDiagram.removeRaw_wellFormed input selection
            (deiterationDomains input selection)⟩
        (deiterationRetainedSelection input selection witness) =
      deiterationRetainedExtract input selection witness := by
  exact selectedFragment_eq_extractOpenRaw
    (input :=
      ⟨input.val.removeRaw selection (deiterationDomains input selection),
        ConcreteDiagram.removeRaw_wellFormed input selection
          (deiterationDomains input selection)⟩)
    (selection := deiterationRetainedSelection input selection witness)
    (layout := deiterationRetainedLayout input selection witness)

theorem deiterationOriginal_selectedFragment_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    selectedFragment input witness.justifier =
      deiterationOriginalExtract input selection witness := by
  exact selectedFragment_eq_extractOpenRaw input witness.justifier
    (deiterationOriginalLayout input selection witness)

def deiterationRetainedOccurrenceEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    OpenOccurrenceEquiv
      (selectedFragment
        ⟨input.val.removeRaw selection (deiterationDomains input selection),
          ConcreteDiagram.removeRaw_wellFormed input selection
            (deiterationDomains input selection)⟩
        (deiterationRetainedSelection input selection witness))
      (selectedFragment input witness.justifier) := by
  rw [deiterationRetained_selectedFragment_eq input selection witness,
    deiterationOriginal_selectedFragment_eq input selection witness]
  exact deiterationExtractOccurrenceEquiv input selection witness

end VisualProof.Rule.IterationSoundness
