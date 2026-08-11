import VisualProof.Concrete.Elaboration.SpliceRouteFuel
import VisualProof.Concrete.Elaboration.SpliceSiteComputation

/-! Source-derived ancestor compiler alignment for splice elaboration. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private theorem finCast_val {source target : Nat}
    (equality : source = target) (index : Fin source) :
    (FiniteEquiv.finCast equality index).val = index.val := rfl

private theorem mapFrameBinders_empty
    (layout : PlugLayout input) :
    layout.mapFrameBinders
        (BinderContext.empty : BinderContext input.frame.val []) =
      (BinderContext.empty : BinderContext layout.plugRaw []) := by
  funext region
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) region <;>
    simp [mapFrameBinders, BinderContext.empty, PlugLayout.plugRaw,
      PlugLayout.regionCount]

/-- Embedding a source binder context preserves coverage at every retained
frame region. -/
theorem mapFrameBinders_covers_frameRegion
    (layout : PlugLayout input)
    {binders : BinderContext input.frame.val rels}
    (region : Fin input.frame.val.regionCount)
    (sourceCovers : binders.Covers region) :
    (layout.mapFrameBinders binders).Covers
      (layout.frameRegion region) := by
  intro targetBinder targetParent arity targetBubble targetEncloses
  refine Fin.addCases (motive := fun candidate => targetBinder = candidate →
      ∃ relation : RelVar rels arity,
        layout.mapFrameBinders binders targetBinder =
          some ⟨arity, relation⟩)
    (fun frame binderEq => ?_) (fun material binderEq => ?_) targetBinder rfl
  · subst targetBinder
    change layout.plugRaw.regions (layout.frameRegion frame) =
      .bubble targetParent arity at targetBubble
    change layout.plugRaw.Encloses (layout.frameRegion frame)
      (layout.frameRegion region) at targetEncloses
    rw [layout.plugRegion_frameRegion] at targetBubble
    cases sourceRegionEq : input.frame.val.regions frame with
    | sheet => rw [sourceRegionEq] at targetBubble; cases targetBubble
    | cut sourceParent => rw [sourceRegionEq] at targetBubble; cases targetBubble
    | bubble sourceParent sourceArity =>
        rw [sourceRegionEq] at targetBubble
        have arityEq : sourceArity = arity :=
          (CRegion.bubble.inj targetBubble).2
        subst sourceArity
        have sourceEncloses : input.frame.val.Encloses frame region :=
          (layout.encloses_frameRegion_iff
            input.frame.property frame region).1 targetEncloses
        obtain ⟨relation, sourceLookup⟩ := sourceCovers frame sourceParent
          arity sourceRegionEq sourceEncloses
        exact ⟨relation, by
          change layout.mapFrameBinders binders (layout.frameRegion frame) =
            some ⟨arity, relation⟩
          simpa only [layout.mapFrameBinders_frameRegion] using sourceLookup⟩
  · subst targetBinder
    change layout.plugRaw.Encloses (layout.materialRegion material)
      (layout.frameRegion region) at targetEncloses
    exact (layout.materialRegion_not_encloses_frameRegion material region
      targetEncloses).elim

/-- The canonical position equivalence on the inherited-plus-local compiler
context of a retained frame region away from the splice site. -/
noncomputable def frameExtendedContextEquiv
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount) (away : region ≠ input.site) :
    FiniteEquiv (Fin (context.extend region).length)
      (Fin ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion region)).length) :=
  FiniteEquiv.finCast (by
    rw [WireContext.length_extend, WireContext.length_extend,
      layout.exactScopeWires_frameRegion_length_of_ne consistent terminal
        region away]
    simp [mapFrameContext])

@[simp] theorem frameExtendedContextEquiv_val
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount) (away : region ≠ input.site)
    (index : Fin (context.extend region).length) :
    (layout.frameExtendedContextEquiv consistent terminal context region away
      index).val = index.val := rfl

/-- The canonical extended position equivalence retrieves the corresponding
embedded frame wire at every inherited and local position. -/
theorem frameExtendedContextEquiv_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount) (away : region ≠ input.site)
    (index : Fin (context.extend region).length) :
    ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion region)).get
          (layout.frameExtendedContextEquiv consistent terminal context
            region away index) =
      layout.frameWireEmbedding consistent
        ((context.extend region).get index) := by
  have mapped := layout.extendFrameContextIndexMap_get consistent terminal
    context (layout.mapFrameContext consistent context)
    (layout.mapFrameContextEquiv consistent context)
    (layout.mapFrameContext_get consistent context) region away index
  have positions :
      layout.extendFrameContextIndexMap consistent terminal context
          (layout.mapFrameContext consistent context)
          (layout.mapFrameContextEquiv consistent context) region away index =
        layout.frameExtendedContextEquiv consistent terminal context region
          away index := by
    apply Fin.ext
    let split : Fin
        (context.length + (exactScopeWires input.frame.val region).length) :=
      Fin.cast (WireContext.length_extend context region) index
    have splitEq :
        Fin.cast (WireContext.length_extend context region).symm split =
          index := by
      apply Fin.ext
      rfl
    rw [← splitEq]
    refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
    · simp [extendFrameContextIndexMap, extendWireRenaming,
        frameExtendedContextEquiv, mapFrameContextEquiv, mapFrameContext,
        finCast_val]
    · simp [extendFrameContextIndexMap, extendWireRenaming,
        frameExtendedContextEquiv, mapFrameContextEquiv, mapFrameContext,
        finCast_val]
  rw [← positions]
  exact mapped

/-- The normalized outer/local compiler equivalence is definitionally the
same stable position map as `frameExtendedContextEquiv`. -/
theorem extendWireEquiv_frameContext_eq
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount) (away : region ≠ input.site) :
    extendWireEquiv
        (layout.mapFrameContextEquiv consistent context)
        (FiniteEquiv.finCast
          (layout.exactScopeWires_frameRegion_length_of_ne consistent terminal
            region away).symm) =
      castFinEquiv
        (WireContext.length_extend context region).symm
        (WireContext.length_extend
          (layout.mapFrameContext consistent context)
          (layout.frameRegion region)).symm
        (layout.frameExtendedContextEquiv consistent terminal context region
          away) := by
  apply FiniteEquiv.ext
  intro index
  apply Fin.ext
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_)
    index
  · simp [castFinEquiv, frameExtendedContextEquiv, extendWireEquiv,
      mapFrameContextEquiv, mapFrameContext, finCast_val]
  · simp [castFinEquiv, frameExtendedContextEquiv, extendWireEquiv,
      mapFrameContextEquiv, mapFrameContext, finCast_val]

private theorem get_finCast_of_eq_map
    {source target : Type} (embedding : source → target)
    (sourceItems : List source) (targetItems : List target)
    (mapped : targetItems = sourceItems.map embedding)
    (lengthEq : sourceItems.length = targetItems.length)
    (index : Fin sourceItems.length) :
    targetItems.get (FiniteEquiv.finCast lengthEq index) =
      embedding (sourceItems.get index) := by
  subst targetItems
  simp only [List.get_eq_getElem, List.getElem_map, finCast_val]

private theorem openRootWires_length (openRoot : OpenDiagram) :
    openRoot.rootWires.length =
      openRoot.exposedWires.length + openRoot.hiddenWires.length := by
  unfold OpenDiagram.rootWires
  exact List.length_append

/-- Boundary-class positions of the generated open root are the stable
source positions, transported in their existing order. -/
noncomputable def outputExternalEquiv
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount)) :
    FiniteEquiv
      (Fin (frameOpen input boundary).exposedWires.length)
      (Fin (layout.outputOpenRoot input boundary).exposedWires.length) :=
  FiniteEquiv.finCast (by
    rw [layout.outputOpenRoot_exposedWires consistent boundary]
    exact (List.length_map _).symm)

@[simp] theorem outputExternalEquiv_val
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (index : Fin (frameOpen input boundary).exposedWires.length) :
    (layout.outputExternalEquiv consistent boundary index).val = index.val := rfl

/-- The generated exposed-class list retrieves the embedded source class at
the same dense source position. -/
theorem outputExternalEquiv_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (index : Fin (frameOpen input boundary).exposedWires.length) :
    (layout.outputOpenRoot input boundary).exposedWires.get
        (layout.outputExternalEquiv consistent boundary index) =
      layout.frameWireEmbedding consistent
        ((frameOpen input boundary).exposedWires.get index) := by
  unfold outputExternalEquiv
  apply get_finCast_of_eq_map
  exact layout.outputOpenRoot_exposedWires consistent boundary

/-- Ordered boundary positions commute with the source-derived exposed-class
equivalence. -/
theorem outputExternalEquiv_boundaryClass
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (position : Fin (frameOpen input boundary).boundary.length) :
    layout.outputExternalEquiv consistent boundary
        ((frameOpen input boundary).boundaryClass position) =
      (layout.outputOpenRoot input boundary).boundaryClass
        (Fin.cast (by
          simp [frameOpen, PlugLayout.outputOpenRoot]) position) := by
  apply OpenDiagram.boundaryClass_complete
  rw [layout.outputExternalEquiv_get,
    OpenDiagram.boundaryClass_sound]
  simp [frameOpen, PlugLayout.outputOpenRoot, frameWireEmbedding_apply]

/-- Away from a root insertion, the generated hidden block is the stable
source hidden block in the same order. -/
noncomputable def outputHiddenEquiv_of_ne
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site) :
    FiniteEquiv
      (Fin (frameOpen input boundary).hiddenWires.length)
      (Fin (layout.outputOpenRoot input boundary).hiddenWires.length) :=
  FiniteEquiv.finCast (by
    rw [layout.outputOpenRoot_hiddenWires consistent terminal boundary,
      if_neg away, List.append_nil]
    exact (List.length_map _).symm)

@[simp] theorem outputHiddenEquiv_of_ne_val
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site)
    (index : Fin (frameOpen input boundary).hiddenWires.length) :
    (layout.outputHiddenEquiv_of_ne consistent terminal boundary away
      index).val = index.val := rfl

/-- The combined exposed/hidden map preserves every dense source position. -/
theorem outputRootSplitEquiv_of_ne_val
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site)
    (index : Fin
      ((frameOpen input boundary).exposedWires.length +
        (frameOpen input boundary).hiddenWires.length)) :
    (extendWireEquiv
      (layout.outputExternalEquiv consistent boundary)
      (layout.outputHiddenEquiv_of_ne consistent terminal boundary away)
      index).val = index.val := by
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) index
  · simp only [extendWireEquiv_outer, Fin.val_castAdd,
      outputExternalEquiv_val]
  · simp only [extendWireEquiv_local, Fin.val_natAdd,
      outputHiddenEquiv_of_ne_val]
    rw [layout.outputOpenRoot_exposedWires consistent boundary]
    exact congrArg (fun length => length + hidden.val)
      (List.length_map _)

/-- Complete root compiler positions are transported from the exact source
open-root partition without selecting a target presentation. -/
noncomputable def outputRootContextEquiv_of_ne
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site) :
    FiniteEquiv
      (Fin (frameOpen input boundary).rootWires.length)
      (Fin (layout.outputOpenRoot input boundary).rootWires.length) :=
  FiniteEquiv.finCast (by
    rw [layout.outputOpenRoot_rootWires consistent terminal boundary,
      if_neg away, List.append_nil]
    exact (List.length_map _).symm)

@[simp] theorem outputRootContextEquiv_of_ne_val
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site)
    (index : Fin (frameOpen input boundary).rootWires.length) :
    (layout.outputRootContextEquiv_of_ne consistent terminal boundary away
      index).val = index.val := rfl

/-- The complete generated root context retrieves the embedded source root
wire at every stable compiler position. -/
theorem outputRootContextEquiv_of_ne_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site)
    (index : Fin (frameOpen input boundary).rootWires.length) :
    (layout.outputOpenRoot input boundary).rootWires.get
        (layout.outputRootContextEquiv_of_ne consistent terminal boundary away
          index) =
      layout.frameWireEmbedding consistent
        ((frameOpen input boundary).rootWires.get index) := by
  unfold outputRootContextEquiv_of_ne
  apply get_finCast_of_eq_map
  simpa only [if_neg away, List.append_nil] using
    layout.outputOpenRoot_rootWires consistent terminal boundary

/-- The root compiler equivalence is exactly the concatenation of the
source-derived exposed and hidden position maps, modulo `rootWires` lengths. -/
theorem outputRootContextEquiv_of_ne_eq
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site) :
    layout.outputRootContextEquiv_of_ne consistent terminal boundary away =
      castFinEquiv
        (by simp [OpenDiagram.rootWires])
        (by simp [OpenDiagram.rootWires])
        (extendWireEquiv
          (layout.outputExternalEquiv consistent boundary)
          (layout.outputHiddenEquiv_of_ne consistent terminal boundary
            away)) := by
  apply FiniteEquiv.ext
  intro index
  apply Fin.ext
  change index.val =
    (extendWireEquiv
      (layout.outputExternalEquiv consistent boundary)
      (layout.outputHiddenEquiv_of_ne consistent terminal boundary away)
      (Fin.cast (by simp [OpenDiagram.rootWires]) index)).val
  rw [layout.outputRootSplitEquiv_of_ne_val consistent terminal boundary away]
  rfl

/-- A source compiler route and its deterministically mapped target route
reconstruct aligned one-hole abstract contexts.  This record is neutral in
the region isomorphism eventually placed in the hole. -/
structure CompilerRouteAlignment
    {sourceOuter targetOuter sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole))
    (sourceRoot : Region sourceOuter outerRels)
    (targetRoot : Region targetOuter outerRels)
    (sourceSite : Region sourceHole holeRels)
    (targetSite : Region targetHole holeRels) where
  sourceContext : DiagramContext sourceOuter sourceHole outerRels holeRels
  targetContext : DiagramContext targetOuter targetHole outerRels holeRels
  contextIso : DiagramContextIso outerWire holeWire outerRels holeRels
    sourceContext targetContext
  source_rebuild : sourceContext.fill sourceSite = sourceRoot
  target_rebuild : targetContext.fill targetSite = targetRoot

/-- Fill a source-derived route alignment with the local site isomorphism. -/
noncomputable def CompilerRouteAlignment.fill
    {sourceOuter targetOuter sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    {sourceRoot : Region sourceOuter outerRels}
    {targetRoot : Region targetOuter outerRels}
    {sourceSite sourceAfter : Region sourceHole holeRels}
    {targetSite : Region targetHole holeRels}
    (alignment : CompilerRouteAlignment outerWire holeWire
      sourceRoot targetRoot sourceSite targetSite)
    (site : RegionIso holeWire holeRels sourceAfter targetSite) :
    RegionIso outerWire outerRels
      (alignment.sourceContext.fill sourceAfter) targetRoot := by
  exact DiagramContextIso.root alignment.contextIso site rfl
    alignment.target_rebuild

private noncomputable def CompilerRouteAlignment.castSourceSite
    {sourceOuter targetOuter sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    {sourceRoot : Region sourceOuter outerRels}
    {targetRoot : Region targetOuter outerRels}
    {sourceSite normalizedSourceSite : Region sourceHole holeRels}
    {targetSite : Region targetHole holeRels}
    (alignment : CompilerRouteAlignment outerWire holeWire sourceRoot
      targetRoot sourceSite targetSite)
    (sourceSiteEq : sourceSite = normalizedSourceSite) :
    CompilerRouteAlignment outerWire holeWire sourceRoot targetRoot
      normalizedSourceSite targetSite := by
  subst normalizedSourceSite
  exact alignment

private theorem CompilerRouteAlignment.castSourceSite_sourceContext
    {sourceOuter targetOuter sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    {sourceRoot : Region sourceOuter outerRels}
    {targetRoot : Region targetOuter outerRels}
    {sourceSite normalizedSourceSite : Region sourceHole holeRels}
    {targetSite : Region targetHole holeRels}
    (alignment : CompilerRouteAlignment outerWire holeWire sourceRoot
      targetRoot sourceSite targetSite)
    (sourceSiteEq : sourceSite = normalizedSourceSite) :
    (alignment.castSourceSite sourceSiteEq).sourceContext =
      alignment.sourceContext := by
  subst normalizedSourceSite
  rfl

/-- Add one cut compiler frame around a recursively aligned child.  Both
focuses are computed at the already related item positions. -/
private noncomputable def CompilerRouteAlignment.cutFrame
    {sourceOuter targetOuter sourceLocal targetLocal sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) outerRels}
    {targetItems : ItemSeq (targetOuter + targetLocal) outerRels}
    {sourceIndex : Fin sourceItems.length}
    {targetIndex : Fin targetItems.length}
    (frame : ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex)
    {sourceChild : Region (sourceOuter + sourceLocal) outerRels}
    {targetChild : Region (targetOuter + targetLocal) outerRels}
    (sourceItem : sourceItems.get sourceIndex = .cut sourceChild)
    (targetItem : targetItems.get targetIndex = .cut targetChild)
    {sourceSite : Region sourceHole holeRels}
    {targetSite : Region targetHole holeRels}
    (child : CompilerRouteAlignment (extendWireEquiv outerWire localWire)
      holeWire sourceChild targetChild sourceSite targetSite) :
    CompilerRouteAlignment outerWire holeWire
      (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)
      sourceSite targetSite := by
  let sourceFocused := sourceItems.focusAt sourceIndex
  let targetFocused := targetItems.focusAt targetIndex
  refine {
    sourceContext := .cut sourceLocal sourceFocused.focus.before
      sourceFocused.focus.after child.sourceContext
    targetContext := .cut targetLocal targetFocused.focus.before
      targetFocused.focus.after child.targetContext
    contextIso := DiagramContextIso.cutFrame localWire sourceFocused.focus
      targetFocused.focus sourceFocused.atIndex targetFocused.atIndex frame
      child.sourceContext child.targetContext child.contextIso
    source_rebuild := ?_
    target_rebuild := ?_
  }
  · simp only [DiagramContext.fill]
    rw [child.source_rebuild, ← sourceItem, ← sourceFocused.item_eq,
      sourceFocused.focus.rebuild]
  · simp only [DiagramContext.fill]
    rw [child.target_rebuild, ← targetItem, ← targetFocused.item_eq,
      targetFocused.focus.rebuild]

/-- Bubble counterpart of `CompilerRouteAlignment.cutFrame`. -/
private noncomputable def CompilerRouteAlignment.bubbleFrame
    {sourceOuter targetOuter sourceLocal targetLocal sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) outerRels}
    {targetItems : ItemSeq (targetOuter + targetLocal) outerRels}
    {sourceIndex : Fin sourceItems.length}
    {targetIndex : Fin targetItems.length}
    (frame : ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex)
    {sourceChild : Region (sourceOuter + sourceLocal) (arity :: outerRels)}
    {targetChild : Region (targetOuter + targetLocal) (arity :: outerRels)}
    (sourceItem : sourceItems.get sourceIndex =
      .bubble arity sourceChild)
    (targetItem : targetItems.get targetIndex =
      .bubble arity targetChild)
    {sourceSite : Region sourceHole holeRels}
    {targetSite : Region targetHole holeRels}
    (child : CompilerRouteAlignment (extendWireEquiv outerWire localWire)
      holeWire sourceChild targetChild sourceSite targetSite) :
    CompilerRouteAlignment outerWire holeWire
      (.mk sourceLocal sourceItems) (.mk targetLocal targetItems)
      sourceSite targetSite := by
  let sourceFocused := sourceItems.focusAt sourceIndex
  let targetFocused := targetItems.focusAt targetIndex
  refine {
    sourceContext := .bubble sourceLocal sourceFocused.focus.before
      sourceFocused.focus.after arity child.sourceContext
    targetContext := .bubble targetLocal targetFocused.focus.before
      targetFocused.focus.after arity child.targetContext
    contextIso := DiagramContextIso.bubbleFrame localWire sourceFocused.focus
      targetFocused.focus sourceFocused.atIndex targetFocused.atIndex frame
      child.sourceContext child.targetContext child.contextIso
    source_rebuild := ?_
    target_rebuild := ?_
  }
  · simp only [DiagramContext.fill]
    rw [child.source_rebuild, ← sourceItem, ← sourceFocused.item_eq,
      sourceFocused.focus.rebuild]
  · simp only [DiagramContext.fill]
    rw [child.target_rebuild, ← targetItem, ← targetFocused.item_eq,
      targetFocused.focus.rebuild]

/-- The source occurrence position of a specified direct child.  This is the
only occurrence lookup used by the ancestor lift, and it is performed in the
already compiled source frame. -/
noncomputable def sourceChildOccurrenceIndex
    (diagram : Concrete.Diagram) (region child : Fin diagram.regionCount)
    (parent : (diagram.regions child).parent? = some region) :
    Fin (localOccurrences diagram region).length :=
  Classical.choose (indexOf?_complete
    ((mem_localOccurrences_child diagram region child).2 parent))

/-- The source-selected occurrence position denotes the requested child. -/
theorem sourceChildOccurrenceIndex_get
    (diagram : Concrete.Diagram) (region child : Fin diagram.regionCount)
    (parent : (diagram.regions child).parent? = some region) :
    (localOccurrences diagram region).get
        (sourceChildOccurrenceIndex diagram region child parent) =
      .child child :=
  indexOf?_sound (Classical.choose_spec (indexOf?_complete
    ((mem_localOccurrences_child diagram region child).2 parent)))

/-- The retained source position is the successful source `indexOf?` result. -/
theorem sourceChildOccurrenceIndex_found
    (diagram : Concrete.Diagram) (region child : Fin diagram.regionCount)
    (parent : (diagram.regions child).parent? = some region) :
    indexOf? (localOccurrences diagram region) (.child child) =
      some (sourceChildOccurrenceIndex diagram region child parent) :=
  Classical.choose_spec (indexOf?_complete
    ((mem_localOccurrences_child diagram region child).2 parent))

/-- An intrinsic source path index denoting the selected direct child is the
same index used by the canonical source-only occurrence lookup. -/
theorem sourceChildOccurrenceIndex_eq
    (diagram : Concrete.Diagram) (region child : Fin diagram.regionCount)
    (parent : (diagram.regions child).parent? = some region)
    (index : Fin (localOccurrences diagram region).length)
    (occurrence : (localOccurrences diagram region).get index =
      .child child) :
    sourceChildOccurrenceIndex diagram region child parent = index := by
  exact (indexOf?_unique_of_nodup (localOccurrences_nodup diagram region)
    (sourceChildOccurrenceIndex_found diagram region child parent)
    (by simpa only [List.get_eq_getElem] using occurrence)).symm

/-- Two direct children of one parent cannot both enclose the same region in a
well-formed parent tree. -/
theorem direct_children_enclosing_eq
    {diagram : Concrete.Diagram} (wellFormed : diagram.WellFormed)
    {parent first second descendant : Fin diagram.regionCount}
    (firstParent : (diagram.regions first).parent? = some parent)
    (secondParent : (diagram.regions second).parent? = some parent)
    (firstEncloses : diagram.Encloses first descendant)
    (secondEncloses : diagram.Encloses second descendant) : first = second := by
  obtain ⟨firstSteps, firstClimb⟩ := firstEncloses
  obtain ⟨secondSteps, secondClimb⟩ := secondEncloses
  obtain ⟨rootSteps, parentRoot⟩ :=
    wellFormed.all_regions_reach_root parent
  have firstToParent : diagram.climb (firstSteps.val + 1) descendant =
      some parent := by
    apply climb_add firstClimb
    simp [Diagram.climb, firstParent]
  have secondToParent : diagram.climb (secondSteps.val + 1) descendant =
      some parent := by
    apply climb_add secondClimb
    simp [Diagram.climb, secondParent]
  have firstToRoot :
      diagram.climb ((firstSteps.val + 1) + rootSteps.val) descendant =
        some diagram.root := climb_add firstToParent parentRoot
  have secondToRoot :
      diagram.climb ((secondSteps.val + 1) + rootSteps.val) descendant =
        some diagram.root := climb_add secondToParent parentRoot
  have totalEq := ParentTraversal.climb_to_root_steps_unique diagram
    wellFormed.root_is_sheet firstToRoot secondToRoot
  have stepsEq : firstSteps.val = secondSteps.val := by omega
  rw [stepsEq] at firstClimb
  exact Option.some.inj (firstClimb.symm.trans secondClimb)

/-- The distinguished source item position is the source occurrence position
transported through the successful compiler's length equation. -/
noncomputable def sourceChildItemIndex
    (diagram : Concrete.Diagram) (region child : Fin diagram.regionCount)
    (parent : (diagram.regions child).parent? = some region)
    {context : WireContext diagram} {binders : BinderContext diagram rels}
    {recurse : ∀ {innerRels : RelCtx},
      (inner : Fin diagram.regionCount) →
      (innerContext : WireContext diagram) →
      BinderContext diagram innerRels →
        Option (Region innerContext.length innerRels)}
    {items : ItemSeq context.length rels}
    (compiled : compileOccurrencesWith? diagram recurse context binders
      (localOccurrences diagram region) = some items) : Fin items.length :=
  Fin.cast (compileOccurrencesWith?_length recurse context binders compiled).symm
    (sourceChildOccurrenceIndex diagram region child parent)

/-- The corresponding target item position is computed from the same source
occurrence position and the mapped occurrence list's length equation. -/
noncomputable def targetChildItemIndex
    (layout : PlugLayout input)
    (region child : Fin input.frame.val.regionCount)
    (parent : (input.frame.val.regions child).parent? = some region)
    {context : WireContext layout.plugRaw}
    {binders : BinderContext layout.plugRaw rels}
    {recurse : ∀ {innerRels : RelCtx},
      (inner : Fin layout.plugRaw.regionCount) →
      (innerContext : WireContext layout.plugRaw) →
      BinderContext layout.plugRaw innerRels →
        Option (Region innerContext.length innerRels)}
    {items : ItemSeq context.length rels}
    (compiled : compileOccurrencesWith? layout.plugRaw recurse context binders
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some items) : Fin items.length :=
  let occurrenceIndex := sourceChildOccurrenceIndex input.frame.val
    region child parent
  let mappedIndex : Fin
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence).length :=
    Fin.cast (List.length_map layout.mapFrameOccurrence).symm occurrenceIndex
  Fin.cast (compileOccurrencesWith?_length recurse context binders compiled).symm
    mappedIndex

/-- Successful source and mapped-target occurrence blocks have canonically
equivalent item positions. -/
noncomputable def mappedCompilerItemEquiv
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount)
    {sourceContext : WireContext input.frame.val}
    {targetContext : WireContext layout.plugRaw}
    {sourceBinders : BinderContext input.frame.val rels}
    {targetBinders : BinderContext layout.plugRaw rels}
    {sourceRecurse : ∀ {innerRels : RelCtx},
      (inner : Fin input.frame.val.regionCount) →
      (innerContext : WireContext input.frame.val) →
      BinderContext input.frame.val innerRels →
        Option (Region innerContext.length innerRels)}
    {targetRecurse : ∀ {innerRels : RelCtx},
      (inner : Fin layout.plugRaw.regionCount) →
      (innerContext : WireContext layout.plugRaw) →
      BinderContext layout.plugRaw innerRels →
        Option (Region innerContext.length innerRels)}
    {sourceItems : ItemSeq sourceContext.length rels}
    {targetItems : ItemSeq targetContext.length rels}
    (sourceCompiled : compileOccurrencesWith? input.frame.val sourceRecurse
      sourceContext sourceBinders (localOccurrences input.frame.val region) =
        some sourceItems)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw targetRecurse
      targetContext targetBinders
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some targetItems) :
    FiniteEquiv (Fin sourceItems.length) (Fin targetItems.length) :=
  FiniteEquiv.finCast (by
    rw [compileOccurrencesWith?_length sourceRecurse sourceContext
        sourceBinders sourceCompiled,
      compileOccurrencesWith?_length targetRecurse targetContext
        targetBinders targetCompiled,
      List.length_map])

@[simp] theorem mappedCompilerItemEquiv_val
    (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount)
    {sourceContext : WireContext input.frame.val}
    {targetContext : WireContext layout.plugRaw}
    {sourceBinders : BinderContext input.frame.val rels}
    {targetBinders : BinderContext layout.plugRaw rels}
    {sourceRecurse : ∀ {innerRels : RelCtx},
      (inner : Fin input.frame.val.regionCount) →
      (innerContext : WireContext input.frame.val) →
      BinderContext input.frame.val innerRels →
        Option (Region innerContext.length innerRels)}
    {targetRecurse : ∀ {innerRels : RelCtx},
      (inner : Fin layout.plugRaw.regionCount) →
      (innerContext : WireContext layout.plugRaw) →
      BinderContext layout.plugRaw innerRels →
        Option (Region innerContext.length innerRels)}
    {sourceItems : ItemSeq sourceContext.length rels}
    {targetItems : ItemSeq targetContext.length rels}
    (sourceCompiled : compileOccurrencesWith? input.frame.val sourceRecurse
      sourceContext sourceBinders (localOccurrences input.frame.val region) =
        some sourceItems)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw targetRecurse
      targetContext targetBinders
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some targetItems)
    (index : Fin sourceItems.length) :
    (mappedCompilerItemEquiv layout region sourceCompiled targetCompiled
      index).val = index.val := rfl

/-- The item-position equivalence maps the distinguished source child to the
target position computed from that same source occurrence. -/
theorem mappedCompilerItemEquiv_sourceChild
    (layout : PlugLayout input)
    (region child : Fin input.frame.val.regionCount)
    (parent : (input.frame.val.regions child).parent? = some region)
    {sourceContext : WireContext input.frame.val}
    {targetContext : WireContext layout.plugRaw}
    {sourceBinders : BinderContext input.frame.val rels}
    {targetBinders : BinderContext layout.plugRaw rels}
    {sourceRecurse : ∀ {innerRels : RelCtx},
      (inner : Fin input.frame.val.regionCount) →
      (innerContext : WireContext input.frame.val) →
      BinderContext input.frame.val innerRels →
        Option (Region innerContext.length innerRels)}
    {targetRecurse : ∀ {innerRels : RelCtx},
      (inner : Fin layout.plugRaw.regionCount) →
      (innerContext : WireContext layout.plugRaw) →
      BinderContext layout.plugRaw innerRels →
        Option (Region innerContext.length innerRels)}
    {sourceItems : ItemSeq sourceContext.length rels}
    {targetItems : ItemSeq targetContext.length rels}
    (sourceCompiled : compileOccurrencesWith? input.frame.val sourceRecurse
      sourceContext sourceBinders (localOccurrences input.frame.val region) =
        some sourceItems)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw targetRecurse
      targetContext targetBinders
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some targetItems) :
    mappedCompilerItemEquiv layout region sourceCompiled targetCompiled
        (sourceChildItemIndex input.frame.val region child parent
          sourceCompiled) =
      targetChildItemIndex layout region child parent targetCompiled := by
  apply Fin.ext
  rfl

/-- Every item in an enclosing compiler frame except the source-selected
child is transported by the stable retained-frame equivalence.  No target
position is searched: the target index is the mapped source index. -/
private noncomputable def compileAncestorSiblingFrameOfContexts
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (region child : Fin input.frame.val.regionCount)
    (parent : (input.frame.val.regions child).parent? = some region)
    (childEncloses : input.frame.val.Encloses child input.site)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (wire : FiniteEquiv
      (Fin sourceContext.length) (Fin targetContext.length))
    (wireGet : ∀ index, targetContext.get (wire index) =
      layout.frameWireEmbedding consistent (sourceContext.get index))
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.frameRegion region))
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceFuel targetFuel : Nat)
    (sourceItems : ItemSeq sourceContext.length rels)
    (targetItems : ItemSeq targetContext.length rels)
    (sourceCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val sourceFuel) sourceContext
      sourceBinders (localOccurrences input.frame.val region) =
        some sourceItems)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      targetContext
      (layout.mapFrameBinders sourceBinders)
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some targetItems) :
    ItemSeqIso.Frame wire
      (sourceChildItemIndex input.frame.val region child parent sourceCompiled)
      (targetChildItemIndex layout region child parent targetCompiled) := by
  let positions := mappedCompilerItemEquiv layout region sourceCompiled
    targetCompiled
  refine {
    positions := positions
    mapped := layout.mappedCompilerItemEquiv_sourceChild region child parent
      sourceCompiled targetCompiled
    siblings := ?_
  }
  intro sourceIndex distinct
  let sourceLength := compileOccurrencesWith?_length
    (compileRegion? input.frame.val sourceFuel) sourceContext
    sourceBinders sourceCompiled
  let targetLength := compileOccurrencesWith?_length
    (compileRegion? layout.plugRaw targetFuel)
    targetContext
    (layout.mapFrameBinders sourceBinders) targetCompiled
  let occurrenceIndex : Fin (localOccurrences input.frame.val region).length :=
    Fin.cast sourceLength sourceIndex
  let targetOccurrenceIndex : Fin
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence).length :=
    Fin.cast (List.length_map layout.mapFrameOccurrence).symm occurrenceIndex
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex =
      sourceIndex := by
    apply Fin.ext
    rfl
  have targetPosition : Fin.cast targetLength.symm targetOccurrenceIndex =
      positions sourceIndex := by
    apply Fin.ext
    rfl
  have sourceItemCompiled := compileOccurrencesWith?_get
    (compileRegion? input.frame.val sourceFuel) sourceContext
    sourceBinders sourceCompiled occurrenceIndex
  rw [sourcePosition] at sourceItemCompiled
  have targetItemCompiled := compileOccurrencesWith?_get
    (compileRegion? layout.plugRaw targetFuel)
    targetContext
    (layout.mapFrameBinders sourceBinders) targetCompiled
    targetOccurrenceIndex
  have mappedOccurrence :
      ((localOccurrences input.frame.val region).map
          layout.mapFrameOccurrence).get targetOccurrenceIndex =
        layout.mapFrameOccurrence
          ((localOccurrences input.frame.val region).get occurrenceIndex) := by
    exact List.getElem_map layout.mapFrameOccurrence
  have targetItemCompiled' : compileOccurrenceWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      targetContext
      (layout.mapFrameBinders sourceBinders)
      (layout.mapFrameOccurrence
        ((localOccurrences input.frame.val region).get occurrenceIndex)) =
        some (targetItems.get (positions sourceIndex)) := by
    simpa only [List.get_eq_getElem, List.getElem_map, targetPosition] using
      targetItemCompiled
  generalize occurrenceEq :
    (localOccurrences input.frame.val region).get occurrenceIndex = occurrence
  have occurrenceMember : occurrence ∈ localOccurrences input.frame.val region :=
    occurrenceEq ▸ List.get_mem _ occurrenceIndex
  cases occurrence with
  | node node =>
      rw [occurrenceEq] at sourceItemCompiled targetItemCompiled'
      have nodeRegion : (input.frame.val.nodes node).region = region :=
        (mem_localOccurrences_node input.frame.val region node).mp
          occurrenceMember
      have nodeMap := layout.compileNode?_frameNode_map consistent
        sourceContext targetContext
        sourceBinders (layout.mapFrameBinders sourceBinders) node wire
        (fun relation => relation) targetExact.nodup
        wireGet (by
            intro sourceWire port occurs _
            have wireEncloses := sourceWellFormed.wire_scopes_enclose
              sourceWire ⟨node, port⟩ occurs
            exact (sourceExact.mem_iff sourceWire).2 (by
              simpa [nodeRegion] using wireEncloses))
        targetWellFormed.wire_endpoints_are_disjoint (by
          intro nodeOwner binder _
          rw [layout.mapFrameBinders_frameRegion]
          cases sourceBinders binder <;> simp)
      simp only [compileOccurrenceWith?, mapFrameOccurrence] at sourceItemCompiled targetItemCompiled'
      rw [sourceItemCompiled] at nodeMap
      simp only [Option.map_some, Item.renameRelations_id] at nodeMap
      have targetEq := Option.some.inj
        (targetItemCompiled'.symm.trans nodeMap)
      rw [targetEq]
      exact ItemIso.renameWiresEquiv _ wire
  | child sibling =>
      rw [occurrenceEq] at sourceItemCompiled targetItemCompiled'
      have siblingParent :
          (input.frame.val.regions sibling).parent? = some region :=
        (mem_localOccurrences_child input.frame.val region sibling).mp
          occurrenceMember
      have occurrenceNe : occurrenceIndex ≠
          sourceChildOccurrenceIndex input.frame.val region child parent := by
        intro occurrenceEq
        apply distinct
        apply Fin.ext
        simpa [occurrenceIndex, sourceChildItemIndex] using
          congrArg Fin.val occurrenceEq
      have siblingNe : sibling ≠ child := by
        intro siblingEq
        subst sibling
        have indexEq := indexOf?_unique_of_nodup
          (localOccurrences_nodup input.frame.val region)
          (sourceChildOccurrenceIndex_found input.frame.val region child parent)
          (by simpa only [List.get_eq_getElem] using occurrenceEq)
        exact occurrenceNe indexEq
      have siteOutside : ¬input.frame.val.Encloses sibling input.site := by
        intro siblingEncloses
        exact siblingNe (direct_children_enclosing_eq sourceWellFormed
          siblingParent parent siblingEncloses childEncloses)
      have sourceChildExact := sourceExact.extend_child sourceWellFormed
        siblingParent
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion sibling)).parent? =
            some (layout.frameRegion region) := by
        rw [layout.plugRegion_frameRegion]
        exact (layout.mapFrameRegion_parent_eq_some_iff sibling region).2
          siblingParent
      have targetChildExact := targetExact.extend_child targetWellFormed
        targetParent
      simp only [compileOccurrenceWith?, mapFrameOccurrence] at sourceItemCompiled targetItemCompiled'
      cases siblingKind : input.frame.val.regions sibling with
      | sheet => simp [siblingKind] at sourceItemCompiled
      | cut siblingOwner =>
          have ownerEq : siblingOwner = region := by
            simpa [siblingKind, CRegion.parent?] using siblingParent
          subst siblingOwner
          have targetKind : layout.plugRaw.regions
              (layout.frameRegion sibling) =
                .cut (layout.frameRegion region) := by
            rw [layout.plugRegion_frameRegion, siblingKind]
            rfl
          cases sourceChildResult : compileRegion? input.frame.val sourceFuel
              sibling sourceContext sourceBinders with
          | none => simp [siblingKind, sourceChildResult] at sourceItemCompiled
          | some sourceChildBody =>
              simp [siblingKind, sourceChildResult] at sourceItemCompiled
              cases targetChildResult : compileRegion? layout.plugRaw targetFuel
                  (layout.frameRegion sibling)
                  targetContext
                  (layout.mapFrameBinders sourceBinders) with
              | none =>
                  simp [targetKind, targetChildResult] at targetItemCompiled'
              | some targetChildBody =>
                  simp [targetKind, targetChildResult] at targetItemCompiled'
                  have childEq := layout.compileRegion?_frameRegion_map_of_not_encloses_site
                    consistent terminal sourceWellFormed targetWellFormed
                    sibling siteOutside sourceContext targetContext wire
                    wireGet sourceChildExact targetChildExact
                    sourceBinders sourceFuel targetFuel sourceChildBody
                    targetChildBody sourceChildResult targetChildResult
                  rw [← sourceItemCompiled, ← targetItemCompiled', childEq]
                  exact ItemIso.cut
                    (RegionIso.renameWiresEquiv sourceChildBody wire)
      | bubble siblingOwner arity =>
          have ownerEq : siblingOwner = region := by
            simpa [siblingKind, CRegion.parent?] using siblingParent
          subst siblingOwner
          have targetKind : layout.plugRaw.regions
              (layout.frameRegion sibling) =
                .bubble (layout.frameRegion region) arity := by
            rw [layout.plugRegion_frameRegion, siblingKind]
            rfl
          cases sourceChildResult : compileRegion? input.frame.val sourceFuel
              sibling sourceContext
              (sourceBinders.push sibling arity) with
          | none => simp [siblingKind, sourceChildResult] at sourceItemCompiled
          | some sourceChildBody =>
              simp [siblingKind, sourceChildResult] at sourceItemCompiled
              cases targetChildResult : compileRegion? layout.plugRaw targetFuel
                  (layout.frameRegion sibling)
                  targetContext
                  ((layout.mapFrameBinders sourceBinders).push
                    (layout.frameRegion sibling) arity) with
              | none =>
                  simp [targetKind, targetChildResult] at targetItemCompiled'
              | some targetChildBody =>
                  simp [targetKind, targetChildResult] at targetItemCompiled'
                  have targetChildResult' : compileRegion? layout.plugRaw
                      targetFuel (layout.frameRegion sibling)
                      targetContext
                      (layout.mapFrameBinders
                        (sourceBinders.push sibling arity)) =
                        some targetChildBody := by
                    rw [← layout.mapFrameBinders_push]
                    exact targetChildResult
                  have childEq := layout.compileRegion?_frameRegion_map_of_not_encloses_site
                    consistent terminal sourceWellFormed targetWellFormed
                    sibling siteOutside sourceContext targetContext wire
                    wireGet sourceChildExact targetChildExact
                    (sourceBinders.push sibling arity) sourceFuel targetFuel
                    sourceChildBody targetChildBody sourceChildResult
                    targetChildResult'
                  rw [← sourceItemCompiled, ← targetItemCompiled', childEq]
                  exact ItemIso.bubble
                    (RegionIso.renameWiresEquiv sourceChildBody wire)

/-- Region-context specialization of the source-derived sibling-frame
compiler transport. -/
noncomputable def compileAncestorSiblingFrame
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (region child : Fin input.frame.val.regionCount)
    (away : region ≠ input.site)
    (parent : (input.frame.val.regions child).parent? = some region)
    (childEncloses : input.frame.val.Encloses child input.site)
    (context : WireContext input.frame.val)
    (sourceExact : (context.extend region).Exact region)
    (targetExact :
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion region)).Exact (layout.frameRegion region))
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceFuel targetFuel : Nat)
    (sourceItems : ItemSeq (context.extend region).length rels)
    (targetItems : ItemSeq
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion region)).length rels)
    (sourceCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val sourceFuel) (context.extend region)
      sourceBinders (localOccurrences input.frame.val region) =
        some sourceItems)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion region))
      (layout.mapFrameBinders sourceBinders)
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some targetItems) :
    ItemSeqIso.Frame
      (layout.frameExtendedContextEquiv consistent terminal context region away)
      (sourceChildItemIndex input.frame.val region child parent sourceCompiled)
      (targetChildItemIndex layout region child parent targetCompiled) :=
  compileAncestorSiblingFrameOfContexts layout consistent terminal
    sourceWellFormed targetWellFormed region child parent childEncloses
    (context.extend region)
    ((layout.mapFrameContext consistent context).extend
      (layout.frameRegion region))
    (layout.frameExtendedContextEquiv consistent terminal context region away)
    (layout.frameExtendedContextEquiv_get consistent terminal context region
      away)
    sourceExact targetExact sourceBinders sourceFuel targetFuel sourceItems
    targetItems sourceCompiled targetCompiled

/-- Open-root specialization of sibling transport.  The target root context
and every target item position are fixed by the source open root. -/
noncomputable def compileOpenRootSiblingFrame
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (sourceWellFormed : (frameOpen input boundary).WellFormed)
    (targetWellFormed : (layout.outputOpenRoot input boundary).WellFormed)
    (child : Fin input.frame.val.regionCount)
    (away : input.frame.val.root ≠ input.site)
    (parent : (input.frame.val.regions child).parent? =
      some input.frame.val.root)
    (childEncloses : input.frame.val.Encloses child input.site)
    (sourceItems : ItemSeq
      (frameOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq
      (layout.outputOpenRoot input boundary).rootWires.length [])
    (sourceCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val input.frame.val.regionCount)
      (frameOpen input boundary).rootWires BinderContext.empty
      (localOccurrences input.frame.val input.frame.val.root) =
        some sourceItems)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
      (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
      ((localOccurrences input.frame.val input.frame.val.root).map
        layout.mapFrameOccurrence) = some targetItems) :
    ItemSeqIso.Frame
      (layout.outputRootContextEquiv_of_ne consistent terminal boundary away)
      (sourceChildItemIndex input.frame.val input.frame.val.root child parent
        sourceCompiled)
      (targetChildItemIndex layout input.frame.val.root child parent
        targetCompiled) :=
  compileAncestorSiblingFrameOfContexts layout consistent terminal
    sourceWellFormed.diagram_well_formed targetWellFormed.diagram_well_formed
    input.frame.val.root child parent childEncloses
    (frameOpen input boundary).rootWires
    (layout.outputOpenRoot input boundary).rootWires
    (layout.outputRootContextEquiv_of_ne consistent terminal boundary away)
    (layout.outputRootContextEquiv_of_ne_get consistent terminal boundary away)
    (openRootWires_exact sourceWellFormed)
    (openRootWires_exact targetWellFormed)
    BinderContext.empty input.frame.val.regionCount layout.plugRaw.regionCount
    sourceItems targetItems sourceCompiled (by
      rw [mapFrameBinders_empty]
      exact targetCompiled)

/-- The source-selected compiler item is the cut body returned by that
source child call. -/
private theorem compiledSourceCutChild_get
    (diagram : Concrete.Diagram) (region child : Fin diagram.regionCount)
    (parent : (diagram.regions child).parent? = some region)
    (childKind : diagram.regions child = .cut region)
    (context : WireContext diagram)
    (binders : BinderContext diagram rels) (fuel : Nat)
    (items : ItemSeq context.length rels)
    (compiled : compileOccurrencesWith? diagram (compileRegion? diagram fuel)
      context binders (localOccurrences diagram region) = some items)
    (childBody : Region context.length rels)
    (childCompiled : compileRegion? diagram fuel child context binders =
      some childBody) :
    items.get (sourceChildItemIndex diagram region child parent compiled) =
      .cut childBody := by
  have itemCompiled := compileOccurrencesWith?_get
    (compileRegion? diagram fuel) context binders compiled
    (sourceChildOccurrenceIndex diagram region child parent)
  rw [sourceChildOccurrenceIndex_get] at itemCompiled
  simpa [compileOccurrenceWith?, childKind, sourceChildItemIndex,
    childCompiled] using itemCompiled.symm

/-- Bubble counterpart of `compiledSourceCutChild_get`. -/
private theorem compiledSourceBubbleChild_get
    (diagram : Concrete.Diagram) (region child : Fin diagram.regionCount)
    (parent : (diagram.regions child).parent? = some region)
    (childKind : diagram.regions child = .bubble region arity)
    (context : WireContext diagram)
    (binders : BinderContext diagram rels) (fuel : Nat)
    (items : ItemSeq context.length rels)
    (compiled : compileOccurrencesWith? diagram (compileRegion? diagram fuel)
      context binders (localOccurrences diagram region) = some items)
    (childBody : Region context.length (arity :: rels))
    (childCompiled : compileRegion? diagram fuel child context
      (binders.push child arity) = some childBody) :
    items.get (sourceChildItemIndex diagram region child parent compiled) =
      .bubble arity childBody := by
  have itemCompiled := compileOccurrencesWith?_get
    (compileRegion? diagram fuel) context binders compiled
    (sourceChildOccurrenceIndex diagram region child parent)
  rw [sourceChildOccurrenceIndex_get] at itemCompiled
  simpa [compileOccurrenceWith?, childKind, sourceChildItemIndex,
    childCompiled] using itemCompiled.symm

/-- The target item at the source-mapped child position is exactly the cut
body returned by the mapped child call. -/
private theorem compiledMappedCutChild_get
    (layout : PlugLayout input)
    (region child : Fin input.frame.val.regionCount)
    (parent : (input.frame.val.regions child).parent? = some region)
    (targetKind : layout.plugRaw.regions (layout.frameRegion child) =
      .cut (layout.frameRegion region))
    (context : WireContext layout.plugRaw)
    (binders : BinderContext layout.plugRaw rels) (fuel : Nat)
    (items : ItemSeq context.length rels)
    (compiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw fuel) context binders
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some items)
    (childBody : Region context.length rels)
    (childCompiled : compileRegion? layout.plugRaw fuel
      (layout.frameRegion child) context binders = some childBody) :
    items.get (targetChildItemIndex layout region child parent compiled) =
      .cut childBody := by
  let occurrenceIndex := sourceChildOccurrenceIndex input.frame.val
    region child parent
  let mappedIndex : Fin
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence).length :=
    Fin.cast (List.length_map layout.mapFrameOccurrence).symm occurrenceIndex
  have itemCompiled := compileOccurrencesWith?_get
    (compileRegion? layout.plugRaw fuel) context binders compiled mappedIndex
  have itemCompiled' : compileOccurrenceWith? layout.plugRaw
      (compileRegion? layout.plugRaw fuel) context binders
      (layout.mapFrameOccurrence
        ((localOccurrences input.frame.val region).get occurrenceIndex)) =
        some (items.get
          (targetChildItemIndex layout region child parent compiled)) := by
    simpa only [List.get_eq_getElem, List.getElem_map,
      targetChildItemIndex, occurrenceIndex, mappedIndex] using itemCompiled
  rw [sourceChildOccurrenceIndex_get] at itemCompiled'
  simpa [compileOccurrenceWith?, mapFrameOccurrence, targetKind,
    targetChildItemIndex,
    childCompiled, occurrenceIndex, mappedIndex] using itemCompiled'.symm

/-- Bubble counterpart of `compiledMappedCutChild_get`. -/
private theorem compiledMappedBubbleChild_get
    (layout : PlugLayout input)
    (region child : Fin input.frame.val.regionCount)
    (parent : (input.frame.val.regions child).parent? = some region)
    (targetKind : layout.plugRaw.regions (layout.frameRegion child) =
      .bubble (layout.frameRegion region) arity)
    (context : WireContext layout.plugRaw)
    (binders : BinderContext layout.plugRaw rels) (fuel : Nat)
    (items : ItemSeq context.length rels)
    (compiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw fuel) context binders
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence) = some items)
    (childBody : Region context.length (arity :: rels))
    (childCompiled : compileRegion? layout.plugRaw fuel
      (layout.frameRegion child) context
      (binders.push (layout.frameRegion child) arity) = some childBody) :
    items.get (targetChildItemIndex layout region child parent compiled) =
      .bubble arity childBody := by
  let occurrenceIndex := sourceChildOccurrenceIndex input.frame.val
    region child parent
  let mappedIndex : Fin
      ((localOccurrences input.frame.val region).map
        layout.mapFrameOccurrence).length :=
    Fin.cast (List.length_map layout.mapFrameOccurrence).symm occurrenceIndex
  have itemCompiled := compileOccurrencesWith?_get
    (compileRegion? layout.plugRaw fuel) context binders compiled mappedIndex
  have itemCompiled' : compileOccurrenceWith? layout.plugRaw
      (compileRegion? layout.plugRaw fuel) context binders
      (layout.mapFrameOccurrence
        ((localOccurrences input.frame.val region).get occurrenceIndex)) =
        some (items.get
          (targetChildItemIndex layout region child parent compiled)) := by
    simpa only [List.get_eq_getElem, List.getElem_map,
      targetChildItemIndex, occurrenceIndex, mappedIndex] using itemCompiled
  rw [sourceChildOccurrenceIndex_get] at itemCompiled'
  simpa [compileOccurrenceWith?, mapFrameOccurrence, targetKind,
    targetChildItemIndex,
    childCompiled, occurrenceIndex, mappedIndex] using itemCompiled'.symm

/-- Transport a compiler frame across the wire-count casts performed by
`finishRegion` and `finishRoot`. -/
private noncomputable def castCompilerFrame
    {source : ItemSeq sourceWires rels}
    {target : ItemSeq targetWires rels}
    {sourceIndex : Fin source.length} {targetIndex : Fin target.length}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (frame : ItemSeqIso.Frame wire sourceIndex targetIndex)
    (sourceEq : sourceWires = normalizedSourceWires)
    (targetEq : targetWires = normalizedTargetWires)
    (normalizedWire : FiniteEquiv
      (Fin normalizedSourceWires) (Fin normalizedTargetWires))
    (commutes : normalizedWire.toFun ∘ Fin.cast sourceEq =
      Fin.cast targetEq ∘ wire.toFun) :
    ItemSeqIso.Frame (source := source.castWiresEq sourceEq)
      (target := target.castWiresEq targetEq) normalizedWire
      (Fin.cast (ItemSeq.castWiresEq_length sourceEq source).symm sourceIndex)
      (Fin.cast (ItemSeq.castWiresEq_length targetEq target).symm
        targetIndex) := by
  let sourcePositions : FiniteEquiv
      (Fin (source.castWiresEq sourceEq).length) (Fin source.length) :=
    FiniteEquiv.finCast (ItemSeq.castWiresEq_length sourceEq source)
  let targetPositions : FiniteEquiv
      (Fin (target.castWiresEq targetEq).length) (Fin target.length) :=
    FiniteEquiv.finCast (ItemSeq.castWiresEq_length targetEq target)
  refine {
    positions := sourcePositions.trans
      (frame.positions.trans targetPositions.symm)
    mapped := by
      apply Fin.ext
      simpa [sourcePositions, targetPositions, FiniteEquiv.trans_apply,
        finCast_val] using congrArg Fin.val frame.mapped
    siblings := ?_
  }
  intro index distinct
  have sourceDistinct : sourcePositions index ≠ sourceIndex := by
    intro equality
    apply distinct
    apply Fin.ext
    simpa [sourcePositions, finCast_val] using congrArg Fin.val equality
  have sibling := frame.siblings (sourcePositions index) sourceDistinct
  have renamed := sibling.renameWires_commuting (Fin.cast sourceEq)
    (Fin.cast targetEq) normalizedWire commutes
  have sourceIndexEq :
      Fin.cast (ItemSeq.castWiresEq_length sourceEq source).symm
          (sourcePositions index) = index := by
    apply Fin.ext
    rfl
  have targetIndexEq :
      Fin.cast (ItemSeq.castWiresEq_length targetEq target).symm
          (frame.positions (sourcePositions index)) =
        targetPositions.symm (frame.positions (sourcePositions index)) := by
    apply Fin.ext
    rfl
  have sourceGet := ItemSeq.get_castWiresEq sourceEq source
    (sourcePositions index)
  have targetGet := ItemSeq.get_castWiresEq targetEq target
    (frame.positions (sourcePositions index))
  rw [sourceIndexEq] at sourceGet
  rw [targetIndexEq] at targetGet
  have outputIndexEq :
      (sourcePositions.trans (frame.positions.trans targetPositions.symm))
          index =
        targetPositions.symm (frame.positions (sourcePositions index)) := rfl
  rw [sourceGet, outputIndexEq, targetGet]
  simpa only [Item.castWiresEq_eq_renameWires] using renamed

/-- Normalize the outer wire presentations of an already source-derived
route alignment.  Only equality casts are introduced; its hole and every
enclosing-frame choice remain unchanged. -/
private noncomputable def CompilerRouteAlignment.castOuterWires
    {sourceOuter targetOuter normalizedSource normalizedTarget
      sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    {sourceRoot : Region sourceOuter outerRels}
    {targetRoot : Region targetOuter outerRels}
    {sourceSite : Region sourceHole holeRels}
    {targetSite : Region targetHole holeRels}
    (alignment : CompilerRouteAlignment outerWire holeWire
      sourceRoot targetRoot sourceSite targetSite)
    (sourceEq : sourceOuter = normalizedSource)
    (targetEq : targetOuter = normalizedTarget)
    (normalizedWire : FiniteEquiv
      (Fin normalizedSource) (Fin normalizedTarget))
    (commutes : normalizedWire.toFun ∘ Fin.cast sourceEq =
      Fin.cast targetEq ∘ outerWire.toFun) :
    CompilerRouteAlignment normalizedWire holeWire
      (sourceRoot.castWiresEq sourceEq)
      (targetRoot.castWiresEq targetEq) sourceSite targetSite := by
  subst normalizedSource
  subst normalizedTarget
  have wireEq : normalizedWire = outerWire := by
    apply FiniteEquiv.ext
    intro index
    exact congrFun commutes index
  subst normalizedWire
  exact alignment

private theorem CompilerRouteAlignment.castOuterWires_sourceContext_heq
    {sourceOuter targetOuter normalizedSource normalizedTarget
      sourceHole targetHole : Nat}
    {outerRels holeRels : RelCtx}
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {holeWire : FiniteEquiv (Fin sourceHole) (Fin targetHole)}
    {sourceRoot : Region sourceOuter outerRels}
    {targetRoot : Region targetOuter outerRels}
    {sourceSite : Region sourceHole holeRels}
    {targetSite : Region targetHole holeRels}
    (alignment : CompilerRouteAlignment outerWire holeWire
      sourceRoot targetRoot sourceSite targetSite)
    (sourceEq : sourceOuter = normalizedSource)
    (targetEq : targetOuter = normalizedTarget)
    (normalizedWire : FiniteEquiv
      (Fin normalizedSource) (Fin normalizedTarget))
    (commutes : normalizedWire.toFun ∘ Fin.cast sourceEq =
      Fin.cast targetEq ∘ outerWire.toFun) :
    HEq (alignment.castOuterWires sourceEq targetEq normalizedWire
      commutes).sourceContext alignment.sourceContext := by
  subst normalizedSource
  subst normalizedTarget
  have wireEq : normalizedWire = outerWire := by
    apply FiniteEquiv.ext
    intro index
    exact congrFun commutes index
  subst normalizedWire
  rfl

private theorem Region.ContextPath.castWiresEq_toFocus_context_heq
    (equality : source = target)
    (witness : Region.ContextPath region path) :
    HEq (witness.castWiresEq equality).toFocus.context
      witness.toFocus.context := by
  subst target
  rfl

private def castRouteFocusContext
    (wireEq : sourceWires = targetWires)
    (relsEq : sourceRels = targetRels)
    (context : DiagramContext outerWires sourceWires outerRels sourceRels) :
    DiagramContext outerWires targetWires outerRels targetRels := by
  subst targetWires
  subst targetRels
  exact context

private theorem castRouteFocusContext_heq
    (wireEq : sourceWires = targetWires)
    (relsEq : sourceRels = targetRels)
    (context : DiagramContext outerWires sourceWires outerRels sourceRels) :
    HEq (castRouteFocusContext wireEq relsEq context) context := by
  subst targetWires
  subst targetRels
  rfl

private theorem castRouteFocusContext_cut
    (wireEq : sourceWires = targetWires)
    (relsEq : sourceRels = targetRels)
    (before after : ItemSeq (outerWires + localWires) outerRels)
    (child : DiagramContext (outerWires + localWires) sourceWires
      outerRels sourceRels) :
    castRouteFocusContext wireEq relsEq
        (DiagramContext.cut localWires before after child) =
      DiagramContext.cut localWires before after
        (castRouteFocusContext wireEq relsEq child) := by
  subst targetWires
  subst targetRels
  rfl

private theorem castRouteFocusContext_bubble
    (wireEq : sourceWires = targetWires)
    (relsEq : sourceRels = targetRels)
    (before after : ItemSeq (outerWires + localWires) outerRels)
    (child : DiagramContext (outerWires + localWires) sourceWires
      (arity :: outerRels) sourceRels) :
    castRouteFocusContext wireEq relsEq
        (DiagramContext.bubble localWires before after arity child) =
      DiagramContext.bubble localWires before after arity
        (castRouteFocusContext wireEq relsEq child) := by
  subst targetWires
  subst targetRels
  rfl

/-- Canonical mapped inherited context at a retained child, normalized to
the outer-plus-local presentation required by a diagram context layer. -/
private theorem mappedExtendedContext_length
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount) (away : region ≠ input.site) :
    (layout.mapFrameContext consistent (context.extend region)).length =
      (layout.mapFrameContext consistent context).length +
        (exactScopeWires layout.plugRaw
          (layout.frameRegion region)).length := by
  rw [layout.mapFrameContext_extend_of_ne consistent terminal context
      region away,
    WireContext.length_extend]

/-- Put a recursively aligned child into the exact outer/local wire
presentation of its parent compiler frame. -/
private noncomputable def CompilerRouteAlignment.normalizeFrameChild
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount) (away : region ≠ input.site)
    {holeSource holeTarget : Nat} {outerRels holeRels : RelCtx}
    {sourceRoot : Region (context.extend region).length outerRels}
    {targetRoot : Region
      (layout.mapFrameContext consistent (context.extend region)).length
      outerRels}
    {sourceSite : Region holeSource holeRels}
    {targetSite : Region holeTarget holeRels}
    {holeWire : FiniteEquiv (Fin holeSource) (Fin holeTarget)}
    (alignment : CompilerRouteAlignment
      (layout.mapFrameContextEquiv consistent (context.extend region))
      holeWire sourceRoot targetRoot sourceSite targetSite) :
    CompilerRouteAlignment
      (extendWireEquiv
        (layout.mapFrameContextEquiv consistent context)
        (FiniteEquiv.finCast
          (layout.exactScopeWires_frameRegion_length_of_ne consistent terminal
            region away).symm))
      holeWire
      (sourceRoot.castWiresEq (WireContext.length_extend context region))
      (targetRoot.castWiresEq
        (layout.mappedExtendedContext_length consistent terminal context
          region away))
      sourceSite targetSite := by
  apply alignment.castOuterWires
  · funext index
    apply Fin.ext
    let split : Fin
        (context.length + (exactScopeWires input.frame.val region).length) :=
      Fin.cast (WireContext.length_extend context region) index
    have splitEq :
        Fin.cast (WireContext.length_extend context region).symm split =
          index := by
      apply Fin.ext
      rfl
    rw [← splitEq]
    refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_)
      split
    · simp [extendWireEquiv, mapFrameContextEquiv,
        FiniteEquiv.finCast]
    · simp [extendWireEquiv, mapFrameContextEquiv,
        mapFrameContext, FiniteEquiv.finCast]

private theorem CompilerRouteAlignment.normalizeFrameChild_sourceContext_heq
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (context : WireContext input.frame.val)
    (region : Fin input.frame.val.regionCount) (away : region ≠ input.site)
    {holeSource holeTarget : Nat} {outerRels holeRels : RelCtx}
    {sourceRoot : Region (context.extend region).length outerRels}
    {targetRoot : Region
      (layout.mapFrameContext consistent (context.extend region)).length
      outerRels}
    {sourceSite : Region holeSource holeRels}
    {targetSite : Region holeTarget holeRels}
    {holeWire : FiniteEquiv (Fin holeSource) (Fin holeTarget)}
    (alignment : CompilerRouteAlignment
      (layout.mapFrameContextEquiv consistent (context.extend region))
      holeWire sourceRoot targetRoot sourceSite targetSite) :
    HEq (alignment.normalizeFrameChild layout consistent terminal context
      region away).sourceContext alignment.sourceContext := by
  unfold CompilerRouteAlignment.normalizeFrameChild
  apply CompilerRouteAlignment.castOuterWires_sourceContext_heq

/-- The mapped source root context has the generated target's exact
exposed-plus-hidden compiler length away from a root insertion. -/
private theorem mappedOpenRootContext_length_of_ne
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site) :
    (layout.mapFrameContext consistent
        (frameOpen input boundary).rootWires).length =
      (layout.outputOpenRoot input boundary).exposedWires.length +
        (layout.outputOpenRoot input boundary).hiddenWires.length := by
  unfold mapFrameContext
  rw [layout.outputOpenRoot_exposedWires consistent boundary,
    layout.outputOpenRoot_hiddenWires consistent terminal boundary,
    if_neg away, List.append_nil]
  unfold OpenDiagram.rootWires
  calc
    (((frameOpen input boundary).exposedWires ++
        (frameOpen input boundary).hiddenWires).map
      (layout.frameWireEmbedding consistent)).length =
      ((frameOpen input boundary).exposedWires ++
        (frameOpen input boundary).hiddenWires).length := List.length_map _
    _ = (frameOpen input boundary).exposedWires.length +
        (frameOpen input boundary).hiddenWires.length := List.length_append
    _ = ((frameOpen input boundary).exposedWires.map
          (layout.frameWireEmbedding consistent)).length +
        (frameOpen input boundary).hiddenWires.length :=
      congrArg (fun length => length +
        (frameOpen input boundary).hiddenWires.length)
        (List.length_map _).symm
    _ = ((frameOpen input boundary).exposedWires.map
          (layout.frameWireEmbedding consistent)).length +
        ((frameOpen input boundary).hiddenWires.map
          (layout.frameWireEmbedding consistent)).length :=
      congrArg (fun length =>
        ((frameOpen input boundary).exposedWires.map
          (layout.frameWireEmbedding consistent)).length + length)
        (List.length_map _).symm

/-- Normalize a recursively aligned root child from the mapped full-root
presentation to the source-derived exposed/hidden split used by `finishRoot`.
-/
private noncomputable def CompilerRouteAlignment.normalizeOpenRootChild
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site)
    {holeSource holeTarget : Nat} {outerRels holeRels : RelCtx}
    {sourceRoot : Region (frameOpen input boundary).rootWires.length outerRels}
    {targetRoot : Region
      (layout.mapFrameContext consistent
        (frameOpen input boundary).rootWires).length outerRels}
    {sourceSite : Region holeSource holeRels}
    {targetSite : Region holeTarget holeRels}
    {holeWire : FiniteEquiv (Fin holeSource) (Fin holeTarget)}
    (alignment : CompilerRouteAlignment
      (layout.mapFrameContextEquiv consistent
        (frameOpen input boundary).rootWires)
      holeWire sourceRoot targetRoot sourceSite targetSite) :
    CompilerRouteAlignment
      (extendWireEquiv
        (layout.outputExternalEquiv consistent boundary)
        (layout.outputHiddenEquiv_of_ne consistent terminal boundary away))
      holeWire
      (sourceRoot.castWiresEq
        (openRootWires_length (frameOpen input boundary)))
      (targetRoot.castWiresEq
        (layout.mappedOpenRootContext_length_of_ne consistent terminal
          boundary away))
      sourceSite targetSite := by
  apply alignment.castOuterWires
  funext index
  apply Fin.ext
  change
    (extendWireEquiv
      (layout.outputExternalEquiv consistent boundary)
      (layout.outputHiddenEquiv_of_ne consistent terminal boundary away)
      (Fin.cast (openRootWires_length (frameOpen input boundary)) index)).val =
        index.val
  exact layout.outputRootSplitEquiv_of_ne_val consistent terminal boundary
    away _

private theorem
    CompilerRouteAlignment.normalizeOpenRootChild_sourceContext_heq
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (away : input.frame.val.root ≠ input.site)
    {holeSource holeTarget : Nat} {outerRels holeRels : RelCtx}
    {sourceRoot : Region (frameOpen input boundary).rootWires.length
      outerRels}
    {targetRoot : Region
      (layout.mapFrameContext consistent
        (frameOpen input boundary).rootWires).length outerRels}
    {sourceSite : Region holeSource holeRels}
    {targetSite : Region holeTarget holeRels}
    {holeWire : FiniteEquiv (Fin holeSource) (Fin holeTarget)}
    (alignment : CompilerRouteAlignment
      (layout.mapFrameContextEquiv consistent
        (frameOpen input boundary).rootWires)
      holeWire sourceRoot targetRoot sourceSite targetSite) :
    HEq (alignment.normalizeOpenRootChild layout consistent terminal boundary
      away).sourceContext alignment.sourceContext := by
  unfold CompilerRouteAlignment.normalizeOpenRootChild
  apply CompilerRouteAlignment.castOuterWires_sourceContext_heq

/-- One explicit target-site computation at the exact fuel delivered by a
source-derived compiler route. -/
structure ExplicitMappedSite
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (siteContext : WireContext input.frame.val)
    (sourceBinders : BinderContext input.frame.val rels)
    (targetFuel : Nat)
    (targetBody : Region
      (layout.mapFrameContext consistent siteContext).length rels) where
  target_compiled : compileRegion? layout.plugRaw targetFuel
    (layout.frameRegion input.site)
    (layout.mapFrameContext consistent siteContext)
    (layout.mapFrameBinders sourceBinders) = some targetBody

/-- Explicit zero-depth target computation, retaining the canonical mapped
site body separately from its relation and exposed-wire casts. -/
structure ExplicitMappedRootSite
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (siteContext : WireContext input.frame.val)
    (siteRels : RelCtx)
    (targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels) where
  siteRels_eq : siteRels = []
  outer_eq :
    (layout.mapFrameContext consistent siteContext).length =
      (layout.outputOpenRoot input boundary).exposedWires.length
  target_compiled : compileRoot? layout.plugRaw
    (layout.outputOpenRoot input boundary).exposedWires
    (layout.outputOpenRoot input boundary).hiddenWires =
      some ((siteRels_eq ▸ targetSite).castWiresEq outer_eq)

/-- Re-index a fixed explicit site computation by an equality of fuels. -/
private def ExplicitMappedSite.castFuel
    {layout : PlugLayout input} {consistent : input.AttachmentConsistent}
    {siteContext : WireContext input.frame.val}
    {sourceBinders : BinderContext input.frame.val rels}
    {sourceFuel targetFuel : Nat}
    {targetBody : Region
      (layout.mapFrameContext consistent siteContext).length rels}
    (site : ExplicitMappedSite layout consistent siteContext sourceBinders
      sourceFuel targetBody)
    (fuelEq : sourceFuel = targetFuel) :
    ExplicitMappedSite layout consistent siteContext sourceBinders
      targetFuel targetBody := by
  subst targetFuel
  exact site

/-- Transport only the concrete lexical-context presentation of a successful
region compiler call. -/
private theorem compileRegion?_castContext
    {diagram : Concrete.Diagram} {region : Fin diagram.regionCount}
    {sourceContext targetContext : WireContext diagram}
    (contextEq : sourceContext = targetContext)
    (binders : BinderContext diagram rels) (fuel : Nat)
    (body : Region sourceContext.length rels)
    (compiled : compileRegion? diagram fuel region sourceContext binders =
      some body) :
    compileRegion? diagram fuel region targetContext binders =
      some (body.castWiresEq (congrArg List.length contextEq)) := by
  subst targetContext
  exact compiled

/-- Bottom-up result of compiling one mapped source route.  Its terminal
source and target bodies are retained existentially, while the target
ancestor body and its compiler equation are explicit. -/
structure MappedRegionRouteResult
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (origin : Fin input.frame.val.regionCount)
    (context siteContext : WireContext input.frame.val)
    (sourceBinders : BinderContext input.frame.val rels)
    (path : List Nat) (targetFuel : Nat)
    (sourceBody : Region context.length rels)
    {siteRels : RelCtx}
    (targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels) where
  targetBody : Region
    (layout.mapFrameContext consistent context).length rels
  target_compiled : compileRegion? layout.plugRaw targetFuel
    (layout.frameRegion origin)
    (layout.mapFrameContext consistent context)
    (layout.mapFrameBinders sourceBinders) = some targetBody
  sourceSite : Region siteContext.length siteRels
  alignment : CompilerRouteAlignment
    (layout.mapFrameContextEquiv consistent context)
    (layout.mapFrameContextEquiv consistent siteContext)
    sourceBody targetBody sourceSite targetSite
  sourceWitness : Region.ContextPath sourceBody path
  source_focus_wires : sourceWitness.toFocus.holeWires = siteContext.length
  source_focus_rels : sourceWitness.toFocus.holeRels = siteRels
  source_focus_body : HEq sourceWitness.toFocus.body sourceSite
  source_context_heq :
    HEq alignment.sourceContext sourceWitness.toFocus.context

/-- Bottom-up open-root result.  Its target root body and compiler equation
are constructed from the source route; no target elaboration witness is
selected. -/
structure MappedOpenRouteResult
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (siteContext : WireContext input.frame.val)
    (path : List Nat)
    (sourceBody : Region
      (frameOpen input boundary).exposedWires.length [])
    {siteRels : RelCtx}
    (targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels) where
  targetBody : Region
    (layout.outputOpenRoot input boundary).exposedWires.length []
  target_compiled : compileRoot? layout.plugRaw
    (layout.outputOpenRoot input boundary).exposedWires
    (layout.outputOpenRoot input boundary).hiddenWires = some targetBody
  sourceSite : Region siteContext.length siteRels
  alignment : CompilerRouteAlignment
    (layout.outputExternalEquiv consistent boundary)
    (layout.mapFrameContextEquiv consistent siteContext)
    sourceBody targetBody sourceSite targetSite
  sourceWitness : Region.ContextPath sourceBody path
  source_focus_wires : sourceWitness.toFocus.holeWires = siteContext.length
  source_focus_rels : sourceWitness.toFocus.holeRels = siteRels
  source_focus_body : HEq sourceWitness.toFocus.body sourceSite
  source_context_heq :
    HEq alignment.sourceContext sourceWitness.toFocus.context

/-- GREEN zero-depth open-root assembler.  The target root is the canonical
mapped site body transported only by the generated exposed-length equality. -/
private noncomputable def mappedOpenHere
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (sourceBody : Region
      (frameOpen input boundary).exposedWires.length [])
    (targetSite : Region
      (layout.mapFrameContext consistent
        (frameOpen input boundary).exposedWires).length [])
    (outerEq :
      (layout.mapFrameContext consistent
        (frameOpen input boundary).exposedWires).length =
        (layout.outputOpenRoot input boundary).exposedWires.length)
    (targetCompiled : compileRoot? layout.plugRaw
      (layout.outputOpenRoot input boundary).exposedWires
      (layout.outputOpenRoot input boundary).hiddenWires =
        some (targetSite.castWiresEq outerEq)) :
    MappedOpenRouteResult layout consistent boundary
      (frameOpen input boundary).exposedWires [] sourceBody targetSite := by
  let rawAlignment : CompilerRouteAlignment
      (layout.mapFrameContextEquiv consistent
        (frameOpen input boundary).exposedWires)
      (layout.mapFrameContextEquiv consistent
        (frameOpen input boundary).exposedWires)
      sourceBody targetSite sourceBody targetSite := {
    sourceContext := .hole
    targetContext := .hole
    contextIso := .hole (layout.mapFrameContextEquiv consistent
      (frameOpen input boundary).exposedWires)
    source_rebuild := rfl
    target_rebuild := rfl
  }
  have commutes :
      (layout.outputExternalEquiv consistent boundary).toFun ∘ Fin.cast rfl =
        Fin.cast outerEq ∘
          (layout.mapFrameContextEquiv consistent
            (frameOpen input boundary).exposedWires).toFun := by
    funext index
    apply Fin.ext
    rfl
  let alignment := rawAlignment.castOuterWires rfl outerEq
    (layout.outputExternalEquiv consistent boundary) commutes
  exact {
    targetBody := targetSite.castWiresEq outerEq
    target_compiled := targetCompiled
    sourceSite := sourceBody
    alignment := alignment
    sourceWitness := .here sourceBody
    source_focus_wires := rfl
    source_focus_rels := rfl
    source_focus_body := .rfl
    source_context_heq := by
      exact (rawAlignment.castOuterWires_sourceContext_heq rfl outerEq
        (layout.outputExternalEquiv consistent boundary) commutes).trans
          HEq.rfl
  }

/-- GREEN base case of the mapped-route construction. -/
private noncomputable def mappedRegionHere
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (context : WireContext input.frame.val)
    (binders : BinderContext input.frame.val rels)
    (targetFuel : Nat) (sourceBody : Region context.length rels)
    {targetSite : Region
      (layout.mapFrameContext consistent context).length rels}
    (siteTarget : ExplicitMappedSite layout consistent context binders
      targetFuel targetSite) :
    MappedRegionRouteResult layout consistent input.site context context
      binders [] targetFuel sourceBody targetSite := by
  let alignment : CompilerRouteAlignment
      (layout.mapFrameContextEquiv consistent context)
      (layout.mapFrameContextEquiv consistent context)
      sourceBody targetSite sourceBody targetSite := {
    sourceContext := .hole
    targetContext := .hole
    contextIso := .hole (layout.mapFrameContextEquiv consistent context)
    source_rebuild := rfl
    target_rebuild := rfl
  }
  exact {
    targetBody := targetSite
    target_compiled := siteTarget.target_compiled
    sourceSite := sourceBody
    alignment := alignment
    sourceWitness := .here sourceBody
    source_focus_wires := rfl
    source_focus_rels := rfl
    source_focus_body := .rfl
    source_context_heq := .rfl
  }

/-- GREEN cut-step assembler for the mapped-route construction. -/
private noncomputable def mappedRegionCutStep
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    {origin child : Fin input.frame.val.regionCount}
    (away : origin ≠ input.site)
    (parent : (input.frame.val.regions child).parent? = some origin)
    (childKind : input.frame.val.regions child = .cut origin)
    (childEncloses : input.frame.val.Encloses child input.site)
    (index : Fin (localOccurrences input.frame.val origin).length)
    (occurrence : (localOccurrences input.frame.val origin).get index =
      .child child)
    {context siteContext : WireContext input.frame.val}
    {rels : RelCtx} (sourceBinders : BinderContext input.frame.val rels)
    (sourceExact : (context.extend origin).Exact origin)
    (targetExact : ((layout.mapFrameContext consistent context).extend
      (layout.frameRegion origin)).Exact (layout.frameRegion origin))
    (sourceRecurseFuel targetRecurseFuel : Nat)
    (sourceItems : ItemSeq (context.extend origin).length rels)
    (targetItems : ItemSeq
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin)).length rels)
    (sourceItemsCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val sourceRecurseFuel)
      (context.extend origin) sourceBinders
      (localOccurrences input.frame.val origin) = some sourceItems)
    (targetItemsCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetRecurseFuel)
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin))
      (layout.mapFrameBinders sourceBinders)
      ((localOccurrences input.frame.val origin).map
        layout.mapFrameOccurrence) = some targetItems)
    (sourceChildBody : Region (context.extend origin).length rels)
    (sourceChildCompiled : compileRegion? input.frame.val sourceRecurseFuel
      child (context.extend origin) sourceBinders = some sourceChildBody)
    {siteRels : RelCtx}
    {targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels}
    {path : List Nat}
    (nested : MappedRegionRouteResult layout consistent child
      (context.extend origin) siteContext sourceBinders path
      targetRecurseFuel sourceChildBody targetSite) :
    MappedRegionRouteResult layout consistent origin context siteContext
      sourceBinders (index.val :: path) (targetRecurseFuel + 1)
      (finishRegion input.frame.val context origin sourceItems) targetSite := by
  let sourceEq := WireContext.length_extend context origin
  let targetEq := WireContext.length_extend
    (layout.mapFrameContext consistent context) (layout.frameRegion origin)
  let localWire : FiniteEquiv
      (Fin (exactScopeWires input.frame.val origin).length)
      (Fin (exactScopeWires layout.plugRaw
        (layout.frameRegion origin)).length) :=
    FiniteEquiv.finCast
      (layout.exactScopeWires_frameRegion_length_of_ne consistent terminal
        origin away).symm
  let normalizedWire := extendWireEquiv
    (layout.mapFrameContextEquiv consistent context) localWire
  let sourceIndex := sourceChildItemIndex input.frame.val origin child parent
    sourceItemsCompiled
  let targetIndex := targetChildItemIndex layout origin child parent
    targetItemsCompiled
  let normalizedSourceIndex : Fin
      (sourceItems.castWiresEq sourceEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length sourceEq sourceItems).symm sourceIndex
  let normalizedTargetIndex : Fin
      (targetItems.castWiresEq targetEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length targetEq targetItems).symm targetIndex
  have targetKind : layout.plugRaw.regions (layout.frameRegion child) =
      .cut (layout.frameRegion origin) := by
    rw [layout.plugRegion_frameRegion, childKind]
    rfl
  let targetContextEq := layout.mapFrameContext_extend_of_ne consistent
    terminal context origin away
  let rawTargetChild : Region
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin)).length rels :=
    nested.targetBody.castWiresEq (congrArg List.length targetContextEq)
  have targetChildCompiled : compileRegion? layout.plugRaw
      targetRecurseFuel (layout.frameRegion child)
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin))
      (layout.mapFrameBinders sourceBinders) = some rawTargetChild := by
    exact compileRegion?_castContext targetContextEq
      (layout.mapFrameBinders sourceBinders) targetRecurseFuel
      nested.targetBody nested.target_compiled
  have sourceRawItem := compiledSourceCutChild_get input.frame.val origin child
    parent childKind (context.extend origin) sourceBinders sourceRecurseFuel
    sourceItems sourceItemsCompiled sourceChildBody sourceChildCompiled
  have targetRawItem := compiledMappedCutChild_get layout origin child parent
    targetKind
    ((layout.mapFrameContext consistent context).extend
      (layout.frameRegion origin))
    (layout.mapFrameBinders sourceBinders) targetRecurseFuel targetItems
    targetItemsCompiled rawTargetChild targetChildCompiled
  have sourceNormalizedItem :
      (sourceItems.castWiresEq sourceEq).get normalizedSourceIndex =
        .cut (sourceChildBody.castWiresEq sourceEq) := by
    rw [ItemSeq.get_castWiresEq]
    calc
      (sourceItems.get sourceIndex).castWiresEq sourceEq =
          (Item.cut sourceChildBody).castWiresEq sourceEq :=
        congrArg (Item.castWiresEq sourceEq) (by
          simpa only [sourceIndex] using sourceRawItem)
      _ = Item.cut (sourceChildBody.castWiresEq sourceEq) :=
        Item.castWiresEq_cut sourceEq sourceChildBody
  have targetChildCast : rawTargetChild.castWiresEq targetEq =
      nested.targetBody.castWiresEq
        (layout.mappedExtendedContext_length consistent terminal context
          origin away) := by
    simp only [rawTargetChild, Region.castWiresEq_trans]
  have targetNormalizedItem :
      (targetItems.castWiresEq targetEq).get normalizedTargetIndex =
        .cut (nested.targetBody.castWiresEq
          (layout.mappedExtendedContext_length consistent terminal context
            origin away)) := by
    rw [ItemSeq.get_castWiresEq]
    calc
      (targetItems.get targetIndex).castWiresEq targetEq =
          (Item.cut rawTargetChild).castWiresEq targetEq :=
        congrArg (Item.castWiresEq targetEq) (by
          simpa only [targetIndex] using targetRawItem)
      _ = Item.cut (rawTargetChild.castWiresEq targetEq) :=
        Item.castWiresEq_cut targetEq rawTargetChild
      _ = Item.cut (nested.targetBody.castWiresEq
          (layout.mappedExtendedContext_length consistent terminal context
            origin away)) := congrArg Item.cut targetChildCast
  let rawFrame := layout.compileAncestorSiblingFrame consistent terminal
    sourceWellFormed targetWellFormed origin child away parent childEncloses
    context sourceExact targetExact sourceBinders sourceRecurseFuel
    targetRecurseFuel sourceItems targetItems sourceItemsCompiled
    targetItemsCompiled
  have frameCommutes : normalizedWire.toFun ∘ Fin.cast sourceEq =
      Fin.cast targetEq ∘
        (layout.frameExtendedContextEquiv consistent terminal context origin
          away).toFun := by
    dsimp only [normalizedWire, localWire]
    rw [layout.extendWireEquiv_frameContext_eq consistent terminal context
      origin away]
    rfl
  let normalizedFrame := castCompilerFrame rawFrame sourceEq targetEq
    normalizedWire frameCommutes
  let nestedAlignment := nested.alignment.normalizeFrameChild layout
    consistent terminal context origin away
  let alignment := CompilerRouteAlignment.cutFrame normalizedFrame
    sourceNormalizedItem targetNormalizedItem nestedAlignment
  let sourceFocused :=
    (sourceItems.castWiresEq sourceEq).focusAt normalizedSourceIndex
  have sourceIsCut : sourceFocused.focus.item =
      .cut (sourceChildBody.castWiresEq sourceEq) :=
    sourceFocused.item_eq.trans sourceNormalizedItem
  let nestedWitness := nested.sourceWitness.castWiresEq sourceEq
  have pathHead : normalizedSourceIndex.val = index.val := by
    change sourceIndex.val = index.val
    exact congrArg Fin.val
      (sourceChildOccurrenceIndex_eq input.frame.val origin child parent
        index occurrence)
  have sourceAtIntrinsic :
      (sourceItems.castWiresEq sourceEq).focusAt? index.val =
        some sourceFocused.focus := by
    simpa only [pathHead] using sourceFocused.atIndex
  let sourceWitness : Region.ContextPath
      (finishRegion input.frame.val context origin sourceItems)
      (index.val :: path) :=
    .cut sourceFocused.focus sourceAtIntrinsic sourceIsCut nestedWitness
  have focusWires : sourceWitness.toFocus.holeWires = siteContext.length := by
    change nestedWitness.toFocus.holeWires = siteContext.length
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeWires] using
      nested.source_focus_wires
  have focusRels : sourceWitness.toFocus.holeRels = siteRels := by
    change nestedWitness.toFocus.holeRels = siteRels
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeRels] using
      nested.source_focus_rels
  have focusBody : HEq sourceWitness.toFocus.body nested.sourceSite := by
    have castBody := Region.ContextPath.castWiresEq_toFocus_body_heq
      sourceEq nested.sourceWitness
    change HEq nestedWitness.toFocus.body nested.sourceSite
    exact castBody.trans nested.source_focus_body
  exact {
    targetBody := finishRegion layout.plugRaw
      (layout.mapFrameContext consistent context)
      (layout.frameRegion origin) targetItems
    target_compiled := by
      simp only [compileRegion?]
      rw [layout.localOccurrences_frameRegion_of_ne_site origin away]
      change (compileOccurrencesWith? layout.plugRaw
        (compileRegion? layout.plugRaw targetRecurseFuel)
        ((layout.mapFrameContext consistent context).extend
          (layout.frameRegion origin))
        (layout.mapFrameBinders sourceBinders)
        ((localOccurrences input.frame.val origin).map
          layout.mapFrameOccurrence)).bind
            (fun items => some (finishRegion layout.plugRaw
              (layout.mapFrameContext consistent context)
              (layout.frameRegion origin) items)) = _
      rw [targetItemsCompiled]
      rfl
    sourceSite := nested.sourceSite
    alignment := alignment
    sourceWitness := sourceWitness
    source_focus_wires := focusWires
    source_focus_rels := focusRels
    source_focus_body := focusBody
    source_context_heq := by
      have normalizedContext :
          HEq nestedAlignment.sourceContext
            nested.alignment.sourceContext :=
        nested.alignment.normalizeFrameChild_sourceContext_heq layout
          consistent terminal context origin away
      have castWitness : HEq nestedWitness.toFocus.context
          nested.sourceWitness.toFocus.context :=
        Region.ContextPath.castWiresEq_toFocus_context_heq sourceEq
          nested.sourceWitness
      have childHeq : HEq nestedAlignment.sourceContext
          nestedWitness.toFocus.context :=
        normalizedContext.trans
          (nested.source_context_heq.trans castWitness.symm)
      let normalizedNestedContext := castRouteFocusContext focusWires
        focusRels nestedWitness.toFocus.context
      have normalizedNestedHeq : HEq normalizedNestedContext
          nestedWitness.toFocus.context :=
        castRouteFocusContext_heq focusWires focusRels
          nestedWitness.toFocus.context
      have childEq : nestedAlignment.sourceContext =
          normalizedNestedContext :=
        eq_of_heq (childHeq.trans normalizedNestedHeq.symm)
      have parentEq : alignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            sourceWitness.toFocus.context := by
        change DiagramContext.cut _ sourceFocused.focus.before
            sourceFocused.focus.after nestedAlignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            (DiagramContext.cut _ sourceFocused.focus.before
              sourceFocused.focus.after nestedWitness.toFocus.context)
        rw [castRouteFocusContext_cut, childEq]
      exact (heq_of_eq parentEq).trans
        (castRouteFocusContext_heq focusWires focusRels
          sourceWitness.toFocus.context)
  }

/-- GREEN bubble-step assembler for the mapped-route construction. -/
private noncomputable def mappedRegionBubbleStep
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    {origin child : Fin input.frame.val.regionCount}
    (away : origin ≠ input.site)
    (parent : (input.frame.val.regions child).parent? = some origin)
    (childKind : input.frame.val.regions child = .bubble origin arity)
    (childEncloses : input.frame.val.Encloses child input.site)
    (index : Fin (localOccurrences input.frame.val origin).length)
    (occurrence : (localOccurrences input.frame.val origin).get index =
      .child child)
    {context siteContext : WireContext input.frame.val}
    {rels : RelCtx} (sourceBinders : BinderContext input.frame.val rels)
    (sourceExact : (context.extend origin).Exact origin)
    (targetExact : ((layout.mapFrameContext consistent context).extend
      (layout.frameRegion origin)).Exact (layout.frameRegion origin))
    (sourceRecurseFuel targetRecurseFuel : Nat)
    (sourceItems : ItemSeq (context.extend origin).length rels)
    (targetItems : ItemSeq
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin)).length rels)
    (sourceItemsCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val sourceRecurseFuel)
      (context.extend origin) sourceBinders
      (localOccurrences input.frame.val origin) = some sourceItems)
    (targetItemsCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetRecurseFuel)
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin))
      (layout.mapFrameBinders sourceBinders)
      ((localOccurrences input.frame.val origin).map
        layout.mapFrameOccurrence) = some targetItems)
    (sourceChildBody : Region (context.extend origin).length
      (arity :: rels))
    (sourceChildCompiled : compileRegion? input.frame.val sourceRecurseFuel
      child (context.extend origin) (sourceBinders.push child arity) =
        some sourceChildBody)
    {siteRels : RelCtx}
    {targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels}
    {path : List Nat}
    (nested : MappedRegionRouteResult layout consistent child
      (context.extend origin) siteContext (sourceBinders.push child arity)
      path targetRecurseFuel sourceChildBody targetSite) :
    MappedRegionRouteResult layout consistent origin context siteContext
      sourceBinders (index.val :: path) (targetRecurseFuel + 1)
      (finishRegion input.frame.val context origin sourceItems) targetSite := by
  let sourceEq := WireContext.length_extend context origin
  let targetEq := WireContext.length_extend
    (layout.mapFrameContext consistent context) (layout.frameRegion origin)
  let localWire : FiniteEquiv
      (Fin (exactScopeWires input.frame.val origin).length)
      (Fin (exactScopeWires layout.plugRaw
        (layout.frameRegion origin)).length) :=
    FiniteEquiv.finCast
      (layout.exactScopeWires_frameRegion_length_of_ne consistent terminal
        origin away).symm
  let normalizedWire := extendWireEquiv
    (layout.mapFrameContextEquiv consistent context) localWire
  let sourceIndex := sourceChildItemIndex input.frame.val origin child parent
    sourceItemsCompiled
  let targetIndex := targetChildItemIndex layout origin child parent
    targetItemsCompiled
  let normalizedSourceIndex : Fin
      (sourceItems.castWiresEq sourceEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length sourceEq sourceItems).symm sourceIndex
  let normalizedTargetIndex : Fin
      (targetItems.castWiresEq targetEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length targetEq targetItems).symm targetIndex
  have targetKind : layout.plugRaw.regions (layout.frameRegion child) =
      .bubble (layout.frameRegion origin) arity := by
    rw [layout.plugRegion_frameRegion, childKind]
    rfl
  let targetContextEq := layout.mapFrameContext_extend_of_ne consistent
    terminal context origin away
  let rawTargetChild : Region
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin)).length (arity :: rels) :=
    nested.targetBody.castWiresEq (congrArg List.length targetContextEq)
  have targetChildCompiled : compileRegion? layout.plugRaw
      targetRecurseFuel (layout.frameRegion child)
      ((layout.mapFrameContext consistent context).extend
        (layout.frameRegion origin))
      ((layout.mapFrameBinders sourceBinders).push
        (layout.frameRegion child) arity) = some rawTargetChild := by
    have casted := compileRegion?_castContext targetContextEq
      (layout.mapFrameBinders (sourceBinders.push child arity))
      targetRecurseFuel nested.targetBody nested.target_compiled
    simpa only [layout.mapFrameBinders_push] using casted
  have sourceRawItem := compiledSourceBubbleChild_get input.frame.val origin
    child parent childKind (context.extend origin) sourceBinders
    sourceRecurseFuel sourceItems sourceItemsCompiled sourceChildBody
    sourceChildCompiled
  have targetRawItem := compiledMappedBubbleChild_get layout origin child parent
    targetKind
    ((layout.mapFrameContext consistent context).extend
      (layout.frameRegion origin))
    (layout.mapFrameBinders sourceBinders) targetRecurseFuel targetItems
    targetItemsCompiled rawTargetChild targetChildCompiled
  have sourceNormalizedItem :
      (sourceItems.castWiresEq sourceEq).get normalizedSourceIndex =
        .bubble arity (sourceChildBody.castWiresEq sourceEq) := by
    rw [ItemSeq.get_castWiresEq]
    change (sourceItems.get sourceIndex).castWiresEq sourceEq = _
    rw [sourceRawItem, Item.castWiresEq_bubble]
  have targetChildCast : rawTargetChild.castWiresEq targetEq =
      nested.targetBody.castWiresEq
        (layout.mappedExtendedContext_length consistent terminal context
          origin away) := by
    simp only [rawTargetChild, Region.castWiresEq_trans]
  have targetNormalizedItem :
      (targetItems.castWiresEq targetEq).get normalizedTargetIndex =
        .bubble arity (nested.targetBody.castWiresEq
          (layout.mappedExtendedContext_length consistent terminal context
            origin away)) := by
    rw [ItemSeq.get_castWiresEq]
    change (targetItems.get targetIndex).castWiresEq targetEq = _
    rw [targetRawItem, Item.castWiresEq_bubble, targetChildCast]
  let rawFrame := layout.compileAncestorSiblingFrame consistent terminal
    sourceWellFormed targetWellFormed origin child away parent childEncloses
    context sourceExact targetExact sourceBinders sourceRecurseFuel
    targetRecurseFuel sourceItems targetItems sourceItemsCompiled
    targetItemsCompiled
  have frameCommutes : normalizedWire.toFun ∘ Fin.cast sourceEq =
      Fin.cast targetEq ∘
        (layout.frameExtendedContextEquiv consistent terminal context origin
          away).toFun := by
    dsimp only [normalizedWire, localWire]
    rw [layout.extendWireEquiv_frameContext_eq consistent terminal context
      origin away]
    rfl
  let normalizedFrame := castCompilerFrame rawFrame sourceEq targetEq
    normalizedWire frameCommutes
  let nestedAlignment := nested.alignment.normalizeFrameChild layout
    consistent terminal context origin away
  let alignment := CompilerRouteAlignment.bubbleFrame normalizedFrame
    sourceNormalizedItem targetNormalizedItem nestedAlignment
  let sourceFocused :=
    (sourceItems.castWiresEq sourceEq).focusAt normalizedSourceIndex
  have sourceIsBubble : sourceFocused.focus.item =
      .bubble arity (sourceChildBody.castWiresEq sourceEq) :=
    sourceFocused.item_eq.trans sourceNormalizedItem
  let nestedWitness := nested.sourceWitness.castWiresEq sourceEq
  have pathHead : normalizedSourceIndex.val = index.val := by
    change sourceIndex.val = index.val
    exact congrArg Fin.val
      (sourceChildOccurrenceIndex_eq input.frame.val origin child parent
        index occurrence)
  have sourceAtIntrinsic :
      (sourceItems.castWiresEq sourceEq).focusAt? index.val =
        some sourceFocused.focus := by
    simpa only [pathHead] using sourceFocused.atIndex
  let sourceWitness : Region.ContextPath
      (finishRegion input.frame.val context origin sourceItems)
      (index.val :: path) :=
    .bubble sourceFocused.focus sourceAtIntrinsic sourceIsBubble nestedWitness
  have focusWires : sourceWitness.toFocus.holeWires = siteContext.length := by
    change nestedWitness.toFocus.holeWires = siteContext.length
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeWires] using
      nested.source_focus_wires
  have focusRels : sourceWitness.toFocus.holeRels = siteRels := by
    change nestedWitness.toFocus.holeRels = siteRels
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeRels] using
      nested.source_focus_rels
  have focusBody : HEq sourceWitness.toFocus.body nested.sourceSite := by
    have castBody := Region.ContextPath.castWiresEq_toFocus_body_heq
      sourceEq nested.sourceWitness
    change HEq nestedWitness.toFocus.body nested.sourceSite
    exact castBody.trans nested.source_focus_body
  exact {
    targetBody := finishRegion layout.plugRaw
      (layout.mapFrameContext consistent context)
      (layout.frameRegion origin) targetItems
    target_compiled := by
      simp only [compileRegion?]
      rw [layout.localOccurrences_frameRegion_of_ne_site origin away]
      change (compileOccurrencesWith? layout.plugRaw
        (compileRegion? layout.plugRaw targetRecurseFuel)
        ((layout.mapFrameContext consistent context).extend
          (layout.frameRegion origin))
        (layout.mapFrameBinders sourceBinders)
        ((localOccurrences input.frame.val origin).map
          layout.mapFrameOccurrence)).bind
            (fun items => some (finishRegion layout.plugRaw
              (layout.mapFrameContext consistent context)
              (layout.frameRegion origin) items)) = _
      rw [targetItemsCompiled]
      rfl
    sourceSite := nested.sourceSite
    alignment := alignment
    sourceWitness := sourceWitness
    source_focus_wires := focusWires
    source_focus_rels := focusRels
    source_focus_body := focusBody
    source_context_heq := by
      have normalizedContext :
          HEq nestedAlignment.sourceContext
            nested.alignment.sourceContext :=
        nested.alignment.normalizeFrameChild_sourceContext_heq layout
          consistent terminal context origin away
      have castWitness : HEq nestedWitness.toFocus.context
          nested.sourceWitness.toFocus.context :=
        Region.ContextPath.castWiresEq_toFocus_context_heq sourceEq
          nested.sourceWitness
      have childHeq : HEq nestedAlignment.sourceContext
          nestedWitness.toFocus.context :=
        normalizedContext.trans
          (nested.source_context_heq.trans castWitness.symm)
      let normalizedNestedContext := castRouteFocusContext focusWires
        focusRels nestedWitness.toFocus.context
      have normalizedNestedHeq : HEq normalizedNestedContext
          nestedWitness.toFocus.context :=
        castRouteFocusContext_heq focusWires focusRels
          nestedWitness.toFocus.context
      have childEq : nestedAlignment.sourceContext =
          normalizedNestedContext :=
        eq_of_heq (childHeq.trans normalizedNestedHeq.symm)
      have parentEq : alignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            sourceWitness.toFocus.context := by
        change DiagramContext.bubble _ sourceFocused.focus.before
            sourceFocused.focus.after _ nestedAlignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            (DiagramContext.bubble _ sourceFocused.focus.before
              sourceFocused.focus.after _ nestedWitness.toFocus.context)
        rw [castRouteFocusContext_bubble, childEq]
      exact (heq_of_eq parentEq).trans
        (castRouteFocusContext_heq focusWires focusRels
          sourceWitness.toFocus.context)
  }

/-- GREEN cut-step assembler from a proper root child to the generated open
root. -/
private noncomputable def mappedOpenCutStep
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (sourceWellFormed : (frameOpen input boundary).WellFormed)
    (targetWellFormed : (layout.outputOpenRoot input boundary).WellFormed)
    {child : Fin input.frame.val.regionCount}
    (away : input.frame.val.root ≠ input.site)
    (parent : (input.frame.val.regions child).parent? =
      some input.frame.val.root)
    (childKind : input.frame.val.regions child =
      .cut input.frame.val.root)
    (childEncloses : input.frame.val.Encloses child input.site)
    (index : Fin
      (localOccurrences input.frame.val input.frame.val.root).length)
    (occurrence :
      (localOccurrences input.frame.val input.frame.val.root).get index =
        .child child)
    {siteContext : WireContext input.frame.val}
    (sourceItems : ItemSeq
      (frameOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq
      (layout.outputOpenRoot input boundary).rootWires.length [])
    (sourceItemsCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val input.frame.val.regionCount)
      (frameOpen input boundary).rootWires BinderContext.empty
      (localOccurrences input.frame.val input.frame.val.root) =
        some sourceItems)
    (targetItemsCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
      (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
      ((localOccurrences input.frame.val input.frame.val.root).map
        layout.mapFrameOccurrence) = some targetItems)
    (sourceChildBody : Region
      (frameOpen input boundary).rootWires.length [])
    (sourceChildCompiled : compileRegion? input.frame.val
      input.frame.val.regionCount child
      (frameOpen input boundary).rootWires BinderContext.empty =
        some sourceChildBody)
    {siteRels : RelCtx}
    {targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels}
    {path : List Nat}
    (nested : MappedRegionRouteResult layout consistent child
      (frameOpen input boundary).rootWires siteContext BinderContext.empty
      path layout.plugRaw.regionCount sourceChildBody targetSite) :
    MappedOpenRouteResult layout consistent boundary siteContext
      (index.val :: path)
      (finishRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires sourceItems) targetSite := by
  let sourceEq : (frameOpen input boundary).rootWires.length =
      (frameOpen input boundary).exposedWires.length +
        (frameOpen input boundary).hiddenWires.length := by
    simp [OpenDiagram.rootWires]
  let targetEq :
      (layout.outputOpenRoot input boundary).rootWires.length =
        (layout.outputOpenRoot input boundary).exposedWires.length +
          (layout.outputOpenRoot input boundary).hiddenWires.length := by
    simp [OpenDiagram.rootWires]
  let localWire :=
    layout.outputHiddenEquiv_of_ne consistent terminal boundary away
  let normalizedWire := extendWireEquiv
    (layout.outputExternalEquiv consistent boundary) localWire
  let sourceIndex := sourceChildItemIndex input.frame.val
    input.frame.val.root child parent sourceItemsCompiled
  let targetIndex := targetChildItemIndex layout input.frame.val.root child
    parent targetItemsCompiled
  let normalizedSourceIndex : Fin
      (sourceItems.castWiresEq sourceEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length sourceEq sourceItems).symm sourceIndex
  let normalizedTargetIndex : Fin
      (targetItems.castWiresEq targetEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length targetEq targetItems).symm targetIndex
  have targetKind : layout.plugRaw.regions (layout.frameRegion child) =
      .cut layout.plugRaw.root := by
    rw [layout.plugRegion_frameRegion, childKind]
    rfl
  have targetContextEq :
      layout.mapFrameContext consistent
          (frameOpen input boundary).rootWires =
        (layout.outputOpenRoot input boundary).rootWires := by
    symm
    simpa only [mapFrameContext, if_neg away, List.append_nil] using
      layout.outputOpenRoot_rootWires consistent terminal boundary
  let rawTargetChild : Region
      (layout.outputOpenRoot input boundary).rootWires.length [] :=
    nested.targetBody.castWiresEq (congrArg List.length targetContextEq)
  have targetChildCompiled : compileRegion? layout.plugRaw
      layout.plugRaw.regionCount (layout.frameRegion child)
      (layout.outputOpenRoot input boundary).rootWires BinderContext.empty =
        some rawTargetChild := by
    have casted := compileRegion?_castContext targetContextEq
      (layout.mapFrameBinders
        (BinderContext.empty : BinderContext input.frame.val []))
      layout.plugRaw.regionCount nested.targetBody nested.target_compiled
    rw [mapFrameBinders_empty] at casted
    exact casted
  have sourceRawItem := compiledSourceCutChild_get input.frame.val
    input.frame.val.root child parent childKind
    (frameOpen input boundary).rootWires BinderContext.empty
    input.frame.val.regionCount sourceItems sourceItemsCompiled sourceChildBody
    sourceChildCompiled
  have targetRawItem := compiledMappedCutChild_get layout
    input.frame.val.root child parent targetKind
    (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
    layout.plugRaw.regionCount targetItems targetItemsCompiled rawTargetChild
    targetChildCompiled
  have sourceNormalizedItem :
      (sourceItems.castWiresEq sourceEq).get normalizedSourceIndex =
        .cut (sourceChildBody.castWiresEq sourceEq) := by
    rw [ItemSeq.get_castWiresEq]
    calc
      (sourceItems.get sourceIndex).castWiresEq sourceEq =
          (Item.cut sourceChildBody).castWiresEq sourceEq :=
        congrArg (Item.castWiresEq sourceEq) (by
          simpa only [sourceIndex] using sourceRawItem)
      _ = Item.cut (sourceChildBody.castWiresEq sourceEq) :=
        Item.castWiresEq_cut sourceEq sourceChildBody
  have targetChildCast : rawTargetChild.castWiresEq targetEq =
      nested.targetBody.castWiresEq
        (layout.mappedOpenRootContext_length_of_ne consistent terminal
          boundary away) := by
    simp only [rawTargetChild, Region.castWiresEq_trans]
    exact Region.castWiresEq_proof_irrel _ _ nested.targetBody
  have targetNormalizedItem :
      (targetItems.castWiresEq targetEq).get normalizedTargetIndex =
        .cut (nested.targetBody.castWiresEq
          (layout.mappedOpenRootContext_length_of_ne consistent terminal
            boundary away)) := by
    rw [ItemSeq.get_castWiresEq]
    calc
      (targetItems.get targetIndex).castWiresEq targetEq =
          (Item.cut rawTargetChild).castWiresEq targetEq :=
        congrArg (Item.castWiresEq targetEq) (by
          simpa only [targetIndex] using targetRawItem)
      _ = Item.cut (rawTargetChild.castWiresEq targetEq) :=
        Item.castWiresEq_cut targetEq rawTargetChild
      _ = Item.cut (nested.targetBody.castWiresEq
          (layout.mappedOpenRootContext_length_of_ne consistent terminal
            boundary away)) := congrArg Item.cut targetChildCast
  let rawFrame := layout.compileOpenRootSiblingFrame consistent terminal
    boundary sourceWellFormed targetWellFormed child away parent childEncloses
    sourceItems targetItems sourceItemsCompiled targetItemsCompiled
  have frameCommutes : normalizedWire.toFun ∘ Fin.cast sourceEq =
      Fin.cast targetEq ∘
        (layout.outputRootContextEquiv_of_ne consistent terminal boundary
          away).toFun := by
    dsimp only [normalizedWire, localWire]
    rw [layout.outputRootContextEquiv_of_ne_eq consistent terminal boundary
      away]
    rfl
  let normalizedFrame := castCompilerFrame rawFrame sourceEq targetEq
    normalizedWire frameCommutes
  let nestedAlignment := nested.alignment.normalizeOpenRootChild layout
    consistent terminal boundary away
  let alignment := CompilerRouteAlignment.cutFrame normalizedFrame
    sourceNormalizedItem targetNormalizedItem nestedAlignment
  let sourceFocused :=
    (sourceItems.castWiresEq sourceEq).focusAt normalizedSourceIndex
  have sourceIsCut : sourceFocused.focus.item =
      .cut (sourceChildBody.castWiresEq sourceEq) :=
    sourceFocused.item_eq.trans sourceNormalizedItem
  let nestedWitness := nested.sourceWitness.castWiresEq sourceEq
  have pathHead : normalizedSourceIndex.val = index.val := by
    change sourceIndex.val = index.val
    exact congrArg Fin.val
      (sourceChildOccurrenceIndex_eq input.frame.val input.frame.val.root child
        parent index occurrence)
  have sourceAtIntrinsic :
      (sourceItems.castWiresEq sourceEq).focusAt? index.val =
        some sourceFocused.focus := by
    simpa only [pathHead] using sourceFocused.atIndex
  let sourceWitness : Region.ContextPath
      (finishRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires sourceItems)
      (index.val :: path) :=
    .cut sourceFocused.focus sourceAtIntrinsic sourceIsCut nestedWitness
  have focusWires : sourceWitness.toFocus.holeWires = siteContext.length := by
    change nestedWitness.toFocus.holeWires = siteContext.length
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeWires] using
      nested.source_focus_wires
  have focusRels : sourceWitness.toFocus.holeRels = siteRels := by
    change nestedWitness.toFocus.holeRels = siteRels
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeRels] using
      nested.source_focus_rels
  have focusBody : HEq sourceWitness.toFocus.body nested.sourceSite := by
    have castBody := Region.ContextPath.castWiresEq_toFocus_body_heq
      sourceEq nested.sourceWitness
    change HEq nestedWitness.toFocus.body nested.sourceSite
    exact castBody.trans nested.source_focus_body
  exact {
    targetBody := finishRoot
      (layout.outputOpenRoot input boundary).exposedWires
      (layout.outputOpenRoot input boundary).hiddenWires targetItems
    target_compiled := by
      simp only [compileRoot?]
      change (compileOccurrencesWith? layout.plugRaw
        (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
        (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
        (localOccurrences layout.plugRaw
          (layout.frameRegion input.frame.val.root))).bind
          (fun items => some (finishRoot
            (layout.outputOpenRoot input boundary).exposedWires
            (layout.outputOpenRoot input boundary).hiddenWires items)) = _
      rw [layout.localOccurrences_frameRegion_of_ne_site
        input.frame.val.root away]
      exact (congrArg
        (fun result => result.bind (fun items => some (finishRoot
          (layout.outputOpenRoot input boundary).exposedWires
          (layout.outputOpenRoot input boundary).hiddenWires items)))
        targetItemsCompiled).trans rfl
    sourceSite := nested.sourceSite
    alignment := alignment
    sourceWitness := sourceWitness
    source_focus_wires := focusWires
    source_focus_rels := focusRels
    source_focus_body := focusBody
    source_context_heq := by
      have normalizedContext :
          HEq nestedAlignment.sourceContext
            nested.alignment.sourceContext :=
        nested.alignment.normalizeOpenRootChild_sourceContext_heq layout
          consistent terminal boundary away
      have castWitness : HEq nestedWitness.toFocus.context
          nested.sourceWitness.toFocus.context :=
        Region.ContextPath.castWiresEq_toFocus_context_heq sourceEq
          nested.sourceWitness
      have childHeq : HEq nestedAlignment.sourceContext
          nestedWitness.toFocus.context :=
        normalizedContext.trans
          (nested.source_context_heq.trans castWitness.symm)
      let normalizedNestedContext := castRouteFocusContext focusWires
        focusRels nestedWitness.toFocus.context
      have normalizedNestedHeq : HEq normalizedNestedContext
          nestedWitness.toFocus.context :=
        castRouteFocusContext_heq focusWires focusRels
          nestedWitness.toFocus.context
      have childEq : nestedAlignment.sourceContext =
          normalizedNestedContext :=
        eq_of_heq (childHeq.trans normalizedNestedHeq.symm)
      have parentEq : alignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            sourceWitness.toFocus.context := by
        change DiagramContext.cut _ sourceFocused.focus.before
            sourceFocused.focus.after nestedAlignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            (DiagramContext.cut _ sourceFocused.focus.before
              sourceFocused.focus.after nestedWitness.toFocus.context)
        rw [castRouteFocusContext_cut, childEq]
      exact (heq_of_eq parentEq).trans
        (castRouteFocusContext_heq focusWires focusRels
          sourceWitness.toFocus.context)
  }

/-- GREEN bubble-step assembler from a proper root child to the generated
open root. -/
private noncomputable def mappedOpenBubbleStep
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (sourceWellFormed : (frameOpen input boundary).WellFormed)
    (targetWellFormed : (layout.outputOpenRoot input boundary).WellFormed)
    {child : Fin input.frame.val.regionCount}
    (away : input.frame.val.root ≠ input.site)
    (parent : (input.frame.val.regions child).parent? =
      some input.frame.val.root)
    (childKind : input.frame.val.regions child =
      .bubble input.frame.val.root arity)
    (childEncloses : input.frame.val.Encloses child input.site)
    (index : Fin
      (localOccurrences input.frame.val input.frame.val.root).length)
    (occurrence :
      (localOccurrences input.frame.val input.frame.val.root).get index =
        .child child)
    {siteContext : WireContext input.frame.val}
    (sourceItems : ItemSeq
      (frameOpen input boundary).rootWires.length [])
    (targetItems : ItemSeq
      (layout.outputOpenRoot input boundary).rootWires.length [])
    (sourceItemsCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val input.frame.val.regionCount)
      (frameOpen input boundary).rootWires BinderContext.empty
      (localOccurrences input.frame.val input.frame.val.root) =
        some sourceItems)
    (targetItemsCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
      (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
      ((localOccurrences input.frame.val input.frame.val.root).map
        layout.mapFrameOccurrence) = some targetItems)
    (sourceChildBody : Region
      (frameOpen input boundary).rootWires.length [arity])
    (sourceChildCompiled : compileRegion? input.frame.val
      input.frame.val.regionCount child
      (frameOpen input boundary).rootWires
      (BinderContext.empty.push child arity) = some sourceChildBody)
    {siteRels : RelCtx}
    {targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels}
    {path : List Nat}
    (nested : MappedRegionRouteResult layout consistent child
      (frameOpen input boundary).rootWires siteContext
      (BinderContext.empty.push child arity) path
      layout.plugRaw.regionCount sourceChildBody targetSite) :
    MappedOpenRouteResult layout consistent boundary siteContext
      (index.val :: path)
      (finishRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires sourceItems) targetSite := by
  let sourceEq := openRootWires_length (frameOpen input boundary)
  let targetEq := openRootWires_length
    (layout.outputOpenRoot input boundary)
  let localWire :=
    layout.outputHiddenEquiv_of_ne consistent terminal boundary away
  let normalizedWire := extendWireEquiv
    (layout.outputExternalEquiv consistent boundary) localWire
  let sourceIndex := sourceChildItemIndex input.frame.val
    input.frame.val.root child parent sourceItemsCompiled
  let targetIndex := targetChildItemIndex layout input.frame.val.root child
    parent targetItemsCompiled
  let normalizedSourceIndex : Fin
      (sourceItems.castWiresEq sourceEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length sourceEq sourceItems).symm sourceIndex
  let normalizedTargetIndex : Fin
      (targetItems.castWiresEq targetEq).length :=
    Fin.cast (ItemSeq.castWiresEq_length targetEq targetItems).symm targetIndex
  have targetKind : layout.plugRaw.regions (layout.frameRegion child) =
      .bubble layout.plugRaw.root arity := by
    rw [layout.plugRegion_frameRegion, childKind]
    rfl
  have targetContextEq :
      layout.mapFrameContext consistent
          (frameOpen input boundary).rootWires =
        (layout.outputOpenRoot input boundary).rootWires := by
    symm
    simpa only [mapFrameContext, if_neg away, List.append_nil] using
      layout.outputOpenRoot_rootWires consistent terminal boundary
  let rawTargetChild : Region
      (layout.outputOpenRoot input boundary).rootWires.length [arity] :=
    nested.targetBody.castWiresEq (congrArg List.length targetContextEq)
  have targetChildCompiled : compileRegion? layout.plugRaw
      layout.plugRaw.regionCount (layout.frameRegion child)
      (layout.outputOpenRoot input boundary).rootWires
      (BinderContext.empty.push (layout.frameRegion child) arity) =
        some rawTargetChild := by
    have casted := compileRegion?_castContext targetContextEq
      (layout.mapFrameBinders
        ((BinderContext.empty : BinderContext input.frame.val []).push
          child arity))
      layout.plugRaw.regionCount nested.targetBody nested.target_compiled
    rw [← layout.mapFrameBinders_push] at casted
    rw [mapFrameBinders_empty] at casted
    exact casted
  have sourceRawItem := compiledSourceBubbleChild_get input.frame.val
    input.frame.val.root child parent childKind
    (frameOpen input boundary).rootWires BinderContext.empty
    input.frame.val.regionCount sourceItems sourceItemsCompiled sourceChildBody
    sourceChildCompiled
  have targetRawItem := compiledMappedBubbleChild_get layout
    input.frame.val.root child parent targetKind
    (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
    layout.plugRaw.regionCount targetItems targetItemsCompiled rawTargetChild
    targetChildCompiled
  have sourceNormalizedItem :
      (sourceItems.castWiresEq sourceEq).get normalizedSourceIndex =
        .bubble arity (sourceChildBody.castWiresEq sourceEq) := by
    rw [ItemSeq.get_castWiresEq]
    calc
      (sourceItems.get sourceIndex).castWiresEq sourceEq =
          (Item.bubble arity sourceChildBody).castWiresEq sourceEq :=
        congrArg (Item.castWiresEq sourceEq) (by
          simpa only [sourceIndex] using sourceRawItem)
      _ = Item.bubble arity (sourceChildBody.castWiresEq sourceEq) :=
        Item.castWiresEq_bubble sourceEq arity sourceChildBody
  have targetChildCast : rawTargetChild.castWiresEq targetEq =
      nested.targetBody.castWiresEq
        (layout.mappedOpenRootContext_length_of_ne consistent terminal
          boundary away) := by
    simp only [rawTargetChild, Region.castWiresEq_trans]
    exact Region.castWiresEq_proof_irrel _ _ nested.targetBody
  have targetNormalizedItem :
      (targetItems.castWiresEq targetEq).get normalizedTargetIndex =
        .bubble arity (nested.targetBody.castWiresEq
          (layout.mappedOpenRootContext_length_of_ne consistent terminal
            boundary away)) := by
    rw [ItemSeq.get_castWiresEq]
    calc
      (targetItems.get targetIndex).castWiresEq targetEq =
          (Item.bubble arity rawTargetChild).castWiresEq targetEq :=
        congrArg (Item.castWiresEq targetEq) (by
          simpa only [targetIndex] using targetRawItem)
      _ = Item.bubble arity (rawTargetChild.castWiresEq targetEq) :=
        Item.castWiresEq_bubble targetEq arity rawTargetChild
      _ = Item.bubble arity (nested.targetBody.castWiresEq
          (layout.mappedOpenRootContext_length_of_ne consistent terminal
            boundary away)) := congrArg (Item.bubble arity) targetChildCast
  let rawFrame := layout.compileOpenRootSiblingFrame consistent terminal
    boundary sourceWellFormed targetWellFormed child away parent childEncloses
    sourceItems targetItems sourceItemsCompiled targetItemsCompiled
  have frameCommutes : normalizedWire.toFun ∘ Fin.cast sourceEq =
      Fin.cast targetEq ∘
        (layout.outputRootContextEquiv_of_ne consistent terminal boundary
          away).toFun := by
    dsimp only [normalizedWire, localWire]
    rw [layout.outputRootContextEquiv_of_ne_eq consistent terminal boundary
      away]
    rfl
  let normalizedFrame := castCompilerFrame rawFrame sourceEq targetEq
    normalizedWire frameCommutes
  let nestedAlignment := nested.alignment.normalizeOpenRootChild layout
    consistent terminal boundary away
  let alignment := CompilerRouteAlignment.bubbleFrame normalizedFrame
    sourceNormalizedItem targetNormalizedItem nestedAlignment
  let sourceFocused :=
    (sourceItems.castWiresEq sourceEq).focusAt normalizedSourceIndex
  have sourceIsBubble : sourceFocused.focus.item =
      .bubble arity (sourceChildBody.castWiresEq sourceEq) :=
    sourceFocused.item_eq.trans sourceNormalizedItem
  let nestedWitness := nested.sourceWitness.castWiresEq sourceEq
  have pathHead : normalizedSourceIndex.val = index.val := by
    change sourceIndex.val = index.val
    exact congrArg Fin.val
      (sourceChildOccurrenceIndex_eq input.frame.val input.frame.val.root child
        parent index occurrence)
  have sourceAtIntrinsic :
      (sourceItems.castWiresEq sourceEq).focusAt? index.val =
        some sourceFocused.focus := by
    simpa only [pathHead] using sourceFocused.atIndex
  let sourceWitness : Region.ContextPath
      (finishRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires sourceItems)
      (index.val :: path) :=
    .bubble sourceFocused.focus sourceAtIntrinsic sourceIsBubble nestedWitness
  have focusWires : sourceWitness.toFocus.holeWires = siteContext.length := by
    change nestedWitness.toFocus.holeWires = siteContext.length
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeWires] using
      nested.source_focus_wires
  have focusRels : sourceWitness.toFocus.holeRels = siteRels := by
    change nestedWitness.toFocus.holeRels = siteRels
    simpa only [nestedWitness,
      Region.ContextPath.castWiresEq_toFocus_holeRels] using
      nested.source_focus_rels
  have focusBody : HEq sourceWitness.toFocus.body nested.sourceSite := by
    have castBody := Region.ContextPath.castWiresEq_toFocus_body_heq
      sourceEq nested.sourceWitness
    change HEq nestedWitness.toFocus.body nested.sourceSite
    exact castBody.trans nested.source_focus_body
  exact {
    targetBody := finishRoot
      (layout.outputOpenRoot input boundary).exposedWires
      (layout.outputOpenRoot input boundary).hiddenWires targetItems
    target_compiled := by
      simp only [compileRoot?]
      change (compileOccurrencesWith? layout.plugRaw
        (compileRegion? layout.plugRaw layout.plugRaw.regionCount)
        (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
        (localOccurrences layout.plugRaw
          (layout.frameRegion input.frame.val.root))).bind
          (fun items => some (finishRoot
            (layout.outputOpenRoot input boundary).exposedWires
            (layout.outputOpenRoot input boundary).hiddenWires items)) = _
      rw [layout.localOccurrences_frameRegion_of_ne_site
        input.frame.val.root away]
      exact (congrArg
        (fun result => result.bind (fun items => some (finishRoot
          (layout.outputOpenRoot input boundary).exposedWires
          (layout.outputOpenRoot input boundary).hiddenWires items)))
        targetItemsCompiled).trans rfl
    sourceSite := nested.sourceSite
    alignment := alignment
    sourceWitness := sourceWitness
    source_focus_wires := focusWires
    source_focus_rels := focusRels
    source_focus_body := focusBody
    source_context_heq := by
      have normalizedContext :
          HEq nestedAlignment.sourceContext
            nested.alignment.sourceContext :=
        nested.alignment.normalizeOpenRootChild_sourceContext_heq layout
          consistent terminal boundary away
      have castWitness : HEq nestedWitness.toFocus.context
          nested.sourceWitness.toFocus.context :=
        Region.ContextPath.castWiresEq_toFocus_context_heq sourceEq
          nested.sourceWitness
      have childHeq : HEq nestedAlignment.sourceContext
          nestedWitness.toFocus.context :=
        normalizedContext.trans
          (nested.source_context_heq.trans castWitness.symm)
      let normalizedNestedContext := castRouteFocusContext focusWires
        focusRels nestedWitness.toFocus.context
      have normalizedNestedHeq : HEq normalizedNestedContext
          nestedWitness.toFocus.context :=
        castRouteFocusContext_heq focusWires focusRels
          nestedWitness.toFocus.context
      have childEq : nestedAlignment.sourceContext =
          normalizedNestedContext :=
        eq_of_heq (childHeq.trans normalizedNestedHeq.symm)
      have parentEq : alignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            sourceWitness.toFocus.context := by
        change DiagramContext.bubble _ sourceFocused.focus.before
            sourceFocused.focus.after _ nestedAlignment.sourceContext =
          castRouteFocusContext focusWires focusRels
            (DiagramContext.bubble _ sourceFocused.focus.before
              sourceFocused.focus.after _ nestedWitness.toFocus.context)
        rw [castRouteFocusContext_bubble, childEq]
      exact (heq_of_eq parentEq).trans
        (castRouteFocusContext_heq focusWires focusRels
          sourceWitness.toFocus.context)
  }

/-- Compile the deterministically mapped target route bottom-up from one
successful source region call.  The terminal target call is supplied at the
fuel obtained by subtracting exactly the retained source-route depth. -/
noncomputable def compileMappedRegionRoute
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    {origin : Fin input.frame.val.regionCount}
    {context siteContext : WireContext input.frame.val}
    {rels siteRels : RelCtx}
    {sourceBinders : BinderContext input.frame.val rels}
    {siteBinders : BinderContext input.frame.val siteRels}
    {path : List Nat}
    {route : ConcreteCompilerRoute input.frame.val
      (.region origin context) input.site siteContext}
    (derivation : route.Derivation sourceBinders path siteBinders)
    (sourceExact : (context.extend origin).Exact origin)
    (targetExact : ((layout.mapFrameContext consistent context).extend
      (layout.frameRegion origin)).Exact (layout.frameRegion origin))
    (sourceCovers : sourceBinders.Covers origin)
    (sourceFuel targetDepth targetFuel : Nat)
    (targetClimb : layout.plugRaw.climb targetDepth
      (layout.frameRegion origin) = some layout.plugRaw.root)
    (targetEnough : targetDepth + targetFuel =
      layout.plugRaw.regionCount + 1)
    (sourceBody : Region context.length rels)
    (sourceCompiled : compileRegion? input.frame.val sourceFuel origin
      context sourceBinders = some sourceBody)
    {targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels}
    (siteTarget : ExplicitMappedSite layout consistent siteContext siteBinders
      (targetFuel - route.depth) targetSite) :
    MappedRegionRouteResult layout consistent origin context siteContext
      sourceBinders path targetFuel sourceBody targetSite := by
  cases derivation with
  | regionHere =>
      have siteTarget' : ExplicitMappedSite layout consistent context
          sourceBinders
          targetFuel targetSite := by
        simpa [ConcreteCompilerRoute.depth] using siteTarget
      exact mappedRegionHere layout consistent context sourceBinders targetFuel
        sourceBody siteTarget'
  | @regionStepCut _ child _ _ _ _ _ parent childKind index occurrence
      _ _ _ nestedRoute nested =>
      have away : origin ≠ input.site := by
        intro atSite
        have childEncloses := Splice.Input.CompilerRoute.region_encloses
          sourceWellFormed nestedRoute
        have childEnclosesOrigin : input.frame.val.Encloses child origin := by
          simpa [atSite] using childEncloses
        exact (checked_direct_child_not_encloses_parent sourceWellFormed
          parent) childEnclosesOrigin
      have childEncloses : input.frame.val.Encloses child input.site :=
        Splice.Input.CompilerRoute.region_encloses sourceWellFormed nestedRoute
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some (layout.frameRegion origin) := by
        rw [layout.plugRegion_frameRegion]
        exact (layout.mapFrameRegion_parent_eq_some_iff child origin).2 parent
      have childSourceExact := sourceExact.extend_child sourceWellFormed parent
      have childTargetExact := targetExact.extend_child targetWellFormed
        targetParent
      have childTargetExact' :
          ((layout.mapFrameContext consistent (context.extend origin)).extend
            (layout.frameRegion child)).Exact
              (layout.frameRegion child) := by
        rw [layout.mapFrameContext_extend_of_ne consistent terminal context
          origin away]
        exact childTargetExact
      have childCovers := BinderContext.covers_cut_child sourceCovers childKind
      cases sourceFuel with
      | zero => simp [compileRegion?] at sourceCompiled
      | succ sourceRecurseFuel =>
          simp only [compileRegion?] at sourceCompiled
          cases sourceItemsResult : compileOccurrencesWith? input.frame.val
              (compileRegion? input.frame.val sourceRecurseFuel)
              (context.extend origin) sourceBinders
              (localOccurrences input.frame.val origin) with
          | none => simp [sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              simp [sourceItemsResult] at sourceCompiled
              subst sourceBody
              have sourceItemCompiled := compileOccurrencesWith?_get
                (compileRegion? input.frame.val sourceRecurseFuel)
                (context.extend origin) sourceBinders sourceItemsResult index
              rw [occurrence] at sourceItemCompiled
              simp only [compileOccurrenceWith?, childKind] at sourceItemCompiled
              cases sourceChildResult : compileRegion? input.frame.val
                  sourceRecurseFuel child (context.extend origin)
                  sourceBinders with
              | none => simp [sourceChildResult] at sourceItemCompiled
              | some sourceChildBody =>
                  cases targetFuel with
                  | zero =>
                      have targetDepthBound :=
                        ParentTraversal.climb_to_root_steps_le_regionCount
                          layout.plugRaw targetWellFormed.root_is_sheet
                          targetWellFormed.all_regions_reach_root targetClimb
                      omega
                  | succ targetRecurseFuel =>
                      have childTargetClimb : layout.plugRaw.climb
                          (targetDepth + 1) (layout.frameRegion child) =
                            some layout.plugRaw.root := by
                        have targetStep : layout.plugRaw.climb 1
                            (layout.frameRegion child) =
                              some (layout.frameRegion origin) := by
                          simp only [Diagram.climb]
                          rw [targetParent]
                          rfl
                        simpa [Nat.add_comm] using
                          climb_add targetStep targetClimb
                      have childTargetEnough : targetDepth + 1 +
                          targetRecurseFuel =
                            layout.plugRaw.regionCount + 1 := by
                        omega
                      let nestedSiteTarget : ExplicitMappedSite layout
                          consistent siteContext siteBinders
                          (targetRecurseFuel - nestedRoute.depth)
                          targetSite := by
                        simpa [ConcreteCompilerRoute.depth] using siteTarget
                      let nestedResult := compileMappedRegionRoute layout
                        consistent terminal sourceWellFormed targetWellFormed
                        nested childSourceExact childTargetExact' childCovers
                        sourceRecurseFuel (targetDepth + 1)
                        targetRecurseFuel childTargetClimb childTargetEnough
                        sourceChildBody sourceChildResult nestedSiteTarget
                      let targetItemsExistence :=
                        compileDirectOccurrences?_complete targetWellFormed
                          targetClimb childTargetEnough targetExact
                          (layout.mapFrameBinders_covers_frameRegion origin
                            sourceCovers)
                          ((localOccurrences input.frame.val origin).map
                            layout.mapFrameOccurrence) (by
                              intro targetOccurrence targetMember
                              rw [layout.localOccurrences_frameRegion_of_ne_site
                                origin away]
                              exact targetMember)
                      let targetItems := Classical.choose targetItemsExistence
                      have targetItemsResult :=
                        Classical.choose_spec targetItemsExistence
                      simpa [Nat.succ_eq_add_one] using
                        mappedRegionCutStep layout consistent terminal
                          sourceWellFormed targetWellFormed away parent childKind
                          childEncloses index occurrence sourceBinders sourceExact
                          targetExact sourceRecurseFuel targetRecurseFuel
                          sourceItems targetItems sourceItemsResult
                          targetItemsResult sourceChildBody sourceChildResult
                          nestedResult
  | @regionStepBubble _ child _ _ _ _ _ arity parent childKind index occurrence
      _ _ _ nestedRoute nested =>
      have away : origin ≠ input.site := by
        intro atSite
        have childEncloses := Splice.Input.CompilerRoute.region_encloses
          sourceWellFormed nestedRoute
        have childEnclosesOrigin : input.frame.val.Encloses child origin := by
          simpa [atSite] using childEncloses
        exact (checked_direct_child_not_encloses_parent sourceWellFormed
          parent) childEnclosesOrigin
      have childEncloses : input.frame.val.Encloses child input.site :=
        Splice.Input.CompilerRoute.region_encloses sourceWellFormed nestedRoute
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some (layout.frameRegion origin) := by
        rw [layout.plugRegion_frameRegion]
        exact (layout.mapFrameRegion_parent_eq_some_iff child origin).2 parent
      have childSourceExact := sourceExact.extend_child sourceWellFormed parent
      have childTargetExact := targetExact.extend_child targetWellFormed
        targetParent
      have childTargetExact' :
          ((layout.mapFrameContext consistent (context.extend origin)).extend
            (layout.frameRegion child)).Exact
              (layout.frameRegion child) := by
        rw [layout.mapFrameContext_extend_of_ne consistent terminal context
          origin away]
        exact childTargetExact
      have childCovers := BinderContext.push_covers_bubble_child sourceCovers
        childKind
      cases sourceFuel with
      | zero => simp [compileRegion?] at sourceCompiled
      | succ sourceRecurseFuel =>
          simp only [compileRegion?] at sourceCompiled
          cases sourceItemsResult : compileOccurrencesWith? input.frame.val
              (compileRegion? input.frame.val sourceRecurseFuel)
              (context.extend origin) sourceBinders
              (localOccurrences input.frame.val origin) with
          | none => simp [sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              simp [sourceItemsResult] at sourceCompiled
              subst sourceBody
              have sourceItemCompiled := compileOccurrencesWith?_get
                (compileRegion? input.frame.val sourceRecurseFuel)
                (context.extend origin) sourceBinders sourceItemsResult index
              rw [occurrence] at sourceItemCompiled
              simp only [compileOccurrenceWith?, childKind] at sourceItemCompiled
              cases sourceChildResult : compileRegion? input.frame.val
                  sourceRecurseFuel child (context.extend origin)
                  (sourceBinders.push child arity) with
              | none => simp [sourceChildResult] at sourceItemCompiled
              | some sourceChildBody =>
                  cases targetFuel with
                  | zero =>
                      have targetDepthBound :=
                        ParentTraversal.climb_to_root_steps_le_regionCount
                          layout.plugRaw targetWellFormed.root_is_sheet
                          targetWellFormed.all_regions_reach_root targetClimb
                      omega
                  | succ targetRecurseFuel =>
                      have childTargetClimb : layout.plugRaw.climb
                          (targetDepth + 1) (layout.frameRegion child) =
                            some layout.plugRaw.root := by
                        have targetStep : layout.plugRaw.climb 1
                            (layout.frameRegion child) =
                              some (layout.frameRegion origin) := by
                          simp only [Diagram.climb]
                          rw [targetParent]
                          rfl
                        simpa [Nat.add_comm] using
                          climb_add targetStep targetClimb
                      have childTargetEnough : targetDepth + 1 +
                          targetRecurseFuel =
                            layout.plugRaw.regionCount + 1 := by
                        omega
                      let nestedSiteTarget : ExplicitMappedSite layout
                          consistent siteContext siteBinders
                          (targetRecurseFuel - nestedRoute.depth)
                          targetSite := by
                        simpa [ConcreteCompilerRoute.depth] using siteTarget
                      let nestedResult := compileMappedRegionRoute layout
                        consistent terminal sourceWellFormed targetWellFormed
                        nested childSourceExact childTargetExact' childCovers
                        sourceRecurseFuel (targetDepth + 1)
                        targetRecurseFuel childTargetClimb childTargetEnough
                        sourceChildBody sourceChildResult nestedSiteTarget
                      let targetItemsExistence :=
                        compileDirectOccurrences?_complete targetWellFormed
                          targetClimb childTargetEnough targetExact
                          (layout.mapFrameBinders_covers_frameRegion origin
                            sourceCovers)
                          ((localOccurrences input.frame.val origin).map
                            layout.mapFrameOccurrence) (by
                              intro targetOccurrence targetMember
                              rw [layout.localOccurrences_frameRegion_of_ne_site
                                origin away]
                              exact targetMember)
                      let targetItems := Classical.choose targetItemsExistence
                      have targetItemsResult :=
                        Classical.choose_spec targetItemsExistence
                      simpa [Nat.succ_eq_add_one] using
                        mappedRegionBubbleStep layout consistent terminal
                          sourceWellFormed targetWellFormed away parent childKind
                          childEncloses index occurrence sourceBinders sourceExact
                          targetExact sourceRecurseFuel targetRecurseFuel
                          sourceItems targetItems sourceItemsResult
                          targetItemsResult sourceChildBody sourceChildResult
                          nestedResult
termination_by path.length
decreasing_by
  all_goals
    simp_all only [List.length_cons]
    omega

/-- Reconstruct the generated open root from the source compiler route.  The
root and nonroot terminal computations are source-indexed inputs; every
ancestor occurrence block and target item position is then constructed
bottom-up. -/
noncomputable def compileMappedOpenRoute
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount))
    (sourceWellFormed : (frameOpen input boundary).WellFormed)
    (targetWellFormed : (layout.outputOpenRoot input boundary).WellFormed)
    {siteContext : WireContext input.frame.val}
    {siteRels : RelCtx}
    {siteBinders : BinderContext input.frame.val siteRels}
    {path : List Nat}
    {route : ConcreteCompilerRoute input.frame.val
      (.openRoot (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires)
      input.site siteContext}
    (derivation : route.Derivation BinderContext.empty path siteBinders)
    (sourceBody : Region
      (frameOpen input boundary).exposedWires.length [])
    (sourceCompiled : compileRoot? input.frame.val
      (frameOpen input boundary).exposedWires
      (frameOpen input boundary).hiddenWires = some sourceBody)
    (targetSite : Region
      (layout.mapFrameContext consistent siteContext).length siteRels)
    (rootTarget : input.site = input.frame.val.root →
      ExplicitMappedRootSite layout consistent boundary siteContext siteRels
        targetSite)
    (regionTarget : input.site ≠ input.frame.val.root →
      ExplicitMappedSite layout consistent siteContext siteBinders
        (layout.plugRaw.regionCount + 1 - route.depth) targetSite) :
    MappedOpenRouteResult layout consistent boundary siteContext path
      sourceBody targetSite := by
  have targetDiagramWellFormed : layout.plugRaw.WellFormed := by
    simpa only [PlugLayout.outputOpenRoot] using
      targetWellFormed.diagram_well_formed
  generalize siteEq : input.site = site at route derivation
  cases derivation with
  | root =>
      let target := rootTarget siteEq
      exact mappedOpenHere layout consistent boundary sourceBody
        (target.siteRels_eq ▸ targetSite) target.outer_eq
        target.target_compiled
  | @rootStepCut _ _ child _ _ parent childKind index occurrence
      _ _ _ nestedRoute nested =>
      subst site
      have away : input.frame.val.root ≠ input.site := by
        intro atRoot
        have childEncloses := Splice.Input.CompilerRoute.region_encloses
          sourceWellFormed.diagram_well_formed nestedRoute
        have childEnclosesRoot : input.frame.val.Encloses child
            input.frame.val.root := by
          simpa [atRoot] using childEncloses
        exact (checked_direct_child_not_encloses_parent
          sourceWellFormed.diagram_well_formed parent) childEnclosesRoot
      have childEncloses : input.frame.val.Encloses child input.site :=
        Splice.Input.CompilerRoute.region_encloses
          sourceWellFormed.diagram_well_formed nestedRoute
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some layout.plugRaw.root := by
        rw [layout.plugRegion_frameRegion]
        exact (layout.mapFrameRegion_parent_eq_some_iff child
          input.frame.val.root).2 parent
      have sourceChildExact :=
        (openRootWires_exact sourceWellFormed).extend_child
          sourceWellFormed.diagram_well_formed parent
      have targetChildExactActual :=
        (openRootWires_exact targetWellFormed).extend_child
          targetWellFormed.diagram_well_formed targetParent
      have targetContextEq :
          layout.mapFrameContext consistent
              (frameOpen input boundary).rootWires =
            (layout.outputOpenRoot input boundary).rootWires := by
        symm
        simpa only [mapFrameContext, if_neg away, List.append_nil] using
          layout.outputOpenRoot_rootWires consistent terminal boundary
      have targetChildExact :
          ((layout.mapFrameContext consistent
            (frameOpen input boundary).rootWires).extend
              (layout.frameRegion child)).Exact
            (layout.frameRegion child) := by
        rw [targetContextEq]
        exact targetChildExactActual
      have sourceCovers :
          (BinderContext.empty : BinderContext input.frame.val []).Covers
            input.frame.val.root :=
        BinderContext.empty_covers_root
          sourceWellFormed.diagram_well_formed
      have childCovers := BinderContext.covers_cut_child sourceCovers childKind
      simp only [compileRoot?] at sourceCompiled
      cases sourceItemsResult : compileOccurrencesWith? input.frame.val
          (compileRegion? input.frame.val input.frame.val.regionCount)
          ((frameOpen input boundary).exposedWires ++
            (frameOpen input boundary).hiddenWires) BinderContext.empty
          (localOccurrences input.frame.val input.frame.val.root) with
      | none =>
          have impossible := (congrArg (fun result => result.bind
            (fun items => some (finishRoot
              (frameOpen input boundary).exposedWires
              (frameOpen input boundary).hiddenWires items)))
            sourceItemsResult).symm.trans sourceCompiled
          contradiction
      | some sourceItems =>
          have sourceBodyEq := (congrArg (fun result => result.bind
            (fun items => some (finishRoot
              (frameOpen input boundary).exposedWires
              (frameOpen input boundary).hiddenWires items)))
            sourceItemsResult).symm.trans sourceCompiled
          simp only [Option.bind_some, Option.some.injEq] at sourceBodyEq
          replace sourceCompiled := sourceBodyEq
          subst sourceBody
          have sourceItemCompiled := compileOccurrencesWith?_get
            (compileRegion? input.frame.val input.frame.val.regionCount)
            (frameOpen input boundary).rootWires BinderContext.empty
            sourceItemsResult index
          rw [occurrence] at sourceItemCompiled
          simp only [compileOccurrenceWith?, childKind] at sourceItemCompiled
          cases sourceChildResult : compileRegion? input.frame.val
              input.frame.val.regionCount child
              (frameOpen input boundary).rootWires BinderContext.empty with
          | none => simp [sourceChildResult] at sourceItemCompiled
          | some sourceChildBody =>
              have childTargetClimb : layout.plugRaw.climb 1
                  (layout.frameRegion child) = some layout.plugRaw.root := by
                simp only [Diagram.climb]
                rw [targetParent]
              have childTargetEnough :
                  1 + layout.plugRaw.regionCount =
                    layout.plugRaw.regionCount + 1 := by omega
              let suppliedTarget := regionTarget (Ne.symm away)
              let nestedSiteTarget : ExplicitMappedSite layout consistent
                  siteContext siteBinders
                  (layout.plugRaw.regionCount - nestedRoute.depth)
                  targetSite :=
                suppliedTarget.castFuel (by
                  simp [ConcreteCompilerRoute.depth])
              let nestedResult := compileMappedRegionRoute layout consistent
                terminal sourceWellFormed.diagram_well_formed
                targetWellFormed.diagram_well_formed nested sourceChildExact
                targetChildExact childCovers input.frame.val.regionCount 1
                layout.plugRaw.regionCount childTargetClimb childTargetEnough
                sourceChildBody sourceChildResult nestedSiteTarget
              let targetItemsExistence := compileDirectOccurrences?_complete
                targetDiagramWellFormed (depth := 0)
                (fuel := layout.plugRaw.regionCount)
                (region := layout.frameRegion input.frame.val.root)
                (context := (layout.outputOpenRoot input boundary).rootWires)
                (binders := BinderContext.empty) (by rfl) (by omega)
                (openRootWires_exact targetWellFormed)
                (BinderContext.empty_covers_root
                  targetDiagramWellFormed)
                ((localOccurrences input.frame.val input.frame.val.root).map
                  layout.mapFrameOccurrence) (by
                    intro targetOccurrence targetMember
                    change targetOccurrence ∈ localOccurrences layout.plugRaw
                      (layout.frameRegion input.frame.val.root)
                    rw [layout.localOccurrences_frameRegion_of_ne_site
                      input.frame.val.root away]
                    exact targetMember)
              let targetItems := Classical.choose targetItemsExistence
              have targetItemsResult :=
                Classical.choose_spec targetItemsExistence
              exact mappedOpenCutStep layout consistent terminal boundary
                sourceWellFormed targetWellFormed away parent childKind
                childEncloses index occurrence sourceItems targetItems
                sourceItemsResult targetItemsResult sourceChildBody
                sourceChildResult nestedResult
  | @rootStepBubble _ _ child _ _ arity parent childKind index occurrence
      _ _ _ nestedRoute nested =>
      subst site
      have away : input.frame.val.root ≠ input.site := by
        intro atRoot
        have childEncloses := Splice.Input.CompilerRoute.region_encloses
          sourceWellFormed.diagram_well_formed nestedRoute
        have childEnclosesRoot : input.frame.val.Encloses child
            input.frame.val.root := by
          simpa [atRoot] using childEncloses
        exact (checked_direct_child_not_encloses_parent
          sourceWellFormed.diagram_well_formed parent) childEnclosesRoot
      have childEncloses : input.frame.val.Encloses child input.site :=
        Splice.Input.CompilerRoute.region_encloses
          sourceWellFormed.diagram_well_formed nestedRoute
      have targetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some layout.plugRaw.root := by
        rw [layout.plugRegion_frameRegion]
        exact (layout.mapFrameRegion_parent_eq_some_iff child
          input.frame.val.root).2 parent
      have sourceChildExact :=
        (openRootWires_exact sourceWellFormed).extend_child
          sourceWellFormed.diagram_well_formed parent
      have targetChildExactActual :=
        (openRootWires_exact targetWellFormed).extend_child
          targetWellFormed.diagram_well_formed targetParent
      have targetContextEq :
          layout.mapFrameContext consistent
              (frameOpen input boundary).rootWires =
            (layout.outputOpenRoot input boundary).rootWires := by
        symm
        simpa only [mapFrameContext, if_neg away, List.append_nil] using
          layout.outputOpenRoot_rootWires consistent terminal boundary
      have targetChildExact :
          ((layout.mapFrameContext consistent
            (frameOpen input boundary).rootWires).extend
              (layout.frameRegion child)).Exact
            (layout.frameRegion child) := by
        rw [targetContextEq]
        exact targetChildExactActual
      have sourceCovers :
          (BinderContext.empty : BinderContext input.frame.val []).Covers
            input.frame.val.root :=
        BinderContext.empty_covers_root
          sourceWellFormed.diagram_well_formed
      have childCovers := BinderContext.push_covers_bubble_child sourceCovers
        childKind
      simp only [compileRoot?] at sourceCompiled
      cases sourceItemsResult : compileOccurrencesWith? input.frame.val
          (compileRegion? input.frame.val input.frame.val.regionCount)
          ((frameOpen input boundary).exposedWires ++
            (frameOpen input boundary).hiddenWires) BinderContext.empty
          (localOccurrences input.frame.val input.frame.val.root) with
      | none =>
          have impossible := (congrArg (fun result => result.bind
            (fun items => some (finishRoot
              (frameOpen input boundary).exposedWires
              (frameOpen input boundary).hiddenWires items)))
            sourceItemsResult).symm.trans sourceCompiled
          contradiction
      | some sourceItems =>
          have sourceBodyEq := (congrArg (fun result => result.bind
            (fun items => some (finishRoot
              (frameOpen input boundary).exposedWires
              (frameOpen input boundary).hiddenWires items)))
            sourceItemsResult).symm.trans sourceCompiled
          simp only [Option.bind_some, Option.some.injEq] at sourceBodyEq
          replace sourceCompiled := sourceBodyEq
          subst sourceBody
          have sourceItemCompiled := compileOccurrencesWith?_get
            (compileRegion? input.frame.val input.frame.val.regionCount)
            (frameOpen input boundary).rootWires BinderContext.empty
            sourceItemsResult index
          rw [occurrence] at sourceItemCompiled
          simp only [compileOccurrenceWith?, childKind] at sourceItemCompiled
          cases sourceChildResult : compileRegion? input.frame.val
              input.frame.val.regionCount child
              (frameOpen input boundary).rootWires
              (BinderContext.empty.push child arity) with
          | none => simp [sourceChildResult] at sourceItemCompiled
          | some sourceChildBody =>
              have childTargetClimb : layout.plugRaw.climb 1
                  (layout.frameRegion child) = some layout.plugRaw.root := by
                simp only [Diagram.climb]
                rw [targetParent]
              have childTargetEnough :
                  1 + layout.plugRaw.regionCount =
                    layout.plugRaw.regionCount + 1 := by omega
              let suppliedTarget := regionTarget (Ne.symm away)
              let nestedSiteTarget : ExplicitMappedSite layout consistent
                  siteContext siteBinders
                  (layout.plugRaw.regionCount - nestedRoute.depth)
                  targetSite :=
                suppliedTarget.castFuel (by
                  simp [ConcreteCompilerRoute.depth])
              let nestedResult := compileMappedRegionRoute layout consistent
                terminal sourceWellFormed.diagram_well_formed
                targetWellFormed.diagram_well_formed nested sourceChildExact
                targetChildExact childCovers input.frame.val.regionCount 1
                layout.plugRaw.regionCount childTargetClimb childTargetEnough
                sourceChildBody sourceChildResult nestedSiteTarget
              let targetItemsExistence := compileDirectOccurrences?_complete
                targetDiagramWellFormed (depth := 0)
                (fuel := layout.plugRaw.regionCount)
                (region := layout.frameRegion input.frame.val.root)
                (context := (layout.outputOpenRoot input boundary).rootWires)
                (binders := BinderContext.empty) (by rfl) (by omega)
                (openRootWires_exact targetWellFormed)
                (BinderContext.empty_covers_root
                  targetDiagramWellFormed)
                ((localOccurrences input.frame.val input.frame.val.root).map
                  layout.mapFrameOccurrence) (by
                    intro targetOccurrence targetMember
                    change targetOccurrence ∈ localOccurrences layout.plugRaw
                      (layout.frameRegion input.frame.val.root)
                    rw [layout.localOccurrences_frameRegion_of_ne_site
                      input.frame.val.root away]
                    exact targetMember)
              let targetItems := Classical.choose targetItemsExistence
              have targetItemsResult :=
                Classical.choose_spec targetItemsExistence
              exact mappedOpenBubbleStep layout consistent terminal boundary
                sourceWellFormed targetWellFormed away parent childKind
                childEncloses index occurrence sourceItems targetItems
                sourceItemsResult targetItemsResult sourceChildBody
                sourceChildResult nestedResult

/-- Canonical source-derived route reconstruction for one splice.  Both hole
endpoints are the retained compiler sites, while the generated root and its
compiler equation are explicit. -/
structure SpliceMappedOpenRouteResult
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer) where
  targetBody : Region
    (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).exposedWires.length []
  target_compiled : compileRoot? layout.plugRaw
    (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).exposedWires
    (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).hiddenWires = some targetBody
  alignment : CompilerRouteAlignment
    (layout.outputExternalEquiv consistent source.checked.val.boundary)
    (layout.mapFrameContextEquiv consistent host.siteContext)
    source.checked.elaborate.body targetBody host.siteBody
    (layout.spliceCompilerSiteBody normalized consistent admissible host
      host.kernel host.kernel.blocks material material.kernel
      material.kernel.blocks)
  source_context_eq : alignment.sourceContext =
    host.siteOccurrence.context

/-- Identify the source terminal retained by a mapped open route with the
source compiler site's intrinsic terminal.  The target terminal is already
the exact caller-supplied index of the mapped result. -/
noncomputable def MappedOpenRouteResult.alignCompiledSite
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (host : CompiledSite source normalized.site)
    {targetSite : Region
      (layout.mapFrameContext consistent host.siteContext).length
        host.siteRels}
    (result : MappedOpenRouteResult layout consistent
      source.checked.val.boundary host.siteContext host.path
      source.checked.elaborate.body targetSite) :
    CompilerRouteAlignment
      (layout.outputExternalEquiv consistent source.checked.val.boundary)
      (layout.mapFrameContextEquiv consistent host.siteContext)
      source.checked.elaborate.body result.targetBody host.siteBody
      targetSite := by
  have witnessEq : result.sourceWitness = host.witness :=
    Region.ContextPath.unique result.sourceWitness host.witness
  have sourceSiteEq : result.sourceSite = host.siteBody := by
    apply eq_of_heq
    have resultFocus := result.source_focus_body
    rw [witnessEq] at resultFocus
    exact resultFocus.symm.trans host.focus_body
  exact result.alignment.castSourceSite sourceSiteEq

/-- Normalizing the terminal body of a mapped route preserves its intrinsic
source context, which is exactly the source compiler occurrence context. -/
theorem MappedOpenRouteResult.alignCompiledSite_sourceContext
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (host : CompiledSite source normalized.site)
    {targetSite : Region
      (layout.mapFrameContext consistent host.siteContext).length
        host.siteRels}
    (result : MappedOpenRouteResult layout consistent
      source.checked.val.boundary host.siteContext host.path
      source.checked.elaborate.body targetSite) :
    (result.alignCompiledSite normalized layout consistent host).sourceContext =
      host.siteOccurrence.context := by
  have witnessEq : result.sourceWitness = host.witness :=
    Region.ContextPath.unique result.sourceWitness host.witness
  have sourceSiteEq : result.sourceSite = host.siteBody := by
    apply eq_of_heq
    have resultFocus := result.source_focus_body
    rw [witnessEq] at resultFocus
    exact resultFocus.symm.trans host.focus_body
  calc
    (result.alignCompiledSite normalized layout consistent host).sourceContext =
        result.alignment.sourceContext :=
      result.alignment.castSourceSite_sourceContext sourceSiteEq
    _ = host.siteOccurrence.context := by
      have context := result.source_context_heq
      rw [witnessEq] at context
      exact eq_of_heq
        (context.trans host.siteOccurrence_context_heq.symm)

/-- Reconstruct the generated splice root solely from the retained source
compiler route and the canonical source-derived site computations. -/
noncomputable def compileSpliceMappedOpenRoute
    {source : State arity} (normalized : SourceNormalized source)
    (layout : PlugLayout normalized.toInput)
    (consistent : normalized.toInput.AttachmentConsistent)
    (admissible : normalized.toInput.Admissible)
    (host : CompiledSite source normalized.site)
    (material : CompiledSite normalized.toInput.patternState
      normalized.binderSpine.bodyContainer)
    (targetWellFormed : (layout.outputOpenRoot normalized.toInput
      source.checked.val.boundary).WellFormed) :
    SpliceMappedOpenRouteResult normalized layout consistent admissible host
      material := by
  let targetSite := layout.spliceCompilerSiteBody normalized consistent
    admissible host host.kernel host.kernel.blocks material material.kernel
    material.kernel.blocks
  let sourceDiagramWellFormed :=
    source.checked.property.diagram_well_formed
  let fuel := layout.sourceDerivedSiteFuel sourceDiagramWellFormed
  let rootTarget : normalized.site = normalized.toInput.frame.val.root →
      ExplicitMappedRootSite layout consistent source.checked.val.boundary
        host.siteContext host.siteRels targetSite := fun atRoot => by
    let computation := layout.spliceCompilerRootSiteComputation normalized
      consistent admissible host material targetWellFormed atRoot
    exact {
      siteRels_eq := computation.siteRels_eq
      outer_eq := computation.outer_eq
      target_compiled := computation.compiled
    }
  let regionTarget : normalized.site ≠ normalized.toInput.frame.val.root →
      ExplicitMappedSite layout consistent host.siteContext host.siteBinders
        (layout.plugRaw.regionCount + 1 - host.route.depth) targetSite :=
    fun away => by
      let computation := layout.spliceCompilerRegionSiteComputation normalized
        consistent admissible host material targetWellFormed away
      let exactFuel : ExplicitMappedSite layout consistent host.siteContext
          host.siteBinders (fuel.recurseFuel + 1) targetSite := {
        target_compiled := computation
      }
      exact exactFuel.castFuel (by
        have routeFuel := layout.sourceDerivedSiteFuel_route_recurseFuel
          sourceDiagramWellFormed host.route
        have routeFuel' : host.route.depth + fuel.recurseFuel =
            layout.plugRaw.regionCount := by
          simpa only [fuel] using routeFuel
        omega)
  let result := compileMappedOpenRoute layout consistent
    admissible.terminal_body source.checked.val.boundary
    source.checked.property targetWellFormed host.derivation
    source.checked.elaborate.body host.root_compiled targetSite rootTarget
    regionTarget
  exact {
    targetBody := result.targetBody
    target_compiled := result.target_compiled
    alignment := result.alignCompiledSite normalized layout consistent host
    source_context_eq :=
      result.alignCompiledSite_sourceContext normalized layout consistent host
  }

end Splice.Input.PlugLayout

end VisualProof.Concrete
