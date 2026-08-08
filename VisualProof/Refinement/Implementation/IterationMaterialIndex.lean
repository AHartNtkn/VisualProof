import VisualProof.Refinement.Implementation.IterationTransport

namespace VisualProof.Refinement.Implementation.IterationMaterialIndex

open VisualProof.Concrete
open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationTransport
open VisualProof.Refinement.Implementation.IterationExtraction

/-- Every wire inherited by the extracted terminal body occurs in the full
selection-anchor context. -/
theorem iterationTerminalAnchorMember
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Concrete.Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((Concrete.Splice.Input.compiledSpliceTerminalView
          (iterationInput input selection target) hnonempty
        ).leaf.inheritedWires.get index) ∈
      (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (IterationQuotient.coalescedFrameIso input selection target).wires) := by
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := IterationAnchor.coalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let targetContext := sourceContext.map
    (IterationQuotient.coalescedFrameIso input selection target).wires
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  have targetExact : Concrete.Elaboration.WireContext.Exact targetContext
      selection.val.anchor :=
    anchorView.compilerLeaf.wiresExact.mapIso
      (IterationQuotient.coalescedFrameIso input selection target)
  have patternVisible : spliceInput.pattern.val.diagram.Encloses
      (spliceInput.pattern.val.diagram.wires
        (pattern.leaf.inheritedWires.get index)).scope
      spliceInput.binderSpine.bodyContainer := by
    apply (pattern.leaf.wiresExact.mem_iff _).1
    apply List.mem_append.mpr
    exact Or.inl (List.get_mem _ index)
  have hostVisible := fragmentWireOrigin_scope_encloses_anchor input selection
    layout (pattern.leaf.inheritedWires.get index) patternVisible
  exact (targetExact.mem_iff _).2 hostVisible

/-- Canonical anchor-context index of a wire inherited by the extracted
terminal body. -/
noncomputable def iterationTerminalAnchorIndex
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Concrete.Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    Fin (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (IterationQuotient.coalescedFrameIso input selection target).wires).length :=
  Classical.choose (indexOf?_complete
    (iterationTerminalAnchorMember input selection target hadmissible
      hnonempty index))

theorem iterationTerminalAnchorIndex_get
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Concrete.Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (IterationQuotient.coalescedFrameIso input selection target).wires).get
          (iterationTerminalAnchorIndex input selection target hadmissible
            hnonempty index) =
      input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((Concrete.Splice.Input.compiledSpliceTerminalView
          (iterationInput input selection target) hnonempty
        ).leaf.inheritedWires.get index) := by
  classical
  unfold iterationTerminalAnchorIndex
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (iterationTerminalAnchorMember input selection target hadmissible
      hnonempty index)))

theorem iterationTerminalAnchorIndex_related
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Concrete.Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (Concrete.Splice.Input.compiledSpliceTerminalView
        (iterationInput input selection target) hnonempty).leaf.inheritedWires
      (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (IterationQuotient.coalescedFrameIso input selection target).wires)
    ) index (iterationTerminalAnchorIndex input selection target
      hadmissible hnonempty index) := by
  unfold extractionContextRelation
  exact (iterationTerminalAnchorIndex_get input selection target hadmissible
    hnonempty index).symm

/-- Every exposed wire of an empty-spine extracted root occurs in the full
selection-anchor context. -/
theorem iterationRootAnchorMember
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((iterationInput input selection target).pattern.val.exposedWires.get
          index) ∈
      (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (IterationQuotient.coalescedFrameIso input selection target).wires) := by
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := IterationAnchor.coalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let targetContext := sourceContext.map
    (IterationQuotient.coalescedFrameIso input selection target).wires
  have bodyEq : layout.bodyContainer = spliceInput.pattern.val.diagram.root :=
    layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero
  have fragmentExact : Concrete.Elaboration.WireContext.Exact
      spliceInput.pattern.val.rootWires layout.bodyContainer := by
    rw [bodyEq]
    exact Concrete.Elaboration.openRootWires_exact spliceInput.pattern.property
  have targetExact : Concrete.Elaboration.WireContext.Exact targetContext
      selection.val.anchor :=
    anchorView.compilerLeaf.wiresExact.mapIso
      (IterationQuotient.coalescedFrameIso input selection target)
  apply (targetExact.mem_iff _).2
  apply fragmentWireOrigin_scope_encloses_anchor input selection layout
  apply (fragmentExact.mem_iff _).1
  apply List.mem_append.mpr
  exact Or.inl (List.get_mem _ index)

/-- Canonical anchor-context index of an exposed wire of the empty-spine
extracted root. -/
noncomputable def iterationRootAnchorIndex
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    Fin (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (IterationQuotient.coalescedFrameIso input selection target).wires).length :=
  Classical.choose (indexOf?_complete
    (iterationRootAnchorMember input selection target hadmissible hzero index))

theorem iterationRootAnchorIndex_get
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (IterationQuotient.coalescedFrameIso input selection target).wires).get
          (iterationRootAnchorIndex input selection target hadmissible hzero
            index) =
      input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((iterationInput input selection target).pattern.val.exposedWires.get
          index) := by
  classical
  unfold iterationRootAnchorIndex
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (iterationRootAnchorMember input selection target hadmissible hzero index)))

theorem iterationRootAnchorIndex_related
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (iterationInput input selection target).pattern.val.exposedWires
      (((IterationAnchor.coalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (IterationQuotient.coalescedFrameIso input selection target).wires)
    ) index (iterationRootAnchorIndex input selection target hadmissible
      hzero index) := by
  unfold extractionContextRelation
  exact (iterationRootAnchorIndex_get input selection target hadmissible hzero
    index).symm

end VisualProof.Refinement.Implementation.IterationMaterialIndex
