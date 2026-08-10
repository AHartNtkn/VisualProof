import VisualProof.Refinement.Implementation.IterationFragment
import VisualProof.Refinement.Implementation.IterationRoute
import VisualProof.Diagram.RenamingIsomorphism
import VisualProof.Rule.Iteration

namespace VisualProof.Refinement.Implementation.IterationSourceFactor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationPartition
open VisualProof.Refinement.Implementation.IterationRoute
open VisualProof.Refinement.Implementation.IterationFragment

/-- One presentation of the compiler's complete anchor wire carrier.  The
chosen split is authoritative for every object in the factor assembly: an
open-root consumer may place exposed wires in `ancestorWires` and hidden wires
in `anchorLocal`, while a nested consumer may choose its own inherited/local
split. -/
structure SourcePartition
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)) where
  ancestorWires : Nat
  anchorLocal : Nat
  wire : FiniteEquiv
    (Fin (anchorLeaf.inheritedWires.extend selection.val.anchor).length)
    (Fin (ancestorWires + anchorLocal))
  sourceItems : ItemSeq (ancestorWires + anchorLocal) rels
  sourceItems_iso : ItemSeqIso wire rels anchorLeaf.items sourceItems

def SourcePartition.sourceRegion
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    Region partition.ancestorWires rels :=
  .mk partition.anchorLocal partition.sourceItems

/-- The original compiler-context position represented by a selected explicit
wire.  It is selected from the one exact anchor context, rather than from a
second canonical permutation. -/
private noncomputable def sourceExplicitIndex
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (fresh : Fin selection.val.explicitWires.length) :
    Fin (anchorLeaf.inheritedWires.extend selection.val.anchor).length :=
  Classical.choose (indexOf?_complete (by
    apply (anchorLeaf.wiresExact.mem_iff _).2
    rw [selection.property.explicitWires_at_anchor _
      (List.get_mem selection.val.explicitWires fresh)]
    exact Concrete.Diagram.Encloses.refl input.val selection.val.anchor))

private theorem sourceExplicitIndex_spec
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (fresh : Fin selection.val.explicitWires.length) :
    (anchorLeaf.inheritedWires.extend selection.val.anchor).get
        (sourceExplicitIndex input selection anchorLeaf fresh) =
      selection.val.explicitWires.get fresh := by
  unfold sourceExplicitIndex
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete (by
    apply (anchorLeaf.wiresExact.mem_iff _).2
    rw [selection.property.explicitWires_at_anchor _
      (List.get_mem selection.val.explicitWires fresh)]
    exact Concrete.Diagram.Encloses.refl input.val selection.val.anchor)))

private theorem partitionSourceOfFresh_injective
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    Function.Injective (fun fresh =>
      partition.wire (sourceExplicitIndex input selection anchorLeaf fresh)) := by
  intro left right equality
  have sourceIndexEq :
      sourceExplicitIndex input selection anchorLeaf left =
        sourceExplicitIndex input selection anchorLeaf right :=
    partition.wire.injective equality
  apply Fin.ext
  apply (List.getElem_inj selection.property.explicitWires_nodup).mp
  simpa only [List.get_eq_getElem] using
    (sourceExplicitIndex_spec input selection anchorLeaf left).symm.trans
      (congrArg
        (fun index =>
          (anchorLeaf.inheritedWires.extend selection.val.anchor).get index)
        sourceIndexEq |>.trans
          (sourceExplicitIndex_spec input selection anchorLeaf right))

private noncomputable def sourceFactorCopyWire
    {sourceWires targetWires freshWires : Nat}
    (sourceOfFresh : Fin freshWires → Fin sourceWires)
    (inherited : Fin sourceWires → Fin targetWires) :
    Fin sourceWires → Fin (targetWires + freshWires) := fun source =>
  if present : ∃ fresh, sourceOfFresh fresh = source then
    Fin.natAdd targetWires (Classical.choose present)
  else
    Fin.castAdd freshWires (inherited source)

private theorem sourceFactorCopyWire_fresh
    {sourceWires targetWires freshWires : Nat}
    (sourceOfFresh : Fin freshWires → Fin sourceWires)
    (sourceOfFreshInjective : Function.Injective sourceOfFresh)
    (inherited : Fin sourceWires → Fin targetWires)
    (fresh : Fin freshWires) :
    sourceFactorCopyWire sourceOfFresh inherited (sourceOfFresh fresh) =
      Fin.natAdd targetWires fresh := by
  unfold sourceFactorCopyWire
  rw [dif_pos ⟨fresh, rfl⟩]
  apply congrArg (Fin.natAdd targetWires)
  exact sourceOfFreshInjective (Classical.choose_spec
    (show ∃ candidate, sourceOfFresh candidate = sourceOfFresh fresh from
      ⟨fresh, rfl⟩))

private theorem sourceFactorCopyWire_inherited
    {sourceWires targetWires freshWires : Nat}
    (sourceOfFresh : Fin freshWires → Fin sourceWires)
    (inherited : Fin sourceWires → Fin targetWires)
    (source : Fin sourceWires)
    (notFresh : ∀ fresh, sourceOfFresh fresh ≠ source) :
    sourceFactorCopyWire sourceOfFresh inherited source =
      Fin.castAdd freshWires (inherited source) := by
  unfold sourceFactorCopyWire
  rw [dif_neg (by
    intro present
    obtain ⟨fresh, equality⟩ := present
    exact notFresh fresh equality)]

private theorem diagramContext_fill_transport_outer
    {sourceOuter targetOuter holeWires : Nat}
    {outerRels holeRels : RelCtx}
    (equality : sourceOuter = targetOuter)
    (context : DiagramContext sourceOuter holeWires outerRels holeRels)
    (body : Region holeWires holeRels) :
    (Eq.mp
        (congrArg
          (fun outer =>
            DiagramContext outer holeWires outerRels holeRels)
          equality)
        context).fill body =
      (context.fill body).castWiresEq equality := by
  subst targetOuter
  rfl

private noncomputable def routedSelectedTarget
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf)
    (selectedItems : ItemSeq
      (partition.ancestorWires + partition.anchorLocal) rels)
    {keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels}
    {routedPath : List Nat}
    (routed : Region.ContextPath
      ((Region.mk 0 keptItems).renameWires partition.wire)
      routedPath) : Region partition.ancestorWires rels :=
  Region.adjoinAt partition.anchorLocal .nil
    ((Region.mk 0 selectedItems).conjoin
      (routed.toFocus.context.fill routed.toFocus.body))

private noncomputable def fragmentSelectedItems
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    (fragment : FragmentInput input selection layout spliceInput)
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    ItemSeq (partition.ancestorWires + partition.anchorLocal) rels :=
  let binderWitness :=
    IterationExtraction.ExtractionBinderWitness.terminal input selection layout
      fragment.binders fragment.enumeration anchorLeaf.binders
      anchorLeaf.bindersCover
  let preparedItems :=
    (fragment.items.renameRelations binderWitness.relationMap).renameWires
      (IterationExtraction.extractionContextIndexMap input selection layout
        fragment.context
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        fragment.contextExact anchorLeaf.wiresExact)
  preparedItems.renameWires partition.wire

/-- The actual compiler-fragment wire embedding into the source partition.
This is the wire map used to prepare `fragmentSelectedItems`; it is not a
canonical presentation chosen independently of the fragment compiler witness. -/
private noncomputable def factorFragmentSourceEmbedding
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    (fragment : FragmentInput input selection layout spliceInput)
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    Fin fragment.context.length →
      Fin (partition.ancestorWires + partition.anchorLocal) :=
  partition.wire ∘
    IterationExtraction.extractionContextIndexMap input selection layout
      fragment.context
      (anchorLeaf.inheritedWires.extend selection.val.anchor)
      fragment.contextExact anchorLeaf.wiresExact

private noncomputable def fragmentMaterialSource
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    (fragment : FragmentInput input selection layout spliceInput)
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    Region partition.ancestorWires rels :=
  .mk partition.anchorLocal (fragmentSelectedItems fragment partition)

private noncomputable def factorPartitionResult
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)) :
    PartitionResult input selection.val.anchor anchorLeaf
      (selectedOccurrences input.val selection)
      (keptOccurrences input.val selection) :=
  partition_complete input selection anchorLeaf

private noncomputable def factorKeptItems
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)) :
    ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels :=
  (factorPartitionResult anchorLeaf).keptItems

private noncomputable def factorKeptRoute
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    @KeptRouteResult input selection outer rels anchorBody anchorLeaf
      (factorKeptItems anchorLeaf) target path route :=
  keptRoute_complete input selection anchorLeaf (factorKeptItems anchorLeaf)
    (factorPartitionResult anchorLeaf).keptCompiled route targetNotSelected

private noncomputable def factorRouteAlignment
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    (RegionIso.renameWiresEquiv
      (Region.mk 0 (factorKeptItems anchorLeaf))
      partition.wire).ContextPathAlignment
        (factorKeptRoute input selection anchorLeaf route
          targetNotSelected).witness :=
  (RegionIso.renameWiresEquiv
    (Region.mk 0 (factorKeptItems anchorLeaf))
    partition.wire).alignContextPath
      (factorKeptRoute input selection anchorLeaf route
        targetNotSelected).witness

private theorem routedSelectedTarget_localCount
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf)
    (selectedItems : ItemSeq
      (partition.ancestorWires + partition.anchorLocal) rels)
    {keptItems : ItemSeq
      (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels}
    {routedPath : List Nat}
    (routed : Region.ContextPath
      ((Region.mk 0 keptItems).renameWires partition.wire) routedPath) :
    (routedSelectedTarget partition selectedItems routed).localCount =
      partition.anchorLocal := by
  unfold routedSelectedTarget
  rw [routed.toFocus.rebuild]
  rfl

private theorem fragmentMaterialTarget_localCount
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf)
    (selectedItems : ItemSeq
      (partition.ancestorWires + partition.anchorLocal) rels) :
    (Region.adjoinAt partition.anchorLocal .nil
      (Region.mk 0 selectedItems)).localCount = partition.anchorLocal := by
  rfl

/-- The structural inclusion of the material endpoint's selected carrier into
the routed source endpoint.  Both endpoints use the assembly's actual target
regions; only their definitionally shared selected coordinate placement is
used. -/
private noncomputable def factorSourceSelectedEmbedding
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {spliceInput : Concrete.Splice.Input}
    (fragment : FragmentInput input selection layout spliceInput)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    Fin (partition.ancestorWires +
      (Region.adjoinAt partition.anchorLocal .nil
        (Region.mk 0 (fragmentSelectedItems fragment partition))).localCount) →
    Fin (partition.ancestorWires +
      (routedSelectedTarget partition
        (fragmentSelectedItems fragment partition)
        (factorRouteAlignment input selection anchorLeaf route
          targetNotSelected partition).targetWitness).localCount) :=
  Fin.cast (congrArg (fun localCount => partition.ancestorWires + localCount)
    ((fragmentMaterialTarget_localCount partition
        (fragmentSelectedItems fragment partition)).trans
      (routedSelectedTarget_localCount partition
        (fragmentSelectedItems fragment partition)
        (factorRouteAlignment input selection anchorLeaf route
          targetNotSelected partition).targetWitness).symm))

private theorem regionIso_extendedWire_commuting
    {outer : Nat} {rels : RelCtx}
    {leftSource rightSource leftTarget rightTarget : Region outer rels}
    (leftIso : RegionIso (FiniteEquiv.refl (Fin outer)) rels
      leftSource leftTarget)
    (rightIso : RegionIso (FiniteEquiv.refl (Fin outer)) rels
      rightSource rightTarget)
    {sourceLocal targetLocal : Nat}
    (leftSourceLocal : leftSource.localCount = sourceLocal)
    (rightSourceLocal : rightSource.localCount = sourceLocal)
    (leftTargetLocal : leftTarget.localCount = targetLocal)
    (rightTargetLocal : rightTarget.localCount = targetLocal)
    (localEq :
      leftIso.localEquivCast leftSourceLocal leftTargetLocal =
        rightIso.localEquivCast rightSourceLocal rightTargetLocal) :
    Fin.cast (congrArg (fun localCount => outer + localCount)
          (leftTargetLocal.trans rightTargetLocal.symm)) ∘
        ((extendWireEquiv (FiniteEquiv.refl (Fin outer))
            leftIso.localEquiv).toFun ∘
          Fin.cast (congrArg (fun localCount => outer + localCount)
            leftSourceLocal.symm)) =
      (extendWireEquiv (FiniteEquiv.refl (Fin outer))
          rightIso.localEquiv).toFun ∘
        Fin.cast (congrArg (fun localCount => outer + localCount)
          rightSourceLocal.symm) := by
  cases leftIso
  cases rightIso
  cases leftSourceLocal
  cases rightSourceLocal
  cases leftTargetLocal
  cases rightTargetLocal
  simp only [RegionIso.localEquivCast, RegionIso.localEquiv] at localEq
  simp only [RegionIso.localEquiv]
  rw [localEq]
  funext index
  apply Fin.ext
  rfl

/-- One dependent assembly for the source factor.  The compiler partition,
retained route, route alignment, selected presentation, and copy freshening are
derived from the indices and the route-admissibility premise.  The endpoint
isomorphisms use those exact derived values and carry their selected-embedding
square in the same construction authority. -/
private structure FactorAssemblyCore
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {spliceInput : Concrete.Splice.Input}
    (fragment : FragmentInput input selection layout spliceInput)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) where
  targetNotSelected : ¬ selection.val.SelectsRegion target
  source_iso : RegionIso
    (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
    partition.sourceRegion
    (routedSelectedTarget partition (fragmentSelectedItems fragment partition)
      (factorRouteAlignment input selection anchorLeaf route
        targetNotSelected partition).targetWitness)
  material_iso : RegionIso
    (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
    (fragmentMaterialSource fragment partition)
    (Region.adjoinAt partition.anchorLocal .nil
      (Region.mk 0 (fragmentSelectedItems fragment partition)))
  selected_embedding_commuting :
    factorSourceSelectedEmbedding input selection anchorLeaf fragment route
        targetNotSelected partition ∘
          ((extendWireEquiv
            (FiniteEquiv.refl (Fin partition.ancestorWires))
            material_iso.localEquiv).toFun ∘
              factorFragmentSourceEmbedding fragment partition) =
      (extendWireEquiv
          (FiniteEquiv.refl (Fin partition.ancestorWires))
          source_iso.localEquiv).toFun ∘
            factorFragmentSourceEmbedding fragment partition

/-- Public name for the assembly type.  Its constructor and raw fields remain
module-private; consumers use only the coherent projections below. -/
abbrev FactorAssembly := FactorAssemblyCore

namespace FactorAssembly

variable {input : Concrete.Checked}
variable {selection : CheckedSelection input.val}
variable {layout : FragmentLayout input.val selection}
variable {outer : Nat} {rels : RelCtx}
variable {anchorBody : Region outer rels}
variable {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
  selection.val.anchor (.here anchorBody)}
variable {spliceInput : Concrete.Splice.Input}
variable {fragment : FragmentInput input selection layout spliceInput}
variable {target : Fin input.val.regionCount} {path : List Nat}
variable {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
  target path}
variable {partition : @SourcePartition input selection outer rels anchorBody
  anchorLeaf}
variable (assembly : @FactorAssembly input selection layout outer rels
  anchorBody anchorLeaf spliceInput fragment target path route partition)

noncomputable def keptItems
    (_assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) : ItemSeq
    (anchorLeaf.inheritedWires.extend selection.val.anchor).length rels :=
  factorKeptItems anchorLeaf

noncomputable def keptRoute : @KeptRouteResult input selection outer rels
    anchorBody anchorLeaf assembly.keptItems target path route := by
  exact factorKeptRoute input selection anchorLeaf route
    (FactorAssemblyCore.targetNotSelected assembly)

noncomputable def route_alignment :
    (RegionIso.renameWiresEquiv (Region.mk 0 assembly.keptItems)
      partition.wire).ContextPathAlignment assembly.keptRoute.witness := by
  exact factorRouteAlignment input selection anchorLeaf route
    (FactorAssemblyCore.targetNotSelected assembly) partition

end FactorAssembly

noncomputable def FactorAssembly.selected
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (_assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    Region (partition.ancestorWires + partition.anchorLocal) rels :=
  .mk 0 (fragmentSelectedItems fragment partition)

noncomputable def FactorAssembly.sourceBody
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    Region partition.ancestorWires rels :=
  routedSelectedTarget partition (fragmentSelectedItems fragment partition)
    assembly.route_alignment.targetWitness

theorem FactorAssembly.sourceBody_localCount
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    assembly.sourceBody.localCount = partition.anchorLocal := by
  exact routedSelectedTarget_localCount partition
    (fragmentSelectedItems fragment partition)
    assembly.route_alignment.targetWitness

noncomputable def FactorAssembly.descendant
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    DiagramContext
      (partition.ancestorWires + assembly.sourceBody.localCount)
      assembly.route_alignment.targetWitness.toFocus.holeWires rels
      assembly.route_alignment.targetWitness.toFocus.holeRels := by
  let equality :
      partition.ancestorWires + partition.anchorLocal =
        partition.ancestorWires + assembly.sourceBody.localCount :=
    congrArg (fun localCount => partition.ancestorWires + localCount)
      assembly.sourceBody_localCount.symm
  exact Eq.mp
    (congrArg
      (fun sourceWires => DiagramContext sourceWires
        assembly.route_alignment.targetWitness.toFocus.holeWires rels
        assembly.route_alignment.targetWitness.toFocus.holeRels)
      equality)
    assembly.route_alignment.targetWitness.toFocus.context

noncomputable def FactorAssembly.remainder
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    Region assembly.route_alignment.targetWitness.toFocus.holeWires
      assembly.route_alignment.targetWitness.toFocus.holeRels :=
  assembly.route_alignment.targetWitness.toFocus.body

noncomputable def FactorAssembly.materialSource
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (_assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    Region partition.ancestorWires rels :=
  fragmentMaterialSource fragment partition

noncomputable def FactorAssembly.materialTarget
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    Region partition.ancestorWires rels :=
  Region.adjoinAt partition.anchorLocal .nil assembly.selected

namespace FactorAssembly

variable {input : Concrete.Checked}
variable {selection : CheckedSelection input.val}
variable {layout : FragmentLayout input.val selection}
variable {outer : Nat} {rels : RelCtx}
variable {anchorBody : Region outer rels}
variable {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
  selection.val.anchor (.here anchorBody)}
variable {spliceInput : Concrete.Splice.Input}
variable {fragment : FragmentInput input selection layout spliceInput}
variable {target : Fin input.val.regionCount} {path : List Nat}
variable {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
  target path}
variable {partition : @SourcePartition input selection outer rels anchorBody
  anchorLeaf}
variable (assembly : @FactorAssembly input selection layout outer rels
  anchorBody anchorLeaf spliceInput fragment target path route partition)

noncomputable def source_iso : RegionIso
    (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
    partition.sourceRegion assembly.sourceBody := by
  exact FactorAssemblyCore.source_iso assembly

/-- The assembly's actual full source-carrier normalization.  Its codomain is
the carrier in which the routed source body, descendant, and copy freshening
are observed. -/
noncomputable def sourceWire : FiniteEquiv
    (Fin (partition.ancestorWires + partition.anchorLocal))
    (Fin (partition.ancestorWires + assembly.sourceBody.localCount)) :=
  extendWireEquiv
    (FiniteEquiv.refl (Fin partition.ancestorWires))
    assembly.source_iso.localEquiv

noncomputable def material_iso : RegionIso
    (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
    assembly.materialSource assembly.materialTarget := by
  exact FactorAssemblyCore.material_iso assembly

/-- The selected compiler fragment's actual wire embedding into the assembly's
source carrier. -/
noncomputable def fragmentSourceEmbedding
    (_assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    Fin fragment.context.length →
      Fin (partition.ancestorWires + partition.anchorLocal) :=
  factorFragmentSourceEmbedding fragment partition

/-- The structural inclusion of the selected material endpoint into the
routed source endpoint. -/
noncomputable def sourceSelectedEmbedding :
    Fin (partition.ancestorWires + assembly.materialTarget.localCount) →
      Fin (partition.ancestorWires + assembly.sourceBody.localCount) := by
  exact factorSourceSelectedEmbedding input selection anchorLeaf fragment route
    (FactorAssemblyCore.targetNotSelected assembly) partition

/-- The source and material isomorphisms agree on the actual selected compiler
fragment embedding.  This is the assembly's semantic factorization square. -/
theorem selectedEmbedding_commuting :
    assembly.sourceSelectedEmbedding ∘
        ((extendWireEquiv
          (FiniteEquiv.refl (Fin partition.ancestorWires))
          assembly.material_iso.localEquiv).toFun ∘
            assembly.fragmentSourceEmbedding) =
      (extendWireEquiv
          (FiniteEquiv.refl (Fin partition.ancestorWires))
          assembly.source_iso.localEquiv).toFun ∘
        assembly.fragmentSourceEmbedding := by
  simpa only [sourceSelectedEmbedding, fragmentSourceEmbedding, source_iso,
    material_iso, sourceBody, materialTarget] using
      (FactorAssemblyCore.selected_embedding_commuting assembly)

noncomputable def copyWires : VisualProof.Rule.Iteration.WireFreshening
    (partition.ancestorWires + assembly.sourceBody.localCount)
    assembly.route_alignment.targetWitness.toFocus.holeWires
    selection.val.explicitWires.length
    assembly.descendant.outerWire := by
  let sourceOfFresh : Fin selection.val.explicitWires.length →
      Fin (partition.ancestorWires + assembly.sourceBody.localCount) :=
    fun fresh => assembly.sourceWire
      (partition.wire (sourceExplicitIndex input selection anchorLeaf fresh))
  have sourceOfFreshInjective : Function.Injective sourceOfFresh := by
    intro left right equality
    exact partitionSourceOfFresh_injective input selection anchorLeaf partition
      (assembly.sourceWire.injective equality)
  let copyWire := sourceFactorCopyWire sourceOfFresh
    assembly.descendant.outerWire
  exact {
    sourceOfFresh := sourceOfFresh
    sourceOfFresh_injective := sourceOfFreshInjective
    wire := copyWire
    wire_fresh := by
      intro fresh
      exact sourceFactorCopyWire_fresh sourceOfFresh sourceOfFreshInjective
        assembly.descendant.outerWire fresh
    wire_inherited := by
      intro source notFresh
      exact sourceFactorCopyWire_inherited sourceOfFresh
        assembly.descendant.outerWire source notFresh
  }

theorem copyWires_sourceOfFresh_get
    (fresh : Fin selection.val.explicitWires.length) :
    (anchorLeaf.inheritedWires.extend selection.val.anchor).get
        (partition.wire.symm
          (assembly.sourceWire.symm
            (assembly.copyWires.sourceOfFresh fresh))) =
      selection.val.explicitWires.get fresh := by
  change (anchorLeaf.inheritedWires.extend selection.val.anchor).get
      (partition.wire.symm
        (assembly.sourceWire.symm
          (assembly.sourceWire
            (partition.wire
              (sourceExplicitIndex input selection anchorLeaf fresh))))) = _
  have sourceCancellation : assembly.sourceWire.symm
        (assembly.sourceWire
          (partition.wire
            (sourceExplicitIndex input selection anchorLeaf fresh))) =
      partition.wire
        (sourceExplicitIndex input selection anchorLeaf fresh) :=
    assembly.sourceWire.left_inv _
  rw [sourceCancellation]
  have partitionCancellation : partition.wire.symm
        (partition.wire
          (sourceExplicitIndex input selection anchorLeaf fresh)) =
      sourceExplicitIndex input selection anchorLeaf fresh :=
    partition.wire.left_inv _
  rw [partitionCancellation]
  exact sourceExplicitIndex_spec input selection anchorLeaf fresh

/-- A fragment coordinate representing the selected explicit wire `fresh`
lands at that wire's distinguished fresh source after the assembly's actual
source normalization. -/
theorem sourceWire_fragmentSourceEmbedding_eq_sourceOfFresh
    (index : Fin fragment.context.length)
    (fresh : Fin selection.val.explicitWires.length)
    (represents :
      input.val.fragmentWireOrigin selection layout
          (fragment.context.get index) =
        selection.val.explicitWires.get fresh) :
    assembly.sourceWire (assembly.fragmentSourceEmbedding index) =
      assembly.copyWires.sourceOfFresh fresh := by
  change assembly.sourceWire
      (partition.wire
        (IterationExtraction.extractionContextIndexMap input selection layout
          fragment.context
          (anchorLeaf.inheritedWires.extend selection.val.anchor)
          fragment.contextExact anchorLeaf.wiresExact index)) =
    assembly.sourceWire
      (partition.wire
        (sourceExplicitIndex input selection anchorLeaf fresh))
  apply congrArg assembly.sourceWire
  apply congrArg partition.wire
  apply Fin.ext
  apply (List.getElem_inj anchorLeaf.wiresExact.nodup).mp
  simpa only [List.get_eq_getElem] using
    (IterationExtraction.extractionContextIndexMap_spec input selection layout
      fragment.context
      (anchorLeaf.inheritedWires.extend selection.val.anchor)
      fragment.contextExact anchorLeaf.wiresExact index).symm.trans
        (represents.trans
          (sourceExplicitIndex_spec input selection anchorLeaf fresh).symm)

end FactorAssembly

theorem FactorAssembly.keptPath_eq_nil_of_here
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment selection.val.anchor []
      (.here selection.val.anchor) partition) :
    assembly.keptRoute.keptPath = [] := by
  rfl

theorem FactorAssembly.routed_focus_eq
    {input : Concrete.Checked}
    {selection : CheckedSelection input.val}
    {layout : FragmentLayout input.val selection}
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    {anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody)}
    {spliceInput : Concrete.Splice.Input}
    {fragment : FragmentInput input selection layout spliceInput}
    {target : Fin input.val.regionCount} {path : List Nat}
    {route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path}
    {partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf}
    (assembly : @FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) :
    assembly.descendant.fill assembly.remainder =
      (Region.mk 0
        (assembly.keptItems.renameWires partition.wire)).castWiresEq
          (congrArg (fun localCount => partition.ancestorWires + localCount)
            assembly.sourceBody_localCount.symm) := by
  let equality :
      partition.ancestorWires + partition.anchorLocal =
        partition.ancestorWires + assembly.sourceBody.localCount :=
    congrArg (fun localCount => partition.ancestorWires + localCount)
      assembly.sourceBody_localCount.symm
  have transported := diagramContext_fill_transport_outer equality
    assembly.route_alignment.targetWitness.toFocus.context assembly.remainder
  have rebuilt :
      assembly.route_alignment.targetWitness.toFocus.context.fill
          assembly.remainder =
        Region.mk 0 (assembly.keptItems.renameWires partition.wire) := by
    simpa only [FactorAssembly.remainder, Region.renameWires,
      extendWireRenaming_zero] using
        assembly.route_alignment.targetWitness.toFocus.rebuild
  calc
    assembly.descendant.fill assembly.remainder =
        (assembly.route_alignment.targetWitness.toFocus.context.fill
          assembly.remainder).castWiresEq equality := by
      simpa only [FactorAssembly.descendant, equality] using transported
    _ = (Region.mk 0
          (assembly.keptItems.renameWires partition.wire)).castWiresEq
            equality :=
      congrArg (Region.castWiresEq equality) rebuilt

/-- Construct the coherent source factor from one carrier partition and one
fragment compiler witness. -/
theorem sourceFactor_complete
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (layout : FragmentLayout input.val selection)
    {outer : Nat} {rels : RelCtx}
    {anchorBody : Region outer rels}
    (anchorLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here anchorBody))
    {spliceInput : Concrete.Splice.Input}
    (fragment : FragmentInput input selection layout spliceInput)
    {target : Fin input.val.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input.val selection.val.anchor
      target path)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (partition : @SourcePartition input selection outer rels anchorBody
      anchorLeaf) :
    Nonempty (@FactorAssembly input selection layout outer rels anchorBody
      anchorLeaf spliceInput fragment target path route partition) := by
  let compiledPartition := factorPartitionResult anchorLeaf
  let hostSelectedItems := compiledPartition.selectedItems
  let keptItems := factorKeptItems anchorLeaf
  let selectedCompiled := compiledPartition.selectedCompiled
  let partitionIso := compiledPartition.iso
  let binderWitness :=
    IterationExtraction.ExtractionBinderWitness.terminal input selection layout
      fragment.binders fragment.enumeration anchorLeaf.binders
      anchorLeaf.bindersCover
  let preparedItems :=
    (fragment.items.renameRelations binderWitness.relationMap).renameWires
      (IterationExtraction.extractionContextIndexMap input selection layout
        fragment.context
        (anchorLeaf.inheritedWires.extend selection.val.anchor)
        fragment.contextExact anchorLeaf.wiresExact)
  have extractionIso :=
    IterationExtraction.extractionCompileSelectedItems_iso input selection
      layout fragment.fuel anchorLeaf.fuel fragment.context
      (anchorLeaf.inheritedWires.extend selection.val.anchor) fragment.binders
      anchorLeaf.binders fragment.enumeration anchorLeaf.binderEnumeration
      anchorLeaf.bindersCover fragment.contextExact anchorLeaf.wiresExact
      fragment.items hostSelectedItems fragment.computation selectedCompiled
  let selectedItems := fragmentSelectedItems fragment partition
  have selectedFactorIso : ItemSeqIso partition.wire rels hostSelectedItems
      selectedItems := by
    have renamed := ItemSeqIso.renameWiresEquiv preparedItems partition.wire
    have combined := extractionIso.trans renamed
    simpa only [selectedItems, fragmentSelectedItems, preparedItems,
      binderWitness, FiniteEquiv.trans, FiniteEquiv.refl] using combined
  have keptFactorIso : ItemSeqIso partition.wire rels keptItems
      (keptItems.renameWires partition.wire) :=
    ItemSeqIso.renameWiresEquiv keptItems partition.wire
  have partitionFactorIso : ItemSeqIso partition.wire rels anchorLeaf.items
      (selectedItems.append (keptItems.renameWires partition.wire)) := by
    have partitionItems : ItemSeqIso
        (FiniteEquiv.refl
          (Fin (anchorLeaf.inheritedWires.extend
            selection.val.anchor).length)) rels
        anchorLeaf.items (hostSelectedItems.append keptItems) := by
      have reversed := partitionIso.symm
      cases reversed with
      | mk localEquiv items =>
          have ambientSymm :
              (FiniteEquiv.refl
                (Fin (anchorLeaf.inheritedWires.extend
                  selection.val.anchor).length)).symm =
                FiniteEquiv.refl
                  (Fin (anchorLeaf.inheritedWires.extend
                    selection.val.anchor).length) := by
            apply FiniteEquiv.ext
            intro wire
            rfl
          rw [ambientSymm] at items
          have extendedRefl :
              extendWireEquiv
                  (FiniteEquiv.refl
                    (Fin (anchorLeaf.inheritedWires.extend
                      selection.val.anchor).length))
                  localEquiv =
                FiniteEquiv.refl
                  (Fin (anchorLeaf.inheritedWires.extend
                    selection.val.anchor).length) := by
            apply FiniteEquiv.ext
            intro wire
            refine Fin.addCases (fun index => ?_) (fun index => ?_) wire
            · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
            · exact Fin.elim0 index
          simpa only [extendedRefl] using items
    have partitioned := partitionItems.trans
      (ItemSeqIso.append selectedFactorIso keptFactorIso)
    simpa [FiniteEquiv.trans, FiniteEquiv.refl] using partitioned
  have sourceFactorItems : ItemSeqIso
      (FiniteEquiv.refl
        (Fin (partition.ancestorWires + partition.anchorLocal))) rels
      partition.sourceItems
      (selectedItems.append (keptItems.renameWires partition.wire)) := by
    have combined := partition.sourceItems_iso.symm.trans partitionFactorIso
    have cancel : partition.wire.symm.trans partition.wire =
        FiniteEquiv.refl
          (Fin (partition.ancestorWires + partition.anchorLocal)) := by
      apply FiniteEquiv.ext
      intro index
      exact partition.wire.right_inv index
    rw [cancel] at combined
    exact combined
  let routedAlignment := factorRouteAlignment input selection anchorLeaf route
    targetNotSelected partition
  have sourceTargetEq :
      routedSelectedTarget partition selectedItems
          routedAlignment.targetWitness =
        Region.mk partition.anchorLocal
          (selectedItems.append (keptItems.renameWires partition.wire)) := by
    unfold routedSelectedTarget
    rw [routedAlignment.targetWitness.toFocus.rebuild]
    simp only [Region.renameWires, extendWireRenaming_zero,
      Region.conjoin, Region.adjoinAt, Nat.add_zero,
      Region.conjoinLeftWire_zero, Region.conjoinRightWire_zero,
      Region.adjoinMaterialWire_zero, ItemSeq.renameWires_id,
      ItemSeq.renameWires, ItemSeq.nil_append, keptItems]
  let rawSourceIso : RegionIso
      (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
      partition.sourceRegion
      (Region.mk partition.anchorLocal
        (selectedItems.append (keptItems.renameWires partition.wire))) := by
    apply RegionIso.mk (FiniteEquiv.refl (Fin partition.anchorLocal))
    have extendedRefl :
        extendWireEquiv
            (FiniteEquiv.refl (Fin partition.ancestorWires))
            (FiniteEquiv.refl (Fin partition.anchorLocal)) =
          FiniteEquiv.refl
            (Fin (partition.ancestorWires + partition.anchorLocal)) := by
      apply FiniteEquiv.ext
      intro index
      refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
      · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
      · simp only [extendWireEquiv_local, FiniteEquiv.refl_apply]
    simpa only [extendedRefl] using sourceFactorItems
  let sourceIso : RegionIso
      (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
      partition.sourceRegion
      (routedSelectedTarget partition selectedItems
        routedAlignment.targetWitness) :=
    Eq.mp (congrArg (fun targetRegion => RegionIso
      (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
      partition.sourceRegion targetRegion) sourceTargetEq.symm) rawSourceIso
  let materialSource := fragmentMaterialSource fragment partition
  let materialIso : RegionIso
      (FiniteEquiv.refl (Fin partition.ancestorWires)) rels
      materialSource
      (Region.adjoinAt partition.anchorLocal .nil
        (Region.mk 0 selectedItems)) := by
    apply RegionIso.mk (FiniteEquiv.refl (Fin partition.anchorLocal))
    have extendedRefl :
        extendWireEquiv
            (FiniteEquiv.refl (Fin partition.ancestorWires))
            (FiniteEquiv.refl (Fin partition.anchorLocal)) =
          FiniteEquiv.refl
            (Fin (partition.ancestorWires + partition.anchorLocal)) := by
      apply FiniteEquiv.ext
      intro index
      refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
      · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
      · simp only [extendWireEquiv_local, FiniteEquiv.refl_apply]
    rw [extendedRefl]
    simpa only [Region.adjoinAt, Nat.add_zero, Region.adjoinMaterialWire_zero,
      ItemSeq.renameWires_id, ItemSeq.renameWires, ItemSeq.nil_append,
      materialSource, fragmentMaterialSource, selectedItems] using
      (ItemSeqIso.refl selectedItems)
  exact ⟨{
    targetNotSelected := targetNotSelected
    source_iso := sourceIso
    material_iso := materialIso
    selected_embedding_commuting := by
      have sourceLocal :
          sourceIso.localEquivCast rfl
              (routedSelectedTarget_localCount partition selectedItems
                routedAlignment.targetWitness) =
            FiniteEquiv.refl (Fin partition.anchorLocal) := by
        have transported := RegionIso.localEquivCast_castEndpoints
          rawSourceIso rfl sourceTargetEq.symm rfl rfl rfl
            (routedSelectedTarget_localCount partition selectedItems
              routedAlignment.targetWitness)
        simpa only [sourceIso, rawSourceIso, RegionIso.localEquivCast]
          using transported
      have materialLocal :
          materialIso.localEquivCast rfl
              (fragmentMaterialTarget_localCount partition selectedItems) =
            FiniteEquiv.refl (Fin partition.anchorLocal) := by
        rfl
      have fullWire := regionIso_extendedWire_commuting materialIso sourceIso
        rfl rfl (fragmentMaterialTarget_localCount partition selectedItems)
        (routedSelectedTarget_localCount partition selectedItems
          routedAlignment.targetWitness)
        (materialLocal.trans sourceLocal.symm)
      have selectedWire := congrArg
        (fun wireMap => wireMap ∘
          factorFragmentSourceEmbedding fragment partition) fullWire
      simpa only [factorSourceSelectedEmbedding, Function.comp_def]
        using selectedWire
  }⟩

end VisualProof.Refinement.Implementation.IterationSourceFactor
