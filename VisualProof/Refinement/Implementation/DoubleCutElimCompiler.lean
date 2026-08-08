import VisualProof.Refinement.Implementation.DoubleCutElimTransport
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.DoubleCutElimCompiler

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutElimTransport

/-- Pointwise agreement of the visible wire identities across promotion. -/
def PromotionWireContextsAgree
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (source : Concrete.Elaboration.WireContext input)
    (target : Concrete.Elaboration.WireContext (Target trace))
    (ambient : FiniteEquiv (Fin source.length) (Fin target.length)) : Prop :=
  ∀ index, target.get (ambient index) = source.get index

/-- Pointwise binder agreement through the compact survivor origin map. -/
def PromotionBinderContextsAgree
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (source : Concrete.Elaboration.BinderContext input rels)
    (target : Concrete.Elaboration.BinderContext (Target trace) rels) : Prop :=
  ∀ binder, target binder =
    source ((Domain input outer trace.inner).origin binder)

private theorem region_ne_target
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (notAboveTarget : ¬ input.Encloses region trace.target) :
    region ≠ trace.target := by
  intro equality
  subst region
  exact notAboveTarget (Concrete.Diagram.Encloses.refl input trace.target)

private theorem child_survives
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    {region child : Fin input.regionCount}
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (parent : (input.regions child).parent? = some region) :
    (Domain input outer trace.inner).survives child = true := by
  rw [domain_survives_iff]
  have regionCases := (domain_survives_iff input outer trace.inner region).1
    regionSurvives
  constructor
  · intro equality
    subst child
    have outerParent : (input.regions outer).parent? = some trace.target := by
      rw [trace.outer_eq]
      rfl
    have : region = trace.target := Option.some.inj (parent.symm.trans outerParent)
    exact regionNeTarget this
  · intro equality
    subst child
    have innerParent : (input.regions trace.inner).parent? = some outer := by
      rw [trace.inner_eq]
      rfl
    exact regionCases.1 (Option.some.inj (parent.symm.trans innerParent))

private theorem child_not_above_target
    {input : Concrete.Diagram} (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    {region child : Fin input.regionCount}
    (notAboveTarget : ¬ input.Encloses region trace.target)
    (parent : (input.regions child).parent? = some region) :
    ¬ input.Encloses child trace.target := by
  intro childAbove
  have regionAboveChild : input.Encloses region child := by
    refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
    simp [Concrete.Diagram.climb, parent]
  exact notAboveTarget (Concrete.Elaboration.checked_encloses_trans
    inputWellFormed regionAboveChild childAbove)

private theorem exact_scope_mem_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (wire : Fin input.wireCount) :
    wire ∈ Concrete.Elaboration.exactScopeWires (Target trace)
        ((Domain input outer trace.inner).index region regionSurvives) ↔
      wire ∈ Concrete.Elaboration.exactScopeWires input region := by
  let domain := Domain input outer trace.inner
  have regionNeInner :=
    (domain_survives_iff input outer trace.inner region).1 regionSurvives |>.2
  constructor
  · intro member
    have equality := (Concrete.Elaboration.mem_exactScopeWires
      (Target trace) (domain.index region regionSurvives)
      (show Fin (Target trace).wireCount from wire)).1 member
    rw [target_wire_scope input inputWellFormed trace wire] at equality
    have origins := congrArg domain.origin equality
    rw [promoteRegionIndex_origin, domain.origin_index] at origins
    by_cases innerCase : (input.wires wire).scope = trace.inner
    · simp only [if_pos innerCase] at origins
      exact False.elim (regionNeTarget origins.symm)
    · exact (Concrete.Elaboration.mem_exactScopeWires input region wire).2
        (by simpa only [if_neg innerCase] using origins)
  · intro member
    have equality := (Concrete.Elaboration.mem_exactScopeWires
      input region wire).1 member
    have targetEquality : ((Target trace).wires wire).scope =
        domain.index region regionSurvives := by
      rw [target_wire_scope input inputWellFormed trace wire]
      apply domain.origin_injective
      rw [promoteRegionIndex_origin, domain.origin_index]
      simp only [equality, if_neg regionNeInner]
    exact (Concrete.Elaboration.mem_exactScopeWires
      (Target trace) (domain.index region regionSurvives)
      (show Fin (Target trace).wireCount from wire)).2 targetEquality

noncomputable def localWireEquiv
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target) :
    FiniteEquiv
      (Fin (Concrete.Elaboration.exactScopeWires input region).length)
      (Fin (Concrete.Elaboration.exactScopeWires (Target trace)
        ((Domain input outer trace.inner).index region regionSurvives)).length) :=
  FiniteEquiv.restrictLists (FiniteEquiv.refl (Fin input.wireCount))
    (Concrete.Elaboration.exactScopeWires input region)
    (Concrete.Elaboration.exactScopeWires (Target trace)
      ((Domain input outer trace.inner).index region regionSurvives))
    (Concrete.Elaboration.exactScopeWires_nodup input region)
    (Concrete.Elaboration.exactScopeWires_nodup (Target trace)
      ((Domain input outer trace.inner).index region regionSurvives))
    (fun wire => by
      simpa using (exact_scope_mem_iff input inputWellFormed trace region
        regionSurvives regionNeTarget wire))

@[simp] theorem localWireEquiv_spec
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (index : Fin (Concrete.Elaboration.exactScopeWires input region).length) :
    (Concrete.Elaboration.exactScopeWires (Target trace)
      ((Domain input outer trace.inner).index region regionSurvives)).get
        (localWireEquiv input inputWellFormed trace region regionSurvives
          regionNeTarget index) =
      (Concrete.Elaboration.exactScopeWires input region).get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.wireCount))
    (Concrete.Elaboration.exactScopeWires input region)
    (Concrete.Elaboration.exactScopeWires (Target trace)
      ((Domain input outer trace.inner).index region regionSurvives))
    (Concrete.Elaboration.exactScopeWires_nodup input region)
    (Concrete.Elaboration.exactScopeWires_nodup (Target trace)
      ((Domain input outer trace.inner).index region regionSurvives))
    (fun wire => by
      simpa using (exact_scope_mem_iff input inputWellFormed trace region
        regionSurvives regionNeTarget wire)) index

private theorem append_agreement
    {sourceAmbient sourceLocal targetAmbient targetLocal : List α}
    (ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length))
    (localEquiv : FiniteEquiv (Fin sourceLocal.length) (Fin targetLocal.length))
    (ambientAgreement : ∀ index,
      targetAmbient.get (ambient index) = sourceAmbient.get index)
    (localAgreement : ∀ index,
      targetLocal.get (localEquiv index) = sourceLocal.get index) :
    ∀ index,
      (targetAmbient ++ targetLocal).get
          (Concrete.Elaboration.appendContextEquiv ambient localEquiv index) =
        (sourceAmbient ++ sourceLocal).get index := by
  intro index
  let sumIndex : Fin (sourceAmbient.length + sourceLocal.length) :=
    Fin.cast (by simp) index
  have sourceIndex : Fin.cast (by simp) sumIndex = index := by
    apply Fin.ext
    rfl
  rw [← sourceIndex]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) sumIndex
  · simp only [Concrete.Elaboration.get_append_castAdd]
    calc
      _ = (targetAmbient ++ targetLocal).get
          (Fin.cast (by simp)
            (Fin.castAdd targetLocal.length (ambient outerIndex))) := by
        congr 1
        apply Fin.ext
        simp [Concrete.Elaboration.appendContextEquiv,
          Concrete.Elaboration.castFinEquiv, extendWireEquiv]
      _ = targetAmbient.get (ambient outerIndex) :=
        Concrete.Elaboration.get_append_castAdd targetAmbient targetLocal _
      _ = sourceAmbient.get outerIndex := ambientAgreement outerIndex
  · simp only [Concrete.Elaboration.get_append_natAdd]
    calc
      _ = (targetAmbient ++ targetLocal).get
          (Fin.cast (by simp)
            (Fin.natAdd targetAmbient.length (localEquiv localIndex))) := by
        congr 1
        apply Fin.ext
        simp [Concrete.Elaboration.appendContextEquiv,
          Concrete.Elaboration.castFinEquiv, extendWireEquiv]
      _ = targetLocal.get (localEquiv localIndex) :=
        Concrete.Elaboration.get_append_natAdd targetAmbient targetLocal _
      _ = sourceLocal.get localIndex := localAgreement localIndex

private def appendContextMap
    {sourceAmbient sourceLocal targetAmbient targetLocal : List α}
    (ambient : Fin sourceAmbient.length → Fin targetAmbient.length)
    (localMap : Fin sourceLocal.length → Fin targetLocal.length) :
    Fin (sourceAmbient ++ sourceLocal).length →
      Fin (targetAmbient ++ targetLocal).length :=
  fun index =>
    let sourceIndex : Fin (sourceAmbient.length + sourceLocal.length) :=
      Fin.cast (by simp) index
    let targetIndex : Fin (targetAmbient.length + targetLocal.length) :=
      Fin.addCases
        (fun outerIndex => Fin.castAdd targetLocal.length (ambient outerIndex))
        (fun localIndex => Fin.natAdd targetAmbient.length (localMap localIndex))
        sourceIndex
    Fin.cast (by simp) targetIndex

private theorem appendContextMap_spec
    {sourceAmbient sourceLocal targetAmbient targetLocal : List α}
    (ambient : Fin sourceAmbient.length → Fin targetAmbient.length)
    (localMap : Fin sourceLocal.length → Fin targetLocal.length)
    (ambientAgreement : ∀ index,
      targetAmbient.get (ambient index) = sourceAmbient.get index)
    (localAgreement : ∀ index,
      targetLocal.get (localMap index) = sourceLocal.get index) :
    ∀ index,
      (targetAmbient ++ targetLocal).get
          (appendContextMap ambient localMap index) =
        (sourceAmbient ++ sourceLocal).get index := by
  intro index
  let sourceIndex : Fin (sourceAmbient.length + sourceLocal.length) :=
    Fin.cast (by simp) index
  have sourceIndexEq : Fin.cast (by simp) sourceIndex = index := by
    apply Fin.ext
    rfl
  rw [← sourceIndexEq]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_)
    sourceIndex
  · simpa [appendContextMap,
      Concrete.Elaboration.get_append_castAdd] using
        ambientAgreement outerIndex
  · simpa [appendContextMap,
      Concrete.Elaboration.get_append_natAdd] using
        localAgreement localIndex

private theorem itemSeqIso_after_rename
    (source : ItemSeq sourceWires rels)
    (target : ItemSeq targetWires rels)
    (wireMap : Fin sourceWires → Fin targetWires)
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : ∀ sourceIndex,
      ItemIso (FiniteEquiv.refl (Fin targetWires)) rels
        ((source.get sourceIndex).renameWires wireMap)
        (target.get (positions sourceIndex))) :
    ItemSeqIso (FiniteEquiv.refl (Fin targetWires)) rels
      (source.renameWires wireMap) target := by
  let sourcePositions := source.renameWiresPositionEquiv wireMap
  let renamedPositions := sourcePositions.symm.trans positions
  apply ItemSeqIso.permute renamedPositions
  intro renamedIndex
  let sourceIndex := sourcePositions.symm renamedIndex
  have sourceIndexEq : sourcePositions sourceIndex = renamedIndex :=
    sourcePositions.right_inv renamedIndex
  rw [← sourceIndexEq]
  change ItemIso (FiniteEquiv.refl (Fin targetWires)) rels
    ((source.renameWires wireMap).get (sourcePositions sourceIndex))
    (target.get (positions sourceIndex))
  rw [ItemSeq.get_renameWires]
  exact items sourceIndex

private noncomputable def extendedWireEquiv
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (notAboveTarget : ¬ input.Encloses region trace.target)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length)) :
    FiniteEquiv (Fin (sourceContext.extend region).length)
      (Fin (targetContext.extend
        ((Domain input outer trace.inner).index region regionSurvives)).length) :=
  Concrete.Elaboration.appendContextEquiv ambient
    (localWireEquiv input inputWellFormed trace region regionSurvives
      (region_ne_target trace region notAboveTarget))

private theorem extendedWireEquiv_spec
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (notAboveTarget : ¬ input.Encloses region trace.target)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (agreement : ∀ index,
      targetContext.get (ambient index) = sourceContext.get index) :
    ∀ index,
      (targetContext.extend
        ((Domain input outer trace.inner).index region regionSurvives)).get
          (extendedWireEquiv input inputWellFormed trace region regionSurvives
            notAboveTarget sourceContext targetContext ambient index) =
        (sourceContext.extend region).get index := by
  exact append_agreement ambient
    (localWireEquiv input inputWellFormed trace region regionSurvives
      (region_ne_target trace region notAboveTarget)) agreement
    (localWireEquiv_spec input inputWellFormed trace region regionSurvives
      (region_ne_target trace region notAboveTarget))

private theorem mem_iff_of_agreement
    {source target : List α}
    (equiv : FiniteEquiv (Fin source.length) (Fin target.length))
    (agreement : ∀ index, target.get (equiv index) = source.get index)
    (value : α) : value ∈ target ↔ value ∈ source := by
  constructor
  · intro targetMember
    obtain ⟨targetIndex, targetValue⟩ := List.mem_iff_get.mp targetMember
    let sourceIndex := equiv.symm targetIndex
    apply List.mem_iff_get.mpr
    refine ⟨sourceIndex, ?_⟩
    calc
      source.get sourceIndex = target.get (equiv sourceIndex) :=
        (agreement sourceIndex).symm
      _ = target.get targetIndex := by
        rw [show equiv sourceIndex = targetIndex from equiv.right_inv targetIndex]
      _ = value := targetValue
  · intro sourceMember
    obtain ⟨sourceIndex, sourceValue⟩ := List.mem_iff_get.mp sourceMember
    apply List.mem_iff_get.mpr
    refine ⟨equiv sourceIndex, ?_⟩
    exact (agreement sourceIndex).trans sourceValue

theorem promoted_cut
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    {parent child : Fin input.regionCount}
    (parentNeOuter : parent ≠ outer)
    (childSurvives : (Domain input outer trace.inner).survives child = true)
    (shape : input.regions child = .cut parent) :
    (Target trace).regions
        ((Domain input outer trace.inner).index child childSurvives) =
      .cut (promoteRegionIndex input inputWellFormed trace parent
        parentNeOuter) := by
  change trace.promotion.regions
      ((Domain input outer trace.inner).index child childSurvives) = _
  have result := trace.promotion.region_result
    ((Domain input outer trace.inner).index child childSurvives)
  have originEq :=
    (Domain input outer trace.inner).origin_index child childSurvives
  rw [originEq, shape] at result
  unfold promoteRegionIndex
  by_cases parentEqInner : parent = trace.inner
  · rw [dif_pos parentEqInner]
    simp only [Concrete.promoteRegion?, if_pos parentEqInner,
      (Domain input outer trace.inner).index?_index trace.target
        (target_survives input inputWellFormed trace.outer_eq
          trace.inner_eq), Option.map_some] at result
    exact (Option.some.inj result).symm
  · rw [dif_neg parentEqInner]
    have parentSurvives :=
      (domain_survives_iff input outer trace.inner parent).2
        ⟨parentNeOuter, parentEqInner⟩
    simp only [Concrete.promoteRegion?, if_neg parentEqInner,
      (Domain input outer trace.inner).index?_index parent parentSurvives,
      Option.map_some] at result
    exact (Option.some.inj result).symm

theorem promoted_bubble
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    {parent child : Fin input.regionCount}
    (parentNeOuter : parent ≠ outer)
    (childSurvives : (Domain input outer trace.inner).survives child = true)
    {arity : Nat} (shape : input.regions child = .bubble parent arity) :
    (Target trace).regions
        ((Domain input outer trace.inner).index child childSurvives) =
      .bubble (promoteRegionIndex input inputWellFormed trace parent
        parentNeOuter)
        arity := by
  change trace.promotion.regions
      ((Domain input outer trace.inner).index child childSurvives) = _
  have result := trace.promotion.region_result
    ((Domain input outer trace.inner).index child childSurvives)
  have originEq :=
    (Domain input outer trace.inner).origin_index child childSurvives
  rw [originEq, shape] at result
  unfold promoteRegionIndex
  by_cases parentEqInner : parent = trace.inner
  · rw [dif_pos parentEqInner]
    simp only [Concrete.promoteRegion?, if_pos parentEqInner,
      (Domain input outer trace.inner).index?_index trace.target
        (target_survives input inputWellFormed trace.outer_eq
          trace.inner_eq), Option.map_some] at result
    exact (Option.some.inj result).symm
  · rw [dif_neg parentEqInner]
    have parentSurvives :=
      (domain_survives_iff input outer trace.inner parent).2
        ⟨parentNeOuter, parentEqInner⟩
    simp only [Concrete.promoteRegion?, if_neg parentEqInner,
      (Domain input outer trace.inner).index?_index parent parentSurvives,
      Option.map_some] at result
    exact (Option.some.inj result).symm

def promoteOccurrence
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (fallback : Fin (Domain input outer trace.inner).count) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount →
      Concrete.Elaboration.LocalOccurrence (Target trace).regionCount
        (Target trace).nodeCount
  | .node node => .node node
  | .child child => .child (if survives :
      (Domain input outer trace.inner).survives child = true then
        (Domain input outer trace.inner).index child survives
      else fallback)

def sourceOccurrence
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.LocalOccurrence (Target trace).regionCount
        (Target trace).nodeCount →
      Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount
  | .node node => .node node
  | .child child =>
      .child ((Domain input outer trace.inner).origin child)

theorem promote_sourceOccurrence
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (fallback : Fin (Domain input outer trace.inner).count)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      (Target trace).regionCount (Target trace).nodeCount) :
    promoteOccurrence trace fallback (sourceOccurrence trace occurrence) =
      occurrence := by
  cases occurrence with
  | node node => rfl
  | child child =>
      simp only [sourceOccurrence, promoteOccurrence]
      rw [dif_pos ((Domain input outer trace.inner).origin_survives child)]
      exact congrArg Concrete.Elaboration.LocalOccurrence.child
        ((Domain input outer trace.inner).index_origin child)

theorem source_promoteOccurrence
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (fallback : Fin (Domain input outer trace.inner).count)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount)
    (survival : match occurrence with
      | .node _ => True
      | .child child =>
          (Domain input outer trace.inner).survives child = true) :
    sourceOccurrence trace (promoteOccurrence trace fallback occurrence) =
      occurrence := by
  cases occurrence with
  | node node => rfl
  | child child =>
      simp only [promoteOccurrence, sourceOccurrence]
      rw [dif_pos survival]
      exact congrArg Concrete.Elaboration.LocalOccurrence.child
        ((Domain input outer trace.inner).origin_index child survival)

theorem source_promoteOccurrence_of_children_survive
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (fallback : Fin (Domain input outer trace.inner).count)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount)
    (childrenSurvive : ∀ child,
      occurrence = .child child →
        (Domain input outer trace.inner).survives child = true) :
    sourceOccurrence trace (promoteOccurrence trace fallback occurrence) =
      occurrence := by
  cases occurrence with
  | node node => rfl
  | child child =>
      exact source_promoteOccurrence trace fallback (.child child)
        (childrenSurvive child rfl)

private theorem promoteRegionIndex_eq_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (candidate : Fin input.regionCount) (candidateNeOuter : candidate ≠ outer) :
    promoteRegionIndex input inputWellFormed trace candidate candidateNeOuter =
        (Domain input outer trace.inner).index region regionSurvives ↔
      candidate = region := by
  have regionNeInner :=
    (domain_survives_iff input outer trace.inner region).1 regionSurvives |>.2
  constructor
  · intro equality
    have origins := congrArg (Domain input outer trace.inner).origin equality
    rw [promoteRegionIndex_origin,
      (Domain input outer trace.inner).origin_index region regionSurvives]
      at origins
    by_cases innerCase : candidate = trace.inner
    · simp only [if_pos innerCase] at origins
      exact False.elim (regionNeTarget origins.symm)
    · simpa only [if_neg innerCase] using origins
  · intro equality
    subst candidate
    apply (Domain input outer trace.inner).origin_injective
    rw [promoteRegionIndex_origin,
      (Domain input outer trace.inner).origin_index region regionSurvives]
    simp only [if_neg regionNeInner]

private theorem target_node_region_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (node : Fin input.nodeCount) :
    ((Target trace).nodes node).region =
        (Domain input outer trace.inner).index region regionSurvives ↔
      (input.nodes node).region = region := by
  change (trace.promotion.nodes node).region = _ ↔ _
  rw [promotion_node input inputWellFormed trace node]
  unfold promotedNodeValue
  split
  · rename_i owner arity nodeEq
    have ownerNe : owner ≠ outer := by
      simpa [nodeEq] using node_region_ne_outer trace node
    simpa only [nodeEq, Concrete.CNode.region] using
      promoteRegionIndex_eq_iff input inputWellFormed trace region
        regionSurvives regionNeTarget owner ownerNe
  · rename_i owner binder nodeEq
    have ownerNe : owner ≠ outer := by
      simpa [nodeEq] using node_region_ne_outer trace node
    simpa only [nodeEq, Concrete.CNode.region] using
      promoteRegionIndex_eq_iff input inputWellFormed trace region
        regionSurvives regionNeTarget owner ownerNe

private theorem target_child_parent_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (child : Fin (Domain input outer trace.inner).count) :
    ((Target trace).regions child).parent? =
        some ((Domain input outer trace.inner).index region regionSurvives) ↔
      (input.regions
        ((Domain input outer trace.inner).origin child)).parent? = some region := by
  change (trace.promotion.regions child).parent? = some _ ↔ _
  rw [promotion_region input inputWellFormed trace child]
  unfold promotedRegionValue
  split
  · rename_i regionEq
    rw [regionEq]
    simp [Concrete.CRegion.parent?]
  · rename_i parent regionEq
    have parentNe := survivor_parent_ne_outer trace child parent (by
      rw [regionEq]
      rfl)
    simpa only [regionEq, Concrete.CRegion.parent?, Option.some.injEq] using
      promoteRegionIndex_eq_iff input inputWellFormed trace region
        regionSurvives regionNeTarget parent parentNe
  · rename_i parent arity regionEq
    have parentNe := survivor_parent_ne_outer trace child parent (by
      rw [regionEq]
      rfl)
    simpa only [regionEq, Concrete.CRegion.parent?, Option.some.injEq] using
      promoteRegionIndex_eq_iff input inputWellFormed trace region
        regionSurvives regionNeTarget parent parentNe

private theorem promoteOccurrence_mem
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount)
    (member : occurrence ∈ Concrete.Elaboration.localOccurrences input region) :
    promoteOccurrence trace
        ((Domain input outer trace.inner).index region regionSurvives)
        occurrence ∈
      Concrete.Elaboration.localOccurrences (Target trace)
        ((Domain input outer trace.inner).index region regionSurvives) := by
  cases occurrence with
  | node node =>
      simp only [promoteOccurrence]
      rw [Concrete.Elaboration.mem_localOccurrences_node] at member ⊢
      exact (target_node_region_iff input inputWellFormed trace region
        regionSurvives regionNeTarget node).2 member
  | child child =>
      have survival := child_survives trace regionSurvives regionNeTarget
        ((Concrete.Elaboration.mem_localOccurrences_child input region child).1
          member)
      simp only [promoteOccurrence, dif_pos survival]
      rw [Concrete.Elaboration.mem_localOccurrences_child]
      apply (target_child_parent_iff input inputWellFormed trace region
        regionSurvives regionNeTarget
        ((Domain input outer trace.inner).index child survival)).2
      rw [(Domain input outer trace.inner).origin_index child survival]
      exact (Concrete.Elaboration.mem_localOccurrences_child input region child).1
        member

private theorem sourceOccurrence_mem
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      (Target trace).regionCount (Target trace).nodeCount)
    (member : occurrence ∈ Concrete.Elaboration.localOccurrences
      (Target trace)
      ((Domain input outer trace.inner).index region regionSurvives)) :
    sourceOccurrence trace occurrence ∈
      Concrete.Elaboration.localOccurrences input region := by
  cases occurrence with
  | node node =>
      simp only [sourceOccurrence]
      rw [Concrete.Elaboration.mem_localOccurrences_node] at member ⊢
      exact (target_node_region_iff input inputWellFormed trace region
        regionSurvives regionNeTarget node).1 member
  | child child =>
      simp only [sourceOccurrence]
      rw [Concrete.Elaboration.mem_localOccurrences_child] at member ⊢
      exact (target_child_parent_iff input inputWellFormed trace region
        regionSurvives regionNeTarget child).1 member

noncomputable def localOccurrenceEquiv
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target) :
    FiniteEquiv
      (Fin (Concrete.Elaboration.localOccurrences input region).length)
      (Fin (Concrete.Elaboration.localOccurrences (Target trace)
        ((Domain input outer trace.inner).index region regionSurvives)).length) where
  toFun := fun index => Classical.choose (indexOf?_complete
    (promoteOccurrence_mem input inputWellFormed trace region regionSurvives
      regionNeTarget _ (List.get_mem _ index)))
  invFun := fun index => Classical.choose (indexOf?_complete
    (sourceOccurrence_mem input inputWellFormed trace region regionSurvives
      regionNeTarget _ (List.get_mem _ index)))
  left_inv := by
    intro index
    apply Fin.ext
    apply (List.getElem_inj
      (Concrete.Elaboration.localOccurrences_nodup input region)).mp
    have forward := indexOf?_sound (Classical.choose_spec (indexOf?_complete
      (promoteOccurrence_mem input inputWellFormed trace region regionSurvives
        regionNeTarget _ (List.get_mem _ index))))
    have backward := indexOf?_sound (Classical.choose_spec (indexOf?_complete
      (sourceOccurrence_mem input inputWellFormed trace region regionSurvives
        regionNeTarget _ (List.get_mem _ (Classical.choose
          (indexOf?_complete
            (promoteOccurrence_mem input inputWellFormed trace region
              regionSurvives regionNeTarget _ (List.get_mem _ index))))))))
    have roundtrip : sourceOccurrence trace
        (promoteOccurrence trace
          ((Domain input outer trace.inner).index region regionSurvives)
          ((Concrete.Elaboration.localOccurrences input region).get index)) =
        (Concrete.Elaboration.localOccurrences input region).get index := by
      cases occurrenceEq :
          (Concrete.Elaboration.localOccurrences input region).get index with
      | node node => rfl
      | child child =>
          have member : Concrete.Elaboration.LocalOccurrence.child child ∈
              Concrete.Elaboration.localOccurrences input region := by
            rw [← occurrenceEq]
            exact List.get_mem _ index
          have survival := child_survives trace regionSurvives regionNeTarget
            ((Concrete.Elaboration.mem_localOccurrences_child input region
              child).1 member)
          simpa only [occurrenceEq] using
            (source_promoteOccurrence trace
              ((Domain input outer trace.inner).index region regionSurvives)
              (Concrete.Elaboration.LocalOccurrence.child child) survival)
    calc
      _ = sourceOccurrence trace
          ((Concrete.Elaboration.localOccurrences (Target trace)
            ((Domain input outer trace.inner).index region regionSurvives)).get
              (Classical.choose (indexOf?_complete
                (promoteOccurrence_mem input inputWellFormed trace region
                  regionSurvives regionNeTarget _ (List.get_mem _ index))))) :=
        backward
      _ = sourceOccurrence trace
          (promoteOccurrence trace
            ((Domain input outer trace.inner).index region regionSurvives)
            ((Concrete.Elaboration.localOccurrences input region).get index)) :=
        congrArg (sourceOccurrence trace) (by
          simpa only [List.get_eq_getElem] using forward)
      _ = _ := roundtrip
  right_inv := by
    intro index
    apply Fin.ext
    apply (List.getElem_inj
      (Concrete.Elaboration.localOccurrences_nodup (Target trace)
        ((Domain input outer trace.inner).index region regionSurvives))).mp
    have backward := indexOf?_sound (Classical.choose_spec (indexOf?_complete
      (sourceOccurrence_mem input inputWellFormed trace region regionSurvives
        regionNeTarget _ (List.get_mem _ index))))
    have forward := indexOf?_sound (Classical.choose_spec (indexOf?_complete
      (promoteOccurrence_mem input inputWellFormed trace region regionSurvives
        regionNeTarget _ (List.get_mem _ (Classical.choose
          (indexOf?_complete
            (sourceOccurrence_mem input inputWellFormed trace region
              regionSurvives regionNeTarget _ (List.get_mem _ index))))))))
    calc
      _ = promoteOccurrence trace
          ((Domain input outer trace.inner).index region regionSurvives)
          ((Concrete.Elaboration.localOccurrences input region).get
            (Classical.choose (indexOf?_complete
              (sourceOccurrence_mem input inputWellFormed trace region
                regionSurvives regionNeTarget _ (List.get_mem _ index))))) :=
        forward
      _ = promoteOccurrence trace
          ((Domain input outer trace.inner).index region regionSurvives)
          (sourceOccurrence trace
            ((Concrete.Elaboration.localOccurrences (Target trace)
              ((Domain input outer trace.inner).index region regionSurvives)).get
                index)) :=
        congrArg (promoteOccurrence trace
          ((Domain input outer trace.inner).index region regionSurvives)) (by
            simpa only [List.get_eq_getElem] using backward)
      _ = _ := promote_sourceOccurrence trace _ _

theorem localOccurrenceEquiv_spec
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (regionSurvives : (Domain input outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (index : Fin (Concrete.Elaboration.localOccurrences input region).length) :
    (Concrete.Elaboration.localOccurrences (Target trace)
      ((Domain input outer trace.inner).index region regionSurvives)).get
        (localOccurrenceEquiv input inputWellFormed trace region regionSurvives
          regionNeTarget index) =
      promoteOccurrence trace
        ((Domain input outer trace.inner).index region regionSurvives)
        ((Concrete.Elaboration.localOccurrences input region).get index) := by
  unfold localOccurrenceEquiv
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (promoteOccurrence_mem input inputWellFormed trace region regionSurvives
      regionNeTarget _ (List.get_mem _ index))))

private theorem endpointOccurs_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) (node : Fin input.nodeCount)
    (port : Concrete.CPort) :
    (Target trace).EndpointOccurs wire ⟨node, port⟩ ↔
      input.EndpointOccurs wire ⟨node, port⟩ := by
  unfold Concrete.Diagram.EndpointOccurs
  change ⟨node, port⟩ ∈ (trace.promotion.wires wire).endpoints ↔ _
  rw [promotion_wire input inputWellFormed trace wire]
  rfl

theorem compileNode_promotion
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {rels : RelCtx}
    (region : Fin input.regionCount)
    (regionNeOuter : region ≠ outer)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireAgreement : ∀ index,
      targetContext.get (wireMap index) = sourceContext.get index)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact
      (promoteRegionIndex input inputWellFormed trace region regionNeOuter))
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (binderAgreement : ∀ binder,
      targetBinders binder = sourceBinders
        ((Domain input outer trace.inner).origin binder))
    (node : Fin input.nodeCount)
    (nodeRegion : (input.nodes node).region = region)
    {sourceItem : Item sourceContext.length rels}
    {targetItem : Item targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileNode? input sourceContext
      sourceBinders node = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileNode? (Target trace)
      targetContext targetBinders node = some targetItem) :
    ItemIso (FiniteEquiv.refl (Fin targetContext.length)) rels
      (sourceItem.renameWires wireMap) targetItem := by
  have ports : ∀ port,
      Concrete.Elaboration.resolvePort? (Target trace) targetContext node port =
        (Concrete.Elaboration.resolvePort? input sourceContext node port).map
          wireMap := by
    intro port
    exact Concrete.Elaboration.resolvePort?_map_of_embedding
      sourceContext targetContext node node id (fun _ _ equality => equality)
      wireMap targetExact.nodup
      (by simpa using wireAgreement)
      (fun candidate occurs =>
        (endpointOccurs_iff input inputWellFormed trace candidate node
          port).2 occurs)
      (fun candidate occurs =>
        ⟨candidate, rfl,
          (endpointOccurs_iff input inputWellFormed trace candidate node
            port).1 occurs⟩)
      (fun candidate occurs _ =>
        sourceExact.covers candidate (by
          have enclosed := inputWellFormed.wire_scopes_enclose candidate
            ⟨node, port⟩ occurs
          simpa [nodeRegion] using enclosed))
      targetWellFormed.wire_endpoints_are_disjoint
  cases nodeEq : input.nodes node with
  | identity owner arity =>
      have ownerEq : owner = region := by
        simpa [nodeEq] using nodeRegion
      subst owner
      have targetNode : (Target trace).nodes node =
          .identity (promoteRegionIndex input inputWellFormed trace region
            regionNeOuter) arity := by
        change trace.promotion.nodes node = _
        have result := trace.promotion.node_result node
        rw [nodeEq] at result
        unfold promoteRegionIndex
        by_cases innerCase : region = trace.inner
        · rw [dif_pos innerCase]
          simp only [Concrete.promoteNode?, if_pos innerCase,
            (Domain input outer trace.inner).index?_index trace.target
              (target_survives input inputWellFormed trace.outer_eq
                trace.inner_eq), Option.map_some] at result
          exact (Option.some.inj result).symm
        · rw [dif_neg innerCase]
          have regionSurvives :=
            (domain_survives_iff input outer trace.inner region).2
              ⟨regionNeOuter, innerCase⟩
          simp only [Concrete.promoteNode?, if_neg innerCase,
            (Domain input outer trace.inner).index?_index region
              regionSurvives, Option.map_some] at result
          exact (Option.some.inj result).symm
      have mapped := Concrete.Elaboration.compileNode?_map
        sourceContext targetContext sourceBinders targetBinders node node
        (fun _ => promoteRegionIndex input inputWellFormed trace region
          regionNeOuter)
        (fun _ => promoteRegionIndex input inputWellFormed trace region
          regionNeOuter)
        wireMap (fun relation => relation)
        (by simp only [nodeEq, targetNode]) ports (by
          intro owner' binder' impossible
          simp [nodeEq] at impossible)
      rw [sourceCompiled, targetCompiled] at mapped
      simp only [Option.map_some, Item.renameRelations_id] at mapped
      rw [Option.some.inj mapped]
      exact ItemIso.refl _

  | atom owner binder =>
      have ownerEq : owner = region := by
        simpa [nodeEq] using nodeRegion
      subst owner
      have binderSurvives :
          (Domain input outer trace.inner).survives binder = true :=
        (domain_survives_iff input outer trace.inner binder).2
          ⟨atom_binder_ne_outer input inputWellFormed trace node region binder
              nodeEq,
            atom_binder_ne_inner input inputWellFormed trace node region binder
              nodeEq⟩
      have targetNode : (Target trace).nodes node =
          .atom (promoteRegionIndex input inputWellFormed trace region
              regionNeOuter)
            ((Domain input outer trace.inner).index binder binderSurvives) := by
        change trace.promotion.nodes node = _
        have result := trace.promotion.node_result node
        rw [nodeEq] at result
        unfold promoteRegionIndex
        by_cases innerCase : region = trace.inner
        · rw [dif_pos innerCase]
          simp only [Concrete.promoteNode?, if_pos innerCase,
            (Domain input outer trace.inner).index?_index trace.target
              (target_survives input inputWellFormed trace.outer_eq
                trace.inner_eq),
              (Domain input outer trace.inner).index?_index binder
                binderSurvives, Option.pure_def] at result
          exact (Option.some.inj result).symm
        · rw [dif_neg innerCase]
          have regionSurvives :=
            (domain_survives_iff input outer trace.inner region).2
              ⟨regionNeOuter, innerCase⟩
          simp only [Concrete.promoteNode?, if_neg innerCase,
            (Domain input outer trace.inner).index?_index region
              regionSurvives,
              (Domain input outer trace.inner).index?_index binder
                binderSurvives, Option.pure_def] at result
          exact (Option.some.inj result).symm
      have mapped := Concrete.Elaboration.compileNode?_map
        sourceContext targetContext sourceBinders targetBinders node node
        (fun _ => promoteRegionIndex input inputWellFormed trace region
          regionNeOuter)
        (fun _ => (Domain input outer trace.inner).index binder binderSurvives)
        wireMap (fun relation => relation)
        (by simp only [nodeEq, targetNode]) ports (by
          intro owner' binder' equality
          have binderEq : binder' = binder := by
            exact (Concrete.CNode.atom.inj (nodeEq.symm.trans equality)).2.symm
          subst binder'
          rw [binderAgreement,
            (Domain input outer trace.inner).origin_index binder binderSurvives]
          simp)
      rw [sourceCompiled, targetCompiled] at mapped
      simp only [Option.map_some, Item.renameRelations_id] at mapped
      rw [Option.some.inj mapped]
      exact ItemIso.refl _

theorem push_binder_agreement
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    {rels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (binderAgreement : ∀ binder,
      targetBinders binder = sourceBinders
        ((Domain input outer trace.inner).origin binder))
    (child : Fin input.regionCount)
    (childSurvives :
      (Domain input outer trace.inner).survives child = true)
    (arity : Nat) :
    ∀ binder,
      (targetBinders.push
        ((Domain input outer trace.inner).index child childSurvives) arity)
          binder =
        (sourceBinders.push child arity)
          ((Domain input outer trace.inner).origin binder) := by
  intro binder
  by_cases binderEq : binder =
      (Domain input outer trace.inner).index child childSurvives
  · subst binder
    rw [(Domain input outer trace.inner).origin_index child childSurvives]
    simp
  · have originNe : (Domain input outer trace.inner).origin binder ≠ child := by
      intro equality
      apply binderEq
      apply (Domain input outer trace.inner).origin_injective
      rw [(Domain input outer trace.inner).origin_index child childSurvives]
      exact equality
    rw [Concrete.Elaboration.BinderContext.push_other targetBinders arity
        binderEq,
      Concrete.Elaboration.BinderContext.push_other sourceBinders arity
        originNe,
      binderAgreement]

theorem compileRegion_promotion
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {rels : RelCtx}
    {sourceFuel targetFuel : Nat}
    (sourceRegion : Fin input.regionCount)
    (sourceSurvives :
      (Domain input outer trace.inner).survives sourceRegion = true)
    (notAboveTarget : ¬ input.Encloses sourceRegion trace.target)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireAgreement : ∀ index,
      targetContext.get (wireMap index) = sourceContext.get index)
    (sourceExact : (sourceContext.extend sourceRegion).Exact sourceRegion)
    (targetExact :
      (targetContext.extend
        ((Domain input outer trace.inner).index
          sourceRegion sourceSurvives)).Exact
        ((Domain input outer trace.inner).index
          sourceRegion sourceSurvives))
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (binderAgreement : ∀ binder,
      targetBinders binder = sourceBinders
        ((Domain input outer trace.inner).origin binder))
    {sourceBody : Region sourceContext.length rels}
    {targetBody : Region targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input sourceFuel
      sourceRegion sourceContext sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (Target trace) targetFuel
      ((Domain input outer trace.inner).index
        sourceRegion sourceSurvives)
      targetContext targetBinders = some targetBody) :
    RegionIso (FiniteEquiv.refl (Fin targetContext.length)) rels
      (sourceBody.renameWires wireMap) targetBody := by
  induction sourceFuel generalizing targetFuel sourceRegion sourceContext
      targetContext rels sourceBinders targetBinders sourceBody targetBody with
  | zero =>
      simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ sourceFuel induction =>
      cases targetFuel with
      | zero =>
          simp [Concrete.Elaboration.compileRegion?] at targetCompiled
      | succ targetFuel =>
          let targetRegion := (Domain input outer trace.inner).index
            sourceRegion sourceSurvives
          let sourceExtended := sourceContext.extend sourceRegion
          let targetExtended := targetContext.extend targetRegion
          let extended := appendContextMap wireMap
            (localWireEquiv input inputWellFormed trace sourceRegion
              sourceSurvives
              (region_ne_target trace sourceRegion notAboveTarget))
          have extendedAgreement : ∀ index,
              targetExtended.get (extended index) =
                sourceExtended.get index := by
            exact appendContextMap_spec wireMap
              (localWireEquiv input inputWellFormed trace sourceRegion
                sourceSurvives
                (region_ne_target trace sourceRegion notAboveTarget))
              wireAgreement
              (localWireEquiv_spec input inputWellFormed trace sourceRegion
                sourceSurvives
                (region_ne_target trace sourceRegion notAboveTarget))
          have occurrenceIso : ∀
              (occurrence : Concrete.Elaboration.LocalOccurrence
                input.regionCount input.nodeCount),
              occurrence ∈ Concrete.Elaboration.localOccurrences input
                  sourceRegion →
              ∀ (sourceItem : Item sourceExtended.length rels)
                (targetItem : Item targetExtended.length rels),
              Concrete.Elaboration.compileOccurrenceWith? input
                  (Concrete.Elaboration.compileRegion? input sourceFuel)
                  sourceExtended sourceBinders occurrence = some sourceItem →
              Concrete.Elaboration.compileOccurrenceWith? (Target trace)
                  (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
                  targetExtended targetBinders
                  (promoteOccurrence trace targetRegion occurrence) =
                    some targetItem →
              ItemIso (FiniteEquiv.refl (Fin targetExtended.length)) rels
                (sourceItem.renameWires extended) targetItem := by
            intro occurrence occurrenceMember sourceItem targetItem
              sourceItemCompiled targetItemCompiled
            cases occurrence with
            | node node =>
                have sourceRegionNeOuter :=
                  (domain_survives_iff input outer trace.inner sourceRegion).1
                    sourceSurvives |>.1
                have sourceRegionNeInner :=
                  (domain_survives_iff input outer trace.inner sourceRegion).1
                    sourceSurvives |>.2
                exact compileNode_promotion input inputWellFormed trace
                  targetWellFormed sourceRegion sourceRegionNeOuter
                  sourceExtended targetExtended extended extendedAgreement
                  sourceExact (by
                    simpa [promoteRegionIndex, sourceRegionNeInner] using
                      targetExact) sourceBinders targetBinders
                  binderAgreement node
                  ((Concrete.Elaboration.mem_localOccurrences_node input
                    sourceRegion node).1 occurrenceMember)
                  (by simpa [Concrete.Elaboration.compileOccurrenceWith?] using
                    sourceItemCompiled)
                  (by simpa [promoteOccurrence,
                    Concrete.Elaboration.compileOccurrenceWith?] using
                    targetItemCompiled)
            | child child =>
                have sourceParent :=
                  (Concrete.Elaboration.mem_localOccurrences_child input
                    sourceRegion child).1 occurrenceMember
                have childSurvives := child_survives trace sourceSurvives
                  (region_ne_target trace sourceRegion notAboveTarget)
                  sourceParent
                have childNotAbove := child_not_above_target inputWellFormed
                  trace notAboveTarget sourceParent
                let targetChild := (Domain input outer trace.inner).index child
                  childSurvives
                simp only [promoteOccurrence, dif_pos childSurvives,
                  Concrete.Elaboration.compileOccurrenceWith?]
                  at targetItemCompiled
                simp only [Concrete.Elaboration.compileOccurrenceWith?]
                  at sourceItemCompiled
                cases childShape : input.regions child with
                | sheet =>
                    simp [childShape] at sourceItemCompiled
                | cut parent =>
                    have parentEq : parent = sourceRegion := by
                      simpa [childShape, Concrete.CRegion.parent?] using
                        sourceParent
                    subst parent
                    have sourceRegionNeOuter :=
                      (domain_survives_iff input outer trace.inner
                        sourceRegion).1 sourceSurvives |>.1
                    have sourceRegionNeInner :=
                      (domain_survives_iff input outer trace.inner
                        sourceRegion).1 sourceSurvives |>.2
                    have targetShape : (Target trace).regions targetChild =
                        .cut targetRegion := by
                      simpa [targetChild, targetRegion, promoteRegionIndex,
                        sourceRegionNeInner] using
                        (promoted_cut input inputWellFormed trace
                          sourceRegionNeOuter childSurvives childShape)
                    have sourceChildExact := sourceExact.extend_child
                      inputWellFormed (by simpa [childShape])
                    have targetParent :
                        ((Target trace).regions targetChild).parent? =
                          some targetRegion := by
                      change ((Target trace).regions
                        ((Domain input outer trace.inner).index child
                          childSurvives)).parent? =
                        some ((Domain input outer trace.inner).index
                          sourceRegion sourceSurvives)
                      rw [targetShape]
                      rfl
                    have targetChildExact := targetExact.extend_child
                      targetWellFormed targetParent
                    simp only [childShape] at sourceItemCompiled
                    rw [targetShape] at targetItemCompiled
                    cases sourceChildCompiled :
                        Concrete.Elaboration.compileRegion? input sourceFuel
                          child sourceExtended sourceBinders with
                    | none =>
                        simp [sourceChildCompiled] at sourceItemCompiled
                    | some compiledSource =>
                        simp [sourceChildCompiled] at sourceItemCompiled
                        subst sourceItem
                        cases targetChildCompiled :
                            Concrete.Elaboration.compileRegion? (Target trace)
                              targetFuel targetChild targetExtended targetBinders with
                        | none =>
                            rw [targetChildCompiled] at targetItemCompiled
                            contradiction
                        | some compiledTarget =>
                            rw [targetChildCompiled] at targetItemCompiled
                            cases targetItemCompiled
                            apply ItemIso.cut
                            exact induction child childSurvives childNotAbove
                              sourceExtended targetExtended extended
                              extendedAgreement sourceChildExact targetChildExact
                              sourceBinders targetBinders binderAgreement
                              sourceChildCompiled targetChildCompiled
                | bubble parent arity =>
                    have parentEq : parent = sourceRegion := by
                      simpa [childShape, Concrete.CRegion.parent?] using
                        sourceParent
                    subst parent
                    have sourceRegionNeOuter :=
                      (domain_survives_iff input outer trace.inner
                        sourceRegion).1 sourceSurvives |>.1
                    have sourceRegionNeInner :=
                      (domain_survives_iff input outer trace.inner
                        sourceRegion).1 sourceSurvives |>.2
                    have targetShape : (Target trace).regions targetChild =
                        .bubble targetRegion arity := by
                      simpa [targetChild, targetRegion, promoteRegionIndex,
                        sourceRegionNeInner] using
                        (promoted_bubble input inputWellFormed trace
                          sourceRegionNeOuter childSurvives childShape)
                    have sourceChildExact := sourceExact.extend_child
                      inputWellFormed (by simpa [childShape])
                    have targetParent :
                        ((Target trace).regions targetChild).parent? =
                          some targetRegion := by
                      change ((Target trace).regions
                        ((Domain input outer trace.inner).index child
                          childSurvives)).parent? =
                        some ((Domain input outer trace.inner).index
                          sourceRegion sourceSurvives)
                      rw [targetShape]
                      rfl
                    have targetChildExact := targetExact.extend_child
                      targetWellFormed targetParent
                    have childBinders := push_binder_agreement trace
                      sourceBinders targetBinders binderAgreement child
                      childSurvives arity
                    simp only [childShape] at sourceItemCompiled
                    rw [targetShape] at targetItemCompiled
                    simp only at targetItemCompiled
                    cases sourceChildCompiled :
                        Concrete.Elaboration.compileRegion? input sourceFuel
                          child sourceExtended
                          (sourceBinders.push child arity) with
                    | none =>
                        simp [sourceChildCompiled] at sourceItemCompiled
                    | some compiledSource =>
                        simp [sourceChildCompiled] at sourceItemCompiled
                        subst sourceItem
                        cases targetChildCompiled :
                            Concrete.Elaboration.compileRegion? (Target trace)
                              targetFuel targetChild targetExtended
                              (targetBinders.push targetChild arity) with
                        | none =>
                            rw [targetChildCompiled] at targetItemCompiled
                            contradiction
                        | some compiledTarget =>
                            rw [targetChildCompiled] at targetItemCompiled
                            cases targetItemCompiled
                            apply ItemIso.bubble
                            exact induction child childSurvives childNotAbove
                              sourceExtended targetExtended extended
                              extendedAgreement sourceChildExact targetChildExact
                              (sourceBinders.push child arity)
                              (targetBinders.push targetChild arity) childBinders
                              sourceChildCompiled targetChildCompiled
          simp only [Concrete.Elaboration.compileRegion?]
            at sourceCompiled targetCompiled
          cases sourceItemsCompiled :
              Concrete.Elaboration.compileOccurrencesWith? input
                (Concrete.Elaboration.compileRegion? input sourceFuel)
                sourceExtended sourceBinders
                (Concrete.Elaboration.localOccurrences input sourceRegion) with
          | none =>
              simp [sourceExtended, sourceItemsCompiled] at sourceCompiled
          | some sourceItems =>
              simp [sourceExtended, sourceItemsCompiled] at sourceCompiled
              subst sourceBody
              cases targetItemsCompiled :
                  Concrete.Elaboration.compileOccurrencesWith? (Target trace)
                    (Concrete.Elaboration.compileRegion? (Target trace)
                      targetFuel)
                    targetExtended targetBinders
                    (Concrete.Elaboration.localOccurrences (Target trace)
                      targetRegion) with
              | none =>
                  rw [targetItemsCompiled] at targetCompiled
                  contradiction
              | some targetItems =>
                  rw [targetItemsCompiled] at targetCompiled
                  cases targetCompiled
                  have itemsIso : ItemSeqIso
                      (FiniteEquiv.refl (Fin targetExtended.length)) rels
                      (sourceItems.renameWires extended) targetItems := by
                    let occurrencePositions := localOccurrenceEquiv input
                      inputWellFormed trace sourceRegion sourceSurvives
                      (region_ne_target trace sourceRegion notAboveTarget)
                    let sourceLength :=
                      Concrete.Elaboration.compileOccurrencesWith?_length
                        (Concrete.Elaboration.compileRegion? input sourceFuel)
                        sourceExtended sourceBinders sourceItemsCompiled
                    let targetLength :=
                      Concrete.Elaboration.compileOccurrencesWith?_length
                        (Concrete.Elaboration.compileRegion? (Target trace)
                          targetFuel)
                        targetExtended targetBinders targetItemsCompiled
                    let positions := (FiniteEquiv.finCast sourceLength).trans
                      (occurrencePositions.trans
                        (FiniteEquiv.finCast targetLength.symm))
                    apply itemSeqIso_after_rename sourceItems targetItems
                      extended positions
                    intro sourceIndex
                    let occurrenceIndex := Fin.cast sourceLength sourceIndex
                    have sourceGet :=
                      Concrete.Elaboration.compileOccurrencesWith?_get
                        (Concrete.Elaboration.compileRegion? input sourceFuel)
                        sourceExtended sourceBinders sourceItemsCompiled
                        occurrenceIndex
                    have targetGet :=
                      Concrete.Elaboration.compileOccurrencesWith?_get
                        (Concrete.Elaboration.compileRegion? (Target trace)
                          targetFuel)
                        targetExtended targetBinders targetItemsCompiled
                        (localOccurrenceEquiv input inputWellFormed trace
                          sourceRegion sourceSurvives
                          (region_ne_target trace sourceRegion notAboveTarget)
                          occurrenceIndex)
                    rw [localOccurrenceEquiv_spec input inputWellFormed trace
                      sourceRegion sourceSurvives
                      (region_ne_target trace sourceRegion notAboveTarget)
                      occurrenceIndex]
                      at targetGet
                    exact occurrenceIso _ (List.get_mem _ _) _ _ sourceGet
                      (by simpa [positions, occurrencePositions, sourceLength,
                        targetLength, occurrenceIndex] using targetGet)
                  unfold Concrete.Elaboration.finishRegion
                  simp only [Region.renameWires]
                  apply RegionIso.mk
                    (localWireEquiv input inputWellFormed trace sourceRegion
                      sourceSurvives
                      (region_ne_target trace sourceRegion notAboveTarget))
                  let sourceEq :=
                    Concrete.Elaboration.WireContext.length_extend
                      sourceContext sourceRegion
                  let targetEq :=
                    Concrete.Elaboration.WireContext.length_extend
                      targetContext targetRegion
                  let localEquiv := localWireEquiv input inputWellFormed trace
                    sourceRegion sourceSurvives
                    (region_ne_target trace sourceRegion notAboveTarget)
                  let combined := extendWireEquiv
                    (FiniteEquiv.refl (Fin targetContext.length)) localEquiv
                  let sourcePrepared :=
                    (sourceItems.castWiresEq sourceEq).renameWires
                      (extendWireRenaming wireMap
                        (Concrete.Elaboration.exactScopeWires input
                          sourceRegion).length)
                  have first := ItemSeqIso.renameWiresEquiv sourcePrepared
                    combined
                  have casted := itemsIso.renameWires_commuting
                    (Fin.cast targetEq) (Fin.cast targetEq)
                    (FiniteEquiv.refl
                      (Fin (targetContext.length +
                        (Concrete.Elaboration.exactScopeWires (Target trace)
                          targetRegion).length))) (by
                      funext index
                      rfl)
                  have factor :
                      (Fin.cast targetEq) ∘ extended =
                        combined.toFun ∘
                          (extendWireRenaming wireMap
                            (Concrete.Elaboration.exactScopeWires input
                              sourceRegion).length) ∘
                            Fin.cast sourceEq := by
                    funext index
                    let sumIndex : Fin (sourceContext.length +
                        (Concrete.Elaboration.exactScopeWires input
                          sourceRegion).length) :=
                      Fin.cast sourceEq index
                    have indexEq : index = Fin.cast sourceEq.symm sumIndex := by
                      apply Fin.ext
                      rfl
                    rw [indexEq]
                    refine Fin.addCases (fun outerIndex => ?_)
                      (fun localIndex => ?_) sumIndex
                    · apply Fin.ext
                      simp [Function.comp_def, extended, appendContextMap,
                        combined, localEquiv, extendWireRenaming,
                        extendWireEquiv, FiniteEquiv.refl]
                      let actual : Fin (sourceContext.length +
                          (Concrete.Elaboration.exactScopeWires input
                            sourceRegion).length) :=
                        Fin.cast sourceEq
                          (Fin.cast sourceEq.symm
                            (Fin.castAdd
                              (Concrete.Elaboration.exactScopeWires input
                                sourceRegion).length outerIndex))
                      let onOuter : Fin sourceContext.length → Fin
                          (targetContext.length +
                            (Concrete.Elaboration.exactScopeWires
                              (Target trace) targetRegion).length) :=
                        fun index => Fin.castAdd
                        (Concrete.Elaboration.exactScopeWires (Target trace)
                          targetRegion).length (wireMap index)
                      let onLocal : Fin
                          (Concrete.Elaboration.exactScopeWires input
                            sourceRegion).length → Fin
                            (targetContext.length +
                              (Concrete.Elaboration.exactScopeWires
                                (Target trace) targetRegion).length) :=
                        fun index => Fin.natAdd targetContext.length
                          (localEquiv index)
                      change (Fin.addCases (motive := fun _ => Fin
                        (targetContext.length +
                          (Concrete.Elaboration.exactScopeWires
                            (Target trace) targetRegion).length))
                        onOuter onLocal actual).val = _
                      have actualEq : actual = Fin.castAdd
                          (Concrete.Elaboration.exactScopeWires input
                            sourceRegion).length outerIndex := by
                        apply Fin.ext
                        rfl
                      rw [actualEq]
                      simp [onOuter]
                    · apply Fin.ext
                      simp [Function.comp_def, extended, appendContextMap,
                        combined, localEquiv, extendWireRenaming,
                        extendWireEquiv, FiniteEquiv.refl]
                      let actual : Fin (sourceContext.length +
                          (Concrete.Elaboration.exactScopeWires input
                            sourceRegion).length) :=
                        Fin.cast sourceEq
                          (Fin.cast sourceEq.symm
                            (Fin.natAdd sourceContext.length localIndex))
                      let onOuter : Fin sourceContext.length → Fin
                          (targetContext.length +
                            (Concrete.Elaboration.exactScopeWires
                              (Target trace) targetRegion).length) :=
                        fun index => Fin.castAdd
                        (Concrete.Elaboration.exactScopeWires (Target trace)
                          targetRegion).length (wireMap index)
                      let onLocal : Fin
                          (Concrete.Elaboration.exactScopeWires input
                            sourceRegion).length → Fin
                            (targetContext.length +
                              (Concrete.Elaboration.exactScopeWires
                                (Target trace) targetRegion).length) :=
                        fun index => Fin.natAdd targetContext.length
                          (localEquiv index)
                      change (Fin.addCases (motive := fun _ => Fin
                        (targetContext.length +
                          (Concrete.Elaboration.exactScopeWires
                            (Target trace) targetRegion).length))
                        onOuter onLocal actual).val = _
                      have actualEq : actual =
                          Fin.natAdd sourceContext.length localIndex := by
                        apply Fin.ext
                        rfl
                      rw [actualEq]
                      simp [onLocal]
                      rfl
                  have middleEq : sourcePrepared.renameWires combined =
                      (sourceItems.renameWires extended).renameWires
                        (Fin.cast targetEq) := by
                    simp only [sourcePrepared,
                      ItemSeq.castWiresEq_eq_renameWires,
                      ItemSeq.renameWires_comp]
                    exact (congrArg (fun map => sourceItems.renameWires map)
                      factor.symm).trans
                        (ItemSeq.renameWires_comp sourceItems extended
                          (Fin.cast targetEq)).symm
                  rw [middleEq] at first
                  have result := first.trans casted
                  simpa only [sourcePrepared,
                    ItemSeq.castWiresEq_eq_renameWires,
                    ItemSeq.renameWires_comp, factor,
                    ← ItemSeq.castWiresEq_eq_renameWires] using result

theorem compileOccurrence_promotion
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {rels : RelCtx} {sourceFuel targetFuel : Nat}
    (region : Fin input.regionCount) (regionNeOuter : region ≠ outer)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireAgreement : ∀ index,
      targetContext.get (wireMap index) = sourceContext.get index)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact
      (promoteRegionIndex input inputWellFormed trace region regionNeOuter))
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (binderAgreement : ∀ binder,
      targetBinders binder = sourceBinders
        ((Domain input outer trace.inner).origin binder))
    (occurrence : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount)
    (occurrenceMember : occurrence ∈
      Concrete.Elaboration.localOccurrences input region)
    (childrenSurvive : ∀ child, occurrence = .child child →
      (Domain input outer trace.inner).survives child = true)
    (childrenNotAbove : ∀ child, occurrence = .child child →
      ¬ input.Encloses child trace.target)
    {sourceItem : Item sourceContext.length rels}
    {targetItem : Item targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith? input
      (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
      sourceBinders occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith? (Target trace)
      (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
      targetContext targetBinders
      (promoteOccurrence trace (promotedTarget input inputWellFormed trace)
        occurrence) = some targetItem) :
    ItemIso (FiniteEquiv.refl (Fin targetContext.length)) rels
      (sourceItem.renameWires wireMap) targetItem := by
  cases occurrence with
  | node node =>
      exact compileNode_promotion input inputWellFormed trace targetWellFormed
        region regionNeOuter sourceContext targetContext wireMap wireAgreement
        sourceExact targetExact sourceBinders targetBinders binderAgreement node
        ((Concrete.Elaboration.mem_localOccurrences_node input region node).1
          occurrenceMember)
        (by simpa [Concrete.Elaboration.compileOccurrenceWith?] using
          sourceCompiled)
        (by simpa [promoteOccurrence,
          Concrete.Elaboration.compileOccurrenceWith?] using targetCompiled)
  | child child =>
      have childSurvives := childrenSurvive child rfl
      have childNotAbove := childrenNotAbove child rfl
      let targetChild := (Domain input outer trace.inner).index child
        childSurvives
      simp only [promoteOccurrence, dif_pos childSurvives,
        Concrete.Elaboration.compileOccurrenceWith?] at targetCompiled
      simp only [Concrete.Elaboration.compileOccurrenceWith?] at sourceCompiled
      have sourceParent :=
        (Concrete.Elaboration.mem_localOccurrences_child input region child).1
          occurrenceMember
      cases childShape : input.regions child with
      | sheet => simp [childShape] at sourceCompiled
      | cut parent =>
          have parentEq : parent = region := by
            simpa [childShape, Concrete.CRegion.parent?] using sourceParent
          subst parent
          have targetShape := promoted_cut input inputWellFormed trace
            regionNeOuter childSurvives childShape
          have sourceChildExact := sourceExact.extend_child inputWellFormed
            (by simpa [childShape])
          have targetChildExact := targetExact.extend_child targetWellFormed
            (by
              have parentShape := congrArg Concrete.CRegion.parent? targetShape
              simpa [targetChild] using parentShape)
          simp only [childShape] at sourceCompiled
          rw [targetShape] at targetCompiled
          simp only at targetCompiled
          cases sourceChildCompiled : Concrete.Elaboration.compileRegion? input
              sourceFuel child sourceContext sourceBinders with
          | none => simp [sourceChildCompiled] at sourceCompiled
          | some compiledSource =>
              simp [sourceChildCompiled] at sourceCompiled
              subst sourceItem
              cases targetChildCompiled : Concrete.Elaboration.compileRegion?
                  (Target trace) targetFuel targetChild targetContext
                  targetBinders with
              | none => rw [targetChildCompiled] at targetCompiled; contradiction
              | some compiledTarget =>
                  rw [targetChildCompiled] at targetCompiled
                  cases targetCompiled
                  apply ItemIso.cut
                  exact compileRegion_promotion input inputWellFormed trace
                    targetWellFormed child childSurvives childNotAbove
                    sourceContext targetContext wireMap wireAgreement
                    sourceChildExact targetChildExact sourceBinders targetBinders
                    binderAgreement sourceChildCompiled targetChildCompiled
      | bubble parent arity =>
          have parentEq : parent = region := by
            simpa [childShape, Concrete.CRegion.parent?] using sourceParent
          subst parent
          have targetShape := promoted_bubble input inputWellFormed trace
            regionNeOuter childSurvives childShape
          have sourceChildExact := sourceExact.extend_child inputWellFormed
            (by simpa [childShape])
          have targetChildExact := targetExact.extend_child targetWellFormed
            (by
              have parentShape := congrArg Concrete.CRegion.parent? targetShape
              simpa [targetChild] using parentShape)
          have childBinders := push_binder_agreement trace sourceBinders
            targetBinders binderAgreement child childSurvives arity
          simp only [childShape] at sourceCompiled
          rw [targetShape] at targetCompiled
          simp only at targetCompiled
          cases sourceChildCompiled : Concrete.Elaboration.compileRegion? input
              sourceFuel child sourceContext (sourceBinders.push child arity) with
          | none => simp [sourceChildCompiled] at sourceCompiled
          | some compiledSource =>
              simp [sourceChildCompiled] at sourceCompiled
              subst sourceItem
              cases targetChildCompiled : Concrete.Elaboration.compileRegion?
                  (Target trace) targetFuel targetChild targetContext
                  (targetBinders.push targetChild arity) with
              | none => rw [targetChildCompiled] at targetCompiled; contradiction
              | some compiledTarget =>
                  rw [targetChildCompiled] at targetCompiled
                  cases targetCompiled
                  apply ItemIso.bubble
                  exact compileRegion_promotion input inputWellFormed trace
                    targetWellFormed child childSurvives childNotAbove
                    sourceContext targetContext wireMap wireAgreement
                    sourceChildExact targetChildExact
                    (sourceBinders.push child arity)
                    (targetBinders.push targetChild arity) childBinders
                    sourceChildCompiled targetChildCompiled

end VisualProof.Refinement.Implementation.DoubleCutElimCompiler
