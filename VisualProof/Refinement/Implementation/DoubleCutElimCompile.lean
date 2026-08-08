import VisualProof.Refinement.Implementation.DoubleCutElimCompiler
import VisualProof.Refinement.Implementation.DoubleCutElimOccurrence
import VisualProof.Refinement.Implementation.DoubleCutIntroCompile
import VisualProof.Refinement.Implementation.IterationPartition
import VisualProof.Rule.DoubleCut

namespace VisualProof.Refinement.Implementation.DoubleCutElimCompile

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutElimTransport
open VisualProof.Refinement.Implementation.DoubleCutElimCompiler
open VisualProof.Refinement.Implementation.DoubleCutElimOccurrence
open VisualProof.Refinement.Implementation.DoubleCutIntroCompile

private theorem promoteRegionIndex_eq_promotedTarget
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount) (regionNeOuter : region ≠ outer) :
    promoteRegionIndex input inputWellFormed trace region regionNeOuter =
        promotedTarget input inputWellFormed trace ↔
      region = trace.target ∨ region = trace.inner := by
  constructor
  · intro equality
    have origins := congrArg (Domain input outer trace.inner).origin equality
    rw [promoteRegionIndex_origin, promotedTarget_origin] at origins
    by_cases innerCase : region = trace.inner
    · exact Or.inr innerCase
    · exact Or.inl (by simpa [innerCase] using origins)
  · intro cases
    rcases cases with targetCase | innerCase
    · have targetNeInner := target_ne_inner input inputWellFormed
        trace.outer_eq trace.inner_eq
      unfold promoteRegionIndex
      rw [dif_neg (targetCase ▸ targetNeInner)]
      apply (Domain input outer trace.inner).origin_injective
      rw [(Domain input outer trace.inner).origin_index,
        promotedTarget_origin, targetCase]
    · unfold promoteRegionIndex
      rw [dif_pos innerCase]

private theorem target_node_focus_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) :
    ((Target trace).nodes node).region =
        promotedTarget input inputWellFormed trace ↔
      (input.nodes node).region = trace.target ∨
        (input.nodes node).region = trace.inner := by
  have ownerNe := node_region_ne_outer trace node
  have ownerEq : ((Target trace).nodes node).region =
      promoteRegionIndex input inputWellFormed trace
        (input.nodes node).region ownerNe := by
    change (trace.promotion.nodes node).region = _
    rw [promotion_node input inputWellFormed trace node]
    unfold promotedNodeValue
    split <;> simp_all [Concrete.CNode.region]
  rw [ownerEq]
  exact promoteRegionIndex_eq_promotedTarget input inputWellFormed trace
    (input.nodes node).region ownerNe

private theorem target_child_focus_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (child : Fin (Target trace).regionCount) :
    ((Target trace).regions child).parent? =
        some (promotedTarget input inputWellFormed trace) ↔
      (input.regions ((Domain input outer trace.inner).origin child)).parent? =
          some trace.target ∨
        (input.regions
          ((Domain input outer trace.inner).origin child)).parent? =
            some trace.inner := by
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
    simp only [regionEq, Concrete.CRegion.parent?, Option.some.injEq]
    exact promoteRegionIndex_eq_promotedTarget input inputWellFormed trace
      parent parentNe
  · rename_i parent arity regionEq
    have parentNe := survivor_parent_ne_outer trace child parent (by
      rw [regionEq]
      rfl)
    simp only [regionEq, Concrete.CRegion.parent?, Option.some.injEq]
    exact promoteRegionIndex_eq_promotedTarget input inputWellFormed trace
      parent parentNe

private def focusSourceOccurrences
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :=
  hostOccurrences trace ++ innerOccurrences trace

private def OccurrenceSurvives
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount → Prop
  | .node _ => True
  | .child child =>
      (Domain input outer trace.inner).survives child = true

private theorem focusOccurrence_survives
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount)
    (member : occurrence ∈ focusSourceOccurrences trace) :
    OccurrenceSurvives trace occurrence := by
  cases occurrence with
  | node node => trivial
  | child child =>
      change (Domain input outer trace.inner).survives child = true
      rw [domain_survives_iff]
      have cases := List.mem_append.mp member
      rcases cases with hostMember | innerMember
      · have filtered := List.mem_filter.mp hostMember
        have childNeOuter : child ≠ outer := by
          simpa using filtered.2
        have parentTarget :=
          (Concrete.Elaboration.mem_localOccurrences_child input trace.target
            child).1 filtered.1
        have childNeInner : child ≠ trace.inner := by
          intro equality
          subst child
          rw [trace.inner_eq] at parentTarget
          have outerEqTarget := Option.some.inj parentTarget
          exact target_ne_outer input inputWellFormed trace.outer_eq
            outerEqTarget.symm
        exact ⟨childNeOuter, childNeInner⟩
      · have parentInner :=
          (Concrete.Elaboration.mem_localOccurrences_child input trace.inner
            child).1 innerMember
        have childNeOuter : child ≠ outer := by
          intro equality
          subst child
          rw [trace.outer_eq] at parentInner
          have targetEqInner := Option.some.inj parentInner
          exact target_ne_inner input inputWellFormed trace.outer_eq
            trace.inner_eq targetEqInner
        have childNeInner : child ≠ trace.inner := by
          intro equality
          subst child
          rw [trace.inner_eq] at parentInner
          have outerEqInner := Option.some.inj parentInner
          exact outer_ne_inner input inputWellFormed trace.inner_eq
            outerEqInner
        exact ⟨childNeOuter, childNeInner⟩

private theorem focusSourceOccurrences_nodup
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    (focusSourceOccurrences trace).Nodup := by
  rw [focusSourceOccurrences, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (Concrete.Elaboration.localOccurrences_nodup input
      trace.target).filter _
  · exact Concrete.Elaboration.localOccurrences_nodup input trace.inner
  · intro occurrence hostMember innerOccurrence innerMember equality
    subst innerOccurrence
    have hostLocal := (List.mem_filter.mp hostMember).1
    cases occurrence with
    | node node =>
        have hostOwner :=
          (Concrete.Elaboration.mem_localOccurrences_node input trace.target
            node).1 hostLocal
        have innerOwner :=
          (Concrete.Elaboration.mem_localOccurrences_node input trace.inner
            node).1 innerMember
        exact target_ne_inner input inputWellFormed trace.outer_eq trace.inner_eq
          (hostOwner.symm.trans innerOwner)
    | child child =>
        have hostParent :=
          (Concrete.Elaboration.mem_localOccurrences_child input trace.target
            child).1 hostLocal
        have innerParent :=
          (Concrete.Elaboration.mem_localOccurrences_child input trace.inner
            child).1 innerMember
        exact target_ne_inner input inputWellFormed trace.outer_eq trace.inner_eq
          (Option.some.inj (hostParent.symm.trans innerParent))

private def focusPromotedOccurrences
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :=
  (focusSourceOccurrences trace).map
    (promoteOccurrence trace (promotedTarget input inputWellFormed trace))

private theorem focusPromotedOccurrences_nodup
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    (focusPromotedOccurrences input inputWellFormed trace).Nodup := by
  unfold focusPromotedOccurrences
  let selected := focusSourceOccurrences trace
  have mappedNodup : ∀ items : List
      (Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount),
      items.Nodup →
      (∀ occurrence, occurrence ∈ items → occurrence ∈ selected) →
      (items.map
        (promoteOccurrence trace
          (promotedTarget input inputWellFormed trace))).Nodup := by
    intro items nodup subset
    induction items with
    | nil => simp
    | cons head tail induction =>
        rw [List.nodup_cons] at nodup
        rw [List.map, List.nodup_cons]
        constructor
        · intro mappedMember
          rw [List.mem_map] at mappedMember
          obtain ⟨other, otherMember, equality⟩ := mappedMember
          have headMember := subset head (by simp)
          have otherSelected := subset other (by simp [otherMember])
          have headRoundtrip :=
            source_promoteOccurrence_of_children_survive trace
              (promotedTarget input inputWellFormed trace) head (by
              intro child equality
              subst head
              exact focusOccurrence_survives input inputWellFormed trace
                (.child child) headMember)
          have otherRoundtrip :=
            source_promoteOccurrence_of_children_survive trace
              (promotedTarget input inputWellFormed trace) other (by
              intro child occurrenceEq
              subst other
              exact focusOccurrence_survives input inputWellFormed trace
                (.child child) otherSelected)
          have sourceEquality := congrArg (sourceOccurrence trace) equality
          rw [otherRoundtrip, headRoundtrip] at sourceEquality
          exact nodup.1 (sourceEquality ▸ otherMember)
        · exact induction nodup.2 (by
            intro occurrence occurrenceMember
            exact subset occurrence (by simp [occurrenceMember]))
  exact mappedNodup selected
    (focusSourceOccurrences_nodup input inputWellFormed trace) (by simp)

private theorem focusPromotedOccurrences_mem_iff
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      (Target trace).regionCount (Target trace).nodeCount) :
    occurrence ∈ focusPromotedOccurrences input inputWellFormed trace ↔
      occurrence ∈ Concrete.Elaboration.localOccurrences (Target trace)
        (promotedTarget input inputWellFormed trace) := by
  constructor
  · intro member
    rw [focusPromotedOccurrences, List.mem_map] at member
    obtain ⟨source, sourceMember, sourceEq⟩ := member
    rw [← sourceEq]
    cases source with
    | node node =>
        simp only [promoteOccurrence]
        rw [Concrete.Elaboration.mem_localOccurrences_node,
          target_node_focus_iff input inputWellFormed trace]
        rcases List.mem_append.mp sourceMember with hostMember | innerMember
        · exact Or.inl
            ((Concrete.Elaboration.mem_localOccurrences_node input
              trace.target node).1 (List.mem_filter.mp hostMember).1)
        · exact Or.inr
            ((Concrete.Elaboration.mem_localOccurrences_node input
              trace.inner node).1 innerMember)
    | child child =>
        have survives := focusOccurrence_survives input inputWellFormed trace
          (.child child) sourceMember
        change (Domain input outer trace.inner).survives child = true at survives
        simp only [promoteOccurrence, dif_pos survives]
        rw [Concrete.Elaboration.mem_localOccurrences_child]
        apply (target_child_focus_iff input inputWellFormed trace
          ((Domain input outer trace.inner).index child survives)).2
        rw [(Domain input outer trace.inner).origin_index child survives]
        rcases List.mem_append.mp sourceMember with hostMember | innerMember
        · exact Or.inl
            ((Concrete.Elaboration.mem_localOccurrences_child input
              trace.target child).1 (List.mem_filter.mp hostMember).1)
        · exact Or.inr
            ((Concrete.Elaboration.mem_localOccurrences_child input
              trace.inner child).1 innerMember)
  · intro member
    rw [focusPromotedOccurrences, List.mem_map]
    cases occurrence with
    | node node =>
        have owners := (target_node_focus_iff input inputWellFormed trace
          node).1 ((Concrete.Elaboration.mem_localOccurrences_node
            (Target trace) (promotedTarget input inputWellFormed trace)
              node).1 member)
        refine ⟨.node node, ?_, rfl⟩
        rcases owners with targetOwner | innerOwner
        · apply List.mem_append_left
          rw [hostOccurrences, List.mem_filter]
          exact ⟨(Concrete.Elaboration.mem_localOccurrences_node input
            trace.target node).2 targetOwner, by simp⟩
        · apply List.mem_append_right
          exact (Concrete.Elaboration.mem_localOccurrences_node input
            trace.inner node).2 innerOwner
    | child child =>
        have parents := (target_child_focus_iff input inputWellFormed trace
          child).1 ((Concrete.Elaboration.mem_localOccurrences_child
            (Target trace) (promotedTarget input inputWellFormed trace)
              child).1 member)
        let sourceChild := (Domain input outer trace.inner).origin child
        have sourceMember : Concrete.Elaboration.LocalOccurrence.child
            sourceChild ∈ focusSourceOccurrences trace := by
          rcases parents with targetParent | innerParent
          · apply List.mem_append_left
            rw [hostOccurrences, List.mem_filter]
            refine ⟨(Concrete.Elaboration.mem_localOccurrences_child input
              trace.target sourceChild).2 targetParent, ?_⟩
            have survives :=
              (Domain input outer trace.inner).origin_survives child
            exact decide_eq_true (by
              intro equality
              exact ((domain_survives_iff input outer trace.inner
                sourceChild).1 survives |>.1)
                (Concrete.Elaboration.LocalOccurrence.child.inj equality))
          · apply List.mem_append_right
            exact (Concrete.Elaboration.mem_localOccurrences_child input
              trace.inner sourceChild).2 innerParent
        refine ⟨.child sourceChild, sourceMember, ?_⟩
        have survives :=
          (Domain input outer trace.inner).origin_survives child
        change Concrete.Elaboration.LocalOccurrence.child
          (if survival : (Domain input outer trace.inner).survives
              sourceChild = true then
            (Domain input outer trace.inner).index sourceChild survival
          else promotedTarget input inputWellFormed trace) =
            Concrete.Elaboration.LocalOccurrence.child child
        rw [dif_pos (by simpa [sourceChild] using survives)]
        exact congrArg Concrete.Elaboration.LocalOccurrence.child
          ((Domain input outer trace.inner).index_origin child)

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

private theorem focus_occurrences_partition
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    (focusPromotedOccurrences input inputWellFormed trace).Perm
      (Concrete.Elaboration.localOccurrences (Target trace)
        (promotedTarget input inputWellFormed trace)) := by
  apply perm_of_nodup_and_mem_iff
    (focusPromotedOccurrences_nodup input inputWellFormed trace)
    (Concrete.Elaboration.localOccurrences_nodup (Target trace)
      (promotedTarget input inputWellFormed trace))
  exact focusPromotedOccurrences_mem_iff input inputWellFormed trace

private theorem compileOccurrences_of_perm
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    {sourceOccurrences targetOccurrences : List
      (Concrete.Elaboration.LocalOccurrence diagram.regionCount
        diagram.nodeCount)}
    (permutation : sourceOccurrences.Perm targetOccurrences)
    (sourceNodup : sourceOccurrences.Nodup)
    (targetNodup : targetOccurrences.Nodup)
    {sourceItems : ItemSeq context.length rels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith? diagram
      recurse context binders sourceOccurrences = some sourceItems) :
    ∃ targetItems,
      Concrete.Elaboration.compileOccurrencesWith? diagram recurse context
        binders targetOccurrences = some targetItems ∧
      ItemSeqIso (FiniteEquiv.refl (Fin context.length)) rels
        sourceItems targetItems := by
  have eachTarget : ∀ occurrence, occurrence ∈ targetOccurrences →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? diagram recurse
        context binders occurrence = some item := by
    intro occurrence targetMember
    have sourceMember := (permutation.mem_iff).2 targetMember
    obtain ⟨index, occurrenceEq⟩ := indexOf?_complete sourceMember
    have compiledGet := Concrete.Elaboration.compileOccurrencesWith?_get
      recurse context binders sourceCompiled index
    have getEq : sourceOccurrences.get index = occurrence := by
      simpa only [List.get_eq_getElem] using indexOf?_sound occurrenceEq
    rw [getEq] at compiledGet
    exact ⟨_, compiledGet⟩
  obtain ⟨targetItems, targetCompiled⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_complete recurse context
      binders targetOccurrences eachTarget
  exact ⟨targetItems, targetCompiled,
    VisualProof.Refinement.Implementation.IterationPartition.compileOccurrences_perm_iso
      diagram recurse context binders permutation sourceNodup targetNodup
      sourceCompiled targetCompiled⟩

private theorem source_partition
    (input : Concrete.Diagram)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    {rels : RelCtx} {sourceFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext input)
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    {sourceBody : Region sourceContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input sourceFuel
      trace.target sourceContext sourceBinders = some sourceBody) :
    ∃ (hostItems : ItemSeq (sourceContext.extend trace.target).length rels)
      (innerBody : Region
        ((sourceContext.extend trace.target).extend outer).length rels)
      (hostFuel innerFuel : Nat),
      Concrete.Elaboration.compileOccurrencesWith? input
          (Concrete.Elaboration.compileRegion? input hostFuel)
          (sourceContext.extend trace.target) sourceBinders
          (hostOccurrences trace) = some hostItems ∧
      Concrete.Elaboration.compileRegion? input innerFuel trace.inner
          ((sourceContext.extend trace.target).extend outer) sourceBinders =
            some innerBody ∧
      RegionIso (FiniteEquiv.refl (Fin sourceContext.length)) rels sourceBody
        (Concrete.Elaboration.finishRegion input sourceContext trace.target
          (hostItems.append (.cons (.cut
            (Concrete.Elaboration.finishRegion input
              (sourceContext.extend trace.target) outer
              (.cons (.cut innerBody) .nil))) .nil))) := by
  cases sourceFuel with
  | zero => simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ hostFuel =>
      simp only [Concrete.Elaboration.compileRegion?] at sourceCompiled
      obtain ⟨sourceItems, sourceItemsCompiled, sourceBodyEq⟩ :=
        Option.bind_eq_some_iff.mp sourceCompiled
      have sourceBodyEq' := Option.some.inj sourceBodyEq
      subst sourceBody
      obtain ⟨orderedItems, orderedCompiled, orderedIso⟩ :=
        compileOccurrences_of_perm input
          (Concrete.Elaboration.compileRegion? input hostFuel)
          (sourceContext.extend trace.target) sourceBinders
          (target_occurrences_partition trace).symm
          (Concrete.Elaboration.localOccurrences_nodup input trace.target)
          ((Concrete.Elaboration.localOccurrences_nodup input trace.target).perm
            (target_occurrences_partition trace).symm)
          sourceItemsCompiled
      obtain ⟨hostItems, outerItems, hostCompiled, outerCompiled,
          orderedEq⟩ :=
        Concrete.Elaboration.compileOccurrencesWith?_append_split
          (Concrete.Elaboration.compileRegion? input hostFuel)
          (sourceContext.extend trace.target) sourceBinders
          (hostOccurrences trace) [.child outer] orderedItems orderedCompiled
      rw [orderedEq] at orderedIso
      simp only [Concrete.Elaboration.compileOccurrencesWith?,
        Concrete.Elaboration.compileOccurrenceWith?, trace.outer_eq]
        at outerCompiled
      cases outerResult : Concrete.Elaboration.compileRegion? input hostFuel
          outer (sourceContext.extend trace.target) sourceBinders with
      | none => simp [outerResult] at outerCompiled
      | some outerBody =>
          simp [outerResult] at outerCompiled
          subst outerItems
          cases hostFuel with
          | zero => simp [Concrete.Elaboration.compileRegion?] at outerResult
          | succ innerFuel =>
              simp only [Concrete.Elaboration.compileRegion?] at outerResult
              rw [outer_localOccurrences trace] at outerResult
              obtain ⟨outerItems, outerItemsCompiled, outerBodyEq⟩ :=
                Option.bind_eq_some_iff.mp outerResult
              have outerBodyEq' := Option.some.inj outerBodyEq
              subst outerBody
              simp only [Concrete.Elaboration.compileOccurrencesWith?,
                Concrete.Elaboration.compileOccurrenceWith?, trace.inner_eq]
                at outerItemsCompiled
              cases innerResult : Concrete.Elaboration.compileRegion? input
                  innerFuel trace.inner
                  ((sourceContext.extend trace.target).extend outer)
                  sourceBinders with
              | none => simp [innerResult] at outerItemsCompiled
              | some innerBody =>
                  simp [innerResult] at outerItemsCompiled
                  subst outerItems
                  refine ⟨hostItems, _, innerFuel + 1, innerFuel,
                    hostCompiled, innerResult, ?_⟩
                  apply Concrete.Elaboration.regionIso_of_cast
                    (Concrete.Elaboration.WireContext.length_extend
                      sourceContext trace.target)
                    (Concrete.Elaboration.WireContext.length_extend
                      sourceContext trace.target)
                    (FiniteEquiv.refl (Fin sourceContext.length))
                    (FiniteEquiv.refl (Fin
                      (Concrete.Elaboration.exactScopeWires input
                        trace.target).length))
                  have wireEq : Concrete.Elaboration.castFinEquiv
                      (Concrete.Elaboration.WireContext.length_extend
                        sourceContext trace.target)
                      (Concrete.Elaboration.WireContext.length_extend
                        sourceContext trace.target)
                      (extendWireEquiv
                        (FiniteEquiv.refl (Fin sourceContext.length))
                        (FiniteEquiv.refl (Fin
                          (Concrete.Elaboration.exactScopeWires input
                            trace.target).length))) =
                    FiniteEquiv.refl
                      (Fin (sourceContext.extend trace.target).length) := by
                    apply FiniteEquiv.ext
                    intro index
                    apply Fin.ext
                    change (extendWireEquiv
                      (FiniteEquiv.refl (Fin sourceContext.length))
                      (FiniteEquiv.refl (Fin
                        (Concrete.Elaboration.exactScopeWires input
                          trace.target).length))
                      (Fin.cast
                        (Concrete.Elaboration.WireContext.length_extend
                          sourceContext trace.target) index)).val = index.val
                    have castVal : (Fin.cast
                        (Concrete.Elaboration.WireContext.length_extend
                          sourceContext trace.target) index).val = index.val := rfl
                    rw [← castVal]
                    refine Fin.addCases (fun outerIndex => ?_)
                      (fun localIndex => ?_)
                      (Fin.cast
                        (Concrete.Elaboration.WireContext.length_extend
                          sourceContext trace.target) index)
                    · rw [extendWireEquiv_outer]
                      rfl
                    · rw [extendWireEquiv_local]
                      rfl
                  rw [wireEq]
                  exact orderedIso

private theorem target_partition
    (input : Concrete.Diagram) (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    {rels : RelCtx} {targetFuel : Nat}
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    {targetBody : Region targetContext.length rels}
    (targetCompiled : Concrete.Elaboration.compileRegion? (Target trace)
      targetFuel (promotedTarget input inputWellFormed trace) targetContext
      targetBinders = some targetBody) :
    ∃ (hostItems innerItems : ItemSeq
        (targetContext.extend
          (promotedTarget input inputWellFormed trace)).length rels)
      (itemFuel : Nat),
      Concrete.Elaboration.compileOccurrencesWith? (Target trace)
          (Concrete.Elaboration.compileRegion? (Target trace) itemFuel)
          (targetContext.extend (promotedTarget input inputWellFormed trace))
          targetBinders
          ((hostOccurrences trace).map
            (promoteOccurrence trace
              (promotedTarget input inputWellFormed trace))) = some hostItems ∧
      Concrete.Elaboration.compileOccurrencesWith? (Target trace)
          (Concrete.Elaboration.compileRegion? (Target trace) itemFuel)
          (targetContext.extend (promotedTarget input inputWellFormed trace))
          targetBinders
          ((innerOccurrences trace).map
            (promoteOccurrence trace
              (promotedTarget input inputWellFormed trace))) = some innerItems ∧
      RegionIso (FiniteEquiv.refl (Fin targetContext.length)) rels targetBody
        (Concrete.Elaboration.finishRegion (Target trace) targetContext
          (promotedTarget input inputWellFormed trace)
          (hostItems.append innerItems)) := by
  cases targetFuel with
  | zero => simp [Concrete.Elaboration.compileRegion?] at targetCompiled
  | succ itemFuel =>
      simp only [Concrete.Elaboration.compileRegion?] at targetCompiled
      obtain ⟨targetItems, targetItemsCompiled, targetBodyEq⟩ :=
        Option.bind_eq_some_iff.mp targetCompiled
      have targetBodyEq' := Option.some.inj targetBodyEq
      subst targetBody
      obtain ⟨orderedItems, orderedCompiled, orderedIso⟩ :=
        compileOccurrences_of_perm (Target trace)
          (Concrete.Elaboration.compileRegion? (Target trace) itemFuel)
          (targetContext.extend (promotedTarget input inputWellFormed trace))
          targetBinders (focus_occurrences_partition input inputWellFormed
            trace).symm
          (Concrete.Elaboration.localOccurrences_nodup (Target trace)
            (promotedTarget input inputWellFormed trace))
          (focusPromotedOccurrences_nodup input inputWellFormed trace)
          targetItemsCompiled
      unfold focusPromotedOccurrences focusSourceOccurrences at orderedCompiled
      rw [List.map_append] at orderedCompiled
      obtain ⟨hostItems, innerItems, hostCompiled, innerCompiled, orderedEq⟩ :=
        Concrete.Elaboration.compileOccurrencesWith?_append_split
          (Concrete.Elaboration.compileRegion? (Target trace) itemFuel)
          (targetContext.extend (promotedTarget input inputWellFormed trace))
          targetBinders
          ((hostOccurrences trace).map
            (promoteOccurrence trace
              (promotedTarget input inputWellFormed trace)))
          ((innerOccurrences trace).map
            (promoteOccurrence trace
              (promotedTarget input inputWellFormed trace)))
          orderedItems orderedCompiled
      rw [orderedEq] at orderedIso
      refine ⟨hostItems, innerItems, itemFuel, hostCompiled, innerCompiled, ?_⟩
      apply Concrete.Elaboration.regionIso_of_cast
        (Concrete.Elaboration.WireContext.length_extend targetContext
          (promotedTarget input inputWellFormed trace))
        (Concrete.Elaboration.WireContext.length_extend targetContext
          (promotedTarget input inputWellFormed trace))
        (FiniteEquiv.refl (Fin targetContext.length))
        (FiniteEquiv.refl (Fin
          (Concrete.Elaboration.exactScopeWires (Target trace)
            (promotedTarget input inputWellFormed trace)).length))
      have wireEq : Concrete.Elaboration.castFinEquiv
          (Concrete.Elaboration.WireContext.length_extend targetContext
            (promotedTarget input inputWellFormed trace))
          (Concrete.Elaboration.WireContext.length_extend targetContext
            (promotedTarget input inputWellFormed trace))
          (extendWireEquiv (FiniteEquiv.refl (Fin targetContext.length))
            (FiniteEquiv.refl (Fin
              (Concrete.Elaboration.exactScopeWires (Target trace)
                (promotedTarget input inputWellFormed trace)).length))) =
        FiniteEquiv.refl (Fin
          (targetContext.extend
            (promotedTarget input inputWellFormed trace)).length) := by
        apply FiniteEquiv.ext
        intro index
        apply Fin.ext
        change (extendWireEquiv
          (FiniteEquiv.refl (Fin targetContext.length))
          (FiniteEquiv.refl (Fin
            (Concrete.Elaboration.exactScopeWires (Target trace)
              (promotedTarget input inputWellFormed trace)).length))
          (Fin.cast
            (Concrete.Elaboration.WireContext.length_extend targetContext
              (promotedTarget input inputWellFormed trace)) index)).val = index.val
        have castVal : (Fin.cast
            (Concrete.Elaboration.WireContext.length_extend targetContext
              (promotedTarget input inputWellFormed trace)) index).val =
            index.val := rfl
        rw [← castVal]
        refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_)
          (Fin.cast
            (Concrete.Elaboration.WireContext.length_extend targetContext
              (promotedTarget input inputWellFormed trace)) index)
        · rw [extendWireEquiv_outer]
          rfl
        · rw [extendWireEquiv_local]
          rfl
      rw [wireEq]
      exact orderedIso

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

private theorem ItemSeqIso.changeWire
    {first second : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (equality : first = second)
    {source : ItemSeq sourceWires rels}
    {target : ItemSeq targetWires rels}
    (iso : ItemSeqIso first rels source target) :
    ItemSeqIso second rels source target := by
  subst second
  exact iso

private theorem RegionIso.changeWire
    {first second : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (equality : first = second)
    {source : Region sourceWires rels}
    {target : Region targetWires rels}
    (iso : RegionIso first rels source target) :
    RegionIso second rels source target := by
  subst second
  exact iso

private theorem ItemSeq.renameRelations_identity
    (items : ItemSeq wires rels) :
    items.renameRelations
        (DoubleCutTransport.identityRelationRenaming rels) = items := by
  simpa [DoubleCutTransport.identityRelationRenaming] using
    ItemSeq.renameRelations_id items

private theorem promotion_items_iso
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
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount))
    (occurrencesLocal : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ Concrete.Elaboration.localOccurrences input region)
    (childrenSurvive : ∀ occurrence, occurrence ∈ occurrences →
      ∀ child, occurrence = .child child →
        (Domain input outer trace.inner).survives child = true)
    (childrenNotAbove : ∀ occurrence, occurrence ∈ occurrences →
      ∀ child, occurrence = .child child →
        ¬ input.Encloses child trace.target)
    {sourceItems : ItemSeq sourceContext.length rels}
    {targetItems : ItemSeq targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith? input
      (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
      sourceBinders occurrences = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith? (Target trace)
      (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
      targetContext targetBinders
      (occurrences.map
        (promoteOccurrence trace (promotedTarget input inputWellFormed trace))) =
        some targetItems) :
    ItemSeqIso (FiniteEquiv.refl (Fin targetContext.length)) rels
      (sourceItems.renameWires wireMap) targetItems := by
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
    sourceBinders sourceCompiled
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
    targetContext targetBinders targetCompiled
  let positions := (FiniteEquiv.finCast sourceLength).trans
    ((FiniteEquiv.finCast (List.length_map _).symm).trans
      (FiniteEquiv.finCast targetLength.symm))
  apply itemSeqIso_after_rename sourceItems targetItems wireMap positions
  intro sourceIndex
  let occurrenceIndex := Fin.cast sourceLength sourceIndex
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
    sourceBinders sourceCompiled occurrenceIndex
  let mappedIndex : Fin (occurrences.map
      (promoteOccurrence trace
        (promotedTarget input inputWellFormed trace))).length :=
    Fin.cast (List.length_map _).symm occurrenceIndex
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
    targetContext targetBinders targetCompiled mappedIndex
  have mappedOccurrence :
      (occurrences.map (promoteOccurrence trace
        (promotedTarget input inputWellFormed trace))).get mappedIndex =
        promoteOccurrence trace (promotedTarget input inputWellFormed trace)
          (occurrences.get occurrenceIndex) := by
    simpa [mappedIndex] using List.get_map occurrences
      (promoteOccurrence trace (promotedTarget input inputWellFormed trace))
      occurrenceIndex
  rw [mappedOccurrence] at targetGet
  exact compileOccurrence_promotion input inputWellFormed trace
    targetWellFormed region regionNeOuter sourceContext targetContext wireMap
    wireAgreement sourceExact targetExact sourceBinders targetBinders
    binderAgreement (occurrences.get occurrenceIndex)
    (occurrencesLocal _ (List.get_mem _ _))
    (childrenSurvive _ (List.get_mem _ _))
    (childrenNotAbove _ (List.get_mem _ _))
    (by simpa [positions, sourceLength, occurrenceIndex] using sourceGet)
    (by simpa [positions, sourceLength, targetLength, occurrenceIndex,
      mappedIndex] using targetGet)

private def appendIntoMap
    {sourceAmbient sourceLocal : List α} {target : List β}
    (ambient : Fin sourceAmbient.length → Fin target.length)
    (localMap : Fin sourceLocal.length → Fin target.length) :
    Fin (sourceAmbient ++ sourceLocal).length → Fin target.length :=
  fun index =>
    Fin.addCases ambient localMap (Fin.cast (by simp) index)

private theorem appendIntoMap_spec
    {sourceAmbient sourceLocal : List α} {target : List α}
    (ambient : Fin sourceAmbient.length → Fin target.length)
    (localMap : Fin sourceLocal.length → Fin target.length)
    (ambientAgreement : ∀ index,
      target.get (ambient index) = sourceAmbient.get index)
    (localAgreement : ∀ index,
      target.get (localMap index) = sourceLocal.get index) :
    ∀ index, target.get (appendIntoMap ambient localMap index) =
      (sourceAmbient ++ sourceLocal).get index := by
  intro index
  let sumIndex : Fin (sourceAmbient.length + sourceLocal.length) :=
    Fin.cast (by simp) index
  have indexEq : Fin.cast (by simp) sumIndex = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) sumIndex
  · simpa [appendIntoMap,
      Concrete.Elaboration.get_append_castAdd] using
        ambientAgreement outerIndex
  · simpa [appendIntoMap,
      Concrete.Elaboration.get_append_natAdd] using
        localAgreement localIndex

private theorem appendIntoMap_castAdd
    {sourceAmbient sourceLocal : List α} {target : List β}
    (ambient : Fin sourceAmbient.length → Fin target.length)
    (localMap : Fin sourceLocal.length → Fin target.length)
    (index : Fin sourceAmbient.length) :
    appendIntoMap ambient localMap
        (Fin.cast (by simp)
          (Fin.castAdd sourceLocal.length index)) = ambient index := by
  simp [appendIntoMap]

private theorem appendIntoMap_natAdd
    {sourceAmbient sourceLocal : List α} {target : List β}
    (ambient : Fin sourceAmbient.length → Fin target.length)
    (localMap : Fin sourceLocal.length → Fin target.length)
    (index : Fin sourceLocal.length) :
    appendIntoMap ambient localMap
        (Fin.cast (by simp)
          (Fin.natAdd sourceAmbient.length index)) = localMap index := by
  simp [appendIntoMap]

private theorem direct_child_encloses
    {input : Concrete.Diagram} {parent child : Fin input.regionCount}
    (relation : (input.regions child).parent? = some parent) :
    input.Encloses parent child := by
  refine ⟨⟨1, Nat.succ_lt_succ (Nat.zero_lt_of_lt child.isLt)⟩, ?_⟩
  change (match (input.regions child).parent? with
    | none => none
    | some directParent => input.climb 0 directParent) = some parent
  rw [relation]
  rfl
/-- The local structural witness at the eliminated double-cut focus.  The
source endpoint is the compiled wrapper at `trace.target`; the target endpoint
is the compiled promoted body at the compact survivor image of that region. -/
theorem focus
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {rels : RelCtx}
    {sourceFuel targetFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (ambient : FiniteEquiv
      (Fin sourceContext.length) (Fin targetContext.length))
    (wireAgreement : ∀ index,
      targetContext.get (ambient index) = sourceContext.get index)
    (sourceExact : (sourceContext.extend trace.target).Exact trace.target)
    (targetExact :
      (targetContext.extend (promotedTarget input inputWellFormed trace)).Exact
        (promotedTarget input inputWellFormed trace))
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (binderAgreement : ∀ binder,
      targetBinders binder = sourceBinders
        ((Domain input outer trace.inner).origin binder))
    {sourceBody : Region sourceContext.length rels}
    {targetBody : Region targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input sourceFuel
      trace.target sourceContext sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion? (Target trace)
      targetFuel (promotedTarget input inputWellFormed trace)
      targetContext targetBinders = some targetBody) :
    ∃ before after : Region sourceContext.length rels,
      Rule.DoubleCut.Local before after ∧
      RegionIso (FiniteEquiv.refl (Fin sourceContext.length)) rels
        sourceBody after ∧
      RegionIso ambient rels before targetBody := by
  obtain ⟨sourceHostItems, innerBody, sourceHostFuel, innerFuel,
      sourceHostCompiled, innerCompiled, sourceCanonical⟩ :=
    source_partition input trace sourceContext sourceBinders
      sourceCompiled
  obtain ⟨targetHostItems, targetInnerItems, targetItemFuel,
      targetHostCompiled, targetInnerCompiled, targetCanonical⟩ :=
    target_partition input inputWellFormed trace targetContext targetBinders
      targetCompiled
  cases innerFuel with
  | zero => simp [Concrete.Elaboration.compileRegion?] at innerCompiled
  | succ innerItemFuel =>
      simp only [Concrete.Elaboration.compileRegion?] at innerCompiled
      obtain ⟨sourceInnerItems, sourceInnerItemsCompiled, innerBodyEq⟩ :=
        Option.bind_eq_some_iff.mp innerCompiled
      have innerBodyEq' := Option.some.inj innerBodyEq
      subst innerBody
      let sourceHost := sourceContext.extend trace.target
      let sourceOuter := sourceHost.extend outer
      let sourceFull := sourceOuter.extend trace.inner
      let targetFull := targetContext.extend
        (promotedTarget input inputWellFormed trace)
      let localWire := exactWireEquiv input inputWellFormed trace
      let ambientFullMap : Fin sourceContext.length → Fin targetFull.length :=
        fun index => Fin.cast
          (Concrete.Elaboration.WireContext.length_extend targetContext
            (promotedTarget input inputWellFormed trace)).symm
          (Fin.castAdd
            (Concrete.Elaboration.exactScopeWires (Target trace)
              (promotedTarget input inputWellFormed trace)).length
            (ambient index))
      have ambientFullAgreement : ∀ index,
          targetFull.get (ambientFullMap index) = sourceContext.get index := by
        intro index
        calc
          _ = targetContext.get (ambient index) := by
            simpa [targetFull, ambientFullMap,
              Concrete.Elaboration.WireContext.extend] using
              (Concrete.Elaboration.get_append_castAdd targetContext
                (Concrete.Elaboration.exactScopeWires (Target trace)
                  (promotedTarget input inputWellFormed trace)) (ambient index))
          _ = sourceContext.get index := wireAgreement index
      let hostLocalMap : Fin (sourceHostWires trace).length →
          Fin targetFull.length := fun index =>
        Fin.cast
          (Concrete.Elaboration.WireContext.length_extend targetContext
            (promotedTarget input inputWellFormed trace)).symm
          (Fin.natAdd targetContext.length
            (localWire (Fin.cast (by simp)
              (Fin.castAdd (sourceInnerWires trace).length index))))
      let hostMap : Fin sourceHost.length → Fin targetFull.length :=
        appendIntoMap ambientFullMap hostLocalMap
      have hostAgreement : ∀ index,
          targetFull.get (hostMap index) = sourceHost.get index := by
        apply appendIntoMap_spec ambientFullMap hostLocalMap
          ambientFullAgreement
        intro index
        have localSpec := exactWireEquiv_spec input inputWellFormed trace
          (Fin.cast (by simp)
            (Fin.castAdd (sourceInnerWires trace).length index))
        calc
          targetFull.get (hostLocalMap index) =
              (Concrete.Elaboration.exactScopeWires (Target trace)
                (promotedTarget input inputWellFormed trace)).get
                (localWire (Fin.cast (by simp)
                  (Fin.castAdd (sourceInnerWires trace).length index))) := by
            simpa [targetFull, hostLocalMap,
              Concrete.Elaboration.WireContext.extend] using
              (Concrete.Elaboration.get_append_natAdd targetContext
                (Concrete.Elaboration.exactScopeWires (Target trace)
                  (promotedTarget input inputWellFormed trace))
                (localWire (Fin.cast (by simp)
                  (Fin.castAdd (sourceInnerWires trace).length index))))
          _ = (sourceHostWires trace).get index := by
            simpa [localWire, targetExactWires, sourceHostWires,
              sourceInnerWires] using localSpec
      let sourceOuterMap : Fin sourceOuter.length → Fin targetFull.length :=
        appendIntoMap hostMap (fun index => Fin.elim0 (by
          simpa [outer_exactScopeWires trace] using index))
      have sourceOuterAgreement : ∀ index,
          targetFull.get (sourceOuterMap index) = sourceOuter.get index := by
        apply appendIntoMap_spec hostMap
          (fun index => Fin.elim0 (by
            simpa [outer_exactScopeWires trace] using index)) hostAgreement
        intro index
        exact Fin.elim0 (by simpa [outer_exactScopeWires trace] using index)
      let innerLocalMap : Fin (sourceInnerWires trace).length →
          Fin targetFull.length := fun index =>
        Fin.cast
          (Concrete.Elaboration.WireContext.length_extend targetContext
            (promotedTarget input inputWellFormed trace)).symm
          (Fin.natAdd targetContext.length
            (localWire (Fin.cast (by simp)
              (Fin.natAdd (sourceHostWires trace).length index))))
      let fullMap : Fin sourceFull.length → Fin targetFull.length :=
        appendIntoMap sourceOuterMap innerLocalMap
      have fullAgreement : ∀ index,
          targetFull.get (fullMap index) = sourceFull.get index := by
        apply appendIntoMap_spec sourceOuterMap innerLocalMap
          sourceOuterAgreement
        intro index
        have localSpec := exactWireEquiv_spec input inputWellFormed trace
          (Fin.cast (by simp)
            (Fin.natAdd (sourceHostWires trace).length index))
        calc
          targetFull.get (innerLocalMap index) =
              (Concrete.Elaboration.exactScopeWires (Target trace)
                (promotedTarget input inputWellFormed trace)).get
                (localWire (Fin.cast (by simp)
                  (Fin.natAdd (sourceHostWires trace).length index))) := by
            simpa [targetFull, innerLocalMap,
              Concrete.Elaboration.WireContext.extend] using
              (Concrete.Elaboration.get_append_natAdd targetContext
                (Concrete.Elaboration.exactScopeWires (Target trace)
                  (promotedTarget input inputWellFormed trace))
                (localWire (Fin.cast (by simp)
                  (Fin.natAdd (sourceHostWires trace).length index))))
          _ = (sourceInnerWires trace).get index := by
            simpa [localWire, targetExactWires, sourceHostWires,
              sourceInnerWires] using localSpec
      have sourceOuterExact : sourceOuter.Exact outer := by
        exact sourceExact.extend_child inputWellFormed (by
          simpa [trace.outer_eq, Concrete.CRegion.parent?])
      have sourceFullExact : sourceFull.Exact trace.inner := by
        exact sourceOuterExact.extend_child inputWellFormed (by
          simpa [trace.inner_eq, Concrete.CRegion.parent?])
      have hostItemsIso := promotion_items_iso input inputWellFormed trace
        targetWellFormed trace.target
        (target_ne_outer input inputWellFormed trace.outer_eq)
        sourceHost targetFull hostMap hostAgreement sourceExact (by
          simpa [targetFull, promoteRegionIndex,
            target_ne_inner input inputWellFormed trace.outer_eq
              trace.inner_eq] using targetExact)
        sourceBinders targetBinders binderAgreement (hostOccurrences trace)
        (by
          intro occurrence member
          exact (List.mem_filter.mp member).1)
        (by
          intro occurrence member child occurrenceEq
          subst occurrence
          exact focusOccurrence_survives input inputWellFormed trace
            (.child child) (List.mem_append_left _ member))
        (by
          intro occurrence member child occurrenceEq
          subst occurrence
          have parent :=
            (Concrete.Elaboration.mem_localOccurrences_child input
              trace.target child).1 (List.mem_filter.mp member).1
          exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
            inputWellFormed parent)
        sourceHostCompiled targetHostCompiled
      have innerItemsIso := promotion_items_iso input inputWellFormed trace
        targetWellFormed trace.inner
        (outer_ne_inner input inputWellFormed trace.inner_eq).symm
        sourceFull targetFull fullMap fullAgreement sourceFullExact (by
          simpa [targetFull, promoteRegionIndex] using targetExact)
        sourceBinders targetBinders binderAgreement (innerOccurrences trace)
        (by intro occurrence member; exact member)
        (by
          intro occurrence member child occurrenceEq
          subst occurrence
          exact focusOccurrence_survives input inputWellFormed trace
            (.child child) (List.mem_append_right _ member))
        (by
          intro occurrence member child occurrenceEq
          subst occurrence
          have childParent :=
            (Concrete.Elaboration.mem_localOccurrences_child input
              trace.inner child).1 member
          intro childEnclosesTarget
          have targetEnclosesOuter : input.Encloses trace.target outer :=
            direct_child_encloses (input := input) (by
            simpa [trace.outer_eq, Concrete.CRegion.parent?])
          have outerEnclosesInner : input.Encloses outer trace.inner :=
            direct_child_encloses (input := input) (by
            simpa [trace.inner_eq, Concrete.CRegion.parent?])
          have childEnclosesInner :=
            Concrete.Elaboration.checked_encloses_trans inputWellFormed
              childEnclosesTarget
              (Concrete.Elaboration.checked_encloses_trans inputWellFormed
                targetEnclosesOuter outerEnclosesInner)
          exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
            inputWellFormed childParent childEnclosesInner)
        sourceInnerItemsCompiled targetInnerCompiled
      let outerWire : FiniteEquiv (Fin sourceOuter.length)
          (Fin (sourceContext.length + (sourceHostWires trace).length)) :=
        FiniteEquiv.finCast (by
          simp [sourceOuter, sourceHost, sourceHostWires,
            outer_exactScopeWires trace,
            Concrete.Elaboration.WireContext.length_extend])
      let material : Region
          (sourceContext.length + (sourceHostWires trace).length) rels :=
        (Concrete.Elaboration.finishRegion input sourceOuter trace.inner
          sourceInnerItems).renameWires outerWire
      let hostItems : ItemSeq
          (sourceContext.length + (sourceHostWires trace).length) rels :=
        sourceHostItems.castWiresEq (by
          simpa [sourceHost, sourceHostWires] using
            Concrete.Elaboration.WireContext.length_extend sourceContext
              trace.target)
      let before : Region sourceContext.length rels :=
        Region.spliceAt (sourceHostWires trace).length hostItems material
          id
          (DoubleCutTransport.identityRelationRenaming rels)
      let after : Region sourceContext.length rels :=
        Region.spliceAt (sourceHostWires trace).length hostItems
          (Rule.DoubleCut.wrap material) id
          (DoubleCutTransport.identityRelationRenaming rels)
      refine ⟨before, after, ?_, ?_, ?_⟩
      · exact Rule.DoubleCut.Local.introduce
          (sourceHostWires trace).length hostItems material id
          (DoubleCutTransport.identityRelationRenaming rels)
      · let innerBody := Concrete.Elaboration.finishRegion input sourceOuter
          trace.inner sourceInnerItems
        have materialIso : RegionIso outerWire rels innerBody material := by
          exact RegionIso.renameWiresEquiv innerBody outerWire
        have materialBack := materialIso.symm
        have innerItemIso := singleton_iso (ItemIso.cut materialBack)
        have outerBodyIso := empty_finish_iso input sourceHost outer
          (outer_exactScopeWires trace) outerWire.symm innerItemIso
        have wrappedIso := singleton_iso (ItemIso.cut outerBodyIso.symm)
        let completeWire : FiniteEquiv (Fin sourceHost.length)
            (Fin (sourceContext.length + (sourceHostWires trace).length)) :=
          FiniteEquiv.finCast (by
            simpa [sourceHost, sourceHostWires] using
              Concrete.Elaboration.WireContext.length_extend sourceContext
                trace.target)
        have wrappedIso' : ItemSeqIso completeWire rels
            (.cons (.cut
              (Concrete.Elaboration.finishRegion input sourceHost outer
                (.cons (.cut innerBody) .nil))) .nil)
            (.cons (.cut (.mk 0 (.cons (.cut material) .nil))) .nil) := by
          apply ItemSeqIso.changeWire _ wrappedIso
          apply FiniteEquiv.ext
          intro index
          apply Fin.ext
          rfl
        have hostIso : ItemSeqIso completeWire rels sourceHostItems hostItems := by
          dsimp only [hostItems]
          rw [ItemSeq.castWiresEq_eq_renameWires]
          apply ItemSeqIso.changeWire _
            (ItemSeqIso.renameWiresEquiv sourceHostItems completeWire)
          apply FiniteEquiv.ext
          intro index
          apply Fin.ext
          rfl
        have combined := ItemSeqIso.append hostIso wrappedIso'
        let wrapped : ItemSeq
            (sourceContext.length + (sourceHostWires trace).length) rels :=
          .cons (.cut (.mk 0 (.cons (.cut material) .nil))) .nil
        have afterEq : after =
            Concrete.Elaboration.finishRegion input sourceContext trace.target
              ((hostItems.append wrapped).castWiresEq
                (Concrete.Elaboration.WireContext.length_extend sourceContext
                  trace.target).symm) := by
          exact splice_partition_eq input sourceContext trace.target
            hostItems wrapped
        let backWire : FiniteEquiv
            (Fin (sourceContext.length + (sourceHostWires trace).length))
            (Fin sourceHost.length) := completeWire.symm
        have combinedBack : ItemSeqIso (FiniteEquiv.refl (Fin sourceHost.length))
            rels
            (sourceHostItems.append (.cons (.cut
              (Concrete.Elaboration.finishRegion input sourceHost outer
                (.cons (.cut innerBody) .nil))) .nil))
            ((hostItems.append wrapped).renameWires backWire) := by
          have transported := combined.renameWires_commuting id backWire
            (FiniteEquiv.refl (Fin sourceHost.length)) (by
              funext index
              exact completeWire.left_inv index)
          simpa [ItemSeq.renameWires_id] using transported
        have castEq :
            (hostItems.append wrapped).castWiresEq
                (Concrete.Elaboration.WireContext.length_extend sourceContext
                  trace.target).symm =
              (hostItems.append wrapped).renameWires backWire := by
          rw [ItemSeq.castWiresEq_eq_renameWires]
          congr 1
        rw [afterEq, castEq]
        exact sourceCanonical.trans
          (Concrete.Elaboration.regionIso_of_cast
            (Concrete.Elaboration.WireContext.length_extend sourceContext
              trace.target)
            (Concrete.Elaboration.WireContext.length_extend sourceContext
              trace.target)
            (FiniteEquiv.refl (Fin sourceContext.length))
            (FiniteEquiv.refl (Fin (sourceHostWires trace).length))
            _ _ (by
              apply ItemSeqIso.changeWire _ combinedBack
              apply FiniteEquiv.ext
              intro index
              apply Fin.ext
              change index.val =
                (extendWireEquiv
                  (FiniteEquiv.refl (Fin sourceContext.length))
                  (FiniteEquiv.refl (Fin (sourceHostWires trace).length))
                  (Fin.cast
                    (Concrete.Elaboration.WireContext.length_extend
                      sourceContext trace.target) index)).val
              have castVal : (Fin.cast
                  (Concrete.Elaboration.WireContext.length_extend
                    sourceContext trace.target) index).val = index.val := rfl
              rw [← castVal]
              refine Fin.addCases (fun outerIndex => ?_)
                (fun localIndex => ?_)
                (Fin.cast
                  (Concrete.Elaboration.WireContext.length_extend
                    sourceContext trace.target) index)
              · simp [sourceHostWires, extendWireEquiv]
              · simp [sourceHostWires, extendWireEquiv]))
      · let localWireSum : FiniteEquiv
            (Fin ((sourceHostWires trace).length +
              (sourceInnerWires trace).length))
            (Fin (targetExactWires input inputWellFormed trace).length) :=
          (FiniteEquiv.finCast (by simp)).trans localWire
        let sourceCombined := sourceContext.length +
          ((sourceHostWires trace).length +
            (sourceInnerWires trace).length)
        let targetCombined := targetContext.length +
          (targetExactWires input inputWellFormed trace).length
        let totalWire : FiniteEquiv (Fin sourceCombined)
            (Fin targetCombined) := extendWireEquiv ambient localWireSum
        let targetCast : Fin targetFull.length → Fin targetCombined :=
          Fin.cast (by
            simpa [targetFull, targetExactWires] using
              Concrete.Elaboration.WireContext.length_extend targetContext
                (promotedTarget input inputWellFormed trace))
        let hostPlacement : Fin sourceHost.length → Fin sourceCombined :=
          fun index => Region.adjoinHostWire sourceContext.length
            (sourceHostWires trace).length (sourceInnerWires trace).length
            (Fin.cast (by
              simpa [sourceHost, sourceHostWires] using
                Concrete.Elaboration.WireContext.length_extend sourceContext
                  trace.target) index)
        let innerPlacement : Fin sourceFull.length → Fin sourceCombined :=
          fun index => Region.adjoinMaterialWire sourceContext.length
            (sourceHostWires trace).length (sourceInnerWires trace).length
            (extendWireRenaming outerWire
              (sourceInnerWires trace).length
              (Fin.cast (by
                simpa [sourceFull, sourceInnerWires] using
                  Concrete.Elaboration.WireContext.length_extend sourceOuter
                    trace.inner) index))
        have hostFactor : totalWire.toFun ∘ hostPlacement =
            targetCast ∘ hostMap := by
          funext index
          apply Fin.ext
          let split : Fin (sourceContext.length +
              (sourceHostWires trace).length) := Fin.cast (by
            simpa [sourceHost, sourceHostWires] using
              Concrete.Elaboration.WireContext.length_extend sourceContext
                trace.target) index
          have indexEq : Fin.cast (by
              simpa [sourceHost, sourceHostWires] using
                (Concrete.Elaboration.WireContext.length_extend sourceContext
                  trace.target).symm) split = index := by
            rfl
          rw [← indexEq]
          refine Fin.addCases (fun ambientIndex => ?_)
            (fun localIndex => ?_) split
          · simp only [Function.comp_apply]
            have placementEq : hostPlacement
                (Fin.cast (by simp [sourceHost, sourceHostWires])
                  (Fin.castAdd (sourceHostWires trace).length ambientIndex)) =
                Fin.castAdd ((sourceHostWires trace).length +
                  (sourceInnerWires trace).length) ambientIndex := by
              apply Fin.ext
              rfl
            rw [placementEq]
            rw [show hostMap
                (Fin.cast (by simp [sourceHost, sourceHostWires])
                  (Fin.castAdd (sourceHostWires trace).length ambientIndex)) =
                ambientFullMap ambientIndex by
              exact appendIntoMap_castAdd ambientFullMap hostLocalMap
                ambientIndex]
            rw [show totalWire
                (Fin.castAdd ((sourceHostWires trace).length +
                  (sourceInnerWires trace).length) ambientIndex) =
                Fin.castAdd (targetExactWires input inputWellFormed trace).length
                  (ambient ambientIndex) by
              simp [totalWire, sourceCombined, targetCombined,
                extendWireEquiv]]
            rfl
          · simp only [Function.comp_apply]
            have placementEq : hostPlacement
                (Fin.cast (by simp [sourceHost, sourceHostWires])
                  (Fin.natAdd sourceContext.length localIndex)) =
                Fin.natAdd sourceContext.length
                  (Fin.castAdd (sourceInnerWires trace).length localIndex) := by
              apply Fin.ext
              rfl
            rw [placementEq]
            rw [show hostMap
                (Fin.cast (by simp [sourceHost, sourceHostWires])
                  (Fin.natAdd sourceContext.length localIndex)) =
                hostLocalMap localIndex by
              exact appendIntoMap_natAdd ambientFullMap hostLocalMap localIndex]
            rw [show totalWire
                (Fin.natAdd sourceContext.length
                  (Fin.castAdd (sourceInnerWires trace).length localIndex)) =
                Fin.natAdd targetContext.length
                  (localWire (Fin.cast (by simp)
                    (Fin.castAdd (sourceInnerWires trace).length localIndex))) by
              simp [totalWire, localWireSum, sourceCombined, targetCombined,
                extendWireEquiv]
              apply Fin.ext
              rfl]
            rfl
        let outerPlacement : Fin sourceOuter.length → Fin sourceCombined :=
          fun index => Region.adjoinHostWire sourceContext.length
            (sourceHostWires trace).length (sourceInnerWires trace).length
            (outerWire index)
        have outerFactor : totalWire.toFun ∘ outerPlacement =
            targetCast ∘ sourceOuterMap := by
          funext index
          let hostIndex : Fin sourceHost.length := Fin.cast (by
            simp [sourceOuter, sourceHost, outer_exactScopeWires trace,
              Concrete.Elaboration.WireContext.length_extend]) index
          have placementEq : outerPlacement index = hostPlacement hostIndex := by
            apply Fin.ext
            rfl
          have mapEq : sourceOuterMap index = hostMap hostIndex := by
            have asAmbient : index = Fin.cast (by
                simp [sourceOuter, sourceHost, outer_exactScopeWires trace,
                  Concrete.Elaboration.WireContext.length_extend])
                (Fin.castAdd 0 hostIndex) := by
              apply Fin.ext
              rfl
            rw [asAmbient]
            exact appendIntoMap_castAdd hostMap
              (fun emptyIndex => Fin.elim0 (by
                simpa [outer_exactScopeWires trace] using emptyIndex)) hostIndex
          simp only [Function.comp_apply]
          rw [placementEq, mapEq]
          exact congrFun hostFactor hostIndex
        have innerFactor : totalWire.toFun ∘ innerPlacement =
            targetCast ∘ fullMap := by
          funext index
          let split : Fin (sourceOuter.length +
              (sourceInnerWires trace).length) := Fin.cast (by
            simpa [sourceFull, sourceInnerWires] using
              Concrete.Elaboration.WireContext.length_extend sourceOuter
                trace.inner) index
          have indexEq : Fin.cast (by
              simpa [sourceFull, sourceInnerWires] using
                (Concrete.Elaboration.WireContext.length_extend sourceOuter
                  trace.inner).symm) split = index := by
            apply Fin.ext
            rfl
          rw [← indexEq]
          refine Fin.addCases (fun outerIndex => ?_)
            (fun innerIndex => ?_) split
          · simp only [Function.comp_apply]
            have placementEq : innerPlacement
                (Fin.cast (by simp [sourceFull, sourceInnerWires])
                  (Fin.castAdd (sourceInnerWires trace).length outerIndex)) =
                outerPlacement outerIndex := by
              apply Fin.ext
              simp [innerPlacement, outerPlacement, outerWire,
                Region.adjoinMaterialWire, Region.adjoinHostWire,
                extendWireRenaming]
            rw [placementEq]
            rw [show fullMap
                (Fin.cast (by simp [sourceFull, sourceInnerWires])
                  (Fin.castAdd (sourceInnerWires trace).length outerIndex)) =
                sourceOuterMap outerIndex by
              exact appendIntoMap_castAdd sourceOuterMap innerLocalMap
                outerIndex]
            exact congrFun outerFactor outerIndex
          · simp only [Function.comp_apply]
            have placementEq : innerPlacement
                (Fin.cast (by simp [sourceFull, sourceInnerWires])
                  (Fin.natAdd sourceOuter.length innerIndex)) =
                Fin.natAdd sourceContext.length
                  (Fin.natAdd (sourceHostWires trace).length innerIndex) := by
              apply Fin.ext
              simp [innerPlacement, outerWire, sourceOuter, sourceHost,
                sourceHostWires,
                Region.adjoinMaterialWire, extendWireRenaming]
              omega
            rw [placementEq]
            rw [show fullMap
                (Fin.cast (by simp [sourceFull, sourceInnerWires])
                  (Fin.natAdd sourceOuter.length innerIndex)) =
                innerLocalMap innerIndex by
              exact appendIntoMap_natAdd sourceOuterMap innerLocalMap innerIndex]
            rw [show totalWire
                (Fin.natAdd sourceContext.length
                  (Fin.natAdd (sourceHostWires trace).length innerIndex)) =
                Fin.natAdd targetContext.length
                  (localWire (Fin.cast (by simp)
                    (Fin.natAdd (sourceHostWires trace).length innerIndex))) by
              simp [totalWire, localWireSum, sourceCombined, targetCombined,
                extendWireEquiv]
              apply Fin.ext
              rfl]
            apply Fin.ext
            rfl
        have hostBack : (totalWire.symm.toFun ∘ targetCast) ∘ hostMap =
            hostPlacement := by
          funext index
          have factor := congrFun hostFactor index
          change totalWire (hostPlacement index) =
            targetCast (hostMap index) at factor
          change totalWire.symm (targetCast (hostMap index)) =
            hostPlacement index
          rw [← factor]
          exact totalWire.left_inv (hostPlacement index)
        have innerBack : (totalWire.symm.toFun ∘ targetCast) ∘ fullMap =
            innerPlacement := by
          funext index
          have factor := congrFun innerFactor index
          change totalWire (innerPlacement index) =
            targetCast (fullMap index) at factor
          change totalWire.symm (targetCast (fullMap index)) =
            innerPlacement index
          rw [← factor]
          exact totalWire.left_inv (innerPlacement index)
        have commute : totalWire.toFun ∘
              (totalWire.symm.toFun ∘ targetCast) =
            targetCast ∘ (FiniteEquiv.refl (Fin targetFull.length)).toFun := by
          funext index
          exact totalWire.right_inv (targetCast index)
        have hostTransported := hostItemsIso.renameWires_commuting
          (totalWire.symm.toFun ∘ targetCast) targetCast totalWire commute
        have innerTransported := innerItemsIso.renameWires_commuting
          (totalWire.symm.toFun ∘ targetCast) targetCast totalWire commute
        have hostFinal : ItemSeqIso totalWire rels
            (sourceHostItems.renameWires hostPlacement)
            (targetHostItems.renameWires targetCast) := by
          simpa only [ItemSeq.renameWires_comp, hostBack] using
            hostTransported
        have innerFinal : ItemSeqIso totalWire rels
            (sourceInnerItems.renameWires innerPlacement)
            (targetInnerItems.renameWires targetCast) := by
          simpa only [ItemSeq.renameWires_comp, innerBack] using
            innerTransported
        have blocks := ItemSeqIso.append hostFinal innerFinal
        have hostSeqEq : hostItems.renameWires
              (Region.adjoinHostWire sourceContext.length
                (sourceHostWires trace).length
                (sourceInnerWires trace).length) =
            sourceHostItems.renameWires hostPlacement := by
          dsimp only [hostItems, hostPlacement]
          rw [ItemSeq.castWiresEq_eq_renameWires,
            ItemSeq.renameWires_comp]
          congr 1
        let innerLayout :=
          Concrete.Elaboration.WireContext.length_extend sourceOuter trace.inner
        have innerSeqEq :
            (((sourceInnerItems.castWiresEq innerLayout).renameWires
                (extendWireRenaming outerWire
                  (sourceInnerWires trace).length)).renameWires
              (Region.adjoinMaterialWire sourceContext.length
                (sourceHostWires trace).length
                (sourceInnerWires trace).length)) =
              sourceInnerItems.renameWires innerPlacement := by
          rw [ItemSeq.castWiresEq_eq_renameWires]
          calc
            _ = (sourceInnerItems.renameWires (Fin.cast innerLayout)).renameWires
                ((Region.adjoinMaterialWire sourceContext.length
                  (sourceHostWires trace).length
                  (sourceInnerWires trace).length) ∘
                    extendWireRenaming outerWire
                      (sourceInnerWires trace).length) :=
              ItemSeq.renameWires_comp
                (sourceInnerItems.renameWires (Fin.cast innerLayout)) _ _
            _ = sourceInnerItems.renameWires
                (((Region.adjoinMaterialWire sourceContext.length
                  (sourceHostWires trace).length
                  (sourceInnerWires trace).length) ∘
                    extendWireRenaming outerWire
                      (sourceInnerWires trace).length) ∘
                  Fin.cast innerLayout) :=
              ItemSeq.renameWires_comp sourceInnerItems _ _
            _ = sourceInnerItems.renameWires innerPlacement := by
              apply congrArg
              rfl
        have targetSeqEq :
            (targetHostItems.append targetInnerItems).castWiresEq (by
                simpa [targetFull, targetExactWires] using
                  Concrete.Elaboration.WireContext.length_extend targetContext
                    (promotedTarget input inputWellFormed trace)) =
              (targetHostItems.renameWires targetCast).append
                (targetInnerItems.renameWires targetCast) := by
          rw [ItemSeq.castWiresEq_eq_renameWires,
            ItemSeq.renameWires_append]
        have beforeCanonical : RegionIso ambient rels before
            (Concrete.Elaboration.finishRegion (Target trace) targetContext
              (promotedTarget input inputWellFormed trace)
              (targetHostItems.append targetInnerItems)) := by
          unfold Concrete.Elaboration.finishRegion
          apply RegionIso.mk localWireSum
          have adjusted : ItemSeqIso (extendWireEquiv ambient localWireSum)
              rels
              ((sourceHostItems.renameWires hostPlacement).append
                (sourceInnerItems.renameWires innerPlacement))
              ((targetHostItems.renameWires targetCast).append
                (targetInnerItems.renameWires targetCast)) := by
            apply ItemSeqIso.changeWire _ blocks
            rfl
          simp only [ItemSeq.renameRelations_identity,
            ItemSeq.renameWires_comp, extendWireRenaming_id,
            Function.id_comp]
          simp only [sourceInnerWires] at hostSeqEq innerSeqEq
          rw [hostSeqEq, ← ItemSeq.renameWires_comp, innerSeqEq,
            ItemSeq.castWiresEq_eq_renameWires, ItemSeq.renameWires_append]
          exact adjusted
        have composed := beforeCanonical.trans targetCanonical.symm
        apply RegionIso.changeWire _ composed
        apply FiniteEquiv.ext
        intro index
        apply Fin.ext
        rfl

/-- The root-site specialization of `focus`, where both surrounding wire
contexts are empty. -/
theorem root_focus
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {rels : RelCtx}
    {sourceFuel targetFuel : Nat}
    (sourceExact :
      (Concrete.Elaboration.WireContext.extend
        ([] : Concrete.Elaboration.WireContext input) trace.target).Exact
          trace.target)
    (targetExact :
      (Concrete.Elaboration.WireContext.extend
        ([] : Concrete.Elaboration.WireContext (Target trace))
          (promotedTarget input inputWellFormed trace)).Exact
          (promotedTarget input inputWellFormed trace))
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (binderAgreement : ∀ binder,
      targetBinders binder = sourceBinders
        ((Domain input outer trace.inner).origin binder))
    {sourceBody targetBody : Region 0 rels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input sourceFuel
      trace.target [] sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion? (Target trace)
      targetFuel (promotedTarget input inputWellFormed trace)
      [] targetBinders = some targetBody) :
    ∃ before after : Region 0 rels,
      Rule.DoubleCut.Local before after ∧
      RegionIso (FiniteEquiv.refl (Fin 0)) rels sourceBody after ∧
      RegionIso (FiniteEquiv.refl (Fin 0)) rels before targetBody := by
  apply focus input inputWellFormed trace targetWellFormed
    ([] : Concrete.Elaboration.WireContext input)
    ([] : Concrete.Elaboration.WireContext (Target trace))
    (FiniteEquiv.refl (Fin 0))
    (fun index => Fin.elim0 index)
    sourceExact targetExact sourceBinders targetBinders binderAgreement
    sourceCompiled targetCompiled

end VisualProof.Refinement.Implementation.DoubleCutElimCompile
