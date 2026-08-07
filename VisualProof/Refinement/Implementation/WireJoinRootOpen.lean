import VisualProof.Refinement.Implementation.WireJoinCompile
import VisualProof.Rule.WireSever
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite

private theorem castBoundaryVal
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (position : Fin targetArity) :
    ((diagram.castArity equality).boundary position).val =
      (diagram.boundary (Fin.cast equality.symm position)).val := by
  subst targetArity
  rfl

private theorem castBody
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity)
    (externalEq : (diagram.castArity equality).externalClasses =
      diagram.externalClasses) :
    (diagram.castArity equality).body =
      diagram.body.renameWires (Fin.cast externalEq.symm) := by
  subst targetArity
  have proofEq : externalEq = rfl := Subsingleton.elim _ _
  rw [proofEq]
  simpa using (Region.renameWires_id diagram.body).symm

noncomputable def exposedIndex
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (member : wire ∈ source.exposedWires) :
    Fin source.exposedWires.length :=
  Classical.choose
    (Concrete.Elaboration.WireContext.lookup?_complete member)

theorem exposedIndex_get
    (source : Concrete.OpenDiagram)
    (wire : Fin source.diagram.wireCount)
    (member : wire ∈ source.exposedWires) :
    source.exposedWires.get (exposedIndex source wire member) = wire :=
  Concrete.Elaboration.WireContext.lookup?_sound
    (Classical.choose_spec
      (Concrete.Elaboration.WireContext.lookup?_complete member))

theorem exposedIndex_ne
    (source : Concrete.OpenDiagram)
    (left right : Fin source.diagram.wireCount)
    (leftMember : left ∈ source.exposedWires)
    (rightMember : right ∈ source.exposedWires)
    (distinct : left ≠ right) :
    exposedIndex source left leftMember ≠
      exposedIndex source right rightMember := by
  intro equality
  apply distinct
  rw [← exposedIndex_get source left leftMember,
    ← exposedIndex_get source right rightMember, equality]

noncomputable def exposedPreimage
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.exposedWires)
    (innerExposed : inner ∈ source.exposedWires)
    (targetIndex : Fin
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length) :
    Fin source.exposedWires.length :=
  let chosen := Classical.choose
    (VisualProof.Refinement.Implementation.WireJoin.exposedMap_surjective source outer inner distinct
      targetIndex)
  let innerIndex := exposedIndex source inner innerExposed
  if chosen = innerIndex then exposedIndex source outer outerExposed else chosen

theorem exposedMap_exposedPreimage
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.exposedWires)
    (innerExposed : inner ∈ source.exposedWires)
    (targetIndex : Fin
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length) :
    VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct
        (exposedPreimage source outer inner distinct outerExposed innerExposed
          targetIndex) =
      targetIndex := by
  let chosen := Classical.choose
    (VisualProof.Refinement.Implementation.WireJoin.exposedMap_surjective source outer inner distinct
      targetIndex)
  have chosenSpec := Classical.choose_spec
    (VisualProof.Refinement.Implementation.WireJoin.exposedMap_surjective source outer inner distinct
      targetIndex)
  let innerIndex := exposedIndex source inner innerExposed
  by_cases equality : chosen = innerIndex
  · unfold exposedPreimage
    dsimp only
    rw [if_pos equality]
    rw [← chosenSpec]
    apply Fin.ext
    apply (List.getElem_inj
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires_nodup).mp
    have chosenGet : source.exposedWires.get chosen = inner := by
      rw [equality]
      exact exposedIndex_get source inner innerExposed
    have mappedWire : VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram outer inner
        distinct outer =
      VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram outer inner distinct inner :=
      (VisualProof.Refinement.Implementation.WireJoin.wireMap_of_ne source.diagram outer inner outer
        distinct distinct).trans
          (VisualProof.Refinement.Implementation.WireJoin.wireMap_inner source.diagram outer inner
            distinct).symm
    have getEquality :
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.get
              (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct
                (exposedIndex source outer outerExposed)) =
          (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.get
              (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct
                chosen) := by
      calc
        _ = VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram outer inner distinct
              outer := by
          rw [VisualProof.Refinement.Implementation.WireJoin.exposedMap_get, exposedIndex_get]
        _ = VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram outer inner distinct
              inner := mappedWire
        _ = VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram outer inner distinct
              (source.exposedWires.get chosen) :=
          congrArg (VisualProof.Refinement.Implementation.WireJoin.wireMap source.diagram outer inner
            distinct) chosenGet.symm
        _ = _ := (VisualProof.Refinement.Implementation.WireJoin.exposedMap_get source outer inner
          distinct chosen).symm
    simpa only [List.get_eq_getElem] using getEquality
  · unfold exposedPreimage
    dsimp only
    rw [if_neg equality]
    exact chosenSpec

theorem exposedPreimage_ne_inner
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.exposedWires)
    (innerExposed : inner ∈ source.exposedWires)
    (targetIndex : Fin
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length) :
    exposedPreimage source outer inner distinct outerExposed innerExposed
        targetIndex ≠ exposedIndex source inner innerExposed := by
  let chosen := Classical.choose
    (VisualProof.Refinement.Implementation.WireJoin.exposedMap_surjective source outer inner distinct
      targetIndex)
  by_cases equality : chosen = exposedIndex source inner innerExposed
  · unfold exposedPreimage
    dsimp only
    rw [if_pos equality]
    exact exposedIndex_ne source outer inner outerExposed innerExposed distinct
  · unfold exposedPreimage
    dsimp only
    rw [if_neg equality]
    exact equality

noncomputable def exposedPlusEmbedding
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.exposedWires)
    (innerExposed : inner ∈ source.exposedWires) :
    Fin ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length + 1) →
      Fin source.exposedWires.length :=
  fun index =>
    if beforeLast : index.val <
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length then
      exposedPreimage source outer inner distinct outerExposed innerExposed
        ⟨index.val, beforeLast⟩
    else
      exposedIndex source inner innerExposed

theorem exposedPlusEmbedding_injective
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.exposedWires)
    (innerExposed : inner ∈ source.exposedWires) :
    Function.Injective
      (exposedPlusEmbedding source outer inner distinct outerExposed
        innerExposed) := by
  intro left right equality
  by_cases leftBefore : left.val <
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length <;>
    by_cases rightBefore : right.val <
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length
  · have reduced : exposedPreimage source outer inner distinct outerExposed
        innerExposed ⟨left.val, leftBefore⟩ =
      exposedPreimage source outer inner distinct outerExposed innerExposed
        ⟨right.val, rightBefore⟩ := by
      simpa only [exposedPlusEmbedding, dif_pos leftBefore,
        dif_pos rightBefore] using equality
    have mapped := congrArg
      (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct) reduced
    rw [exposedMap_exposedPreimage source outer inner distinct outerExposed
        innerExposed ⟨left.val, leftBefore⟩,
      exposedMap_exposedPreimage source outer inner distinct outerExposed
        innerExposed ⟨right.val, rightBefore⟩] at mapped
    exact Fin.ext (congrArg (fun index => index.val) mapped)
  · have reduced : exposedPreimage source outer inner distinct outerExposed
        innerExposed ⟨left.val, leftBefore⟩ =
      exposedIndex source inner innerExposed := by
      simpa only [exposedPlusEmbedding, dif_pos leftBefore,
        dif_neg rightBefore] using equality
    exact False.elim
      (exposedPreimage_ne_inner source outer inner distinct outerExposed
        innerExposed ⟨left.val, leftBefore⟩ reduced)
  · have reduced : exposedIndex source inner innerExposed =
      exposedPreimage source outer inner distinct outerExposed innerExposed
        ⟨right.val, rightBefore⟩ := by
      simpa only [exposedPlusEmbedding, dif_neg leftBefore,
        dif_pos rightBefore] using equality
    exact False.elim
      (exposedPreimage_ne_inner source outer inner distinct outerExposed
        innerExposed ⟨right.val, rightBefore⟩ reduced.symm)
  · apply Fin.ext
    have leftBound := left.isLt
    have rightBound := right.isLt
    omega

noncomputable def exposedQuotientEmbedding
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    Fin source.exposedWires.length →
      Fin ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length + 1) :=
  fun index =>
    if source.exposedWires.get index = inner then
      Fin.last _
    else
      (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct index).castSucc

theorem exposedQuotientEmbedding_injective
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    Function.Injective
      (exposedQuotientEmbedding source outer inner distinct) := by
  intro left right equality
  by_cases leftInner : source.exposedWires.get left = inner <;>
    by_cases rightInner : source.exposedWires.get right = inner
  · apply Fin.ext
    exact (List.getElem_inj source.exposedWires_nodup).mp (by
      simpa only [List.get_eq_getElem] using leftInner.trans rightInner.symm)
  · have impossible : (Fin.last
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length) =
      (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct
        right).castSucc := by
      simpa only [exposedQuotientEmbedding, if_pos leftInner,
        if_neg rightInner] using equality
    exact False.elim (by
      have := congrArg Fin.val impossible
      have bound := (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner
        distinct right).isLt
      simp only [Fin.val_last, Fin.val_castSucc] at this
      omega)
  · have impossible :
      (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct
        left).castSucc =
      Fin.last
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length := by
      simpa only [exposedQuotientEmbedding, if_neg leftInner,
        if_pos rightInner] using equality
    exact False.elim (by
      have := congrArg Fin.val impossible
      have bound := (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner
        distinct left).isLt
      simp only [Fin.val_last, Fin.val_castSucc] at this
      omega)
  · have mappedIndices :
        VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct left =
          VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct right := by
      have reduced :
          (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct
            left).castSucc =
          (VisualProof.Refinement.Implementation.WireJoin.exposedMap source outer inner distinct
            right).castSucc := by
        simpa only [exposedQuotientEmbedding, if_neg leftInner,
          if_neg rightInner] using equality
      apply Fin.ext
      exact congrArg (fun (index : Fin
        ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires.length + 1)) => index.val) reduced
    have targetGetEquality := congrArg
      (List.get
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source outer inner distinct).exposedWires) mappedIndices
    rw [VisualProof.Refinement.Implementation.WireJoin.exposedMap_get,
      VisualProof.Refinement.Implementation.WireJoin.exposedMap_get] at targetGetEquality
    have classified :=
      (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff source.diagram outer inner
        (source.exposedWires.get left) (source.exposedWires.get right)
        distinct).1 targetGetEquality
    have sourceGetEquality : source.exposedWires.get left =
        source.exposedWires.get right := by
      rcases classified with same | outerInner | innerOuter
      · exact same
      · exact False.elim (rightInner outerInner.2)
      · exact False.elim (leftInner innerOuter.1)
    apply Fin.ext
    exact (List.getElem_inj source.exposedWires_nodup).mp (by
      simpa only [List.get_eq_getElem] using sourceGetEquality)

noncomputable def hiddenMapExposed
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.val.exposedWires)
    (innerExposed : inner ∈ source.val.exposedWires) :
    Fin source.val.hiddenWires.length →
      Fin (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
        distinct).hiddenWires.length :=
  fun sourceIndex =>
    let sourceWire := source.val.hiddenWires.get sourceIndex
    let targetWire := VisualProof.Refinement.Implementation.WireJoin.wireMap source.val.diagram outer
      inner distinct sourceWire
    Classical.choose
      (Concrete.Elaboration.WireContext.lookup?_complete (by
        apply (Concrete.OpenDiagram.mem_hiddenWires
          (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct)
          targetWire).2
        have sourceHidden :=
          (Concrete.OpenDiagram.mem_hiddenWires source.val sourceWire).1
            (List.get_mem source.val.hiddenWires sourceIndex)
        have sourceNeInner : sourceWire ≠ inner := by
          intro equality
          exact sourceHidden.2 (equality ▸ innerExposed)
        have sourceNeOuter : sourceWire ≠ outer := by
          intro equality
          exact sourceHidden.2 (equality ▸ outerExposed)
        constructor
        · change ((VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner).wires
              targetWire).scope = source.val.diagram.root
          rw [VisualProof.Refinement.Implementation.WireJoin.target_wire_scope,
            if_neg sourceNeInner]
          exact sourceHidden.1
        · intro targetExposed
          obtain ⟨exposedWire, exposedMember, mapped⟩ :=
            (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw_exposed_mem_iff source.val
              outer inner distinct targetWire).1 targetExposed
          have collision :=
            (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff source.val.diagram outer
              inner exposedWire sourceWire distinct).1 mapped
          rcases collision with same | outerInner | innerOuter
          · exact sourceHidden.2 (same ▸ exposedMember)
          · exact sourceNeInner outerInner.2
          · exact sourceNeOuter innerOuter.2))

theorem hiddenMapExposed_get
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.val.exposedWires)
    (innerExposed : inner ∈ source.val.exposedWires)
    (sourceIndex : Fin source.val.hiddenWires.length) :
    (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).hiddenWires.get
          (hiddenMapExposed source outer inner distinct outerExposed
            innerExposed sourceIndex) =
      VisualProof.Refinement.Implementation.WireJoin.wireMap source.val.diagram outer inner distinct
        (source.val.hiddenWires.get sourceIndex) := by
  exact Concrete.Elaboration.WireContext.lookup?_sound
    (Classical.choose_spec
      (Concrete.Elaboration.WireContext.lookup?_complete (by
        apply (Concrete.OpenDiagram.mem_hiddenWires
          (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct)
          (VisualProof.Refinement.Implementation.WireJoin.wireMap source.val.diagram outer inner distinct
            (source.val.hiddenWires.get sourceIndex))).2
        have sourceHidden :=
          (Concrete.OpenDiagram.mem_hiddenWires source.val
            (source.val.hiddenWires.get sourceIndex)).1
            (List.get_mem source.val.hiddenWires sourceIndex)
        have sourceNeInner : source.val.hiddenWires.get sourceIndex ≠ inner := by
          intro equality
          exact sourceHidden.2 (equality ▸ innerExposed)
        have sourceNeOuter : source.val.hiddenWires.get sourceIndex ≠ outer := by
          intro equality
          exact sourceHidden.2 (equality ▸ outerExposed)
        constructor
        · change ((VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner).wires
              (VisualProof.Refinement.Implementation.WireJoin.wireMap source.val.diagram outer
                inner distinct (source.val.hiddenWires.get sourceIndex))).scope =
            source.val.diagram.root
          rw [VisualProof.Refinement.Implementation.WireJoin.target_wire_scope,
            if_neg sourceNeInner]
          exact sourceHidden.1
        · intro targetExposed
          obtain ⟨exposedWire, exposedMember, mapped⟩ :=
            (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw_exposed_mem_iff source.val
              outer inner distinct _).1 targetExposed
          have collision :=
            (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff source.val.diagram outer
              inner exposedWire (source.val.hiddenWires.get sourceIndex)
              distinct).1 mapped
          rcases collision with same | outerInner | innerOuter
          · exact sourceHidden.2 (same ▸ exposedMember)
          · exact sourceNeInner outerInner.2
          · exact sourceNeOuter innerOuter.2)))

theorem hiddenMapExposed_injective
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.val.exposedWires)
    (innerExposed : inner ∈ source.val.exposedWires) :
    Function.Injective
      (hiddenMapExposed source outer inner distinct outerExposed innerExposed) := by
  intro left right equality
  have targetGetEquality := congrArg
    (List.get (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
      distinct).hiddenWires) equality
  rw [hiddenMapExposed_get, hiddenMapExposed_get] at targetGetEquality
  have classified :=
    (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff source.val.diagram outer inner
      (source.val.hiddenWires.get left) (source.val.hiddenWires.get right)
      distinct).1 targetGetEquality
  have sourceGetEquality : source.val.hiddenWires.get left =
      source.val.hiddenWires.get right := by
    rcases classified with same | outerInner | innerOuter
    · exact same
    · have rightHidden := (Concrete.OpenDiagram.mem_hiddenWires source.val
          (source.val.hiddenWires.get right)).1
          (List.get_mem source.val.hiddenWires right)
      exact False.elim (rightHidden.2 (outerInner.2 ▸ innerExposed))
    · have leftHidden := (Concrete.OpenDiagram.mem_hiddenWires source.val
          (source.val.hiddenWires.get left)).1
          (List.get_mem source.val.hiddenWires left)
      exact False.elim (leftHidden.2 (innerOuter.1 ▸ innerExposed))
  apply Fin.ext
  exact (List.getElem_inj source.val.hiddenWires_nodup).mp (by
    simpa only [List.get_eq_getElem] using sourceGetEquality)

theorem hiddenMapExposed_surjective
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.val.exposedWires)
    (innerExposed : inner ∈ source.val.exposedWires) :
    Function.Surjective
      (hiddenMapExposed source outer inner distinct outerExposed innerExposed) := by
  intro targetIndex
  let targetWire :=
    (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).hiddenWires.get
      targetIndex
  let sourceWire :=
    (Concrete.joinWireDomain source.val.diagram inner).origin targetWire
  have sourceNe : sourceWire ≠ inner := by
    have survives :=
      (Concrete.joinWireDomain source.val.diagram inner).origin_survives
        targetWire
    simpa [sourceWire, Concrete.joinWireDomain] using survives
  have mapped : VisualProof.Refinement.Implementation.WireJoin.wireMap source.val.diagram outer inner
      distinct sourceWire = targetWire := by
    rw [VisualProof.Refinement.Implementation.WireJoin.wireMap_of_ne source.val.diagram outer inner
      sourceWire distinct sourceNe]
    exact (Concrete.joinWireDomain source.val.diagram inner).index_origin
      targetWire
  have targetHidden :=
    (Concrete.OpenDiagram.mem_hiddenWires
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct)
      targetWire).1 (List.get_mem _ targetIndex)
  have sourceRoot : (source.val.diagram.wires sourceWire).scope =
      source.val.diagram.root := by
    have targetScope := targetHidden.1
    change ((VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner).wires
      targetWire).scope = source.val.diagram.root at targetScope
    rw [← mapped, VisualProof.Refinement.Implementation.WireJoin.target_wire_scope,
      if_neg sourceNe] at targetScope
    exact targetScope
  have sourceNotExposed : sourceWire ∉ source.val.exposedWires := by
    intro sourceExposed
    exact targetHidden.2
      ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw_exposed_mem_iff source.val outer
        inner distinct targetWire).2 ⟨sourceWire, sourceExposed, mapped⟩)
  have sourceMember : sourceWire ∈ source.val.hiddenWires :=
    (Concrete.OpenDiagram.mem_hiddenWires source.val sourceWire).2
      ⟨sourceRoot, sourceNotExposed⟩
  obtain ⟨sourceIndex, lookup⟩ :=
    Concrete.Elaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).hiddenWires_nodup).mp (by
        have sourceGet :=
          Concrete.Elaboration.WireContext.lookup?_sound lookup
        have chosenGet := hiddenMapExposed_get source outer inner distinct
          outerExposed innerExposed sourceIndex
        have getEquality :
            (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
              distinct).hiddenWires.get
                (hiddenMapExposed source outer inner distinct outerExposed
                  innerExposed sourceIndex) =
              (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                distinct).hiddenWires.get targetIndex :=
          chosenGet.trans
            ((congrArg (VisualProof.Refinement.Implementation.WireJoin.wireMap source.val.diagram outer
              inner distinct) sourceGet).trans mapped)
        simpa only [List.get_eq_getElem] using getEquality)

noncomputable def hiddenEquivExposed
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (outerExposed : outer ∈ source.val.exposedWires)
    (innerExposed : inner ∈ source.val.exposedWires) :
    FiniteEquiv (Fin source.val.hiddenWires.length)
      (Fin (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
        distinct).hiddenWires.length) where
  toFun := hiddenMapExposed source outer inner distinct outerExposed innerExposed
  invFun := fun targetIndex => Classical.choose
    (hiddenMapExposed_surjective source outer inner distinct outerExposed
      innerExposed targetIndex)
  left_inv := by
    intro sourceIndex
    apply hiddenMapExposed_injective source outer inner distinct outerExposed
      innerExposed
    exact Classical.choose_spec
      (hiddenMapExposed_surjective source outer inner distinct outerExposed
        innerExposed
        (hiddenMapExposed source outer inner distinct outerExposed innerExposed
          sourceIndex))
  right_inv := by
    intro targetIndex
    exact Classical.choose_spec
      (hiddenMapExposed_surjective source outer inner distinct outerExposed
        innerExposed targetIndex)

theorem rootWitness_index_hidden_exposed
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner).WellFormed)
    (outerExposed : outer ∈ source.val.exposedWires)
    (innerExposed : inner ∈ source.val.exposedWires)
    (sourceIndex : Fin source.val.hiddenWires.length) :
    (VisualProof.Refinement.Implementation.WireJoin.rootWitness source outer inner distinct ordered
      targetWellFormed).indexMap
        (VisualProof.Refinement.Implementation.WireJoin.rightIndex source.val.exposedWires
          source.val.hiddenWires sourceIndex) =
      VisualProof.Refinement.Implementation.WireJoin.rightIndex
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).exposedWires
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).hiddenWires
        (hiddenMapExposed source outer inner distinct outerExposed innerExposed
          sourceIndex) := by
  let witness := VisualProof.Refinement.Implementation.WireJoin.rootWitness source outer inner distinct
    ordered targetWellFormed
  apply Fin.ext
  have mappedGet := witness.get
    (VisualProof.Refinement.Implementation.WireJoin.rightIndex source.val.exposedWires
      source.val.hiddenWires sourceIndex)
  rw [VisualProof.Refinement.Implementation.WireJoin.get_rightIndex] at mappedGet
  have targetGetEquality :
      ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).exposedWires ++
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).hiddenWires).get
          (witness.indexMap
            (VisualProof.Refinement.Implementation.WireJoin.rightIndex source.val.exposedWires
              source.val.hiddenWires sourceIndex)) =
        ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).exposedWires ++
          (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).hiddenWires).get
          (VisualProof.Refinement.Implementation.WireJoin.rightIndex
            (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
              distinct).exposedWires
            (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
              distinct).hiddenWires
            (hiddenMapExposed source outer inner distinct outerExposed
              innerExposed sourceIndex)) := by
    simpa only [VisualProof.Refinement.Implementation.WireJoin.get_rightIndex] using
      mappedGet.trans
        (hiddenMapExposed_get source outer inner distinct outerExposed
          innerExposed sourceIndex).symm
  have targetNodup :
      ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).exposedWires ++
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).hiddenWires).Nodup := by
    simpa only [Concrete.OpenDiagram.rootWires] using
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).rootWires_nodup
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using targetGetEquality)

theorem rootOpen
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner).WellFormed)
    (scopeRoot : (source.val.diagram.wires inner).scope =
      source.val.diagram.root)
    (outerExposed : outer ∈ source.val.exposedWires)
    (exposed : inner ∈ source.val.exposedWires) :
    let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
      ordered targetWellFormed
    let targetLength : target.val.boundary.length = source.val.boundary.length :=
      VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq source.val outer inner distinct
    Nonempty (Rule.WireSever.Open
      (target.elaborate.castArity targetLength) source.elaborate) := by
  dsimp only
  let target := VisualProof.Refinement.Implementation.WireJoin.targetOpen source outer inner distinct
    ordered targetWellFormed
  let targetLength : target.val.boundary.length = source.val.boundary.length :=
    VisualProof.Refinement.Implementation.WireJoin.boundaryLengthEq source.val outer inner distinct
  let targetDiagram := target.elaborate.castArity targetLength
  let sourceDiagram := source.elaborate
  change Nonempty (Rule.WireSever.Open targetDiagram sourceDiagram)
  have rawOneMore : source.val.exposedWires.length =
      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).exposedWires.length + 1 := by
    apply Nat.le_antisymm
    · exact fin_card_le_of_injective
        (exposedQuotientEmbedding source.val outer inner distinct)
        (exposedQuotientEmbedding_injective source.val outer inner distinct)
    · exact fin_card_le_of_injective
        (exposedPlusEmbedding source.val outer inner distinct outerExposed
          exposed)
        (exposedPlusEmbedding_injective source.val outer inner distinct
          outerExposed exposed)
  have oneMore : sourceDiagram.externalClasses =
      targetDiagram.externalClasses + 1 := by
    simpa [sourceDiagram, targetDiagram, target,
      VisualProof.Refinement.Implementation.WireJoin.targetOpen] using rawOneMore
  let collapse : Fin sourceDiagram.externalClasses →
      Fin targetDiagram.externalClasses :=
    fun sourceIndex =>
      Fin.cast (by simp [targetDiagram, target,
        VisualProof.Refinement.Implementation.WireJoin.targetOpen])
        (VisualProof.Refinement.Implementation.WireJoin.exposedMap source.val outer inner distinct
          (Fin.cast (by simp [sourceDiagram]) sourceIndex))
  have collapseSurjective : Function.Surjective collapse := by
    intro targetIndex
    let rawTargetIndex : Fin
        (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner distinct).exposedWires.length :=
      Fin.cast (by simp [targetDiagram, target,
        VisualProof.Refinement.Implementation.WireJoin.targetOpen]) targetIndex
    obtain ⟨sourceIndex, mapped⟩ :=
      VisualProof.Refinement.Implementation.WireJoin.exposedMap_surjective source.val outer inner
        distinct rawTargetIndex
    refine ⟨Fin.cast (by simp [sourceDiagram]) sourceIndex, ?_⟩
    apply Fin.ext
    simpa [collapse, rawTargetIndex] using congrArg Fin.val mapped
  have boundary : ∀ position,
      collapse (sourceDiagram.boundary position) =
        targetDiagram.boundary position := by
    intro position
    let targetPosition := Fin.cast targetLength.symm position
    have mapped := VisualProof.Refinement.Implementation.WireJoin.boundaryClass_map source.val outer
      inner distinct targetPosition
    apply Fin.ext
    change (collapse (sourceDiagram.boundary position)).val =
      ((target.elaborate.castArity targetLength).boundary position).val
    rw [castBoundaryVal target.elaborate targetLength position]
    simpa [collapse, sourceDiagram, targetPosition, target,
      VisualProof.Refinement.Implementation.WireJoin.targetOpen] using congrArg Fin.val mapped.symm
  refine ⟨{
    one_more := oneMore
    collapse := collapse
    collapse_surjective := collapseSurjective
    boundary := boundary
    body := ?_
  }⟩
  obtain ⟨sourceBody, sourceRootCompiled, sourceBodyEq⟩ :=
    source.elaborate_body_computation
  obtain ⟨targetBody, targetRootCompiled, targetBodyEq⟩ :=
    target.elaborate_body_computation
  let sourceRoot := source.val.exposedWires ++ source.val.hiddenWires
  let targetRoot := target.val.exposedWires ++ target.val.hiddenWires
  let occurrences := Concrete.Elaboration.localOccurrences source.val.diagram
    source.val.diagram.root
  cases sourceItemsEq : Concrete.Elaboration.compileOccurrencesWith?
      source.val.diagram
      (Concrete.Elaboration.compileRegion? source.val.diagram
        source.val.diagram.regionCount)
      sourceRoot Concrete.Elaboration.BinderContext.empty occurrences with
  | none =>
      unfold Concrete.Elaboration.compileRoot? at sourceRootCompiled
      change (Concrete.Elaboration.compileOccurrencesWith? source.val.diagram
        (Concrete.Elaboration.compileRegion? source.val.diagram
          source.val.diagram.regionCount)
        sourceRoot Concrete.Elaboration.BinderContext.empty occurrences).bind _ =
          some sourceBody at sourceRootCompiled
      rw [sourceItemsEq] at sourceRootCompiled
      contradiction
  | some sourceItems =>
      have sourceBodyShape : sourceBody = Concrete.Elaboration.finishRoot
          source.val.exposedWires source.val.hiddenWires sourceItems := by
        unfold Concrete.Elaboration.compileRoot? at sourceRootCompiled
        change (Concrete.Elaboration.compileOccurrencesWith? source.val.diagram
          (Concrete.Elaboration.compileRegion? source.val.diagram
            source.val.diagram.regionCount)
          sourceRoot Concrete.Elaboration.BinderContext.empty occurrences).bind _ =
            some sourceBody at sourceRootCompiled
        rw [sourceItemsEq] at sourceRootCompiled
        exact Option.some.inj sourceRootCompiled |>.symm
      cases targetItemsEq : Concrete.Elaboration.compileOccurrencesWith?
          target.val.diagram
          (Concrete.Elaboration.compileRegion? target.val.diagram
            target.val.diagram.regionCount)
          targetRoot Concrete.Elaboration.BinderContext.empty occurrences with
      | none =>
          unfold Concrete.Elaboration.compileRoot? at targetRootCompiled
          change (Concrete.Elaboration.compileOccurrencesWith? target.val.diagram
            (Concrete.Elaboration.compileRegion? target.val.diagram
              target.val.diagram.regionCount)
            targetRoot Concrete.Elaboration.BinderContext.empty occurrences).bind _ =
              some targetBody at targetRootCompiled
          rw [targetItemsEq] at targetRootCompiled
          contradiction
      | some targetItems =>
          have targetBodyShape : targetBody = Concrete.Elaboration.finishRoot
              target.val.exposedWires target.val.hiddenWires targetItems := by
            unfold Concrete.Elaboration.compileRoot? at targetRootCompiled
            change (Concrete.Elaboration.compileOccurrencesWith?
              target.val.diagram
              (Concrete.Elaboration.compileRegion? target.val.diagram
                target.val.diagram.regionCount)
              targetRoot Concrete.Elaboration.BinderContext.empty occurrences).bind _ =
                some targetBody at targetRootCompiled
            rw [targetItemsEq] at targetRootCompiled
            exact Option.some.inj targetRootCompiled |>.symm
          let witness := VisualProof.Refinement.Implementation.WireJoin.rootWitness source outer inner
            distinct ordered targetWellFormed
          have rawIso : ItemSeqIso (FiniteEquiv.refl (Fin targetRoot.length)) []
              (sourceItems.renameWires witness.indexMap) targetItems := by
            have targetItemsEq' :
                Concrete.Elaboration.compileOccurrencesWith?
                  (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner)
                  (Concrete.Elaboration.compileRegion?
                    (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner)
                    source.val.diagram.regionCount)
                  ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                    distinct).exposedWires ++
                    (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                      distinct).hiddenWires)
                  Concrete.Elaboration.BinderContext.empty occurrences =
                    some targetItems := by
              simpa [target, targetRoot, VisualProof.Refinement.Implementation.WireJoin.targetOpen,
                VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw] using targetItemsEq
            have sourceExact : Concrete.Elaboration.WireContext.Exact
                sourceRoot source.val.diagram.root := by
              simpa [sourceRoot, Concrete.OpenDiagram.rootWires] using
                Concrete.Elaboration.openRootWires_exact source.property
            have targetExact : Concrete.Elaboration.WireContext.Exact
                ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                    distinct).exposedWires ++
                  (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                    distinct).hiddenWires) source.val.diagram.root := by
              simpa [Concrete.OpenDiagram.rootWires] using
                Concrete.Elaboration.openRootWires_exact target.property
            apply compiledItemSeqIso_after_rename source.val.diagram outer inner
              (Concrete.Elaboration.compileRegion? source.val.diagram
                source.val.diagram.regionCount)
              (Concrete.Elaboration.compileRegion?
                (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner)
                source.val.diagram.regionCount)
              sourceRoot
              ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                distinct).exposedWires ++
                (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                  distinct).hiddenWires)
              Concrete.Elaboration.BinderContext.empty
              Concrete.Elaboration.BinderContext.empty occurrences
              sourceItemsEq targetItemsEq' witness.indexMap
            intro occurrenceIndex
            have sourceGet :=
              Concrete.Elaboration.compileOccurrencesWith?_get
                (Concrete.Elaboration.compileRegion? source.val.diagram
                  source.val.diagram.regionCount)
                sourceRoot Concrete.Elaboration.BinderContext.empty
                sourceItemsEq occurrenceIndex
            have targetGet :=
              Concrete.Elaboration.compileOccurrencesWith?_get
                (Concrete.Elaboration.compileRegion?
                  (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner)
                  source.val.diagram.regionCount)
                ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                  distinct).exposedWires ++
                  (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                    distinct).hiddenWires)
                Concrete.Elaboration.BinderContext.empty targetItemsEq'
                occurrenceIndex
            let occurrence := occurrences.get occurrenceIndex
            have occurrenceMem : occurrence ∈ occurrences := List.get_mem _ _
            change Concrete.Elaboration.compileOccurrenceWith?
                source.val.diagram
                (Concrete.Elaboration.compileRegion? source.val.diagram
                  source.val.diagram.regionCount)
                sourceRoot Concrete.Elaboration.BinderContext.empty occurrence =
                  _ at sourceGet
            change Concrete.Elaboration.compileOccurrenceWith?
                (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner)
                (Concrete.Elaboration.compileRegion?
                  (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer inner)
                  source.val.diagram.regionCount)
                ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                  distinct).exposedWires ++
                  (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                    distinct).hiddenWires)
                Concrete.Elaboration.BinderContext.empty occurrence = _
                  at targetGet
            cases occurrenceShape : occurrence with
            | node node =>
                rw [occurrenceShape] at sourceGet targetGet
                simp only [Concrete.Elaboration.compileOccurrenceWith?]
                  at sourceGet targetGet
                have below : source.val.diagram.Encloses
                    (source.val.diagram.wires inner).scope
                    source.val.diagram.root := by
                  rw [scopeRoot]
                  exact ⟨⟨0, by have := source.val.diagram.root.isLt; omega⟩,
                    rfl⟩
                have mappedNode := compileNode_map source.val.diagram
                  source.property.diagram_well_formed outer inner distinct
                  ordered targetWellFormed source.val.diagram.root below
                  sourceRoot
                  ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                    distinct).exposedWires ++
                    (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                      distinct).hiddenWires)
                  witness sourceExact targetExact
                  Concrete.Elaboration.BinderContext.empty node
                rw [sourceGet] at mappedNode
                have itemEq :
                    targetItems.get (Fin.cast
                      (Concrete.Elaboration.compileOccurrencesWith?_length
                        (Concrete.Elaboration.compileRegion?
                          (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer
                            inner) source.val.diagram.regionCount)
                        ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer
                          inner distinct).exposedWires ++
                          (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer
                            inner distinct).hiddenWires)
                        Concrete.Elaboration.BinderContext.empty
                        targetItemsEq').symm occurrenceIndex) =
                      (sourceItems.get (Fin.cast
                        (Concrete.Elaboration.compileOccurrencesWith?_length
                          (Concrete.Elaboration.compileRegion?
                            source.val.diagram source.val.diagram.regionCount)
                          sourceRoot Concrete.Elaboration.BinderContext.empty
                          sourceItemsEq).symm occurrenceIndex)).renameWires
                        witness.indexMap := by
                  apply Option.some.inj
                  exact targetGet.symm.trans mappedNode
                exact itemEq ▸ ItemIso.refl _
            | child child =>
                rw [occurrenceShape] at sourceGet targetGet
                have childParent : (source.val.diagram.regions child).parent? =
                    some source.val.diagram.root :=
                  (Concrete.Elaboration.mem_localOccurrences_child
                    source.val.diagram source.val.diagram.root child).1 (by
                      rw [← occurrenceShape]
                      exact occurrenceMem)
                have targetChildParent :
                    ((VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram outer
                      inner).regions child).parent? =
                        some source.val.diagram.root := by
                  simpa using childParent
                have rootChild : source.val.diagram.Encloses
                    source.val.diagram.root child := by
                  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
                  simp [Concrete.Diagram.climb, childParent]
                have childBelow : source.val.diagram.Encloses
                    (source.val.diagram.wires inner).scope child := by
                  simpa only [scopeRoot] using rootChild
                have childNotSite : child ≠
                    (source.val.diagram.wires inner).scope := by
                  intro equality
                  have childRoot : child = source.val.diagram.root :=
                    equality.trans scopeRoot
                  rw [childRoot,
                    source.property.diagram_well_formed.root_is_sheet]
                      at childParent
                  simp [Concrete.CRegion.parent?] at childParent
                have sourceChildExact := sourceExact.extend_child
                  source.property.diagram_well_formed childParent
                have targetChildExact := targetExact.extend_child
                  targetWellFormed targetChildParent
                cases childKind : source.val.diagram.regions child with
                | sheet =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?,
                      childKind] at sourceGet
                | cut parent =>
                    simp only [Concrete.Elaboration.compileOccurrenceWith?,
                      childKind, VisualProof.Refinement.Implementation.WireJoin.target_regions]
                        at sourceGet targetGet
                    cases sourceChildEq : Concrete.Elaboration.compileRegion?
                        source.val.diagram source.val.diagram.regionCount child
                        sourceRoot Concrete.Elaboration.BinderContext.empty with
                    | none => simp [sourceChildEq] at sourceGet
                    | some sourceChild =>
                        cases targetChildEq :
                            Concrete.Elaboration.compileRegion?
                              (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram
                                outer inner) source.val.diagram.regionCount child
                              ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                outer inner distinct).exposedWires ++
                                (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                  outer inner distinct).hiddenWires)
                              Concrete.Elaboration.BinderContext.empty with
                        | none => simp [targetChildEq] at targetGet
                        | some targetChild =>
                            rw [sourceChildEq] at sourceGet
                            rw [targetChildEq] at targetGet
                            rw [← Option.some.inj sourceGet,
                              ← Option.some.inj targetGet]
                            exact ItemIso.cut
                              (compileRegion_quotient source.val.diagram
                                source.property.diagram_well_formed outer inner
                                distinct ordered targetWellFormed
                                source.val.diagram.regionCount child childBelow
                                childNotSite sourceRoot
                                ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                  outer inner distinct).exposedWires ++
                                  (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                    outer inner distinct).hiddenWires)
                                witness sourceChildExact targetChildExact
                                Concrete.Elaboration.BinderContext.empty
                                sourceChildEq targetChildEq)
                | bubble parent arity =>
                    simp only [Concrete.Elaboration.compileOccurrenceWith?,
                      childKind, VisualProof.Refinement.Implementation.WireJoin.target_regions]
                        at sourceGet targetGet
                    let childBinders :=
                      Concrete.Elaboration.BinderContext.empty.push child arity
                    cases sourceChildEq : Concrete.Elaboration.compileRegion?
                        source.val.diagram source.val.diagram.regionCount child
                        sourceRoot childBinders with
                    | none =>
                        change (Concrete.Elaboration.compileRegion?
                          source.val.diagram source.val.diagram.regionCount child
                          sourceRoot childBinders).bind _ = _ at sourceGet
                        rw [sourceChildEq] at sourceGet
                        contradiction
                    | some sourceChild =>
                        cases targetChildEq :
                            Concrete.Elaboration.compileRegion?
                              (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram
                                outer inner) source.val.diagram.regionCount child
                              ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                outer inner distinct).exposedWires ++
                                (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                  outer inner distinct).hiddenWires)
                              childBinders with
                        | none =>
                            change (Concrete.Elaboration.compileRegion?
                              (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram
                                outer inner) source.val.diagram.regionCount child
                              ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                outer inner distinct).exposedWires ++
                                (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                  outer inner distinct).hiddenWires)
                              childBinders).bind _ = _ at targetGet
                            rw [targetChildEq] at targetGet
                            contradiction
                        | some targetChild =>
                            change (Concrete.Elaboration.compileRegion?
                              source.val.diagram source.val.diagram.regionCount
                              child sourceRoot childBinders).bind _ = _ at sourceGet
                            change (Concrete.Elaboration.compileRegion?
                              (VisualProof.Refinement.Implementation.WireJoin.Target source.val.diagram
                                outer inner) source.val.diagram.regionCount child
                              ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                outer inner distinct).exposedWires ++
                                (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                  outer inner distinct).hiddenWires)
                              childBinders).bind _ = _ at targetGet
                            rw [sourceChildEq] at sourceGet
                            rw [targetChildEq] at targetGet
                            rw [← Option.some.inj sourceGet,
                              ← Option.some.inj targetGet]
                            exact ItemIso.bubble
                              (compileRegion_quotient source.val.diagram
                                source.property.diagram_well_formed outer inner
                                distinct ordered targetWellFormed
                                source.val.diagram.regionCount child childBelow
                                childNotSite sourceRoot
                                ((VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                  outer inner distinct).exposedWires ++
                                  (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val
                                    outer inner distinct).hiddenWires)
                                witness sourceChildExact targetChildExact
                                childBinders sourceChildEq targetChildEq)
          let sourceRootEq : sourceRoot.length =
              source.val.exposedWires.length + source.val.hiddenWires.length := by
            simp [sourceRoot]
          let targetRootEq : targetRoot.length =
              target.val.exposedWires.length + target.val.hiddenWires.length := by
            simp [targetRoot]
          let sourceCast := FiniteEquiv.finCast sourceRootEq
          let targetCast := FiniteEquiv.finCast targetRootEq
          let hiddenEquiv := hiddenEquivExposed source outer inner distinct
            outerExposed exposed
          let finalWire := extendWireEquiv
            (FiniteEquiv.refl (Fin target.val.exposedWires.length))
            hiddenEquiv.symm
          let rawCollapse := VisualProof.Refinement.Implementation.WireJoin.exposedMap source.val outer
            inner distinct
          let desiredMap := extendWireRenaming rawCollapse
            source.val.hiddenWires.length
          have mapFactor (index : Fin sourceRoot.length) :
              finalWire (targetCast (witness.indexMap index)) =
                desiredMap (sourceCast index) := by
            let split := sourceCast index
            have recover : Fin.cast sourceRootEq.symm split = index := by
              apply Fin.ext
              rfl
            rw [← recover]
            refine Fin.addCases (fun exposedIndex => ?_)
              (fun hiddenIndex => ?_) split
            · have mapped := VisualProof.Refinement.Implementation.WireJoin.rootWitness_index_exposed
                source outer inner distinct ordered targetWellFormed exposedIndex
              have sourceIndexEq :
                  Fin.cast sourceRootEq.symm
                      (Fin.castAdd source.val.hiddenWires.length exposedIndex) =
                    VisualProof.Refinement.Implementation.WireJoin.leftIndex
                      source.val.exposedWires source.val.hiddenWires
                      exposedIndex := by
                apply Fin.ext
                rfl
              rw [sourceIndexEq]
              change finalWire (targetCast
                  ((VisualProof.Refinement.Implementation.WireJoin.rootWitness source outer inner
                    distinct ordered targetWellFormed).indexMap
                    (VisualProof.Refinement.Implementation.WireJoin.leftIndex source.val.exposedWires
                      source.val.hiddenWires exposedIndex))) = _
              rw [mapped]
              have targetIndexEq : targetCast
                    (VisualProof.Refinement.Implementation.WireJoin.leftIndex
                      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer
                        inner distinct).exposedWires
                      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer
                        inner distinct).hiddenWires
                      (VisualProof.Refinement.Implementation.WireJoin.exposedMap source.val outer inner
                        distinct exposedIndex)) =
                  Fin.castAdd target.val.hiddenWires.length
                    (VisualProof.Refinement.Implementation.WireJoin.exposedMap source.val outer inner
                      distinct exposedIndex) := by
                apply Fin.ext
                rfl
              rw [targetIndexEq]
              apply Fin.ext
              simp [sourceCast, finalWire, rawCollapse, desiredMap, target,
                VisualProof.Refinement.Implementation.WireJoin.targetOpen,
                extendWireEquiv, extendWireRenaming,
                VisualProof.Refinement.Implementation.WireJoin.leftIndex, FiniteEquiv.finCast]
            · have mapped := rootWitness_index_hidden_exposed source outer
                inner distinct ordered targetWellFormed outerExposed exposed
                hiddenIndex
              have sourceIndexEq :
                  Fin.cast sourceRootEq.symm
                      (Fin.natAdd source.val.exposedWires.length hiddenIndex) =
                    VisualProof.Refinement.Implementation.WireJoin.rightIndex
                      source.val.exposedWires source.val.hiddenWires
                      hiddenIndex := by
                apply Fin.ext
                rfl
              rw [sourceIndexEq]
              change finalWire (targetCast
                  ((VisualProof.Refinement.Implementation.WireJoin.rootWitness source outer inner
                    distinct ordered targetWellFormed).indexMap
                    (VisualProof.Refinement.Implementation.WireJoin.rightIndex source.val.exposedWires
                      source.val.hiddenWires hiddenIndex))) = _
              rw [mapped]
              have targetIndexEq : targetCast
                    (VisualProof.Refinement.Implementation.WireJoin.rightIndex
                      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer
                        inner distinct).exposedWires
                      (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer
                        inner distinct).hiddenWires
                      (hiddenMapExposed source outer inner distinct outerExposed
                        exposed hiddenIndex)) =
                  Fin.natAdd target.val.exposedWires.length
                    (hiddenMapExposed source outer inner distinct outerExposed
                      exposed hiddenIndex) := by
                apply Fin.ext
                rfl
              rw [targetIndexEq]
              apply Fin.ext
              simp [sourceCast, finalWire, hiddenEquiv, rawCollapse,
                desiredMap, target, VisualProof.Refinement.Implementation.WireJoin.targetOpen,
                extendWireEquiv,
                extendWireRenaming, VisualProof.Refinement.Implementation.WireJoin.rightIndex,
                FiniteEquiv.finCast]
              exact congrArg (fun index => index.val)
                (hiddenEquiv.left_inv hiddenIndex)
          let rawTargetMap : Fin targetRoot.length →
              Fin (target.val.exposedWires.length +
                source.val.hiddenWires.length) :=
            finalWire ∘ targetCast
          have itemsIso : ItemSeqIso finalWire []
              (targetItems.renameWires targetCast)
              (sourceItems.renameWires
                (desiredMap ∘ sourceCast)) := by
            have transported := ItemSeqIso.renameWires_commuting rawIso.symm
              targetCast rawTargetMap finalWire (by
                funext index
                rfl)
            have targetMapEq : rawTargetMap ∘ witness.indexMap =
                desiredMap ∘ sourceCast := by
              funext index
              exact mapFactor index
            rw [ItemSeq.renameWires_comp, targetMapEq] at transported
            exact transported
          have rawBodyIso : Core.Isomorphic targetBody
              (sourceBody.renameWires rawCollapse) := by
            rw [sourceBodyShape, targetBodyShape]
            unfold Concrete.Elaboration.finishRoot Region.renameWires
            apply RegionIso.mk hiddenEquiv.symm
            simpa [sourceCast, targetCast, desiredMap,
              ItemSeq.castWiresEq_eq_renameWires,
              ItemSeq.renameWires_comp] using itemsIso
          have targetBodyCast : targetDiagram.body =
              target.elaborate.body.renameWires
                (Fin.cast (OpenDiagram.castArity_externalClasses
                  target.elaborate targetLength).symm) :=
            castBody target.elaborate targetLength
              (OpenDiagram.castArity_externalClasses
                target.elaborate targetLength)
          rw [targetBodyCast, targetBodyEq, sourceBodyEq]
          let targetMap : Fin
              (VisualProof.Refinement.Implementation.WireJoin.targetOpenRaw source.val outer inner
                distinct).exposedWires.length →
              Fin targetDiagram.externalClasses :=
            Fin.cast (by
              simp [targetDiagram, target,
                VisualProof.Refinement.Implementation.WireJoin.targetOpen])
          have transportedTarget := rawBodyIso.renameWires_commuting
            (Fin.cast (OpenDiagram.castArity_externalClasses
              target.elaborate targetLength).symm)
            targetMap
            (FiniteEquiv.refl (Fin targetDiagram.externalClasses)) (by
              funext index
              rfl)
          simp only [Region.renameWires_comp] at transportedTarget
          have targetMapFactor : targetMap ∘ rawCollapse = collapse := by
            funext index
            apply Fin.ext
            rfl
          rw [← targetMapFactor]
          exact transportedTarget

end VisualProof.Refinement.Implementation.WireJoin
