import VisualProof.Refinement.Implementation.WireJoinCompile
import VisualProof.Rule.WireSever

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof
open VisualProof.Rule
open VisualProof.Theory
open VisualProof.Diagram

noncomputable def siteTargetIndex
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (sourceIndex : Fin (Concrete.Elaboration.exactScopeWires input
      (input.wires inner).scope).length)
    (notInner : (Concrete.Elaboration.exactScopeWires input
      (input.wires inner).scope).get sourceIndex ≠ inner) :
    Fin (Concrete.Elaboration.exactScopeWires
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (input.wires inner).scope).length :=
  Classical.choose (Concrete.Elaboration.WireContext.lookup?_complete (by
    apply (Concrete.Elaboration.mem_exactScopeWires
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (input.wires inner).scope _).2
    rw [VisualProof.Refinement.Implementation.WireJoin.target_wire_scope input outer inner _ distinct,
      if_neg notInner]
    exact (Concrete.Elaboration.mem_exactScopeWires input
      (input.wires inner).scope _).1 (List.get_mem _ sourceIndex)))

theorem siteTargetIndex_get
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (sourceIndex : Fin (Concrete.Elaboration.exactScopeWires input
      (input.wires inner).scope).length)
    (notInner : (Concrete.Elaboration.exactScopeWires input
      (input.wires inner).scope).get sourceIndex ≠ inner) :
    (Concrete.Elaboration.exactScopeWires
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
      (input.wires inner).scope).get
        (siteTargetIndex input outer inner distinct sourceIndex notInner) =
      VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct
        ((Concrete.Elaboration.exactScopeWires input
          (input.wires inner).scope).get sourceIndex) :=
  Concrete.Elaboration.WireContext.lookup?_sound
    (Classical.choose_spec (Concrete.Elaboration.WireContext.lookup?_complete
      (by
        apply (Concrete.Elaboration.mem_exactScopeWires
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
          (input.wires inner).scope _).2
        rw [VisualProof.Refinement.Implementation.WireJoin.target_wire_scope input outer inner _ distinct,
          if_neg notInner]
        exact (Concrete.Elaboration.mem_exactScopeWires input
          (input.wires inner).scope _).1 (List.get_mem _ sourceIndex))))

noncomputable def siteLocalMap
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Fin (Concrete.Elaboration.exactScopeWires input
      (input.wires inner).scope).length →
      Fin ((Concrete.Elaboration.exactScopeWires
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
        (input.wires inner).scope).length + 1) :=
  fun sourceIndex =>
    if isInner : (Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope).get sourceIndex = inner then
      Fin.last _
    else
      Fin.castSucc (siteTargetIndex input outer inner distinct sourceIndex
        isInner)

theorem siteLocalMap_injective
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Function.Injective (siteLocalMap input outer inner distinct) := by
  intro left right equality
  by_cases leftInner : (Concrete.Elaboration.exactScopeWires input
      (input.wires inner).scope).get left = inner
  · by_cases rightInner : (Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope).get right = inner
    · apply Fin.ext
      exact (List.getElem_inj
        (Concrete.Elaboration.exactScopeWires_nodup input
          (input.wires inner).scope)).mp (by
            simpa only [List.get_eq_getElem] using leftInner.trans rightInner.symm)
    · have impossible := congrArg Fin.val equality
      simp only [siteLocalMap, dif_pos leftInner, dif_neg rightInner,
        Fin.val_last, Fin.val_castSucc] at impossible
      omega
  · by_cases rightInner : (Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope).get right = inner
    · have impossible := congrArg Fin.val equality
      simp only [siteLocalMap, dif_neg leftInner, dif_pos rightInner,
        Fin.val_last, Fin.val_castSucc] at impossible
      omega
    · have targetIndexEq :
          siteTargetIndex input outer inner distinct left leftInner =
            siteTargetIndex input outer inner distinct right rightInner := by
        apply Fin.ext
        have values := congrArg Fin.val equality
        simpa only [siteLocalMap, dif_neg leftInner, dif_neg rightInner,
          Fin.val_castSucc] using values
      have targetGetEq := congrArg
        (Concrete.Elaboration.exactScopeWires
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
          (input.wires inner).scope).get targetIndexEq
      rw [siteTargetIndex_get, siteTargetIndex_get] at targetGetEq
      have classified := (VisualProof.Refinement.Implementation.WireJoin.wireMap_eq_iff input outer inner
        ((Concrete.Elaboration.exactScopeWires input
          (input.wires inner).scope).get left)
        ((Concrete.Elaboration.exactScopeWires input
          (input.wires inner).scope).get right) distinct).1 targetGetEq
      have sourceGetEq :
          (Concrete.Elaboration.exactScopeWires input
              (input.wires inner).scope).get left =
            (Concrete.Elaboration.exactScopeWires input
              (input.wires inner).scope).get right := by
        rcases classified with same | outerInner | innerOuter
        · exact same
        · exact False.elim (rightInner outerInner.2)
        · exact False.elim (leftInner innerOuter.1)
      apply Fin.ext
      exact (List.getElem_inj
        (Concrete.Elaboration.exactScopeWires_nodup input
          (input.wires inner).scope)).mp (by
            simpa only [List.get_eq_getElem] using sourceGetEq)

theorem siteLocalMap_surjective
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    Function.Surjective (siteLocalMap input outer inner distinct) := by
  intro target
  refine Fin.lastCases (motive := fun target =>
      ∃ source, siteLocalMap input outer inner distinct source = target)
    ?_ (fun targetIndex => ?_) target
  · have innerMember : inner ∈ Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope :=
      (Concrete.Elaboration.mem_exactScopeWires input
        (input.wires inner).scope inner).2 rfl
    obtain ⟨sourceIndex, sourceLookup⟩ :=
      Concrete.Elaboration.WireContext.lookup?_complete innerMember
    have sourceGet :=
      Concrete.Elaboration.WireContext.lookup?_sound sourceLookup
    have sourceGetList : (Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope).get sourceIndex = inner := by
      simpa only [List.get_eq_getElem] using sourceGet
    refine ⟨sourceIndex, ?_⟩
    unfold siteLocalMap
    rw [dif_pos sourceGetList]
  · let targetWires := Concrete.Elaboration.exactScopeWires
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) (input.wires inner).scope
    let targetWire := targetWires.get targetIndex
    let sourceWire := (Concrete.joinWireDomain input inner).origin targetWire
    have sourceNe : sourceWire ≠ inner := by
      have survives := (Concrete.joinWireDomain input inner).origin_survives
        targetWire
      simpa [sourceWire, Concrete.joinWireDomain] using survives
    have mapped : VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct
        sourceWire = targetWire := by
      rw [VisualProof.Refinement.Implementation.WireJoin.wireMap_of_ne input outer inner sourceWire
        distinct sourceNe]
      exact (Concrete.joinWireDomain input inner).index_origin targetWire
    have targetScope :
        ((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).wires targetWire).scope =
          (input.wires inner).scope :=
      (Concrete.Elaboration.mem_exactScopeWires
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
        (input.wires inner).scope targetWire).1 (List.get_mem _ targetIndex)
    have sourceScope : (input.wires sourceWire).scope =
        (input.wires inner).scope := by
      rw [VisualProof.Refinement.Implementation.WireJoin.target_wire_scope_origin] at targetScope
      change (if sourceWire = outer then (input.wires outer).scope
        else (input.wires sourceWire).scope) =
          (input.wires inner).scope at targetScope
      by_cases isOuter : sourceWire = outer
      · simpa [isOuter] using targetScope
      · simpa [isOuter] using targetScope
    have sourceMember : sourceWire ∈ Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope :=
      (Concrete.Elaboration.mem_exactScopeWires input
        (input.wires inner).scope sourceWire).2 sourceScope
    obtain ⟨sourceIndex, sourceLookup⟩ :=
      Concrete.Elaboration.WireContext.lookup?_complete sourceMember
    have sourceGet :=
      Concrete.Elaboration.WireContext.lookup?_sound sourceLookup
    have sourceGetList : (Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope).get sourceIndex = sourceWire := by
      simpa only [List.get_eq_getElem] using sourceGet
    have sourceIndexNe :
        (Concrete.Elaboration.exactScopeWires input
          (input.wires inner).scope).get sourceIndex ≠ inner := by
      rw [sourceGetList]
      exact sourceNe
    have targetGet := siteTargetIndex_get input outer inner distinct
      sourceIndex sourceIndexNe
    rw [sourceGetList, mapped] at targetGet
    have targetIndexEq :
        siteTargetIndex input outer inner distinct sourceIndex sourceIndexNe =
          targetIndex := by
      apply Fin.ext
      exact (List.getElem_inj
        (Concrete.Elaboration.exactScopeWires_nodup
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
          (input.wires inner).scope)).mp (by
            simpa only [List.get_eq_getElem, targetWire, targetWires] using
              targetGet)
    refine ⟨sourceIndex, ?_⟩
    simp only [siteLocalMap, dif_neg sourceIndexNe]
    exact congrArg Fin.castSucc targetIndexEq

noncomputable def siteLocalEquiv
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    FiniteEquiv
      (Fin (Concrete.Elaboration.exactScopeWires input
        (input.wires inner).scope).length)
      (Fin ((Concrete.Elaboration.exactScopeWires
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
        (input.wires inner).scope).length + 1)) where
  toFun := siteLocalMap input outer inner distinct
  invFun := fun target => Classical.choose
    (siteLocalMap_surjective input outer inner distinct target)
  left_inv := by
    intro source
    apply siteLocalMap_injective input outer inner distinct
    exact Classical.choose_spec
      (siteLocalMap_surjective input outer inner distinct
        (siteLocalMap input outer inner distinct source))
  right_inv := by
    intro target
    exact Classical.choose_spec
      (siteLocalMap_surjective input outer inner distinct target)

theorem siteLocal
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner))
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (input.wires inner).scope).Exact
        (input.wires inner).scope)
    (targetExact :
      (targetContext.extend (input.wires inner).scope).Exact
        (input.wires inner).scope)
    (innerAbsent : inner ∉ sourceContext)
    (fuel : Nat)
    (binders : Concrete.Elaboration.BinderContext input rels)
    {sourceBody : Region sourceContext.length rels}
    {targetBody : Region targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input fuel
      (input.wires inner).scope sourceContext binders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel
      (input.wires inner).scope targetContext binders = some targetBody) :
    let sourceNodup : sourceContext.Nodup := by
      have extended := sourceExact.nodup
      rw [Concrete.Elaboration.WireContext.extend, List.nodup_append] at extended
      exact extended.1
    let inherited := contextEquiv witness sourceNodup innerAbsent
    ∃ before after : Region targetContext.length rels,
      VisualProof.Rule.WireSever.Local before after ∧
      Core.Isomorphic targetBody before ∧
      RegionIso inherited rels sourceBody after := by
  dsimp only
  cases fuel with
  | zero => simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ fuel =>
      let site := (input.wires inner).scope
      let sourceExtended := sourceContext.extend site
      let targetExtended := targetContext.extend site
      let extendedWitness := witness.extend inputWellFormed ordered site
        sourceExact targetExact
      let sourceOccurrences := Concrete.Elaboration.localOccurrences input site
      let targetOccurrences := Concrete.Elaboration.localOccurrences
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) site
      cases sourceItemsEq : Concrete.Elaboration.compileOccurrencesWith? input
          (Concrete.Elaboration.compileRegion? input fuel) sourceExtended
          binders sourceOccurrences with
      | none =>
          simp only [Concrete.Elaboration.compileRegion?] at sourceCompiled
          change (Concrete.Elaboration.compileOccurrencesWith? input
            (Concrete.Elaboration.compileRegion? input fuel) sourceExtended
            binders sourceOccurrences).bind _ = some sourceBody at sourceCompiled
          rw [sourceItemsEq] at sourceCompiled
          contradiction
      | some sourceItems =>
          cases targetItemsEq : Concrete.Elaboration.compileOccurrencesWith?
              (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
              (Concrete.Elaboration.compileRegion?
                (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
              targetExtended binders targetOccurrences with
          | none =>
              simp only [Concrete.Elaboration.compileRegion?] at targetCompiled
              change (Concrete.Elaboration.compileOccurrencesWith?
                (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                (Concrete.Elaboration.compileRegion?
                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                targetExtended binders targetOccurrences).bind _ =
                  some targetBody at targetCompiled
              rw [targetItemsEq] at targetCompiled
              contradiction
          | some targetItems =>
              have sourceBodyEq : sourceBody =
                  Concrete.Elaboration.finishRegion input sourceContext site
                    sourceItems := by
                simp only [Concrete.Elaboration.compileRegion?] at sourceCompiled
                change (Concrete.Elaboration.compileOccurrencesWith? input
                  (Concrete.Elaboration.compileRegion? input fuel)
                  sourceExtended binders sourceOccurrences).bind _ =
                    some sourceBody at sourceCompiled
                rw [sourceItemsEq] at sourceCompiled
                exact Option.some.inj sourceCompiled |>.symm
              have targetBodyEq : targetBody =
                  Concrete.Elaboration.finishRegion
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetContext
                    site targetItems := by
                simp only [Concrete.Elaboration.compileRegion?] at targetCompiled
                change (Concrete.Elaboration.compileOccurrencesWith?
                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                  (Concrete.Elaboration.compileRegion?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                  targetExtended binders targetOccurrences).bind _ =
                    some targetBody at targetCompiled
                rw [targetItemsEq] at targetCompiled
                exact Option.some.inj targetCompiled |>.symm
              have occurrencesEq : targetOccurrences = sourceOccurrences := by
                simp [targetOccurrences, sourceOccurrences]
              have siteBelow : input.Encloses site site := ⟨0, rfl⟩
              have rawIso : ItemSeqIso
                  (FiniteEquiv.refl (Fin targetExtended.length)) rels
                  (sourceItems.renameWires extendedWitness.indexMap)
                  targetItems := by
                refine compiledItemSeqIso_after_rename input outer inner
                  (Concrete.Elaboration.compileRegion? input fuel)
                  (Concrete.Elaboration.compileRegion?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                  sourceExtended targetExtended binders binders
                  sourceOccurrences (sourceCompiled := sourceItemsEq)
                  (targetCompiled := ?_) (wireMap := extendedWitness.indexMap)
                  ?_
                · simpa only [occurrencesEq] using targetItemsEq
                · intro occurrenceIndex
                  have sourceGet :=
                    Concrete.Elaboration.compileOccurrencesWith?_get
                      (Concrete.Elaboration.compileRegion? input fuel)
                      sourceExtended binders sourceItemsEq occurrenceIndex
                  have targetGet :=
                    Concrete.Elaboration.compileOccurrencesWith?_get
                      (Concrete.Elaboration.compileRegion?
                        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                      targetExtended binders (by
                        simpa only [occurrencesEq] using targetItemsEq)
                      occurrenceIndex
                  let occurrence := sourceOccurrences.get occurrenceIndex
                  have occurrenceMem : occurrence ∈ sourceOccurrences :=
                    List.get_mem _ _
                  change Concrete.Elaboration.compileOccurrenceWith? input
                      (Concrete.Elaboration.compileRegion? input fuel)
                      sourceExtended binders occurrence = some _ at sourceGet
                  change Concrete.Elaboration.compileOccurrenceWith?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                      (Concrete.Elaboration.compileRegion?
                        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                      targetExtended binders occurrence = some _ at targetGet
                  cases occurrenceShape : occurrence with
                  | node node =>
                      rw [occurrenceShape] at sourceGet targetGet
                      simp only [Concrete.Elaboration.compileOccurrenceWith?]
                        at sourceGet targetGet
                      have mapped := compileNode_map input inputWellFormed outer
                        inner distinct ordered targetWellFormed site siteBelow
                        sourceExtended targetExtended extendedWitness sourceExact
                        targetExact binders node
                      rw [sourceGet] at mapped
                      have itemEq := Option.some.inj (targetGet.symm.trans mapped)
                      rw [itemEq]
                      exact ItemIso.refl _
                  | child child =>
                      rw [occurrenceShape] at sourceGet targetGet
                      have childParent : (input.regions child).parent? =
                          some site :=
                        (Concrete.Elaboration.mem_localOccurrences_child input
                          site child).1 (by
                            rw [← occurrenceShape]
                            exact occurrenceMem)
                      have targetChildParent :
                          ((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).regions
                            child).parent? = some site := by
                        simpa using childParent
                      have siteChild : input.Encloses site child := by
                        refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
                        simp [Concrete.Diagram.climb, childParent]
                      have childNotSite : child ≠ site := by
                        intro equality
                        subst child
                        have reverse := siteChild
                        exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
                          inputWellFormed childParent reverse
                      have sourceChildExact := sourceExact.extend_child
                        inputWellFormed childParent
                      have targetChildExact := targetExact.extend_child
                        targetWellFormed targetChildParent
                      cases childKind : input.regions child with
                      | sheet =>
                          simp [Concrete.Elaboration.compileOccurrenceWith?,
                            childKind] at sourceGet
                      | cut parent =>
                          simp only [Concrete.Elaboration.compileOccurrenceWith?,
                            childKind, VisualProof.Refinement.Implementation.WireJoin.target_regions]
                              at sourceGet targetGet
                          cases sourceChildEq :
                              Concrete.Elaboration.compileRegion? input fuel
                                child sourceExtended binders with
                          | none => simp [sourceChildEq] at sourceGet
                          | some sourceChild =>
                              cases targetChildEq :
                                  Concrete.Elaboration.compileRegion?
                                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                                    fuel child targetExtended binders with
                              | none => simp [targetChildEq] at targetGet
                              | some targetChild =>
                                  rw [sourceChildEq] at sourceGet
                                  rw [targetChildEq] at targetGet
                                  have sourceItemEq :=
                                    Option.some.inj sourceGet |>.symm
                                  have targetItemEq :=
                                    Option.some.inj targetGet |>.symm
                                  rw [sourceItemEq, targetItemEq]
                                  exact ItemIso.cut (compileRegion_quotient input
                                    inputWellFormed outer inner distinct ordered
                                    targetWellFormed fuel child siteChild
                                    childNotSite sourceExtended targetExtended
                                    extendedWitness sourceChildExact
                                    targetChildExact binders sourceChildEq
                                    targetChildEq)
                      | bubble parent arity =>
                          simp only [Concrete.Elaboration.compileOccurrenceWith?,
                            childKind, VisualProof.Refinement.Implementation.WireJoin.target_regions]
                              at sourceGet targetGet
                          let childBinders := binders.push child arity
                          cases sourceChildEq :
                              Concrete.Elaboration.compileRegion? input fuel
                                child sourceExtended childBinders with
                          | none =>
                              change (Concrete.Elaboration.compileRegion? input
                                fuel child sourceExtended childBinders).bind _ =
                                  some _ at sourceGet
                              rw [sourceChildEq] at sourceGet
                              contradiction
                          | some sourceChild =>
                              cases targetChildEq :
                                  Concrete.Elaboration.compileRegion?
                                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                                    fuel child targetExtended childBinders with
                              | none =>
                                  change (Concrete.Elaboration.compileRegion?
                                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                                    fuel child targetExtended childBinders).bind
                                      _ = some _ at targetGet
                                  rw [targetChildEq] at targetGet
                                  contradiction
                              | some targetChild =>
                                  change (Concrete.Elaboration.compileRegion?
                                    input fuel child sourceExtended
                                    childBinders).bind _ = some _ at sourceGet
                                  change (Concrete.Elaboration.compileRegion?
                                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                                    fuel child targetExtended childBinders).bind
                                      _ = some _ at targetGet
                                  rw [sourceChildEq] at sourceGet
                                  rw [targetChildEq] at targetGet
                                  have sourceItemEq :=
                                    Option.some.inj sourceGet |>.symm
                                  have targetItemEq :=
                                    Option.some.inj targetGet |>.symm
                                  rw [sourceItemEq, targetItemEq]
                                  exact ItemIso.bubble (compileRegion_quotient
                                    input inputWellFormed outer inner distinct
                                    ordered targetWellFormed fuel child siteChild
                                    childNotSite sourceExtended targetExtended
                                    extendedWitness sourceChildExact
                                    targetChildExact childBinders sourceChildEq
                                    targetChildEq)
              let sourceLocal := Concrete.Elaboration.exactScopeWires input
                site |>.length
              let targetLocal := Concrete.Elaboration.exactScopeWires
                (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) site |>.length
              let sourceExtendEq :=
                Concrete.Elaboration.WireContext.length_extend sourceContext site
              let targetExtendEq :=
                Concrete.Elaboration.WireContext.length_extend targetContext site
              let sourceCast : FiniteEquiv (Fin sourceExtended.length)
                  (Fin (sourceContext.length + sourceLocal)) :=
                FiniteEquiv.finCast (by
                  simpa only [sourceExtended, sourceLocal] using sourceExtendEq)
              let targetCast : FiniteEquiv (Fin targetExtended.length)
                  (Fin (targetContext.length + targetLocal)) :=
                FiniteEquiv.finCast (by
                  simpa only [targetExtended, targetLocal] using targetExtendEq)
              let sourceNodup : sourceContext.Nodup := by
                have extended := sourceExact.nodup
                rw [Concrete.Elaboration.WireContext.extend,
                  List.nodup_append] at extended
                exact extended.1
              let inherited := contextEquiv witness sourceNodup innerAbsent
              let localIso := siteLocalEquiv input outer inner distinct
              let totalEquiv := extendWireEquiv inherited localIso
              let sourceFreshLocal : Fin sourceLocal :=
                localIso.symm (Fin.last targetLocal)
              let sourceFreshExtended : Fin sourceExtended.length :=
                sourceCast.symm
                  (Fin.natAdd sourceContext.length sourceFreshLocal)
              let joined : Fin (targetContext.length + targetLocal) :=
                targetCast (extendedWitness.indexMap sourceFreshExtended)
              have mapFactor (index : Fin sourceExtended.length) :
                  targetCast (extendedWitness.indexMap index) =
                    VisualProof.Rule.WireSever.collapseLocal
                      targetContext.length targetLocal joined
                      (totalEquiv (sourceCast index)) := by
                let sourcePosition := sourceCast index
                have recover : sourceCast.symm sourcePosition = index :=
                  sourceCast.left_inv index
                rw [← recover]
                have sourceRoundtrip :
                    sourceCast (sourceCast.symm sourcePosition) =
                      sourcePosition := sourceCast.right_inv sourcePosition
                rw [sourceRoundtrip]
                refine Fin.addCases (fun inheritedIndex => ?_)
                  (fun localIndex => ?_) sourcePosition
                · have indexEq : extendedWitness.indexMap
                        (sourceCast.symm
                          (Fin.castAdd sourceLocal inheritedIndex)) =
                      targetCast.symm
                        (Fin.castAdd targetLocal
                          (witness.indexMap inheritedIndex)) := by
                    simpa [extendedWitness, sourceCast, targetCast, sourceLocal,
                      targetLocal, sourceExtended, targetExtended,
                      FiniteEquiv.finCast] using
                        (VisualProof.Refinement.Implementation.WireJoin.ContextWitness.extend_index_inherited
                          witness inputWellFormed ordered site sourceExact
                          targetExact inheritedIndex)
                  rw [indexEq]
                  have targetRoundtrip : targetCast
                      (targetCast.symm
                        (Fin.castAdd targetLocal
                          (witness.indexMap inheritedIndex))) =
                      Fin.castAdd targetLocal
                        (witness.indexMap inheritedIndex) :=
                    targetCast.right_inv _
                  rw [targetRoundtrip]
                  unfold totalEquiv
                  rw [extendWireEquiv_outer]
                  unfold VisualProof.Rule.WireSever.collapseLocal
                  rw [dif_pos (by
                    exact Nat.lt_add_right targetLocal
                      (inherited inheritedIndex).isLt)]
                  apply Fin.ext
                  rfl
                · by_cases isInner :
                      (Concrete.Elaboration.exactScopeWires input site).get
                        localIndex = inner
                  · have localValue : localIso localIndex =
                        Fin.last targetLocal := by
                      change siteLocalMap input outer inner distinct localIndex =
                        Fin.last targetLocal
                      unfold siteLocalMap
                      rw [dif_pos (by simpa only [site] using isInner)]
                    have freshEq : localIndex = sourceFreshLocal := by
                      apply localIso.injective
                      rw [localValue]
                      exact localIso.right_inv (Fin.last targetLocal) |>.symm
                    subst localIndex
                    unfold totalEquiv
                    rw [extendWireEquiv_local]
                    have freshValue : localIso sourceFreshLocal =
                        Fin.last targetLocal :=
                      localIso.right_inv (Fin.last targetLocal)
                    rw [freshValue]
                    unfold VisualProof.Rule.WireSever.collapseLocal
                    rw [dif_neg (by simp)]
                  · let targetLocalIndex := siteTargetIndex input outer inner
                      distinct localIndex (by simpa only [site] using isInner)
                    let sourceRaw : Fin sourceExtended.length :=
                      sourceCast.symm
                        (Fin.natAdd sourceContext.length localIndex)
                    let targetRaw : Fin targetExtended.length :=
                      targetCast.symm
                        (Fin.natAdd targetContext.length targetLocalIndex)
                    have sourceGet : sourceExtended.get sourceRaw =
                        (Concrete.Elaboration.exactScopeWires input site).get
                          localIndex := by
                      simp [sourceRaw, sourceCast, sourceExtended, sourceLocal,
                        Concrete.Elaboration.WireContext.extend,
                        FiniteEquiv.finCast]
                    have targetGet : targetExtended.get targetRaw =
                        (Concrete.Elaboration.exactScopeWires
                          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) site).get
                            targetLocalIndex := by
                      simp [targetRaw, targetCast, targetExtended, targetLocal,
                        Concrete.Elaboration.WireContext.extend,
                        FiniteEquiv.finCast]
                    have mappedGet := extendedWitness.get sourceRaw
                    rw [sourceGet] at mappedGet
                    have localGet := siteTargetIndex_get input outer inner
                      distinct localIndex (by simpa only [site] using isInner)
                    have localGetSite :
                        (Concrete.Elaboration.exactScopeWires
                          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) site).get
                            targetLocalIndex =
                          VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct
                            ((Concrete.Elaboration.exactScopeWires input site).get
                              localIndex) := by
                      simpa only [site, targetLocalIndex] using localGet
                    have targetRawEq : extendedWitness.indexMap sourceRaw =
                        targetRaw := by
                      apply Fin.ext
                      exact (List.getElem_inj targetExact.nodup).mp (by
                        simpa only [List.get_eq_getElem, targetGet] using
                          mappedGet.trans (targetGet.trans localGetSite).symm)
                    have sourceRawEq :
                        sourceCast.symm
                            (Fin.natAdd sourceContext.length localIndex) =
                          sourceRaw := rfl
                    rw [sourceRawEq, targetRawEq]
                    have targetCastValue : targetCast targetRaw =
                        Fin.natAdd targetContext.length targetLocalIndex :=
                      targetCast.right_inv _
                    rw [targetCastValue]
                    unfold totalEquiv
                    rw [extendWireEquiv_local]
                    have localValue : localIso localIndex =
                        Fin.castSucc targetLocalIndex := by
                      change siteLocalMap input outer inner distinct localIndex =
                        Fin.castSucc targetLocalIndex
                      unfold siteLocalMap
                      rw [dif_neg (by simpa only [site] using isInner)]
                    rw [localValue]
                    unfold VisualProof.Rule.WireSever.collapseLocal
                    rw [dif_pos (by
                      exact Nat.add_lt_add_left targetLocalIndex.isLt
                        targetContext.length)]
                    apply Fin.ext
                    rfl
              let sourceCanonical :
                  ItemSeq (sourceContext.length + sourceLocal) rels :=
                sourceItems.castWiresEq (by
                  simpa only [sourceLocal] using sourceExtendEq)
              let targetCanonical :
                  ItemSeq (targetContext.length + targetLocal) rels :=
                targetItems.castWiresEq (by
                  simpa only [targetLocal] using targetExtendEq)
              let separate :
                  ItemSeq (targetContext.length + (targetLocal + 1)) rels :=
                sourceCanonical.renameWires totalEquiv
              let before : Region targetContext.length rels :=
                .mk targetLocal
                  (separate.renameWires
                    (VisualProof.Rule.WireSever.collapseLocal
                      targetContext.length targetLocal joined))
              let after : Region targetContext.length rels :=
                .mk (targetLocal + 1) separate
              have sourceIso : RegionIso inherited rels sourceBody after := by
                rw [sourceBodyEq]
                unfold Concrete.Elaboration.finishRegion after separate
                apply RegionIso.mk localIso
                exact ItemSeqIso.renameWiresEquiv sourceCanonical totalEquiv
              have separateCollapsedEq :
                  separate.renameWires
                      (VisualProof.Rule.WireSever.collapseLocal
                        targetContext.length targetLocal joined) =
                    (sourceItems.renameWires extendedWitness.indexMap).renameWires
                      targetCast := by
                unfold separate sourceCanonical
                simp only [ItemSeq.castWiresEq_eq_renameWires]
                rw [ItemSeq.renameWires_comp, ItemSeq.renameWires_comp,
                  ItemSeq.renameWires_comp]
                apply congrArg (sourceItems.renameWires ·)
                funext index
                exact (mapFactor index).symm
              have rawCasted : ItemSeqIso
                  (FiniteEquiv.refl
                    (Fin (targetContext.length + targetLocal))) rels
                  ((sourceItems.renameWires extendedWitness.indexMap).renameWires
                    targetCast)
                  targetCanonical := by
                unfold targetCanonical
                simp only [ItemSeq.castWiresEq_eq_renameWires]
                apply ItemSeqIso.renameWires_commuting rawIso targetCast
                  targetCast (FiniteEquiv.refl _)
                funext index
                rfl
              have targetItemsIso : ItemSeqIso
                  (FiniteEquiv.refl
                    (Fin (targetContext.length + targetLocal))) rels
                  targetCanonical
                  (separate.renameWires
                    (VisualProof.Rule.WireSever.collapseLocal
                      targetContext.length targetLocal joined)) := by
                rw [separateCollapsedEq]
                simpa [FiniteEquiv.symm, FiniteEquiv.refl] using rawCasted.symm
              have targetIso : Core.Isomorphic targetBody before := by
                rw [targetBodyEq]
                unfold Concrete.Elaboration.finishRegion before
                change RegionIso (FiniteEquiv.refl (Fin targetContext.length))
                  rels (.mk targetLocal targetCanonical)
                    (.mk targetLocal
                      (separate.renameWires
                        (VisualProof.Rule.WireSever.collapseLocal
                          targetContext.length targetLocal joined)))
                apply RegionIso.mk (FiniteEquiv.refl (Fin targetLocal))
                have extendedRefl : extendWireEquiv
                    (FiniteEquiv.refl (Fin targetContext.length))
                    (FiniteEquiv.refl (Fin targetLocal)) =
                      FiniteEquiv.refl
                        (Fin (targetContext.length + targetLocal)) := by
                  apply FiniteEquiv.ext
                  intro wire
                  refine Fin.addCases (fun inheritedIndex => ?_)
                    (fun localIndex => ?_) wire
                  · simp only [extendWireEquiv_outer,
                      FiniteEquiv.refl_apply]
                  · simp only [extendWireEquiv_local,
                      FiniteEquiv.refl_apply]
                rw [extendedRefl]
                exact targetItemsIso
              exact ⟨before, after,
                VisualProof.Rule.WireSever.Local.sever joined separate,
                targetIso, sourceIso⟩

end VisualProof.Refinement.Implementation.WireJoin
