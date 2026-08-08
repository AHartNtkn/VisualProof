import VisualProof.Refinement.Implementation.WireJoin
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

noncomputable def compileRegion_quotient
    (input : Concrete.Diagram)
    (inputWellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    (fuel : Nat)
    (region : Fin input.regionCount)
    (below : input.Encloses (input.wires inner).scope region)
    (notSite : region ≠ (input.wires inner).scope)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner))
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (binders : Concrete.Elaboration.BinderContext input rels)
    {sourceBody : Region sourceContext.length rels}
    {targetBody : Region targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input fuel region
      sourceContext binders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel region targetContext
      binders = some targetBody) :
    RegionIso (FiniteEquiv.refl (Fin targetContext.length)) rels
      (sourceBody.renameWires witness.indexMap) targetBody := by
  induction fuel generalizing rels region sourceContext targetContext
      sourceBody targetBody with
  | zero => simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ fuel ih =>
      let sourceExtended := sourceContext.extend region
      let targetExtended := targetContext.extend region
      let extendedWitness := witness.extend inputWellFormed ordered region
        sourceExact targetExact
      let sourceOccurrences := Concrete.Elaboration.localOccurrences input region
      let targetOccurrences := Concrete.Elaboration.localOccurrences
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) region
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
                  Concrete.Elaboration.finishRegion input sourceContext region
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
                    region targetItems := by
                simp only [Concrete.Elaboration.compileRegion?] at targetCompiled
                change (Concrete.Elaboration.compileOccurrencesWith?
                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                  (Concrete.Elaboration.compileRegion?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                  targetExtended binders targetOccurrences).bind _ =
                    some targetBody at targetCompiled
                rw [targetItemsEq] at targetCompiled
                exact Option.some.inj targetCompiled |>.symm
              let sourceLength :=
                Concrete.Elaboration.compileOccurrencesWith?_length
                  (Concrete.Elaboration.compileRegion? input fuel)
                  sourceExtended binders sourceItemsEq
              let targetLength :=
                Concrete.Elaboration.compileOccurrencesWith?_length
                  (Concrete.Elaboration.compileRegion?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                  targetExtended binders targetItemsEq
              have occurrencesEq : targetOccurrences = sourceOccurrences := by
                simp [targetOccurrences, sourceOccurrences]
              let positions : FiniteEquiv (Fin sourceItems.length)
                  (Fin targetItems.length) :=
                (FiniteEquiv.finCast sourceLength).trans
                  ((FiniteEquiv.finCast (congrArg List.length occurrencesEq)).symm
                    |>.trans (FiniteEquiv.finCast targetLength.symm))
              have pointwise (sourceIndex : Fin sourceItems.length) :
                  ItemIso (FiniteEquiv.refl (Fin targetExtended.length)) rels
                    ((sourceItems.get sourceIndex).renameWires
                      extendedWitness.indexMap)
                    (targetItems.get (positions sourceIndex)) := by
                let occurrenceIndex : Fin sourceOccurrences.length :=
                  Fin.cast sourceLength sourceIndex
                let targetOccurrenceIndex : Fin targetOccurrences.length :=
                  Fin.cast (congrArg List.length occurrencesEq).symm
                    occurrenceIndex
                have sourcePosition : Fin.cast sourceLength.symm
                    occurrenceIndex = sourceIndex := by
                  apply Fin.ext
                  rfl
                have targetPosition : Fin.cast targetLength.symm
                    targetOccurrenceIndex = positions sourceIndex := by
                  apply Fin.ext
                  rfl
                have sourceGet :=
                  Concrete.Elaboration.compileOccurrencesWith?_get
                    (Concrete.Elaboration.compileRegion? input fuel)
                    sourceExtended binders sourceItemsEq occurrenceIndex
                have targetGet :=
                  Concrete.Elaboration.compileOccurrencesWith?_get
                    (Concrete.Elaboration.compileRegion?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                    targetExtended binders targetItemsEq targetOccurrenceIndex
                rw [sourcePosition] at sourceGet
                rw [targetPosition] at targetGet
                have occurrenceEq : targetOccurrences.get targetOccurrenceIndex =
                    sourceOccurrences.get occurrenceIndex := by
                  subst targetOccurrences
                  rfl
                let occurrence := sourceOccurrences.get occurrenceIndex
                have occurrenceMem : occurrence ∈ sourceOccurrences :=
                  List.get_mem _ _
                change Concrete.Elaboration.compileOccurrenceWith? input
                    (Concrete.Elaboration.compileRegion? input fuel)
                    sourceExtended binders occurrence =
                  some (sourceItems.get sourceIndex) at sourceGet
                change Concrete.Elaboration.compileOccurrenceWith?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                    (Concrete.Elaboration.compileRegion?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                    targetExtended binders
                    (targetOccurrences.get targetOccurrenceIndex) =
                  some (targetItems.get (positions sourceIndex)) at targetGet
                rw [occurrenceEq] at targetGet
                change Concrete.Elaboration.compileOccurrenceWith?
                    (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                    (Concrete.Elaboration.compileRegion?
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) fuel)
                    targetExtended binders occurrence =
                  some (targetItems.get (positions sourceIndex)) at targetGet
                cases occurrenceShape : occurrence with
                | node node =>
                    rw [occurrenceShape] at sourceGet targetGet
                    simp only [Concrete.Elaboration.compileOccurrenceWith?]
                      at sourceGet targetGet
                    have mapped := compileNode_map input inputWellFormed outer
                      inner distinct ordered targetWellFormed region below
                      sourceExtended targetExtended extendedWitness sourceExact
                      targetExact binders node
                    rw [sourceGet] at mapped
                    have itemEq : targetItems.get (positions sourceIndex) =
                        (sourceItems.get sourceIndex).renameWires
                          extendedWitness.indexMap := by
                      apply Option.some.inj
                      exact targetGet.symm.trans mapped
                    rw [itemEq]
                    exact ItemIso.refl _
                | child child =>
                    rw [occurrenceShape] at sourceGet targetGet
                    have childParent : (input.regions child).parent? =
                        some region :=
                      (Concrete.Elaboration.mem_localOccurrences_child input
                        region child).1 (by
                          rw [← occurrenceShape]
                          exact occurrenceMem)
                    have targetChildParent :
                        ((VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).regions
                          child).parent? = some region := by
                      simpa using childParent
                    have regionChild : input.Encloses region child := by
                      refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
                      simp [Concrete.Diagram.climb, childParent]
                    have childBelow : input.Encloses
                        (input.wires inner).scope child :=
                      Concrete.Elaboration.checked_encloses_trans inputWellFormed
                        below regionChild
                    have childNotSite : child ≠ (input.wires inner).scope := by
                      intro equality
                      subst child
                      have reverse := regionChild
                      exact notSite (Concrete.Elaboration.checked_encloses_antisymm
                        inputWellFormed below reverse).symm
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
                          childKind, VisualProof.Refinement.Implementation.WireJoin.target_regions] at sourceGet targetGet
                        cases sourceChildEq : Concrete.Elaboration.compileRegion?
                            input fuel child sourceExtended binders with
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
                                have sourceItemEq : sourceItems.get sourceIndex =
                                    .cut sourceChild := by
                                  exact Option.some.inj sourceGet |>.symm
                                have targetItemEq :
                                    targetItems.get (positions sourceIndex) =
                                      .cut targetChild := by
                                  exact Option.some.inj targetGet |>.symm
                                rw [sourceItemEq, targetItemEq]
                                exact ItemIso.cut (ih child childBelow
                                  childNotSite sourceExtended targetExtended
                                  extendedWitness sourceChildExact
                                  targetChildExact binders sourceChildEq
                                  targetChildEq)
                    | bubble parent arity =>
                        simp only [Concrete.Elaboration.compileOccurrenceWith?,
                          childKind, VisualProof.Refinement.Implementation.WireJoin.target_regions] at sourceGet targetGet
                        let childBinders := binders.push child arity
                        cases sourceChildEq : Concrete.Elaboration.compileRegion?
                            input fuel child sourceExtended childBinders with
                        | none =>
                            change (Concrete.Elaboration.compileRegion? input
                              fuel child sourceExtended childBinders).bind _ =
                                some (sourceItems.get sourceIndex) at sourceGet
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
                                  fuel child targetExtended childBinders).bind _ =
                                    some (targetItems.get
                                      (positions sourceIndex)) at targetGet
                                rw [targetChildEq] at targetGet
                                contradiction
                            | some targetChild =>
                                change (Concrete.Elaboration.compileRegion? input
                                  fuel child sourceExtended childBinders).bind _ =
                                    some (sourceItems.get sourceIndex) at sourceGet
                                change (Concrete.Elaboration.compileRegion?
                                  (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                                  fuel child targetExtended childBinders).bind _ =
                                    some (targetItems.get
                                      (positions sourceIndex)) at targetGet
                                rw [sourceChildEq] at sourceGet
                                rw [targetChildEq] at targetGet
                                have sourceItemEq : sourceItems.get sourceIndex =
                                    .bubble arity sourceChild := by
                                  exact Option.some.inj sourceGet |>.symm
                                have targetItemEq :
                                    targetItems.get (positions sourceIndex) =
                                      .bubble arity targetChild := by
                                  exact Option.some.inj targetGet |>.symm
                                rw [sourceItemEq, targetItemEq]
                                exact ItemIso.bubble (ih child childBelow
                                  childNotSite sourceExtended targetExtended
                                  extendedWitness sourceChildExact
                                  targetChildExact childBinders sourceChildEq
                                  targetChildEq)
              have rawIso : ItemSeqIso
                  (FiniteEquiv.refl (Fin targetExtended.length)) rels
                  (sourceItems.renameWires extendedWitness.indexMap)
                  targetItems :=
                itemSeqIso_after_rename sourceItems targetItems
                  extendedWitness.indexMap positions pointwise
              subst sourceBody
              subst targetBody
              unfold Concrete.Elaboration.finishRegion
              simp only [Region.renameWires]
              let localIso := localEquiv input outer inner distinct region
                notSite
              apply RegionIso.mk localIso
              let sourceExtendEq :=
                Concrete.Elaboration.WireContext.length_extend sourceContext
                  region
              let targetExtendEq :=
                Concrete.Elaboration.WireContext.length_extend targetContext
                  region
              let sourceCast : FiniteEquiv (Fin sourceExtended.length)
                  (Fin (sourceContext.length +
                    (Concrete.Elaboration.exactScopeWires input region).length)) :=
                FiniteEquiv.finCast (by
                  simpa only [sourceExtended] using sourceExtendEq)
              let targetCast : FiniteEquiv (Fin targetExtended.length)
                  (Fin (targetContext.length +
                    (Concrete.Elaboration.exactScopeWires
                      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                      region).length)) :=
                FiniteEquiv.finCast (by
                  simpa only [targetExtended] using targetExtendEq)
              let finalWire := extendWireEquiv
                (FiniteEquiv.refl (Fin targetContext.length)) localIso
              let sourceCanonical := sourceItems.castWiresEq sourceExtendEq
              let sourceRenamedCanonical := sourceCanonical.renameWires
                (extendWireRenaming witness.indexMap
                  (Concrete.Elaboration.exactScopeWires input region).length)
              have mapFactor (index : Fin sourceExtended.length) :
                  finalWire
                      (extendWireRenaming witness.indexMap
                        (Concrete.Elaboration.exactScopeWires input region).length
                        (sourceCast index)) =
                    targetCast (extendedWitness.indexMap index) := by
                rw [extend_index_eq_extendedMap input inputWellFormed outer
                  inner distinct ordered region notSite sourceContext
                  targetContext witness sourceExact targetExact]
                let sourcePosition := Fin.cast sourceExtendEq index
                have recover : Fin.cast sourceExtendEq.symm sourcePosition =
                    index := by
                  apply Fin.ext
                  rfl
                rw [← recover]
                refine Fin.addCases (fun inherited => ?_)
                  (fun localIndex => ?_) sourcePosition
                · simp [finalWire, sourceCast, targetCast, localIso,
                    extendedMap, extendWireRenaming,
                    extendWireEquiv, FiniteEquiv.finCast]
                · simp [finalWire, sourceCast, targetCast, localIso,
                    extendedMap, extendWireRenaming,
                    extendWireEquiv, FiniteEquiv.finCast]
              have sourceCanonicalMap :
                  sourceRenamedCanonical.renameWires finalWire =
                    (sourceItems.renameWires extendedWitness.indexMap).renameWires
                      targetCast := by
                unfold sourceRenamedCanonical sourceCanonical
                rw [ItemSeq.castWiresEq_eq_renameWires,
                  ItemSeq.renameWires_comp, ItemSeq.renameWires_comp,
                  ItemSeq.renameWires_comp]
                apply congrArg (sourceItems.renameWires ·)
                funext index
                exact mapFactor index
              have sourceToMapped : ItemSeqIso finalWire rels
                  sourceRenamedCanonical
                  ((sourceItems.renameWires extendedWitness.indexMap).renameWires
                    targetCast) := by
                have renamed := ItemSeqIso.renameWiresEquiv
                  sourceRenamedCanonical finalWire
                rw [sourceCanonicalMap] at renamed
                exact renamed
              have rawCasted : ItemSeqIso
                  (FiniteEquiv.refl
                    (Fin (targetContext.length +
                      (Concrete.Elaboration.exactScopeWires
                        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
                        region).length))) rels
                  ((sourceItems.renameWires extendedWitness.indexMap).renameWires
                    targetCast)
                  (targetItems.renameWires targetCast) := by
                apply ItemSeqIso.renameWires_commuting rawIso targetCast targetCast
                  (FiniteEquiv.refl _)
                funext index
                rfl
              have combined := sourceToMapped.trans rawCasted
              simpa [sourceRenamedCanonical, sourceCanonical, sourceCast,
                targetCast, finalWire, localIso,
                ItemSeq.castWiresEq_eq_renameWires,
                FiniteEquiv.trans, FiniteEquiv.refl] using combined

end VisualProof.Refinement.Implementation.WireJoin
