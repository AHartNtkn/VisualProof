import VisualProof.Refinement.Implementation.WireJoinSiteLocal
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof
open VisualProof.Rule
open VisualProof.Theory
open VisualProof.Diagram

theorem lookup_map_of_ne
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner))
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region)
    (wire : Fin input.wireCount)
    (notInner : wire ≠ inner) :
    targetContext.lookup? (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct
        wire) =
      (sourceContext.lookup? wire).map witness.indexMap := by
  have memEq :
      VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire ∈
          targetContext ↔ wire ∈ sourceContext := by
    constructor
    · intro targetMember
      apply (sourceExact.mem_iff wire).2
      have targetVisible := (targetExact.mem_iff _).1 targetMember
      rw [VisualProof.Refinement.Implementation.WireJoin.target_wire_scope input outer inner wire
        distinct, if_neg notInner,
        VisualProof.Refinement.Implementation.WireJoin.target_encloses_iff] at targetVisible
      exact targetVisible
    · intro sourceMember
      apply (targetExact.mem_iff _).2
      exact VisualProof.Refinement.Implementation.WireJoin.visible_map input wellFormed outer inner wire
        distinct ordered region ((sourceExact.mem_iff wire).1 sourceMember)
  cases sourceLookup : sourceContext.lookup? wire with
  | none =>
      have sourceNotMem : wire ∉ sourceContext := by
        intro member
        obtain ⟨index, lookup⟩ := sourceContext.lookup?_complete member
        rw [sourceLookup] at lookup
        contradiction
      have targetNotMem :
          VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire ∉
            targetContext := fun member => sourceNotMem (memEq.1 member)
      cases targetLookup : targetContext.lookup?
          (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire) with
      | none => rfl
      | some index =>
          have found := Concrete.Elaboration.WireContext.lookup?_sound
            targetLookup
          have member : targetContext.get index ∈ targetContext :=
            List.get_mem targetContext index
          have value : targetContext.get index =
              VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire := by
            simpa only [List.get_eq_getElem] using found
          rw [value] at member
          exact False.elim (targetNotMem member)
  | some sourceIndex =>
      have sourceGet : sourceContext.get sourceIndex = wire := by
        simpa only [List.get_eq_getElem] using
          Concrete.Elaboration.WireContext.lookup?_sound sourceLookup
      have targetMember :
          VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire ∈
            targetContext := memEq.2 (by
          rw [← sourceGet]
          exact List.get_mem sourceContext sourceIndex)
      obtain ⟨targetIndex, targetLookup⟩ :=
        targetContext.lookup?_complete targetMember
      have targetGet : targetContext.get targetIndex =
          VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct wire := by
        simpa only [List.get_eq_getElem] using
          Concrete.Elaboration.WireContext.lookup?_sound targetLookup
      have indices : targetIndex = witness.indexMap sourceIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetExact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            targetGet.trans ((witness.get sourceIndex).trans
              (congrArg (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct)
                sourceGet)).symm)
      simp only [Option.map_some]
      rw [targetLookup, indices]

theorem resolvePort_map_away
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    (region : Fin input.regionCount)
    (notBelow : ¬ input.Encloses (input.wires inner).scope region)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner))
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region)
    (node : Fin input.nodeCount)
    (nodeRegion : (input.nodes node).region = region)
    (port : Concrete.CPort) :
    Concrete.Elaboration.resolvePort?
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetContext node port =
      (Concrete.Elaboration.resolvePort? input sourceContext node port).map
        witness.indexMap := by
  unfold Concrete.Elaboration.resolvePort?
  rw [Concrete.Elaboration.endpointOwner?_map
    (source := input)
    (target := VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) node node
    (VisualProof.Refinement.Implementation.WireJoin.wireMap input outer inner distinct) port
    (fun wire occurs => VisualProof.Refinement.Implementation.WireJoin.endpointOccurs_map input outer inner
      wire distinct ⟨node, port⟩ occurs)
    (fun targetWire occurs => endpointOccurs_preimage input outer inner distinct
      targetWire ⟨node, port⟩ occurs)
    targetWellFormed.wire_endpoints_are_disjoint]
  cases ownerEq : Concrete.Elaboration.endpointOwner? input ⟨node, port⟩ with
  | none => simp
  | some wire =>
      simp only [Option.map_some]
      have occurs := Concrete.Elaboration.endpointOwner?_sound ownerEq
      have wireNe : wire ≠ inner := by
        intro equality
        subst wire
        have enclosed := wellFormed.wire_scopes_enclose inner ⟨node, port⟩
          occurs
        rw [nodeRegion] at enclosed
        exact notBelow enclosed
      exact lookup_map_of_ne input wellFormed outer inner distinct ordered region
        sourceContext targetContext witness sourceExact targetExact wire wireNe

theorem compileNode_map_away
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).WellFormed)
    (region : Fin input.regionCount)
    (notBelow : ¬ input.Encloses (input.wires inner).scope region)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner))
    (witness : VisualProof.Refinement.Implementation.WireJoin.ContextWitness input outer inner distinct
      sourceContext targetContext)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region)
    (binders : Concrete.Elaboration.BinderContext input rels)
    (node : Fin input.nodeCount)
    (nodeRegion : (input.nodes node).region = region) :
    Concrete.Elaboration.compileNode?
        (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner) targetContext binders node =
      (Concrete.Elaboration.compileNode? input sourceContext binders node).map
        (Item.renameWires witness.indexMap) := by
  have nodeShape :
      (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner).nodes node =
        match input.nodes node with
        | .atom nodeRegion binder => .atom (id nodeRegion) (id binder)
        | .identity nodeRegion arity => .identity (id nodeRegion) arity := by
    cases shape : input.nodes node <;> simp [shape]
  have ports : ∀ port,
      Concrete.Elaboration.resolvePort?
          (VisualProof.Refinement.Implementation.WireJoin.Target input outer inner)
          targetContext node port =
        (Concrete.Elaboration.resolvePort? input sourceContext node port).map
          witness.indexMap := by
    intro port
    exact resolvePort_map_away input wellFormed outer inner distinct ordered
      targetWellFormed region notBelow sourceContext targetContext witness
      sourceExact targetExact node nodeRegion port
  have binderMap : ∀ sourceRegion binder,
      input.nodes node = .atom sourceRegion binder →
      binders (id binder) = (binders binder).map (fun relation =>
        ⟨relation.1,
          identityRelationRenaming rels relation.2⟩) := by
    intro sourceRegion binder shape
    simp [identityRelationRenaming]
  have mapped := Concrete.Elaboration.compileNode?_map sourceContext
    targetContext binders binders node node id id witness.indexMap
      (identityRelationRenaming rels)
      nodeShape ports binderMap
  have identity : (fun {arity} =>
      identityRelationRenaming rels :
        RelationRenaming rels rels) = (fun {arity} relation => relation) := rfl
  rw [identity] at mapped
  simpa only [Item.renameRelations_id] using mapped

end VisualProof.Refinement.Implementation.WireJoin

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof
open VisualProof.Rule
open VisualProof.Theory
open VisualProof.Diagram

noncomputable def compileRegion_away
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
    (notSite : region ≠ (input.wires inner).scope)
    (notBelow : ¬ input.Encloses (input.wires inner).scope region)
    (notAbove : ¬ input.Encloses region (input.wires inner).scope)
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
                    have nodeRegion : (input.nodes node).region = region :=
                      (Concrete.Elaboration.mem_localOccurrences_node input
                        region node).1 (by
                          rw [← occurrenceShape]
                          exact occurrenceMem)
                    have mapped := compileNode_map_away input inputWellFormed
                      outer inner distinct ordered targetWellFormed region
                      notBelow
                      sourceExtended targetExtended extendedWitness sourceExact
                      targetExact binders node nodeRegion
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
                    have childNotBelow : ¬ input.Encloses
                        (input.wires inner).scope child := by
                      intro siteChild
                      rcases Concrete.Diagram.enclosingRegions_comparable
                          siteChild regionChild with siteRegion | regionSite
                      · exact notBelow siteRegion
                      · exact notAbove regionSite
                    have childNotAbove : ¬ input.Encloses child
                        (input.wires inner).scope := by
                      intro childSite
                      exact notAbove
                        (Concrete.Elaboration.checked_encloses_trans
                          inputWellFormed regionChild childSite)
                    have childNotSite : child ≠ (input.wires inner).scope := by
                      intro equality
                      subst child
                      exact childNotBelow
                        (Concrete.Diagram.Encloses.refl input
                          (input.wires inner).scope)
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
                                exact ItemIso.cut (ih child childNotSite
                                  childNotBelow childNotAbove sourceExtended targetExtended
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
                                exact ItemIso.bubble (ih child childNotSite
                                  childNotBelow childNotAbove sourceExtended targetExtended
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
