import VisualProof.Rule.Soundness.Equational.AnchoredWireContractCompactionOpen

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace RoutedClosedAnchorSoundness

/-- A finishing monotonicity kernel whose item premise retains the actual
outer and local valuations.  Routed fresh-wire proofs need this stronger
interface to preserve the chosen ancestor witness through bubble descent. -/
theorem finishRegion_denote_mono_with_local
    (d : ConcreteDiagram) (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (sourceItems targetItems : ItemSeq signature
      (context.extend region).length rels)
    (hitems : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (outerEnv : Fin context.length → model.Carrier)
      (localEnv : Fin (ConcreteElaboration.exactScopeWires d region).length →
        model.Carrier)
      (relEnv : RelEnv model.Carrier rels),
      denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment context region outerEnv
            localEnv) relEnv sourceItems →
        denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment context region outerEnv
            localEnv) relEnv targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion d context region sourceItems) →
      denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion d context region targetItems) := by
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk]
  rintro ⟨localEnv, sourceDenotes⟩
  refine ⟨localEnv, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at sourceDenotes ⊢
  have sourceRaw := (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
    (extendWireEnv outerEnv localEnv) relEnv sourceItems).1 sourceDenotes
  have targetRaw := hitems model named outerEnv localEnv relEnv sourceRaw
  exact (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
    (extendWireEnv outerEnv localEnv) relEnv targetItems).2 targetRaw

/-- Fixed-model form of `finishRegion_denote_mono_with_local`, used when the
item implication depends on a particular chosen outer witness value. -/
theorem finishRegion_denote_mono_with_local_at
    (d : ConcreteDiagram) (context : ConcreteElaboration.WireContext d)
    (region : Fin d.regionCount)
    (sourceItems targetItems : ItemSeq signature
      (context.extend region).length rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (hitems : ∀ (localEnv : Fin
        (ConcreteElaboration.exactScopeWires d region).length → model.Carrier),
      denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment context region outerEnv
            localEnv) relEnv sourceItems →
        denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment context region outerEnv
            localEnv) relEnv targetItems) :
    denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion d context region sourceItems) →
      denoteRegion model named outerEnv relEnv
        (ConcreteElaboration.finishRegion d context region targetItems) := by
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk]
  rintro ⟨localEnv, sourceDenotes⟩
  refine ⟨localEnv, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires] at sourceDenotes ⊢
  have sourceRaw := (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
    (extendWireEnv outerEnv localEnv) relEnv sourceItems).1 sourceDenotes
  have targetRaw := hitems localEnv sourceRaw
  exact (denoteItemSeq_renameWires model named
    (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
    (extendWireEnv outerEnv localEnv) relEnv targetItems).2 targetRaw

/-- The singleton appended occurrence compiles to the closed equation assigning
the fresh output wire the denotation of its serialized term. -/
theorem freshOccurrence_denotes_iff
    (input : ConcreteDiagram)
    (region scope : Fin input.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (context : ConcreteElaboration.WireContext
      (spawnNodeRaw input (.term region 0 term) scope 1 (fun _ => .output)))
    (binders : ConcreteElaboration.BinderContext
      (spawnNodeRaw input (.term region 0 term) scope 1
        (fun _ => .output)) rels)
    (recurse : ∀ {currentRels : RelCtx},
      (currentRegion : Fin input.regionCount) →
      (currentContext : ConcreteElaboration.WireContext
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output))) →
      ConcreteElaboration.BinderContext
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output)) currentRels →
      Option (Region signature currentContext.length currentRels))
    (freshItems : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (spawnNodeRaw input (.term region 0 term) scope 1 (fun _ => .output))
      recurse context binders
      [ConcreteElaboration.LocalOccurrence.node
        (regions := input.regionCount) (Fin.last input.nodeCount)] =
          some freshItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (raw : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItemSeq model named raw relEnv freshItems ↔
      ∀ output,
        ConcreteElaboration.resolvePort?
          (spawnNodeRaw input (.term region 0 term) scope 1
            (fun _ => .output)) context
          (Fin.last input.nodeCount) .output = some output →
        raw output = model.eval term Fin.elim0 := by
  simp only [ConcreteElaboration.compileOccurrencesWith?,
    ConcreteElaboration.compileOccurrenceWith?] at compiled
  unfold ConcreteElaboration.compileNode? at compiled
  simp only [spawnNodeRaw_newNode] at compiled
  cases outputResult : ConcreteElaboration.resolvePort?
      (spawnNodeRaw input (.term region 0 term) scope 1 (fun _ => .output))
      context (Fin.last input.nodeCount) .output with
  | none => simp [outputResult] at compiled
  | some output =>
      rw [outputResult] at compiled
      cases freeResult : ConcreteElaboration.resolvePorts?
          (spawnNodeRaw input (.term region 0 term) scope 1
            (fun _ => .output)) context (Fin.last input.nodeCount) 0
          (fun index => .free index) with
      | none => simp [freeResult] at compiled
      | some free =>
          simp only [freeResult] at compiled
          change some (ItemSeq.cons
            (Item.equation output (term.mapFree free)) ItemSeq.nil) =
              some freshItems at compiled
          injection compiled with itemsEq
          rw [← itemsEq]
          simp only [denoteItemSeq_cons, denoteItem_equation,
            denoteItemSeq_nil, and_true]
          have freeEq : free = Fin.elim0 := by
            funext index
            exact Fin.elim0 index
          rw [freeEq, model.eval_mapFree]
          have envEq : raw ∘ Fin.elim0 = Fin.elim0 := by
            funext index
            exact Fin.elim0 index
          rw [envEq]
          constructor
          · intro equation candidate resolved
            exact Option.some.inj resolved ▸ equation
          · intro equations
            exact equations output rfl

/-- At the appended node's actual region, a closed equation on an inherited
fresh wire is semantically inert exactly when that inherited value is the
closed term's denotation. -/
theorem regionSite_denote_equiv
    (input : ConcreteDiagram)
    (region scope : Fin input.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input (.term region 0 term) scope 1
      (fun _ => .output)).WellFormed signature)
    (scopeEnclosesRegion : input.Encloses scope region)
    (regionNeScope : region ≠ scope)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input)
    (target : ConcreteElaboration.WireContext
      (spawnNodeRaw input (.term region 0 term) scope 1
        (fun _ => .output)))
    (embedding : SpawnContextEmbedding input (.term region 0 term) scope 1
      (fun _ => .output) source target)
    (binders : ConcreteElaboration.BinderContext input rels)
    (hsourceExact : (source.extend region).Exact region)
    (htargetExact : (target.extend region).Exact region)
    (sourceBody : Region signature source.length rels)
    (targetBody : Region signature target.length rels)
    (sourceCompiled : ConcreteElaboration.compileRegion? signature input
      (fuel + 1) region source binders = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRegion? signature
      (spawnNodeRaw input (.term region 0 term) scope 1
        (fun _ => .output))
      (fuel + 1) region target binders = some targetBody)
    (freshIndex : Fin target.length)
    (freshGet : target.get freshIndex =
      Fin.natAdd input.wireCount (0 : Fin 1))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin target.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    (denoteRegion model named outerEnv relEnv targetBody →
      denoteRegion model named (outerEnv ∘ embedding.index) relEnv
        sourceBody) ∧
    (outerEnv freshIndex = model.eval term Fin.elim0 →
      denoteRegion model named (outerEnv ∘ embedding.index) relEnv
        sourceBody →
      denoteRegion model named outerEnv relEnv targetBody) := by
  let sourceNodes :=
    (filterFin fun old => decide ((input.nodes old).region = region)).map
      (fun old => ConcreteElaboration.LocalOccurrence.node
        (regions := input.regionCount) old)
  let sourceChildren :=
    (filterFin fun child =>
      decide ((input.regions child).parent? = some region)).map
      (ConcreteElaboration.LocalOccurrence.child (nodes := input.nodeCount))
  let targetNodes := sourceNodes.map (spawnNodeRaw_oldOccurrence input)
  let targetChildren := sourceChildren.map (spawnNodeRaw_oldOccurrence input)
  let fresh := [ConcreteElaboration.LocalOccurrence.node
    (regions := input.regionCount) (Fin.last input.nodeCount)]
  have sourceOccurrences :
      ConcreteElaboration.localOccurrences input region =
        sourceNodes ++ sourceChildren := by rfl
  have targetOccurrences :
      ConcreteElaboration.localOccurrences
          (spawnNodeRaw input (.term region 0 term) scope 1
            (fun _ => .output)) region =
        targetNodes ++ fresh ++ targetChildren := by
    simp only [spawnNodeRaw_localOccurrences, CNode.region, if_pos]
    simp only [sourceNodes, sourceChildren, targetNodes, targetChildren, fresh,
      List.map_map]
    rfl
  simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
  cases sourceItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
      input (ConcreteElaboration.compileRegion? signature input fuel)
      (source.extend region) binders
      (ConcreteElaboration.localOccurrences input region) with
  | none => simp [sourceItemsEq] at sourceCompiled
  | some sourceItems =>
    simp [sourceItemsEq] at sourceCompiled
    subst sourceBody
    cases targetItemsEq : ConcreteElaboration.compileOccurrencesWith? signature
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output))
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input (.term region 0 term) scope 1
            (fun _ => .output)) fuel)
        (target.extend region) binders
        (ConcreteElaboration.localOccurrences
          (spawnNodeRaw input (.term region 0 term) scope 1
            (fun _ => .output)) region) with
    | none => simp [targetItemsEq] at targetCompiled
    | some targetItems =>
      simp [targetItemsEq] at targetCompiled
      subst targetBody
      have targetOrdered :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input (.term region 0 term) scope 1
                (fun _ => .output))
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input (.term region 0 term) scope 1
                  (fun _ => .output)) fuel)
              (target.extend region) binders
              (targetNodes ++ (fresh ++ targetChildren)) =
            some targetItems := by
        rw [← List.append_assoc, ← targetOccurrences]
        exact targetItemsEq
      obtain ⟨nodeItems, restItems, nodeCompiled, restCompiled,
          targetItemsShape⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input (.term region 0 term) scope 1
              (fun _ => .output)) fuel)
          (target.extend region) binders targetNodes
          (fresh ++ targetChildren) targetItems targetOrdered
      obtain ⟨freshItems, childItems, freshCompiled, childCompiled,
          restItemsShape⟩ :=
        ConcreteElaboration.compileOccurrencesWith?_append_split
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input (.term region 0 term) scope 1
              (fun _ => .output)) fuel)
          (target.extend region) binders fresh targetChildren restItems
          restCompiled
      have oldCompiled :
          ConcreteElaboration.compileOccurrencesWith? signature
              (spawnNodeRaw input (.term region 0 term) scope 1
                (fun _ => .output))
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input (.term region 0 term) scope 1
                  (fun _ => .output)) fuel)
              (target.extend region) binders
              ((ConcreteElaboration.localOccurrences input region).map
                (spawnNodeRaw_oldOccurrence input)) =
            some (nodeItems.append childItems) := by
        rw [sourceOccurrences, List.map_append]
        change ConcreteElaboration.compileOccurrencesWith? signature
            (spawnNodeRaw input (.term region 0 term) scope 1
              (fun _ => .output))
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input (.term region 0 term) scope 1
                (fun _ => .output)) fuel)
            (target.extend region) binders (targetNodes ++ targetChildren) = _
        exact ConcreteElaboration.compileOccurrencesWith?_append
          (ConcreteElaboration.compileRegion? signature
            (spawnNodeRaw input (.term region 0 term) scope 1
              (fun _ => .output)) fuel)
          (target.extend region) binders targetNodes targetChildren nodeItems
          childItems nodeCompiled childCompiled
      have oldMap := spawnNodeRaw_compileOldOccurrencesAtNodeSite input
        (.term region 0 term) scope 1 (fun _ => .output) hinput htarget
        scopeEnclosesRegion fuel source target embedding binders hsourceExact
        htargetExact
      dsimp only [CNode.region] at oldMap
      rw [sourceItemsEq] at oldMap
      simp only [Option.map_some] at oldMap
      rw [oldCompiled] at oldMap
      have oldItems : nodeItems.append childItems =
          sourceItems.renameWires (embedding.extend region).index :=
        Option.some.inj oldMap
      have finishMap :
          ConcreteElaboration.finishRegion
              (spawnNodeRaw input (.term region 0 term) scope 1
                (fun _ => .output)) target region
              (sourceItems.renameWires (embedding.extend region).index) =
            (ConcreteElaboration.finishRegion input source region sourceItems
              ).renameWires embedding.index := by
        have wireMap : (embedding.extend region).index =
            spawnNodeRaw_extendedWireMapOfNe embedding region regionNeScope := by
          funext index
          exact SpawnContextEmbedding.extend_index_eq_map_of_ne embedding region
            regionNeScope htargetExact.nodup index
        rw [wireMap]
        exact spawnNodeRaw_finishRegion_old_of_ne input
          (.term region 0 term) scope region 1 (fun _ => .output) source target
          embedding regionNeScope sourceItems
      have freshMeaning := freshOccurrence_denotes_iff input region scope term
        (target.extend region) binders
        (ConcreteElaboration.compileRegion? signature
          (spawnNodeRaw input (.term region 0 term) scope 1
            (fun _ => .output)) fuel)
        freshItems freshCompiled model named
      have freshOutputIndex : ∀ output,
          ConcreteElaboration.resolvePort?
              (spawnNodeRaw input (.term region 0 term) scope 1
                (fun _ => .output))
              (target.extend region) (Fin.last input.nodeCount) .output =
                some output →
            output = target.outerIndex region freshIndex := by
        intro output resolved
        obtain ⟨wire, occurs, outputGet⟩ :=
          ConcreteElaboration.resolvePort?_sound resolved
        have wireEq : wire = Fin.natAdd input.wireCount (0 : Fin 1) := by
          apply ConcreteElaboration.endpoint_wire_unique
            htarget.wire_endpoints_are_disjoint occurs
          unfold ConcreteDiagram.EndpointOccurs
          simp only [spawnNodeRaw, Fin.addCases_right]
          exact List.mem_singleton.mpr rfl
        rw [wireEq] at outputGet
        apply Fin.ext
        apply (List.getElem_inj htargetExact.nodup).mp
        have outerGet := ConcreteElaboration.WireContext.extend_outer target
          region freshIndex
        exact outputGet.trans (outerGet.trans freshGet).symm
      constructor
      · intro targetDenotes
        have mapped := finishRegion_denote_mono
          (spawnNodeRaw input (.term region 0 term) scope 1
            (fun _ => .output)) target region targetItems
          (sourceItems.renameWires (embedding.extend region).index)
          (by
            intro currentModel currentNamed rawEnv currentRelEnv itemsDenote
            rw [targetItemsShape, restItemsShape, denoteItemSeq_append]
              at itemsDenote
            rcases itemsDenote with ⟨nodesDenote, restDenote⟩
            rw [denoteItemSeq_append] at restDenote
            rcases restDenote with ⟨_, childrenDenote⟩
            rw [← oldItems, denoteItemSeq_append]
            exact ⟨nodesDenote, childrenDenote⟩)
          model named outerEnv relEnv targetDenotes
        rw [finishMap] at mapped
        exact (denoteRegion_renameWires model named embedding.index outerEnv
          relEnv (ConcreteElaboration.finishRegion input source region
            sourceItems)).1 mapped
      · intro freshValue sourceDenotes
        have mapped : denoteRegion model named outerEnv relEnv
            (ConcreteElaboration.finishRegion
              (spawnNodeRaw input (.term region 0 term) scope 1
                (fun _ => .output)) target region
              (sourceItems.renameWires (embedding.extend region).index)) := by
          rw [finishMap]
          exact (denoteRegion_renameWires model named embedding.index outerEnv
            relEnv (ConcreteElaboration.finishRegion input source region
              sourceItems)).2 sourceDenotes
        unfold ConcreteElaboration.finishRegion at mapped ⊢
        simp only [denoteRegion_mk] at mapped ⊢
        rcases mapped with ⟨localEnv, mappedItems⟩
        refine ⟨localEnv, ?_⟩
        rw [ItemSeq.castWiresEq_eq_renameWires] at mappedItems ⊢
        let rawEnv := ConcreteElaboration.extendedEnvironment target region
          outerEnv localEnv
        have oldDenotes := (denoteItemSeq_renameWires model named
          (Fin.cast (ConcreteElaboration.WireContext.length_extend target region))
          (extendWireEnv outerEnv localEnv) relEnv
          (sourceItems.renameWires (embedding.extend region).index)).1
            mappedItems
        rw [← oldItems, denoteItemSeq_append] at oldDenotes
        rcases oldDenotes with ⟨nodesDenote, childrenDenote⟩
        have freshDenotes : denoteItemSeq model named rawEnv relEnv freshItems :=
          (freshMeaning rawEnv relEnv).2 (by
            intro output resolved
            rw [freshOutputIndex output resolved]
            have outerValue : rawEnv (target.outerIndex region freshIndex) =
                outerEnv freshIndex := by
              unfold rawEnv ConcreteElaboration.extendedEnvironment
              simp only [Function.comp_apply, extendWireEnv]
              rw [show Fin.cast
                    (ConcreteElaboration.WireContext.length_extend target region)
                    (target.outerIndex region freshIndex) =
                  Fin.castAdd
                    (ConcreteElaboration.exactScopeWires
                      (spawnNodeRaw input (.term region 0 term) scope 1
                        (fun _ => .output)) region).length freshIndex by
                apply Fin.ext
                rfl]
              exact Fin.addCases_left freshIndex
            exact outerValue.trans freshValue)
        have targetRaw : denoteItemSeq model named rawEnv relEnv targetItems := by
          rw [targetItemsShape, restItemsShape, denoteItemSeq_append]
          refine ⟨nodesDenote, ?_⟩
          rw [denoteItemSeq_append]
          exact ⟨freshDenotes, childrenDenote⟩
        exact (denoteItemSeq_renameWires model named
          (Fin.cast (ConcreteElaboration.WireContext.length_extend target region))
          (extendWireEnv outerEnv localEnv) relEnv targetItems).2 targetRaw

/-- A closed equation on a wire introduced at an ancestor scope is inert
through an executor-certified bubble-only route to the equation node.  The
projection forgets the equation unconditionally; reflection uses the chosen
fresh ancestor value. -/
theorem zeroRoute_region_denote_equiv
    (input : ConcreteDiagram)
    (region scope : Fin input.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input (.term region 0 term) scope 1
      (fun _ => .output)).WellFormed signature)
    (scopeEnclosesRegion : input.Encloses scope region)
    {start : Fin input.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input start region path)
    {depth : Nat} (routeDepth : route.HasCutDepth depth)
    (depthZero : depth = 0)
    (scopeEnclosesStart : input.Encloses scope start)
    (startNeScope : start ≠ scope) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (source : ConcreteElaboration.WireContext input)
      (target : ConcreteElaboration.WireContext
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output)))
      (embedding : SpawnContextEmbedding input (.term region 0 term) scope 1
        (fun _ => .output) source target)
      (binders : ConcreteElaboration.BinderContext input rels)
      (hsourceExact : (source.extend start).Exact start)
      (htargetExact : (target.extend start).Exact start)
      (sourceBody : Region signature source.length rels)
      (targetBody : Region signature target.length rels)
      (sourceCompiled : ConcreteElaboration.compileRegion? signature input
        (fuel + 1) start source binders = some sourceBody)
      (targetCompiled : ConcreteElaboration.compileRegion? signature
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output))
        (fuel + 1) start target binders = some targetBody)
      (freshIndex : Fin target.length)
      (freshGet : target.get freshIndex =
        Fin.natAdd input.wireCount (0 : Fin 1)),
      ∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin target.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        (denoteRegion model named outerEnv relEnv targetBody →
          denoteRegion model named (outerEnv ∘ embedding.index) relEnv
            sourceBody) ∧
        (outerEnv freshIndex = model.eval term Fin.elim0 →
          denoteRegion model named (outerEnv ∘ embedding.index) relEnv
            sourceBody →
          denoteRegion model named outerEnv relEnv targetBody) := by
  revert scopeEnclosesStart startNeScope
  induction routeDepth with
  | here actualRegion =>
      intro scopeEnclosesStart startNeScope rels fuel source target embedding
        binders hsourceExact htargetExact
        sourceBody targetBody sourceCompiled targetCompiled freshIndex freshGet
        model named outerEnv relEnv
      exact regionSite_denote_equiv input actualRegion scope term hinput htarget
        scopeEnclosesRegion startNeScope fuel source target embedding binders
        hsourceExact htargetExact sourceBody targetBody sourceCompiled
        targetCompiled freshIndex freshGet model named outerEnv relEnv
  | cut childIsCut tailDepth ih => omega
  | @bubble routeStart child targetRegion rest depth arity hparent position
      hposition tail childIsBubble tailDepth ih =>
      intro scopeEnclosesStart startNeScope rels fuel source target embedding
        binders hsourceExact htargetExact
        sourceBody targetBody sourceCompiled targetCompiled freshIndex freshGet
        model named outerEnv relEnv
      have startNeRegion : routeStart ≠ targetRegion := by
        intro equality
        subst routeStart
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          hinput hparent) (regionRoute_encloses input hinput tail)
      have childEncloses : input.Encloses routeStart child :=
        AnchoredWireSoundness.split_direct_child_encloses hparent
      have scopeEnclosesChild : input.Encloses scope child :=
        ConcreteElaboration.checked_encloses_trans hinput scopeEnclosesStart
          childEncloses
      have childNeScope : child ≠ scope := by
        intro equality
        subst child
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          hinput hparent) scopeEnclosesStart
      obtain ⟨before, after, localShape, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input routeStart child position hposition
      simp only [ConcreteElaboration.compileRegion?]
        at sourceCompiled targetCompiled
      cases sourceItemsEq : ConcreteElaboration.compileOccurrencesWith?
          signature input
          (ConcreteElaboration.compileRegion? signature input fuel)
          (source.extend routeStart) binders
          (ConcreteElaboration.localOccurrences input routeStart) with
      | none => simp [sourceItemsEq] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsEq] at sourceCompiled
        subst sourceBody
        cases targetItemsEq : ConcreteElaboration.compileOccurrencesWith?
            signature
            (spawnNodeRaw input (.term targetRegion 0 term) scope 1
              (fun _ => .output))
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                (fun _ => .output)) fuel)
            (target.extend routeStart) binders
            (ConcreteElaboration.localOccurrences
              (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                (fun _ => .output)) routeStart) with
        | none => simp [targetItemsEq] at targetCompiled
        | some targetItems =>
          simp [targetItemsEq] at targetCompiled
          subst targetBody
          have targetLocal :
              ConcreteElaboration.localOccurrences
                  (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                    (fun _ => .output)) routeStart =
                (before ++ .child child :: after).map
                  (spawnNodeRaw_oldOccurrence input) := by
            rw [spawnNodeRaw_localOccurrences_old_of_region_ne input
              (.term targetRegion 0 term) scope routeStart 1 (fun _ => .output)
              startNeRegion, localShape]
          have sourceFramed :
              ConcreteElaboration.compileOccurrencesWith? signature input
                (ConcreteElaboration.compileRegion? signature input fuel)
                (source.extend routeStart) binders
                (before ++ .child child :: after) = some sourceItems := by
            rw [← localShape]
            exact sourceItemsEq
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input fuel)
              (source.extend routeStart) binders before after (.child child)
              sourceItems sourceFramed
          have targetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                  (fun _ => .output))
                (ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                    (fun _ => .output)) fuel)
                (target.extend routeStart) binders
                (before.map (spawnNodeRaw_oldOccurrence input) ++
                  spawnNodeRaw_oldOccurrence input (.child child) ::
                  after.map (spawnNodeRaw_oldOccurrence input)) =
                some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← targetLocal]
            exact targetItemsEq
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                  (fun _ => .output)) fuel)
              (target.extend routeStart) binders
              (before.map (spawnNodeRaw_oldOccurrence input))
              (after.map (spawnNodeRaw_oldOccurrence input))
              (spawnNodeRaw_oldOccurrence input (.child child)) targetItems
              targetFramed
          cases fuel with
          | zero =>
              simp [ConcreteElaboration.compileOccurrenceWith?, childIsBubble,
                ConcreteElaboration.compileRegion?] at sourceFocusCompiled
          | succ childFuel =>
            simp only [ConcreteElaboration.compileOccurrenceWith?,
              spawnNodeRaw_oldOccurrence, childIsBubble]
              at sourceFocusCompiled targetFocusCompiled
            rw [show (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                (fun _ => .output)).regions child = input.regions child by rfl,
              childIsBubble] at targetFocusCompiled
            simp only at targetFocusCompiled
            change (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                (fun _ => .output))
              (childFuel + 1) child (target.extend routeStart)
              (binders.push child arity)).bind
                (fun body => some (Item.bubble arity body)) =
                  some targetFocus at targetFocusCompiled
            cases sourceChildEq : ConcreteElaboration.compileRegion? signature
                input (childFuel + 1) child (source.extend routeStart)
                (binders.push child arity) with
            | none => simp [sourceChildEq] at sourceFocusCompiled
            | some sourceChild =>
              simp [sourceChildEq] at sourceFocusCompiled
              subst sourceFocus
              cases targetChildEq : ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                    (fun _ => .output))
                  (childFuel + 1) child (target.extend routeStart)
                  (binders.push child arity) with
              | none => simp [targetChildEq] at targetFocusCompiled
              | some targetChild =>
                simp [targetChildEq] at targetFocusCompiled
                subst targetFocus
                have beforeMap := spawnNodeRaw_compileOccurrencesAwayFromNode
                  input (.term targetRegion 0 term) scope routeStart child 1
                  (fun _ => .output) hinput htarget scopeEnclosesRegion hparent
                  tail (childFuel + 1) source target embedding binders
                  hsourceExact htargetExact before (by
                    intro occurrence member
                    rw [localShape]
                    simp [member]) beforeAway
                rw [sourceBeforeCompiled, targetBeforeCompiled] at beforeMap
                have beforeItems : targetBefore = sourceBefore.renameWires
                    (embedding.extend routeStart).index :=
                  Option.some.inj beforeMap
                have afterMap := spawnNodeRaw_compileOccurrencesAwayFromNode
                  input (.term targetRegion 0 term) scope routeStart child 1
                  (fun _ => .output) hinput htarget scopeEnclosesRegion hparent
                  tail (childFuel + 1) source target embedding binders
                  hsourceExact htargetExact after (by
                    intro occurrence member
                    rw [localShape]
                    simp [member]) afterAway
                rw [sourceAfterCompiled, targetAfterCompiled] at afterMap
                have afterItems : targetAfter = sourceAfter.renameWires
                    (embedding.extend routeStart).index :=
                  Option.some.inj afterMap
                have childFreshGet :
                    (target.extend routeStart).get
                        (target.outerIndex routeStart freshIndex) =
                      Fin.natAdd input.wireCount (0 : Fin 1) :=
                  (ConcreteElaboration.WireContext.extend_outer target
                    routeStart freshIndex).trans freshGet
                have childSemantic := ih htarget scopeEnclosesRegion depthZero
                  scopeEnclosesChild childNeScope childFuel
                  (source.extend routeStart)
                  (target.extend routeStart) (embedding.extend routeStart)
                  (binders.push child arity)
                  (hsourceExact.extend_child hinput hparent)
                  (htargetExact.extend_child htarget hparent)
                  sourceChild targetChild sourceChildEq targetChildEq
                  (target.outerIndex routeStart freshIndex) childFreshGet
                have wireMap : (embedding.extend routeStart).index =
                    spawnNodeRaw_extendedWireMapOfNe embedding routeStart
                      startNeScope := by
                  funext index
                  exact SpawnContextEmbedding.extend_index_eq_map_of_ne
                    embedding routeStart startNeScope htargetExact.nodup index
                have finishMap :
                    ConcreteElaboration.finishRegion
                        (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                          (fun _ => .output)) target routeStart
                        (sourceItems.renameWires
                          (embedding.extend routeStart).index) =
                      (ConcreteElaboration.finishRegion input source routeStart
                        sourceItems).renameWires embedding.index := by
                  rw [wireMap]
                  exact spawnNodeRaw_finishRegion_old_of_ne input
                    (.term targetRegion 0 term) scope routeStart 1
                    (fun _ => .output) source target embedding startNeScope
                    sourceItems
                constructor
                · intro targetDenotes
                  have mapped := finishRegion_denote_mono
                    (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                      (fun _ => .output)) target routeStart targetItems
                    (sourceItems.renameWires
                      (embedding.extend routeStart).index)
                    (by
                      intro currentModel currentNamed rawEnv currentRelEnv
                        itemsDenote
                      rw [targetItemsShape, beforeItems, afterItems,
                        denoteItemSeq_frame] at itemsDenote
                      rw [sourceItemsShape, ItemSeq.renameWires_append,
                        ItemSeq.renameWires, denoteItemSeq_frame]
                      rcases itemsDenote with
                        ⟨beforeDenotes, ⟨relation, childDenotes⟩, afterDenotes⟩
                      refine ⟨beforeDenotes, ?_, afterDenotes⟩
                      refine ⟨relation, ?_⟩
                      have sourceRaw := (childSemantic currentModel currentNamed
                        rawEnv (relation, currentRelEnv)).1 childDenotes
                      exact (denoteRegion_renameWires
                        (relCtx := arity :: rels) currentModel currentNamed
                        (embedding.extend routeStart).index rawEnv
                        (relation, currentRelEnv) sourceChild).2 sourceRaw)
                    model named outerEnv relEnv targetDenotes
                  rw [finishMap] at mapped
                  exact (denoteRegion_renameWires model named embedding.index
                    outerEnv relEnv (ConcreteElaboration.finishRegion input
                      source routeStart sourceItems)).1 mapped
                · intro freshValue sourceDenotes
                  have mapped : denoteRegion model named outerEnv relEnv
                      (ConcreteElaboration.finishRegion
                        (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                          (fun _ => .output)) target routeStart
                        (sourceItems.renameWires
                          (embedding.extend routeStart).index)) := by
                    rw [finishMap]
                    exact (denoteRegion_renameWires model named embedding.index
                      outerEnv relEnv (ConcreteElaboration.finishRegion input
                        source routeStart sourceItems)).2 sourceDenotes
                  apply finishRegion_denote_mono_with_local_at
                    (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                      (fun _ => .output)) target routeStart
                    (sourceItems.renameWires
                      (embedding.extend routeStart).index) targetItems
                    model named outerEnv relEnv _ mapped
                  intro localEnv itemsDenote
                  rw [sourceItemsShape, ItemSeq.renameWires_append,
                    ItemSeq.renameWires, denoteItemSeq_frame] at itemsDenote
                  rw [targetItemsShape, beforeItems, afterItems,
                    denoteItemSeq_frame]
                  rcases itemsDenote with
                    ⟨beforeDenotes, ⟨relation, childDenotes⟩, afterDenotes⟩
                  refine ⟨beforeDenotes, ?_, afterDenotes⟩
                  refine ⟨relation, ?_⟩
                  have childFreshValue :
                      ConcreteElaboration.extendedEnvironment target routeStart
                          outerEnv localEnv
                          (target.outerIndex routeStart freshIndex) =
                        model.eval term Fin.elim0 := by
                    have outerValue :
                        ConcreteElaboration.extendedEnvironment target routeStart
                            outerEnv localEnv
                            (target.outerIndex routeStart freshIndex) =
                          outerEnv freshIndex := by
                      unfold ConcreteElaboration.extendedEnvironment
                      simp only [Function.comp_apply, extendWireEnv]
                      rw [show Fin.cast
                            (ConcreteElaboration.WireContext.length_extend target
                              routeStart)
                            (target.outerIndex routeStart freshIndex) =
                          Fin.castAdd
                            (ConcreteElaboration.exactScopeWires
                              (spawnNodeRaw input (.term targetRegion 0 term) scope 1
                                (fun _ => .output)) routeStart).length
                            freshIndex by
                        apply Fin.ext
                        rfl]
                      exact Fin.addCases_left freshIndex
                    exact outerValue.trans freshValue
                  have sourceRaw := (denoteRegion_renameWires
                    (relCtx := arity :: rels) model named
                    (embedding.extend routeStart).index
                    (ConcreteElaboration.extendedEnvironment target routeStart
                      outerEnv localEnv) (relation, relEnv) sourceChild).1
                      childDenotes
                  exact (childSemantic model named
                    (ConcreteElaboration.extendedEnvironment target routeStart
                      outerEnv localEnv) (relation, relEnv)).2 childFreshValue
                      sourceRaw

/-- At the ancestor wire scope, the fresh local existential is chosen once
and its value is transported through the first bubble into the routed closed
equation. -/
theorem ancestorScope_denote_equiv
    (input : ConcreteDiagram)
    (region scope : Fin input.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (hinput : input.WellFormed signature)
    (htarget : (spawnNodeRaw input (.term region 0 term) scope 1
      (fun _ => .output)).WellFormed signature)
    (scopeEnclosesRegion : input.Encloses scope region)
    (regionNeScope : region ≠ scope)
    {path : List Nat}
    (route : Diagram.Splice.RegionRoute input scope region path)
    {depth : Nat} (routeDepth : route.HasCutDepth depth)
    (depthZero : depth = 0) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (source : ConcreteElaboration.WireContext input)
      (target : ConcreteElaboration.WireContext
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output)))
      (embedding : SpawnContextEmbedding input (.term region 0 term) scope 1
        (fun _ => .output) source target)
      (binders : ConcreteElaboration.BinderContext input rels)
      (hsourceExact : (source.extend scope).Exact scope)
      (htargetExact : (target.extend scope).Exact scope)
      (sourceBody : Region signature source.length rels)
      (targetBody : Region signature target.length rels)
      (sourceCompiled : ConcreteElaboration.compileRegion? signature input
        (fuel + 1) scope source binders = some sourceBody)
      (targetCompiled : ConcreteElaboration.compileRegion? signature
        (spawnNodeRaw input (.term region 0 term) scope 1
          (fun _ => .output))
        (fuel + 1) scope target binders = some targetBody),
      ∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (outerEnv : Fin target.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteRegion model named outerEnv relEnv targetBody ↔
          denoteRegion model named (outerEnv ∘ embedding.index) relEnv
            sourceBody := by
  induction routeDepth with
  | here actualRegion => exact False.elim (regionNeScope rfl)
  | cut childIsCut tailDepth ih => omega
  | @bubble routeStart child targetRegion rest tailDepth arity hparent position
      hposition tail childIsBubble childDepth ih =>
      intro rels fuel source target embedding binders hsourceExact htargetExact
        sourceBody targetBody sourceCompiled targetCompiled model named outerEnv
        relEnv
      simp only [ConcreteElaboration.compileRegion?]
        at sourceCompiled targetCompiled
      cases sourceItemsEq : ConcreteElaboration.compileOccurrencesWith?
          signature input
          (ConcreteElaboration.compileRegion? signature input fuel)
          (source.extend routeStart) binders
          (ConcreteElaboration.localOccurrences input routeStart) with
      | none => simp [sourceItemsEq] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsEq] at sourceCompiled
        subst sourceBody
        cases targetItemsEq : ConcreteElaboration.compileOccurrencesWith?
            signature
            (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
              (fun _ => .output))
            (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                (fun _ => .output)) fuel)
            (target.extend routeStart) binders
            (ConcreteElaboration.localOccurrences
              (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                (fun _ => .output)) routeStart) with
        | none => simp [targetItemsEq] at targetCompiled
        | some targetItems =>
          simp [targetItemsEq] at targetCompiled
          subst targetBody
          obtain ⟨before, after, localShape, beforeAway, afterAway⟩ :=
            localOccurrences_split_at_child input routeStart child position
              hposition
          have targetLocal :
              ConcreteElaboration.localOccurrences
                  (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                    (fun _ => .output)) routeStart =
                (before ++ .child child :: after).map
                  (spawnNodeRaw_oldOccurrence input) := by
            rw [spawnNodeRaw_localOccurrences_old_of_region_ne input
              (.term targetRegion 0 term) routeStart routeStart 1
              (fun _ => .output) (by
                intro equality
                exact regionNeScope equality.symm), localShape]
          have sourceFramed :
              ConcreteElaboration.compileOccurrencesWith? signature input
                (ConcreteElaboration.compileRegion? signature input fuel)
                (source.extend routeStart) binders
                (before ++ .child child :: after) = some sourceItems := by
            rw [← localShape]
            exact sourceItemsEq
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input fuel)
              (source.extend routeStart) binders before after (.child child)
              sourceItems sourceFramed
          have targetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                  (fun _ => .output))
                (ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                    (fun _ => .output)) fuel)
                (target.extend routeStart) binders
                (before.map (spawnNodeRaw_oldOccurrence input) ++
                  spawnNodeRaw_oldOccurrence input (.child child) ::
                  after.map (spawnNodeRaw_oldOccurrence input)) =
                some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← targetLocal]
            exact targetItemsEq
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsShape⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                  (fun _ => .output)) fuel)
              (target.extend routeStart) binders
              (before.map (spawnNodeRaw_oldOccurrence input))
              (after.map (spawnNodeRaw_oldOccurrence input))
              (spawnNodeRaw_oldOccurrence input (.child child)) targetItems
              targetFramed
          cases fuel with
          | zero =>
              simp [ConcreteElaboration.compileOccurrenceWith?, childIsBubble,
                ConcreteElaboration.compileRegion?] at sourceFocusCompiled
          | succ childFuel =>
            simp only [ConcreteElaboration.compileOccurrenceWith?,
              spawnNodeRaw_oldOccurrence, childIsBubble]
              at sourceFocusCompiled targetFocusCompiled
            rw [show (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                (fun _ => .output)).regions child = input.regions child by rfl,
              childIsBubble] at targetFocusCompiled
            simp only at targetFocusCompiled
            change (ConcreteElaboration.compileRegion? signature
              (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                (fun _ => .output))
              (childFuel + 1) child (target.extend routeStart)
              (binders.push child arity)).bind
                (fun body => some (Item.bubble arity body)) =
                  some targetFocus at targetFocusCompiled
            cases sourceChildEq : ConcreteElaboration.compileRegion? signature
                input (childFuel + 1) child (source.extend routeStart)
                (binders.push child arity) with
            | none => simp [sourceChildEq] at sourceFocusCompiled
            | some sourceChild =>
              simp [sourceChildEq] at sourceFocusCompiled
              subst sourceFocus
              cases targetChildEq : ConcreteElaboration.compileRegion? signature
                  (spawnNodeRaw input (.term targetRegion 0 term) routeStart 1
                    (fun _ => .output))
                  (childFuel + 1) child (target.extend routeStart)
                  (binders.push child arity) with
              | none => simp [targetChildEq] at targetFocusCompiled
              | some targetChild =>
                simp [targetChildEq] at targetFocusCompiled
                subst targetFocus
                have beforeMap := spawnNodeRaw_compileOccurrencesAwayFromNode
                  input (.term targetRegion 0 term) routeStart routeStart child 1
                  (fun _ => .output) hinput htarget scopeEnclosesRegion hparent
                  tail (childFuel + 1) source target embedding binders
                  hsourceExact htargetExact before (by
                    intro occurrence member
                    rw [localShape]
                    simp [member]) beforeAway
                rw [sourceBeforeCompiled, targetBeforeCompiled] at beforeMap
                have beforeItems : targetBefore = sourceBefore.renameWires
                    (embedding.extend routeStart).index :=
                  Option.some.inj beforeMap
                have afterMap := spawnNodeRaw_compileOccurrencesAwayFromNode
                  input (.term targetRegion 0 term) routeStart routeStart child 1
                  (fun _ => .output) hinput htarget scopeEnclosesRegion hparent
                  tail (childFuel + 1) source target embedding binders
                  hsourceExact htargetExact after (by
                    intro occurrence member
                    rw [localShape]
                    simp [member]) afterAway
                rw [sourceAfterCompiled, targetAfterCompiled] at afterMap
                have afterItems : targetAfter = sourceAfter.renameWires
                    (embedding.extend routeStart).index :=
                  Option.some.inj afterMap
                let freshIndex := spawnNodeRaw_freshExtendedIndex input
                  (.term targetRegion 0 term) routeStart 1 (fun _ => .output)
                  target 0
                have freshGet : (target.extend routeStart).get freshIndex =
                    Fin.natAdd input.wireCount (0 : Fin 1) := by
                  exact spawnNodeRaw_freshExtendedIndex_get input
                    (.term targetRegion 0 term) routeStart 1
                    (fun _ => .output) target 0
                have scopeEnclosesChild : input.Encloses routeStart child :=
                  AnchoredWireSoundness.split_direct_child_encloses hparent
                have childNeScope : child ≠ routeStart := by
                  intro equality
                  subst child
                  exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
                    hinput hparent) (ConcreteDiagram.Encloses.refl input routeStart)
                have childSemantic := zeroRoute_region_denote_equiv input
                  targetRegion routeStart term hinput htarget scopeEnclosesRegion
                  tail childDepth depthZero scopeEnclosesChild childNeScope
                  childFuel (source.extend routeStart) (target.extend routeStart)
                  (embedding.extend routeStart) (binders.push child arity)
                  (hsourceExact.extend_child hinput hparent)
                  (htargetExact.extend_child htarget hparent)
                  sourceChild targetChild sourceChildEq targetChildEq freshIndex
                  freshGet
                constructor
                · intro targetDenotes
                  refine spawnNodeRaw_finishRegion_site_projects input
                    (.term targetRegion 0 term) routeStart 1
                    (fun _ => .output) source target embedding
                    htargetExact.nodup sourceItems targetItems ?_ model named
                    outerEnv relEnv targetDenotes
                  intro currentModel currentNamed rawEnv currentRelEnv
                    itemsDenote
                  rw [targetItemsShape, beforeItems, afterItems,
                    denoteItemSeq_frame] at itemsDenote
                  rw [sourceItemsShape, ItemSeq.renameWires_append,
                    ItemSeq.renameWires, denoteItemSeq_frame]
                  rcases itemsDenote with
                    ⟨beforeDenotes, ⟨relation, childDenotes⟩, afterDenotes⟩
                  refine ⟨beforeDenotes, ?_, afterDenotes⟩
                  refine ⟨relation, ?_⟩
                  have sourceRaw := (childSemantic currentModel currentNamed
                    rawEnv (relation, currentRelEnv)).1 childDenotes
                  exact (denoteRegion_renameWires
                    (relCtx := arity :: rels) currentModel currentNamed
                    (embedding.extend routeStart).index rawEnv
                    (relation, currentRelEnv) sourceChild).2 sourceRaw
                · intro sourceDenotes
                  refine spawnNodeRaw_finishRegion_site_reflects input
                    (.term targetRegion 0 term) routeStart 1
                    (fun _ => .output) source target embedding
                    htargetExact.nodup sourceItems targetItems model named
                    outerEnv relEnv (fun _ => model.eval term Fin.elim0) ?_
                    sourceDenotes
                  intro rawEnv freshValue itemsDenote
                  rw [sourceItemsShape, ItemSeq.renameWires_append,
                    ItemSeq.renameWires, denoteItemSeq_frame] at itemsDenote
                  rw [targetItemsShape, beforeItems, afterItems,
                    denoteItemSeq_frame]
                  rcases itemsDenote with
                    ⟨beforeDenotes, ⟨relation, childDenotes⟩, afterDenotes⟩
                  refine ⟨beforeDenotes, ?_, afterDenotes⟩
                  refine ⟨relation, ?_⟩
                  have sourceRaw := (denoteRegion_renameWires
                    (relCtx := arity :: rels) model named
                    (embedding.extend routeStart).index rawEnv
                    (relation, relEnv) sourceChild).1 childDenotes
                  exact (childSemantic model named rawEnv (relation, relEnv)).2
                    (freshValue 0) sourceRaw

end RoutedClosedAnchorSoundness

end VisualProof.Rule
