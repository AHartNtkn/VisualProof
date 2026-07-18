import VisualProof.Rule.Soundness.Equational.AnchoredWire

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireSoundness

/-- At the split site, every retained occurrence compiles through the
wire-collapse map.  The only unmatched target occurrence is the freshly
inserted closed-term equation. -/
theorem anchoredWireSplitRaw_compileTargetOld_collapse
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (fuel : Nat)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (originalExact : (original.extend target).Exact target)
    (expandedExact : (expanded.extend target).Exact target)
    (sourceItems : ItemSeq signature (original.extend target).length rels)
    (targetOldItems : ItemSeq signature (expanded.extend target).length rels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (original.extend target) binders
        (ConcreteElaboration.localOccurrences input.val target) =
          some sourceItems)
    (targetOldCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (expanded.extend target) binders
        ((ConcreteElaboration.localOccurrences input.val target).map
          (splitOldOccurrence input)) = some targetOldItems) :
    sourceItems = targetOldItems.renameWires
      (collapse.extend wireEnclosesTarget target expandedExact
        originalExact).indexMap := by
  have mapped := compileOccurrencesWith?_collapse
    (ConcreteElaboration.compileRegion? signature input.val fuel)
    (ConcreteElaboration.compileRegion? signature
      (anchoredWireSplitRaw input wire endpoints target term) fuel)
    (original.extend target) (expanded.extend target) binders binders
    (splitOldOccurrence input)
    (collapse.extend wireEnclosesTarget target expandedExact
      originalExact).indexMap
    (ConcreteElaboration.localOccurrences input.val target)
    (by
      intro occurrence member
      apply anchoredWireSplitRaw_compileOccurrenceWith?_collapse input wire
        endpoints target term selectedOccurs targetWellFormed target
        (expanded.extend target) (original.extend target)
        (collapse.extend wireEnclosesTarget target expandedExact originalExact)
        expandedExact originalExact
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        binders occurrence member
      intro childRels child childBinders occurrenceEq
      subst occurrence
      have childParent :=
        (ConcreteElaboration.mem_localOccurrences_child input.val target child).mp
          member
      have childNotAbove : ¬ input.val.Encloses child target :=
        ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property childParent
      have originalChildExact :=
        originalExact.extend_child input.property childParent
      have targetChildParent :
          ((anchoredWireSplitRaw input wire endpoints target term).regions
            child).parent? = some target := by
        simpa only [anchoredWireSplitRaw_regions] using childParent
      have expandedChildExact :=
        expandedExact.extend_child targetWellFormed targetChildParent
      exact anchoredWireSplitRaw_compileRegion?_collapse_of_not_encloses input
        wire endpoints target term selectedOccurs targetWellFormed
        wireEnclosesTarget fuel child (original.extend target)
        (expanded.extend target)
        (collapse.extend wireEnclosesTarget target expandedExact originalExact)
        childBinders childNotAbove originalChildExact expandedChildExact)
  rw [sourceCompiled, targetOldCompiled] at mapped
  exact Option.some.inj mapped

/-- The unmatched split occurrence is exactly the closed equation assigning
the fresh output wire the denotation of the serialized witness term. -/
theorem anchoredWireSplitRaw_freshOccurrence_denotes_iff
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (context : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (binders : ConcreteElaboration.BinderContext
      (anchoredWireSplitRaw input wire endpoints target term) rels)
    (recurse : ∀ {currentRels : RelCtx},
      (region : Fin input.val.regionCount) →
      (currentContext : ConcreteElaboration.WireContext
        (anchoredWireSplitRaw input wire endpoints target term)) →
      ConcreteElaboration.BinderContext
        (anchoredWireSplitRaw input wire endpoints target term) currentRels →
      Option (Region signature currentContext.length currentRels))
    (freshItems : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (anchoredWireSplitRaw input wire endpoints target term) recurse context
      binders [ConcreteElaboration.LocalOccurrence.node
        (regions := input.val.regionCount) (Fin.last input.val.nodeCount)] =
          some freshItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (rawEnv : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItemSeq model named rawEnv relEnv freshItems ↔
      ∀ output,
        ConcreteElaboration.resolvePort?
          (anchoredWireSplitRaw input wire endpoints target term) context
          (Fin.last input.val.nodeCount) .output = some output →
        rawEnv output = model.eval term Fin.elim0 := by
  simp only [ConcreteElaboration.compileOccurrencesWith?,
    ConcreteElaboration.compileOccurrenceWith?] at compiled
  unfold ConcreteElaboration.compileNode? at compiled
  simp only [anchoredWireSplitRaw_freshNode] at compiled
  cases outputResult : ConcreteElaboration.resolvePort?
      (anchoredWireSplitRaw input wire endpoints target term) context
      (Fin.last input.val.nodeCount) .output with
  | none => simp [outputResult] at compiled
  | some output =>
      simp only [outputResult, Option.bind_some] at compiled
      cases freeResult : ConcreteElaboration.resolvePorts?
          (anchoredWireSplitRaw input wire endpoints target term) context
          (Fin.last input.val.nodeCount) 0 (fun index => .free index) with
      | none => simp [freeResult] at compiled
      | some free =>
          simp only [freeResult] at compiled
          change some (ItemSeq.cons
            (Item.equation output (term.mapFree free)) ItemSeq.nil) =
              some freshItems at compiled
          injection compiled with itemsEq
          subst freshItems
          simp only [denoteItemSeq_cons, denoteItem_equation,
            denoteItemSeq_nil, and_true]
          have freeEq : free = Fin.elim0 := by
            funext index
            exact Fin.elim0 index
          subst free
          rw [model.eval_mapFree]
          have envEq : rawEnv ∘ Fin.elim0 = Fin.elim0 := by
            funext index
            exact Fin.elim0 index
          rw [envEq]
          constructor
          · intro equality candidate candidateResult
            have candidateEq : candidate = output :=
              Option.some.inj candidateResult.symm
            simpa [candidateEq] using equality
          · intro property
            exact property output rfl

private theorem split_target_local_length
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0)) :
    (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) target).length =
      (ConcreteElaboration.exactScopeWires input.val target).length + 1 := by
  rw [anchoredWireSplitRaw_exactScopeWires, if_pos rfl]
  simp [VisualProof.Data.Finite.allFin_eq_finRange]

private theorem split_target_fresh_local_get
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0)) :
    (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) target).get
        (Fin.cast
          (split_target_local_length input wire endpoints target term).symm
          (Fin.last
            (ConcreteElaboration.exactScopeWires input.val target).length)) =
      Fin.last input.val.wireCount := by
  have listEq :
      ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) target =
        (ConcreteElaboration.exactScopeWires input.val target).map
            (Fin.castAdd 1) ++ [Fin.last input.val.wireCount] := by
    rw [anchoredWireSplitRaw_exactScopeWires, if_pos rfl]
    have one : VisualProof.Data.Finite.allFin 1 = [(0 : Fin 1)] := by
      native_decide
    rw [one]
    simp only [List.map_singleton]
    congr 2
  let rightIndex : Fin
      ((ConcreteElaboration.exactScopeWires input.val target).map
          (Fin.castAdd 1) ++ [Fin.last input.val.wireCount]).length :=
    Fin.cast (by simp)
      (Fin.last (ConcreteElaboration.exactScopeWires input.val target).length)
  have getEq := get_of_eq listEq rightIndex
  have indexEq :
      Fin.cast
          (split_target_local_length input wire endpoints target term).symm
          (Fin.last
            (ConcreteElaboration.exactScopeWires input.val target).length) =
        Fin.cast (congrArg List.length listEq).symm rightIndex := by
    apply Fin.ext
    rfl
  rw [indexEq, getEq]
  simp [rightIndex]

private theorem split_target_old_local_get
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input.val target).length) :
    (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) target).get
        (Fin.cast
          (split_target_local_length input wire endpoints target term).symm
          (Fin.castAdd 1 sourceLocal)) =
      ((ConcreteElaboration.exactScopeWires input.val target).get
        sourceLocal).castSucc := by
  have listEq :
      ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) target =
        (ConcreteElaboration.exactScopeWires input.val target).map
            (Fin.castAdd 1) ++ [Fin.last input.val.wireCount] := by
    rw [anchoredWireSplitRaw_exactScopeWires, if_pos rfl]
    have one : VisualProof.Data.Finite.allFin 1 = [(0 : Fin 1)] := by
      native_decide
    rw [one]
    simp only [List.map_singleton]
    congr 2
  let rightIndex : Fin
      ((ConcreteElaboration.exactScopeWires input.val target).map
          (Fin.castAdd 1) ++ [Fin.last input.val.wireCount]).length :=
    Fin.cast (by simp) (Fin.castAdd 1 sourceLocal)
  have getEq := get_of_eq listEq rightIndex
  have indexEq :
      Fin.cast
          (split_target_local_length input wire endpoints target term).symm
          (Fin.castAdd 1 sourceLocal) =
        Fin.cast (congrArg List.length listEq).symm rightIndex := by
    apply Fin.ext
    rfl
  rw [indexEq, getEq]
  simp only [rightIndex, List.get_eq_getElem, Fin.val_cast,
    Fin.val_castAdd]
  have left := List.getElem_append_left
    (as := (ConcreteElaboration.exactScopeWires input.val target).map
      (Fin.castAdd 1))
    (bs := [Fin.last input.val.wireCount]) (i := sourceLocal.val)
    (h' := by simp; omega) (by simpa using sourceLocal.isLt)
  have mapped := List.getElem_map
    (l := ConcreteElaboration.exactScopeWires input.val target)
    (i := sourceLocal.val) (h := by simpa using sourceLocal.isLt)
    (Fin.castAdd 1)
  simpa only [List.get_eq_getElem] using left.trans mapped

/-- The target-local position of an old exact-scope wire collapses to the
corresponding source-local position. -/
theorem SplitContextCollapse.extend_index_local_old_at_target
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (expandedExact : (expanded.extend target).Exact target)
    (originalExact : (original.extend target).Exact target)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input.val target).length) :
    let targetLocal : Fin (ConcreteElaboration.exactScopeWires
        (anchoredWireSplitRaw input wire endpoints target term) target).length :=
      Fin.cast (split_target_local_length input wire endpoints target term).symm
        (Fin.castAdd 1 sourceLocal)
    let targetIndex : Fin (expanded.extend target).length :=
      Fin.cast (ConcreteElaboration.WireContext.length_extend expanded target).symm
        (Fin.natAdd expanded.length targetLocal)
    let sourceIndex : Fin (original.extend target).length :=
      Fin.cast (ConcreteElaboration.WireContext.length_extend original target).symm
        (Fin.natAdd original.length sourceLocal)
    (collapse.extend wireEnclosesTarget target expandedExact
      originalExact).indexMap targetIndex = sourceIndex := by
  dsimp only
  apply Fin.ext
  apply (List.getElem_inj originalExact.nodup).mp
  have targetGet :
      (expanded.extend target).get
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend expanded target).symm
            (Fin.natAdd expanded.length
              (Fin.cast
                (split_target_local_length input wire endpoints target term).symm
                (Fin.castAdd 1 sourceLocal)))) =
        ((ConcreteElaboration.exactScopeWires input.val target).get
          sourceLocal).castSucc := by
    let targetLocal : Fin (ConcreteElaboration.exactScopeWires
        (anchoredWireSplitRaw input wire endpoints target term) target).length :=
      Fin.cast (split_target_local_length input wire endpoints target term).symm
        (Fin.castAdd 1 sourceLocal)
    have listEq :
        ConcreteElaboration.exactScopeWires
            (anchoredWireSplitRaw input wire endpoints target term) target =
          (ConcreteElaboration.exactScopeWires input.val target).map
              (Fin.castAdd 1) ++ [Fin.last input.val.wireCount] := by
      rw [anchoredWireSplitRaw_exactScopeWires, if_pos rfl]
      have one : VisualProof.Data.Finite.allFin 1 = [(0 : Fin 1)] := by
        native_decide
      rw [one]
      simp only [List.map_singleton]
      congr 2
    let rightIndex : Fin
        ((ConcreteElaboration.exactScopeWires input.val target).map
            (Fin.castAdd 1) ++ [Fin.last input.val.wireCount]).length :=
      Fin.cast (by simp) (Fin.castAdd 1 sourceLocal)
    have getEq := get_of_eq listEq rightIndex
    have targetIndexEq :
        targetLocal = Fin.cast (congrArg List.length listEq).symm
          rightIndex := by
      apply Fin.ext
      rfl
    have localGet :
        (ConcreteElaboration.exactScopeWires
          (anchoredWireSplitRaw input wire endpoints target term) target).get
            targetLocal =
          ((ConcreteElaboration.exactScopeWires input.val target).get
            sourceLocal).castSucc := by
      rw [targetIndexEq, getEq]
      simp only [rightIndex, List.get_eq_getElem, Fin.val_cast,
        Fin.val_castAdd]
      have left := List.getElem_append_left
        (as := (ConcreteElaboration.exactScopeWires input.val target).map
          (Fin.castAdd 1))
        (bs := [Fin.last input.val.wireCount]) (i := sourceLocal.val)
        (h' := by simp; omega) (by simpa using sourceLocal.isLt)
      have mapped := List.getElem_map
        (l := ConcreteElaboration.exactScopeWires input.val target)
        (i := sourceLocal.val) (h := by simpa using sourceLocal.isLt)
        (Fin.castAdd 1)
      simpa only [List.get_eq_getElem] using left.trans mapped
    change (expanded ++ ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) target).get _ = _
    simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_natAdd]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simpa only [Nat.add_sub_cancel_left] using localGet
  have sourceGet :
      (original.extend target).get
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend original target).symm
            (Fin.natAdd original.length sourceLocal)) =
        (ConcreteElaboration.exactScopeWires input.val target).get sourceLocal := by
    simp [ConcreteElaboration.WireContext.extend]
  have mappedGet :=
    (collapse.extend wireEnclosesTarget target expandedExact originalExact).get
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend expanded target).symm
        (Fin.natAdd expanded.length
          (Fin.cast
            (split_target_local_length input wire endpoints target term).symm
            (Fin.castAdd 1 sourceLocal))))
  rw [targetGet, splitWireCollapse_old] at mappedGet
  simpa only [List.get_eq_getElem] using mappedGet.trans sourceGet.symm

theorem SplitContextCollapse.extend_oldIndex_inherited_at_target
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (expandedExact : (expanded.extend target).Exact target)
    (originalExact : (original.extend target).Exact target)
    (sourceIndex : Fin original.length) :
    (collapse.extend wireEnclosesTarget target expandedExact
      originalExact).oldIndex
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original target).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.val target).length
            sourceIndex)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend expanded target).symm
        (Fin.castAdd
          (ConcreteElaboration.exactScopeWires
            (anchoredWireSplitRaw input wire endpoints target term)
            target).length
          (collapse.oldIndex sourceIndex)) := by
  apply Fin.ext
  apply (List.getElem_inj expandedExact.nodup).mp
  have oldGet :=
    (collapse.extend wireEnclosesTarget target expandedExact
      originalExact).old_get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original target).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.val target).length
            sourceIndex))
  have sourceGet :
      (original.extend target).get
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend original target).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires input.val target).length
              sourceIndex)) = original.get sourceIndex := by
    simp [ConcreteElaboration.WireContext.extend]
  have targetGet :
      (expanded.extend target).get
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend expanded target).symm
            (Fin.castAdd
              (ConcreteElaboration.exactScopeWires
                (anchoredWireSplitRaw input wire endpoints target term)
                target).length
              (collapse.oldIndex sourceIndex))) =
        expanded.get (collapse.oldIndex sourceIndex) := by
    simp only [ConcreteElaboration.WireContext.extend, List.get_eq_getElem,
      Fin.val_cast, Fin.val_castAdd]
    rw [List.getElem_append_left]
  have rhsGet := targetGet.trans (collapse.old_get sourceIndex)
  rw [sourceGet] at oldGet
  simpa only [List.get_eq_getElem] using oldGet.trans rhsGet.symm

theorem SplitContextCollapse.extend_oldIndex_local_at_target
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (expandedExact : (expanded.extend target).Exact target)
    (originalExact : (original.extend target).Exact target)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input.val target).length) :
    (collapse.extend wireEnclosesTarget target expandedExact
      originalExact).oldIndex
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original target).symm
          (Fin.natAdd original.length sourceLocal)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend expanded target).symm
        (Fin.natAdd expanded.length
          (Fin.cast
            (split_target_local_length input wire endpoints target term).symm
            (Fin.castAdd 1 sourceLocal))) := by
  apply Fin.ext
  apply (List.getElem_inj expandedExact.nodup).mp
  have oldGet :=
    (collapse.extend wireEnclosesTarget target expandedExact
      originalExact).old_get
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend original target).symm
          (Fin.natAdd original.length sourceLocal))
  have sourceGet :
      (original.extend target).get
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend original target).symm
            (Fin.natAdd original.length sourceLocal)) =
        (ConcreteElaboration.exactScopeWires input.val target).get sourceLocal := by
    simp [ConcreteElaboration.WireContext.extend]
  have targetGet :
      (expanded.extend target).get
          (Fin.cast
            (ConcreteElaboration.WireContext.length_extend expanded target).symm
            (Fin.natAdd expanded.length
              (Fin.cast
                (split_target_local_length input wire endpoints target term).symm
                (Fin.castAdd 1 sourceLocal)))) =
        ((ConcreteElaboration.exactScopeWires input.val target).get
          sourceLocal).castSucc := by
    simp only [ConcreteElaboration.WireContext.extend, List.get_eq_getElem,
      Fin.val_cast, Fin.val_natAdd]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem] using
      split_target_old_local_get input wire endpoints target term sourceLocal
  rw [sourceGet] at oldGet
  simpa only [List.get_eq_getElem] using oldGet.trans targetGet.symm

/-- Away from the fresh wire's scope, the retained-old index is also a left
inverse of the collapse.  This is the missing bijectivity fact used by route
frames above the split site: their exact contexts contain only old wires. -/
theorem SplitContextCollapse.oldIndex_indexMap_of_fresh_not_mem
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (expandedNodup : expanded.Nodup)
    (freshNotMem : Fin.last input.val.wireCount ∉ expanded)
    (index : Fin expanded.length) :
    collapse.oldIndex (collapse.indexMap index) = index := by
  refine Fin.lastCases (motive := fun candidate =>
      expanded.get index = candidate →
        collapse.oldIndex (collapse.indexMap index) = index)
    (fun freshEq => ?_) (fun old oldEq => ?_) (expanded.get index) rfl
  · exact False.elim (freshNotMem (freshEq ▸ List.get_mem expanded index))
  · apply Fin.ext
    apply (List.getElem_inj expandedNodup).mp
    have collapsed := collapse.get index
    rw [oldEq, splitWireCollapse_old] at collapsed
    have retained := collapse.old_get (collapse.indexMap index)
    rw [collapsed] at retained
    simpa only [List.get_eq_getElem] using retained.trans oldEq.symm

theorem splitExtendedEnv_outer
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires diagram region).length → D)
    (index : Fin context.length) :
    splitExtendedEnv context region outerEnv localEnv
        (context.outerIndex region index) = outerEnv index := by
  unfold splitExtendedEnv
  simp only [Function.comp_apply]
  have castEq : Fin.cast
      (ConcreteElaboration.WireContext.length_extend context region)
      (context.outerIndex region index) =
        Fin.castAdd
          (ConcreteElaboration.exactScopeWires diagram region).length index := by
    apply Fin.ext
    rfl
  rw [castEq]
  exact Fin.addCases_left index

noncomputable def splitSourceLocalEnvAtTarget
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) target).length → D) :
    Fin (ConcreteElaboration.exactScopeWires input.val target).length → D :=
  fun sourceLocal => targetLocal
    (Fin.cast (split_target_local_length input wire endpoints target term).symm
      (Fin.castAdd 1 sourceLocal))

theorem splitExtendedEnv_oldIndex_at_target
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (expandedExact : (expanded.extend target).Exact target)
    (originalExact : (original.extend target).Exact target)
    (sourceOuter : Fin original.length → D)
    (targetOuter : Fin expanded.length → D)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) target).length → D)
    (sourceIndex : Fin (original.extend target).length) :
    splitExtendedEnv original target sourceOuter
        (splitSourceLocalEnvAtTarget input wire endpoints target term targetLocal)
        sourceIndex =
      splitExtendedEnv expanded target targetOuter targetLocal
        ((collapse.extend wireEnclosesTarget target expandedExact
          originalExact).oldIndex sourceIndex) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend original target) sourceIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend original target).symm split =
        sourceIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun sourceLocal => ?_) split
  · have mapped := collapse.extend_oldIndex_inherited_at_target
      wireEnclosesTarget expandedExact originalExact inherited
    rw [mapped]
    have originalNodup : original.Nodup :=
      (List.nodup_append.mp originalExact.nodup).1
    have indexRight := collapse.indexMap_oldIndex originalNodup inherited
    have agreesAt := congrFun outerAgrees (collapse.oldIndex inherited)
    change sourceOuter (collapse.indexMap (collapse.oldIndex inherited)) =
      targetOuter (collapse.oldIndex inherited) at agreesAt
    rw [indexRight] at agreesAt
    simpa [splitExtendedEnv, extendWireEnv] using agreesAt
  · have mapped := collapse.extend_oldIndex_local_at_target
      wireEnclosesTarget expandedExact originalExact sourceLocal
    rw [mapped]
    simp [splitExtendedEnv, splitSourceLocalEnvAtTarget, extendWireEnv]

/-- At the split site, a target valuation coalesces to a source valuation once
the old and fresh wire positions are both known to carry the witness term. -/
theorem splitExtendedEnv_uncollapse_at_target
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (expandedExact : (expanded.extend target).Exact target)
    (originalExact : (original.extend target).Exact target)
    (sourceOuter : Fin original.length → D)
    (targetOuter : Fin expanded.length → D)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (anchoredWireSplitRaw input wire endpoints target term) target).length → D)
    (termValue : D)
    (sourceOldValue : ∀ sourceIndex,
      (original.extend target).get sourceIndex = wire →
      splitExtendedEnv original target sourceOuter
        (splitSourceLocalEnvAtTarget input wire endpoints target term
          targetLocal) sourceIndex = termValue)
    (targetFreshValue : ∀ targetIndex,
      (expanded.extend target).get targetIndex = Fin.last input.val.wireCount →
      splitExtendedEnv expanded target targetOuter targetLocal targetIndex =
        termValue) :
    splitExtendedEnv original target sourceOuter
          (splitSourceLocalEnvAtTarget input wire endpoints target term
            targetLocal) ∘
        (collapse.extend wireEnclosesTarget target expandedExact
          originalExact).indexMap =
      splitExtendedEnv expanded target targetOuter targetLocal := by
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend expanded target) targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend expanded target).symm
      split = targetIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun targetLocalIndex => ?_) split
  · have mapped := collapse.extend_index_inherited wireEnclosesTarget target
      expandedExact originalExact inherited
    simp only [Function.comp_apply, splitExtendedEnv, extendWireEnv]
    rw [mapped]
    simpa [Function.comp_def] using congrFun outerAgrees inherited
  · let localSplit : Fin
        ((ConcreteElaboration.exactScopeWires input.val target).length + 1) :=
      Fin.cast (split_target_local_length input wire endpoints target term)
        targetLocalIndex
    have localRecover :
        Fin.cast
            (split_target_local_length input wire endpoints target term).symm
            localSplit = targetLocalIndex := by
      apply Fin.ext
      rfl
    refine Fin.lastCases (motive := fun current =>
        localSplit = current →
        (splitExtendedEnv original target sourceOuter
              (splitSourceLocalEnvAtTarget input wire endpoints target term
                targetLocal) ∘
            (collapse.extend wireEnclosesTarget target expandedExact
              originalExact).indexMap)
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend expanded target).symm
              (Fin.natAdd expanded.length targetLocalIndex)) =
          splitExtendedEnv expanded target targetOuter targetLocal
            (Fin.cast
              (ConcreteElaboration.WireContext.length_extend expanded target).symm
              (Fin.natAdd expanded.length targetLocalIndex)))
      ?_ (fun sourceLocal localEq => ?_) localSplit rfl
    · intro localEq
      have targetLocalEq : targetLocalIndex =
          Fin.cast
            (split_target_local_length input wire endpoints target term).symm
            (Fin.last
              (ConcreteElaboration.exactScopeWires input.val target).length) := by
        rw [← localRecover, localEq]
      let freshIndex : Fin (expanded.extend target).length :=
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend expanded target).symm
          (Fin.natAdd expanded.length targetLocalIndex)
      have freshGet : (expanded.extend target).get freshIndex =
          Fin.last input.val.wireCount := by
        have targetLocalGet :
            (ConcreteElaboration.exactScopeWires
              (anchoredWireSplitRaw input wire endpoints target term) target).get
                targetLocalIndex = Fin.last input.val.wireCount :=
          (congrArg
            (ConcreteElaboration.exactScopeWires
              (anchoredWireSplitRaw input wire endpoints target term) target).get
            targetLocalEq).trans
              (split_target_fresh_local_get input wire endpoints target term)
        simp only [freshIndex]
        simp only [ConcreteElaboration.WireContext.extend,
          List.get_eq_getElem, Fin.val_cast, Fin.val_natAdd]
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem] using
          targetLocalGet
      have sourceGet :=
        (collapse.extend wireEnclosesTarget target expandedExact
          originalExact).get freshIndex
      rw [freshGet, splitWireCollapse_fresh] at sourceGet
      exact (sourceOldValue _ sourceGet).trans
        (targetFreshValue freshIndex freshGet).symm
    · have targetLocalEq : targetLocalIndex =
          Fin.cast
            (split_target_local_length input wire endpoints target term).symm
            (Fin.castAdd 1 sourceLocal) := by
        rw [← localRecover, localEq]
        apply Fin.ext
        rfl
      have mapped := collapse.extend_index_local_old_at_target
        wireEnclosesTarget expandedExact originalExact sourceLocal
      simp only at mapped
      simp only [Function.comp_apply]
      rw [targetLocalEq, mapped]
      simp [splitExtendedEnv, splitSourceLocalEnvAtTarget, Function.comp_def,
        extendWireEnv]

/-- Semantic equivalence at the unique split site, assuming the retained
witness equation has already identified the old wire with the serialized
closed term in each directional environment. -/
theorem anchoredWireSplitRaw_target_site_equiv
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    (fuel : Nat)
    (original : ConcreteElaboration.WireContext input.val)
    (expanded : ConcreteElaboration.WireContext
      (anchoredWireSplitRaw input wire endpoints target term))
    (collapse : SplitContextCollapse input wire endpoints target term
      expanded original)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (originalExact : (original.extend target).Exact target)
    (expandedExact : (expanded.extend target).Exact target)
    (sourceItems : ItemSeq signature (original.extend target).length rels)
    (targetItems : ItemSeq signature (expanded.extend target).length rels)
    (sourceCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
        (ConcreteElaboration.compileRegion? signature input.val fuel)
        (original.extend target) binders
        (ConcreteElaboration.localOccurrences input.val target) =
          some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (expanded.extend target) binders
        (ConcreteElaboration.localOccurrences
          (anchoredWireSplitRaw input wire endpoints target term) target) =
          some targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceOuter : Fin original.length → model.Carrier)
    (targetOuter : Fin expanded.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
    (sourceWitness : ∀ sourceLocal,
      denoteItemSeq model named
          (splitExtendedEnv original target sourceOuter sourceLocal)
          relEnv sourceItems →
      ∀ sourceIndex, (original.extend target).get sourceIndex = wire →
        splitExtendedEnv original target sourceOuter sourceLocal sourceIndex =
          model.eval term Fin.elim0)
    (targetWitness : ∀ targetLocal,
      denoteItemSeq model named
          (splitExtendedEnv expanded target targetOuter targetLocal)
          relEnv targetItems →
      ∀ targetIndex,
        (expanded.extend target).get targetIndex = wire.castSucc →
        splitExtendedEnv expanded target targetOuter targetLocal targetIndex =
          model.eval term Fin.elim0) :
    denoteRegion model named sourceOuter relEnv
        (ConcreteElaboration.finishRegion input.val original target sourceItems) ↔
      denoteRegion model named targetOuter relEnv
        (ConcreteElaboration.finishRegion
          (anchoredWireSplitRaw input wire endpoints target term) expanded
          target targetItems) := by
  let sourceNodes :=
    (filterFin fun old => decide ((input.val.nodes old).region = target)).map
      (fun old => ConcreteElaboration.LocalOccurrence.node
        (regions := input.val.regionCount) old)
  let sourceChildren :=
    (filterFin fun child =>
      decide ((input.val.regions child).parent? = some target)).map
        (ConcreteElaboration.LocalOccurrence.child (nodes := input.val.nodeCount))
  let targetBefore := sourceNodes.map (splitOldOccurrence input)
  let targetAfter := sourceChildren.map (splitOldOccurrence input)
  let fresh : ConcreteElaboration.LocalOccurrence input.val.regionCount
      (input.val.nodeCount + 1) := .node (Fin.last input.val.nodeCount)
  have sourceOccurrences :
      ConcreteElaboration.localOccurrences input.val target =
        sourceNodes ++ sourceChildren := by rfl
  have targetOccurrences :
      ConcreteElaboration.localOccurrences
          (anchoredWireSplitRaw input wire endpoints target term) target =
        targetBefore ++ fresh :: targetAfter := by
    rw [anchoredWireSplitRaw_localOccurrences_at_target]
    simp [sourceNodes, sourceChildren, targetBefore, targetAfter, fresh,
      splitOldOccurrence, Function.comp_def]
  have targetFramed :
      ConcreteElaboration.compileOccurrencesWith? signature
          (anchoredWireSplitRaw input wire endpoints target term)
          (ConcreteElaboration.compileRegion? signature
            (anchoredWireSplitRaw input wire endpoints target term) fuel)
          (expanded.extend target) binders
          (targetBefore ++ fresh :: targetAfter) = some targetItems := by
    rw [← targetOccurrences]
    exact targetCompiled
  obtain ⟨targetBeforeItems, freshItem, targetAfterItems,
      beforeCompiled, freshCompiled, afterCompiled, targetItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature
        (anchoredWireSplitRaw input wire endpoints target term) fuel)
      (expanded.extend target) binders targetBefore targetAfter fresh targetItems
      targetFramed
  let targetOldItems := targetBeforeItems.append targetAfterItems
  have targetOldCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (anchoredWireSplitRaw input wire endpoints target term)
          (ConcreteElaboration.compileRegion? signature
            (anchoredWireSplitRaw input wire endpoints target term) fuel)
          (expanded.extend target) binders
          ((ConcreteElaboration.localOccurrences input.val target).map
            (splitOldOccurrence input)) = some targetOldItems := by
    rw [sourceOccurrences, List.map_append]
    change ConcreteElaboration.compileOccurrencesWith? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (expanded.extend target) binders (targetBefore ++ targetAfter) =
          some targetOldItems
    exact ConcreteElaboration.compileOccurrencesWith?_append
      (ConcreteElaboration.compileRegion? signature
        (anchoredWireSplitRaw input wire endpoints target term) fuel)
      (expanded.extend target) binders targetBefore targetAfter
      targetBeforeItems targetAfterItems beforeCompiled afterCompiled
  have oldCollapse := anchoredWireSplitRaw_compileTargetOld_collapse input wire
    endpoints target term selectedOccurs targetWellFormed wireEnclosesTarget
    fuel original expanded collapse binders originalExact expandedExact
    sourceItems targetOldItems sourceCompiled targetOldCompiled
  have freshListCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (anchoredWireSplitRaw input wire endpoints target term)
          (ConcreteElaboration.compileRegion? signature
            (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (expanded.extend target) binders [fresh] =
        some (.cons freshItem .nil) := by
    simp [ConcreteElaboration.compileOccurrencesWith?, freshCompiled]
  have freshOccurs :
      (anchoredWireSplitRaw input wire endpoints target term).EndpointOccurs
        (Fin.last input.val.wireCount)
        { node := Fin.last input.val.nodeCount, port := .output } := by
    unfold ConcreteDiagram.EndpointOccurs
    simp only [anchoredWireSplitRaw, Fin.lastCases_last]
    exact List.mem_cons_self
  constructor
  · intro sourceDenotes
    unfold ConcreteElaboration.finishRegion at sourceDenotes ⊢
    simp only [denoteRegion_mk] at sourceDenotes ⊢
    obtain ⟨sourceLocal, sourceCastDenotes⟩ := sourceDenotes
    refine ⟨splitTargetLocalEnv collapse wireEnclosesTarget target expandedExact
      originalExact sourceOuter sourceLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceCastDenotes ⊢
    let sourceRaw := splitExtendedEnv original target sourceOuter sourceLocal
    let targetLocal := splitTargetLocalEnv collapse wireEnclosesTarget target
      expandedExact originalExact sourceOuter sourceLocal
    let targetRaw := splitExtendedEnv expanded target targetOuter targetLocal
    have sourceRawDenotes := (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend original target))
      (extendWireEnv sourceOuter sourceLocal) relEnv sourceItems).mp
        sourceCastDenotes
    change denoteItemSeq model named sourceRaw relEnv sourceItems at sourceRawDenotes
    have envCollapse := splitExtendedEnv_collapse collapse wireEnclosesTarget
      target expandedExact originalExact sourceOuter sourceLocal
    rw [outerAgrees] at envCollapse
    change sourceRaw ∘
        (collapse.extend wireEnclosesTarget target expandedExact
          originalExact).indexMap = targetRaw at envCollapse
    have oldRenamedDenotes : denoteItemSeq model named sourceRaw relEnv
        (targetOldItems.renameWires
          (collapse.extend wireEnclosesTarget target expandedExact
            originalExact).indexMap) := by
      rw [← oldCollapse]
      exact sourceRawDenotes
    have oldDenotes : denoteItemSeq model named targetRaw relEnv
        targetOldItems := by
      rw [← envCollapse]
      exact (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget target expandedExact
          originalExact).indexMap sourceRaw relEnv targetOldItems).mp
            oldRenamedDenotes
    have sourceEquation := sourceWitness sourceLocal sourceRawDenotes
    have freshDenotes : denoteItemSeq model named targetRaw relEnv
        (.cons freshItem .nil) := by
      apply (anchoredWireSplitRaw_freshOccurrence_denotes_iff input wire
        endpoints target term (expanded.extend target) binders
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (.cons freshItem .nil) freshListCompiled model named targetRaw relEnv).2
      intro output outputResult
      obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
        ConcreteElaboration.resolvePort?_sound outputResult
      have outputWireEq : outputWire = Fin.last input.val.wireCount :=
        ConcreteElaboration.endpoint_wire_unique
          targetWellFormed.wire_endpoints_are_disjoint outputOccurs freshOccurs
      rw [outputWireEq] at outputGet
      have collapseGet :=
        (collapse.extend wireEnclosesTarget target expandedExact
          originalExact).get output
      change (expanded.extend target).get output =
        Fin.last input.val.wireCount at outputGet
      rw [outputGet, splitWireCollapse_fresh] at collapseGet
      have sourceValue := sourceEquation _ collapseGet
      have targetValue := congrFun envCollapse output
      exact targetValue.symm.trans sourceValue
    have targetRawDenotes : denoteItemSeq model named targetRaw relEnv
        targetItems := by
      rw [targetItemsEq, denoteItemSeq_frame]
      rw [denoteItemSeq_append] at oldDenotes
      exact ⟨oldDenotes.1, freshDenotes.1, oldDenotes.2⟩
    apply (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend expanded target))
      (extendWireEnv targetOuter targetLocal) relEnv targetItems).mpr
    change denoteItemSeq model named targetRaw relEnv targetItems
    exact targetRawDenotes
  · intro targetDenotes
    unfold ConcreteElaboration.finishRegion at targetDenotes ⊢
    simp only [denoteRegion_mk] at targetDenotes ⊢
    obtain ⟨targetLocal, targetCastDenotes⟩ := targetDenotes
    refine ⟨splitSourceLocalEnvAtTarget input wire endpoints target term
      targetLocal, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at targetCastDenotes ⊢
    let targetRaw := splitExtendedEnv expanded target targetOuter targetLocal
    let sourceLocal := splitSourceLocalEnvAtTarget input wire endpoints target
      term targetLocal
    let sourceRaw := splitExtendedEnv original target sourceOuter sourceLocal
    have targetRawDenotes := (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend expanded target))
      (extendWireEnv targetOuter targetLocal) relEnv targetItems).mp
        targetCastDenotes
    change denoteItemSeq model named targetRaw relEnv targetItems at targetRawDenotes
    have targetEquation := targetWitness targetLocal targetRawDenotes
    have targetFrame : denoteItemSeq model named targetRaw relEnv
        (targetBeforeItems.append (.cons freshItem targetAfterItems)) := by
      rw [← targetItemsEq]
      exact targetRawDenotes
    rw [denoteItemSeq_frame] at targetFrame
    have freshDenotes : denoteItemSeq model named targetRaw relEnv
        (.cons freshItem .nil) := by
      simpa [denoteItemSeq_append] using targetFrame.2.1
    have freshEquation :=
      (anchoredWireSplitRaw_freshOccurrence_denotes_iff input wire endpoints
        target term (expanded.extend target) binders
        (ConcreteElaboration.compileRegion? signature
          (anchoredWireSplitRaw input wire endpoints target term) fuel)
        (.cons freshItem .nil) freshListCompiled model named targetRaw relEnv).1
          freshDenotes
    have oldDenotes : denoteItemSeq model named targetRaw relEnv
        targetOldItems := by
      rw [denoteItemSeq_append]
      exact ⟨targetFrame.1, targetFrame.2.2⟩
    obtain ⟨freshOutput, freshOutputResult⟩ :=
      ConcreteElaboration.resolvePort?_complete expandedExact.covers
        targetWellFormed.wire_scopes_enclose (by
          exact anchoredWireSplitRaw_freshNode input wire endpoints target term ▸
            rfl) ⟨Fin.last input.val.wireCount, freshOccurs⟩
    have envCollapse := splitExtendedEnv_uncollapse_at_target collapse
      wireEnclosesTarget expandedExact originalExact sourceOuter targetOuter
      outerAgrees targetLocal (model.eval term Fin.elim0)
      (by
        intro sourceIndex sourceGet
        have oldIndexGet :=
          (collapse.extend wireEnclosesTarget target expandedExact
            originalExact).old_get sourceIndex
        rw [sourceGet] at oldIndexGet
        have targetValue := targetEquation _ oldIndexGet
        exact (splitExtendedEnv_oldIndex_at_target collapse wireEnclosesTarget
          expandedExact originalExact sourceOuter targetOuter outerAgrees
          targetLocal sourceIndex).trans targetValue)
      (by
        intro freshIndex freshGet
        have outputValue := freshEquation freshOutput freshOutputResult
        obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
          ConcreteElaboration.resolvePort?_sound freshOutputResult
        have outputWireEq : outputWire = Fin.last input.val.wireCount :=
          ConcreteElaboration.endpoint_wire_unique
            targetWellFormed.wire_endpoints_are_disjoint outputOccurs
              freshOccurs
        rw [outputWireEq] at outputGet
        have indexEq : freshIndex = freshOutput := by
          apply Fin.ext
          exact (List.getElem_inj expandedExact.nodup).mp (by
            simpa only [List.get_eq_getElem] using
              freshGet.trans outputGet.symm)
        simpa [indexEq] using outputValue)
    change sourceRaw ∘
        (collapse.extend wireEnclosesTarget target expandedExact
          originalExact).indexMap = targetRaw at envCollapse
    have sourceRenamedDenotes : denoteItemSeq model named sourceRaw relEnv
        (targetOldItems.renameWires
          (collapse.extend wireEnclosesTarget target expandedExact
            originalExact).indexMap) := by
      apply (denoteItemSeq_renameWires model named
        (collapse.extend wireEnclosesTarget target expandedExact
          originalExact).indexMap sourceRaw relEnv targetOldItems).mpr
      rw [envCollapse]
      exact oldDenotes
    rw [← oldCollapse] at sourceRenamedDenotes
    apply (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend original target))
      (extendWireEnv sourceOuter sourceLocal) relEnv sourceItems).mpr
    change denoteItemSeq model named sourceRaw relEnv sourceItems
    exact sourceRenamedDenotes

/-- The executor-retained closed witness equation forces the old wire to the
serialized term value throughout the complete availability-site context. -/
theorem anchoredWireSplit_witness_value_of_zero_route
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (witness : Fin input.val.nodeCount)
    (witnessRegion : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (witnessShape : input.val.nodes witness = .term witnessRegion 0 term)
    (witnessOccurs : input.val.EndpointOccurs wire
      { node := witness, port := .output })
    {available : Fin input.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val available witnessRegion path)
    (routeZero : route.HasCutDepth 0)
    {rels : RelCtx}
    (context : ConcreteElaboration.WireContext input.val)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (fuel : Nat)
    (items : ItemSeq signature (context.extend available).length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature input.val
      (ConcreteElaboration.compileRegion? signature input.val fuel)
      (context.extend available) binders
      (ConcreteElaboration.localOccurrences input.val available) = some items)
    (exact : (context.extend available).Exact available)
    (bindersCover : binders.Covers available)
    (binderEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val binders available)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (outerEnv : Fin context.length → model.Carrier)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires
      input.val available).length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (itemsDenote : denoteItemSeq model named
      (ConcreteElaboration.extendedEnvironment context available outerEnv localEnv)
      relEnv items) :
    ∀ index, (context.extend available).get index = wire →
      ConcreteElaboration.extendedEnvironment context available outerEnv localEnv
          index = model.eval term Fin.elim0 := by
  obtain ⟨descendant⟩ := CongruenceSoundness.denoted_descendant_leaf input
    route routeZero context binders fuel items compiled exact bindersCover
    binderEnumeration model named outerEnv localEnv relEnv itemsDenote
  obtain ⟨output, free, outputResolved, _, outputEquation⟩ :=
    CongruenceSoundness.compiled_term_node_equation descendant.leaf witness 0
      term witnessShape model named
      (ConcreteElaboration.extendedEnvironment descendant.leaf.inheritedWires
        witnessRegion descendant.outerEnv descendant.localEnv)
      descendant.relEnv descendant.itemsDenote
  obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
    ConcreteElaboration.resolvePort?_sound outputResolved
  have outputWireEq : outputWire = wire :=
    ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint outputOccurs witnessOccurs
  rw [outputWireEq] at outputGet
  have closedEquation :
      ConcreteElaboration.extendedEnvironment descendant.leaf.inheritedWires
          witnessRegion descendant.outerEnv descendant.localEnv output =
        model.eval term Fin.elim0 := by
    have freeEq : free = Fin.elim0 := by
      funext index
      exact Fin.elim0 index
    subst free
    have envEq :
        ConcreteElaboration.extendedEnvironment descendant.leaf.inheritedWires
            witnessRegion descendant.outerEnv descendant.localEnv ∘ Fin.elim0 =
          Fin.elim0 := by
      funext index
      exact Fin.elim0 index
    rw [envEq] at outputEquation
    exact outputEquation
  intro index indexGet
  exact (descendant.agrees index output
    (indexGet.trans outputGet.symm)).trans closedEquation

/-- Once the witness value is present in the inherited context, semantic
equivalence propagates down every executor route to the split site.  Cuts
reverse both implications and bubbles preserve them, so no polarity
restriction is needed. -/
theorem anchoredWireSplitRaw_compileRegion_route_equiv_of_inherited
    (input : CheckedDiagram signature) (wire : Fin input.val.wireCount)
    (endpoints : List (CEndpoint input.val.nodeCount))
    (target : Fin input.val.regionCount)
    (term : Lambda.Term 0 (Fin 0))
    (selectedOccurs : ∀ endpoint, endpoint ∈ endpoints →
      input.val.EndpointOccurs wire endpoint)
    (targetWellFormed :
      (anchoredWireSplitRaw input wire endpoints target term).WellFormed
        signature)
    (wireEnclosesTarget :
      input.val.Encloses (input.val.wires wire).scope target)
    {start : Fin input.val.regionCount} {path : List Nat}
    (route : Diagram.Splice.RegionRoute input.val start target path) :
    ∀ {rels : RelCtx} (fuel : Nat)
      (original : ConcreteElaboration.WireContext input.val)
      (expanded : ConcreteElaboration.WireContext
        (anchoredWireSplitRaw input wire endpoints target term))
      (collapse : SplitContextCollapse input wire endpoints target term
        expanded original)
      (binders : ConcreteElaboration.BinderContext input.val rels)
      (originalExact : (original.extend start).Exact start)
      (expandedExact : (expanded.extend start).Exact start)
      (sourceWire : Fin original.length)
      (sourceWireGet : original.get sourceWire = wire)
      (sourceBody : Region signature original.length rels)
      (targetBody : Region signature expanded.length rels)
      (sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
        (fuel + 1) start original binders = some sourceBody)
      (targetCompiled : ConcreteElaboration.compileRegion? signature
        (anchoredWireSplitRaw input wire endpoints target term)
        (fuel + 1) start expanded binders = some targetBody)
      (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (sourceOuter : Fin original.length → model.Carrier)
      (targetOuter : Fin expanded.length → model.Carrier)
      (relEnv : RelEnv model.Carrier rels)
      (outerAgrees : sourceOuter ∘ collapse.indexMap = targetOuter)
      (sourceWireValue : sourceOuter sourceWire = model.eval term Fin.elim0),
      denoteRegion model named sourceOuter relEnv sourceBody ↔
        denoteRegion model named targetOuter relEnv targetBody := by
  induction route with
  | here region =>
      intro rels fuel original expanded collapse binders originalExact
        expandedExact sourceWire sourceWireGet sourceBody targetBody
        sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
        outerAgrees sourceWireValue
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuel)
            (original.extend region) binders
            (ConcreteElaboration.localOccurrences input.val region) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
          simp [sourceItemsResult] at sourceCompiled
          subst sourceBody
          cases targetItemsResult :
              ConcreteElaboration.compileOccurrencesWith? signature
                (anchoredWireSplitRaw input wire endpoints region term)
                (ConcreteElaboration.compileRegion? signature
                  (anchoredWireSplitRaw input wire endpoints region term) fuel)
                (expanded.extend region) binders
                (ConcreteElaboration.localOccurrences
                  (anchoredWireSplitRaw input wire endpoints region term) region) with
          | none => simp [targetItemsResult] at targetCompiled
          | some targetItems =>
              simp [targetItemsResult] at targetCompiled
              subst targetBody
              apply anchoredWireSplitRaw_target_site_equiv input wire endpoints
                region term selectedOccurs targetWellFormed wireEnclosesTarget
                fuel original expanded collapse binders originalExact
                expandedExact sourceItems targetItems sourceItemsResult
                targetItemsResult model named sourceOuter targetOuter relEnv
                outerAgrees
              · intro sourceLocal _ sourceIndex sourceGet
                have chosenGet : (original.extend region).get
                    (original.outerIndex region sourceWire) = wire := by
                  simpa only [List.get_eq_getElem] using
                    (original.extend_outer region sourceWire).trans sourceWireGet
                have indexEq : sourceIndex = original.outerIndex region sourceWire := by
                  apply Fin.ext
                  exact (List.getElem_inj originalExact.nodup).mp (by
                    simpa only [List.get_eq_getElem] using
                      sourceGet.trans chosenGet.symm)
                rw [indexEq, splitExtendedEnv_outer]
                exact sourceWireValue
              · intro targetLocal _ targetIndex targetGet
                let targetWire := collapse.oldIndex sourceWire
                have targetWireGet : expanded.get targetWire = wire.castSucc := by
                  have retained := collapse.old_get sourceWire
                  rw [sourceWireGet] at retained
                  exact retained
                have chosenGet : (expanded.extend region).get
                    (expanded.outerIndex region targetWire) = wire.castSucc := by
                  simpa only [List.get_eq_getElem] using
                    (expanded.extend_outer region targetWire).trans targetWireGet
                have indexEq : targetIndex = expanded.outerIndex region targetWire := by
                  apply Fin.ext
                  exact (List.getElem_inj expandedExact.nodup).mp (by
                    simpa only [List.get_eq_getElem] using
                      targetGet.trans chosenGet.symm)
                rw [indexEq, splitExtendedEnv_outer]
                have agreesAt := congrFun outerAgrees targetWire
                change sourceOuter
                    (collapse.indexMap (collapse.oldIndex sourceWire)) =
                  targetOuter targetWire at agreesAt
                rw [collapse.indexMap_oldIndex
                  (List.nodup_append.mp originalExact.nodup).1 sourceWire]
                  at agreesAt
                exact agreesAt.symm.trans sourceWireValue
  | @step start child targetRegion rest hparent position hposition tail ih =>
      intro rels fuel original expanded collapse binders originalExact
        expandedExact sourceWire sourceWireGet sourceBody targetBody
        sourceCompiled targetCompiled model named sourceOuter targetOuter relEnv
        outerAgrees sourceWireValue
      have startNe : start ≠ targetRegion := by
        intro equality
        subst start
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property hparent) (regionRoute_encloses input.val input.property tail)
      obtain ⟨before, after, localEq, beforeAway, afterAway⟩ :=
        localOccurrences_split_at_child input.val start child position hposition
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val fuel)
            (original.extend start) binders
            (ConcreteElaboration.localOccurrences input.val start) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        cases targetItemsResult :
            ConcreteElaboration.compileOccurrencesWith? signature
              (anchoredWireSplitRaw input wire endpoints targetRegion term)
              (ConcreteElaboration.compileRegion? signature
                (anchoredWireSplitRaw input wire endpoints targetRegion term) fuel)
              (expanded.extend start) binders
              (ConcreteElaboration.localOccurrences
                (anchoredWireSplitRaw input wire endpoints targetRegion term) start) with
        | none => simp [targetItemsResult] at targetCompiled
        | some targetItems =>
          simp [targetItemsResult] at targetCompiled
          subst targetBody
          have targetLocalEq :
              ConcreteElaboration.localOccurrences
                  (anchoredWireSplitRaw input wire endpoints targetRegion term) start =
                (before ++ .child child :: after).map
                  (splitOldOccurrence input) := by
            rw [anchoredWireSplitRaw_localOccurrences_of_ne input wire endpoints
              targetRegion start term startNe, localEq]
          have sourceFramed :
              ConcreteElaboration.compileOccurrencesWith? signature input.val
                (ConcreteElaboration.compileRegion? signature input.val fuel)
                (original.extend start) binders
                (before ++ .child child :: after) = some sourceItems := by
            rw [← localEq]
            exact sourceItemsResult
          obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
              sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature input.val fuel)
              (original.extend start) binders before after (.child child)
              sourceItems sourceFramed
          have targetFramed :
              ConcreteElaboration.compileOccurrencesWith? signature
                (anchoredWireSplitRaw input wire endpoints targetRegion term)
                (ConcreteElaboration.compileRegion? signature
                  (anchoredWireSplitRaw input wire endpoints targetRegion term) fuel)
                (expanded.extend start) binders
                (before.map (splitOldOccurrence input) ++
                  splitOldOccurrence input (.child child) ::
                  after.map (splitOldOccurrence input)) = some targetItems := by
            rw [← List.map_cons, ← List.map_append, ← targetLocalEq]
            exact targetItemsResult
          obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
              targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
            compileOccurrencesWith?_frame_split
              (ConcreteElaboration.compileRegion? signature
                (anchoredWireSplitRaw input wire endpoints targetRegion term) fuel)
              (expanded.extend start) binders
              (before.map (splitOldOccurrence input))
              (after.map (splitOldOccurrence input))
              (splitOldOccurrence input (.child child)) targetItems targetFramed
          cases fuel with
          | zero =>
              cases kind : input.val.regions child <;>
                simp [ConcreteElaboration.compileOccurrenceWith?, kind,
                  ConcreteElaboration.compileRegion?] at sourceFocusCompiled
          | succ childFuel =>
            have beforeMap := anchoredWireSplitRaw_compileOccurrencesAway input
              wire endpoints targetRegion start child term selectedOccurs
              targetWellFormed wireEnclosesTarget hparent tail (childFuel + 1)
              original expanded collapse binders originalExact expandedExact
              before (by
                intro occurrence member
                rw [localEq]
                simp [member]) beforeAway
            rw [sourceBeforeCompiled, targetBeforeCompiled] at beforeMap
            have beforeEq : sourceBefore = targetBefore.renameWires
                (collapse.extend wireEnclosesTarget start expandedExact
                  originalExact).indexMap := Option.some.inj beforeMap
            have afterMap := anchoredWireSplitRaw_compileOccurrencesAway input
              wire endpoints targetRegion start child term selectedOccurs
              targetWellFormed wireEnclosesTarget hparent tail (childFuel + 1)
              original expanded collapse binders originalExact expandedExact
              after (by
                intro occurrence member
                rw [localEq]
                simp [member]) afterAway
            rw [sourceAfterCompiled, targetAfterCompiled] at afterMap
            have afterEq : sourceAfter = targetAfter.renameWires
                (collapse.extend wireEnclosesTarget start expandedExact
                  originalExact).indexMap := Option.some.inj afterMap
            let childSourceWire : Fin (original.extend start).length :=
              original.outerIndex start sourceWire
            have childSourceWireGet :
                (original.extend start).get childSourceWire = wire := by
              simpa only [childSourceWire, List.get_eq_getElem] using
                (original.extend_outer start sourceWire).trans sourceWireGet
            have childOriginalExact :=
              originalExact.extend_child input.property hparent
            have targetParent :
                ((anchoredWireSplitRaw input wire endpoints targetRegion term).regions
                  child).parent? = some start := by
              simpa only [anchoredWireSplitRaw_regions] using hparent
            have childExpandedExact :=
              expandedExact.extend_child targetWellFormed targetParent
            cases childKind : input.val.regions child with
            | sheet => simp [childKind, CRegion.parent?] at hparent
            | cut childParent =>
              have childParentEq : childParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst childParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                splitOldOccurrence, anchoredWireSplitRaw_regions]
                at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult :
                  ConcreteElaboration.compileRegion? signature input.val
                    (childFuel + 1) child (original.extend start) binders with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                cases targetChildResult :
                    ConcreteElaboration.compileRegion? signature
                      (anchoredWireSplitRaw input wire endpoints targetRegion term)
                      (childFuel + 1) child (expanded.extend start) binders with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  constructor
                  · intro sourceDenotes
                    unfold ConcreteElaboration.finishRegion at sourceDenotes ⊢
                    simp only [denoteRegion_mk] at sourceDenotes ⊢
                    obtain ⟨sourceLocal, sourceCast⟩ := sourceDenotes
                    let targetLocal := splitTargetLocalEnv collapse
                      wireEnclosesTarget start expandedExact originalExact
                      sourceOuter sourceLocal
                    refine ⟨targetLocal, ?_⟩
                    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceCast
                    let sourceRaw := splitExtendedEnv original start sourceOuter
                      sourceLocal
                    let targetRaw := splitExtendedEnv expanded start targetOuter
                      targetLocal
                    have sourceRawItems := (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        original start)) (extendWireEnv sourceOuter sourceLocal)
                      relEnv sourceItems).mp sourceCast
                    change denoteItemSeq model named sourceRaw relEnv sourceItems
                      at sourceRawItems
                    have envCollapse := splitExtendedEnv_collapse collapse
                      wireEnclosesTarget start expandedExact originalExact
                      sourceOuter sourceLocal
                    rw [outerAgrees] at envCollapse
                    change sourceRaw ∘
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap = targetRaw at envCollapse
                    rw [sourceItemsEq, denoteItemSeq_frame] at sourceRawItems
                    rw [ItemSeq.castWiresEq_eq_renameWires]
                    apply (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        expanded start)) (extendWireEnv targetOuter targetLocal)
                      relEnv targetItems).mpr
                    change denoteItemSeq model named targetRaw relEnv targetItems
                    rw [targetItemsEq, denoteItemSeq_frame]
                    have childValue : sourceRaw childSourceWire =
                        model.eval term Fin.elim0 := by
                      change splitExtendedEnv original start sourceOuter sourceLocal
                          (original.outerIndex start sourceWire) = _
                      rw [splitExtendedEnv_outer]
                      exact sourceWireValue
                    have childEquiv := ih targetWellFormed wireEnclosesTarget
                      childFuel (original.extend start)
                      (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) binders childOriginalExact childExpandedExact
                      childSourceWire childSourceWireGet sourceChild targetChild
                      sourceChildResult targetChildResult model named sourceRaw
                      targetRaw relEnv envCollapse childValue
                    have targetBeforeDenotes : denoteItemSeq model named targetRaw
                        relEnv targetBefore := by
                      rw [beforeEq] at sourceRawItems
                      rw [← envCollapse]
                      exact (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetBefore).mp
                            sourceRawItems.1
                    have targetAfterDenotes : denoteItemSeq model named targetRaw
                        relEnv targetAfter := by
                      rw [afterEq] at sourceRawItems
                      rw [← envCollapse]
                      exact (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetAfter).mp
                            sourceRawItems.2.2
                    refine ⟨targetBeforeDenotes, ?_, targetAfterDenotes⟩
                    intro targetChildDenotes
                    exact sourceRawItems.2.1
                      (childEquiv.mpr targetChildDenotes)
                  · intro targetDenotes
                    unfold ConcreteElaboration.finishRegion at targetDenotes ⊢
                    simp only [denoteRegion_mk] at targetDenotes ⊢
                    obtain ⟨targetLocal, targetCast⟩ := targetDenotes
                    let sourceLocal := splitSourceLocalEnvOfNe input wire endpoints
                      targetRegion start term startNe targetLocal
                    refine ⟨sourceLocal, ?_⟩
                    rw [ItemSeq.castWiresEq_eq_renameWires] at targetCast
                    let sourceRaw := splitExtendedEnv original start sourceOuter
                      sourceLocal
                    let targetRaw := splitExtendedEnv expanded start targetOuter
                      targetLocal
                    have targetRawItems := (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        expanded start)) (extendWireEnv targetOuter targetLocal)
                      relEnv targetItems).mp targetCast
                    change denoteItemSeq model named targetRaw relEnv targetItems
                      at targetRawItems
                    have envCollapse := splitExtendedEnv_uncollapse_of_ne collapse
                      wireEnclosesTarget start startNe expandedExact originalExact
                      sourceOuter targetOuter outerAgrees targetLocal
                    change sourceRaw ∘
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap = targetRaw at envCollapse
                    rw [targetItemsEq, denoteItemSeq_frame] at targetRawItems
                    rw [ItemSeq.castWiresEq_eq_renameWires]
                    apply (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        original start)) (extendWireEnv sourceOuter sourceLocal)
                      relEnv sourceItems).mpr
                    change denoteItemSeq model named sourceRaw relEnv sourceItems
                    rw [sourceItemsEq, denoteItemSeq_frame]
                    have childValue : sourceRaw childSourceWire =
                        model.eval term Fin.elim0 := by
                      change splitExtendedEnv original start sourceOuter sourceLocal
                          (original.outerIndex start sourceWire) = _
                      rw [splitExtendedEnv_outer]
                      exact sourceWireValue
                    have childEquiv := ih targetWellFormed wireEnclosesTarget
                      childFuel (original.extend start)
                      (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) binders childOriginalExact childExpandedExact
                      childSourceWire childSourceWireGet sourceChild targetChild
                      sourceChildResult targetChildResult model named sourceRaw
                      targetRaw relEnv envCollapse childValue
                    have sourceBeforeDenotes : denoteItemSeq model named sourceRaw
                        relEnv sourceBefore := by
                      rw [beforeEq]
                      apply (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetBefore).mpr
                      rw [envCollapse]
                      exact targetRawItems.1
                    have sourceAfterDenotes : denoteItemSeq model named sourceRaw
                        relEnv sourceAfter := by
                      rw [afterEq]
                      apply (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetAfter).mpr
                      rw [envCollapse]
                      exact targetRawItems.2.2
                    refine ⟨sourceBeforeDenotes, ?_, sourceAfterDenotes⟩
                    intro sourceChildDenotes
                    exact targetRawItems.2.1
                      (childEquiv.mp sourceChildDenotes)
            | bubble childParent arity =>
              have childParentEq : childParent = start := by
                simpa [childKind, CRegion.parent?] using hparent
              subst childParent
              simp only [ConcreteElaboration.compileOccurrenceWith?, childKind,
                splitOldOccurrence, anchoredWireSplitRaw_regions]
                at sourceFocusCompiled targetFocusCompiled
              cases sourceChildResult :
                  ConcreteElaboration.compileRegion? signature input.val
                    (childFuel + 1) child (original.extend start)
                    (binders.push child arity) with
              | none => simp [sourceChildResult] at sourceFocusCompiled
              | some sourceChild =>
                simp [sourceChildResult] at sourceFocusCompiled
                subst sourceFocus
                change (ConcreteElaboration.compileRegion? signature
                    (anchoredWireSplitRaw input wire endpoints targetRegion term)
                    (childFuel + 1) child (expanded.extend start)
                    (binders.push child arity)).bind
                      (fun body => some (Item.bubble arity body)) =
                    some targetFocus at targetFocusCompiled
                cases targetChildResult :
                    ConcreteElaboration.compileRegion? signature
                      (anchoredWireSplitRaw input wire endpoints targetRegion term)
                      (childFuel + 1) child (expanded.extend start)
                      (binders.push child arity) with
                | none => simp [targetChildResult] at targetFocusCompiled
                | some targetChild =>
                  simp [targetChildResult] at targetFocusCompiled
                  subst targetFocus
                  constructor
                  · intro sourceDenotes
                    unfold ConcreteElaboration.finishRegion at sourceDenotes ⊢
                    simp only [denoteRegion_mk] at sourceDenotes ⊢
                    obtain ⟨sourceLocal, sourceCast⟩ := sourceDenotes
                    let targetLocal := splitTargetLocalEnv collapse
                      wireEnclosesTarget start expandedExact originalExact
                      sourceOuter sourceLocal
                    refine ⟨targetLocal, ?_⟩
                    rw [ItemSeq.castWiresEq_eq_renameWires] at sourceCast
                    let sourceRaw := splitExtendedEnv original start sourceOuter
                      sourceLocal
                    let targetRaw := splitExtendedEnv expanded start targetOuter
                      targetLocal
                    have sourceRawItems := (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        original start)) (extendWireEnv sourceOuter sourceLocal)
                      relEnv sourceItems).mp sourceCast
                    change denoteItemSeq model named sourceRaw relEnv sourceItems
                      at sourceRawItems
                    have envCollapse := splitExtendedEnv_collapse collapse
                      wireEnclosesTarget start expandedExact originalExact
                      sourceOuter sourceLocal
                    rw [outerAgrees] at envCollapse
                    change sourceRaw ∘
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap = targetRaw at envCollapse
                    rw [sourceItemsEq, denoteItemSeq_frame] at sourceRawItems
                    rw [ItemSeq.castWiresEq_eq_renameWires]
                    apply (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        expanded start)) (extendWireEnv targetOuter targetLocal)
                      relEnv targetItems).mpr
                    change denoteItemSeq model named targetRaw relEnv targetItems
                    rw [targetItemsEq, denoteItemSeq_frame]
                    have childValue :
                        sourceRaw childSourceWire = model.eval term Fin.elim0 := by
                      change splitExtendedEnv original start sourceOuter sourceLocal
                          (original.outerIndex start sourceWire) = _
                      rw [splitExtendedEnv_outer]
                      exact sourceWireValue
                    have targetBeforeDenotes : denoteItemSeq model named targetRaw
                        relEnv targetBefore := by
                      rw [beforeEq] at sourceRawItems
                      rw [← envCollapse]
                      exact (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetBefore).mp
                            sourceRawItems.1
                    have targetAfterDenotes : denoteItemSeq model named targetRaw
                        relEnv targetAfter := by
                      rw [afterEq] at sourceRawItems
                      rw [← envCollapse]
                      exact (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetAfter).mp
                            sourceRawItems.2.2
                    obtain ⟨relation, sourceChildDenotes⟩ := sourceRawItems.2.1
                    have childEquiv := ih targetWellFormed wireEnclosesTarget
                      childFuel (original.extend start) (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) (binders.push child arity)
                      childOriginalExact childExpandedExact childSourceWire
                      childSourceWireGet sourceChild targetChild sourceChildResult
                      targetChildResult model named sourceRaw targetRaw
                      (relation, relEnv) envCollapse childValue
                    exact ⟨targetBeforeDenotes,
                      ⟨relation, childEquiv.mp sourceChildDenotes⟩,
                      targetAfterDenotes⟩
                  · intro targetDenotes
                    unfold ConcreteElaboration.finishRegion at targetDenotes ⊢
                    simp only [denoteRegion_mk] at targetDenotes ⊢
                    obtain ⟨targetLocal, targetCast⟩ := targetDenotes
                    let sourceLocal := splitSourceLocalEnvOfNe input wire endpoints
                      targetRegion start term startNe targetLocal
                    refine ⟨sourceLocal, ?_⟩
                    rw [ItemSeq.castWiresEq_eq_renameWires] at targetCast
                    let sourceRaw := splitExtendedEnv original start sourceOuter
                      sourceLocal
                    let targetRaw := splitExtendedEnv expanded start targetOuter
                      targetLocal
                    have targetRawItems := (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        expanded start)) (extendWireEnv targetOuter targetLocal)
                      relEnv targetItems).mp targetCast
                    change denoteItemSeq model named targetRaw relEnv targetItems
                      at targetRawItems
                    have envCollapse := splitExtendedEnv_uncollapse_of_ne collapse
                      wireEnclosesTarget start startNe expandedExact originalExact
                      sourceOuter targetOuter outerAgrees targetLocal
                    change sourceRaw ∘
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap = targetRaw at envCollapse
                    rw [targetItemsEq, denoteItemSeq_frame] at targetRawItems
                    rw [ItemSeq.castWiresEq_eq_renameWires]
                    apply (denoteItemSeq_renameWires model named
                      (Fin.cast (ConcreteElaboration.WireContext.length_extend
                        original start)) (extendWireEnv sourceOuter sourceLocal)
                      relEnv sourceItems).mpr
                    change denoteItemSeq model named sourceRaw relEnv sourceItems
                    rw [sourceItemsEq, denoteItemSeq_frame]
                    have childValue :
                        sourceRaw childSourceWire = model.eval term Fin.elim0 := by
                      change splitExtendedEnv original start sourceOuter sourceLocal
                          (original.outerIndex start sourceWire) = _
                      rw [splitExtendedEnv_outer]
                      exact sourceWireValue
                    have sourceBeforeDenotes : denoteItemSeq model named sourceRaw
                        relEnv sourceBefore := by
                      rw [beforeEq]
                      apply (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetBefore).mpr
                      rw [envCollapse]
                      exact targetRawItems.1
                    have sourceAfterDenotes : denoteItemSeq model named sourceRaw
                        relEnv sourceAfter := by
                      rw [afterEq]
                      apply (denoteItemSeq_renameWires model named
                        (collapse.extend wireEnclosesTarget start expandedExact
                          originalExact).indexMap sourceRaw relEnv targetAfter).mpr
                      rw [envCollapse]
                      exact targetRawItems.2.2
                    obtain ⟨relation, targetChildDenotes⟩ := targetRawItems.2.1
                    have childEquiv := ih targetWellFormed wireEnclosesTarget
                      childFuel (original.extend start) (expanded.extend start)
                      (collapse.extend wireEnclosesTarget start expandedExact
                        originalExact) (binders.push child arity)
                      childOriginalExact childExpandedExact childSourceWire
                      childSourceWireGet sourceChild targetChild sourceChildResult
                      targetChildResult model named sourceRaw targetRaw
                      (relation, relEnv) envCollapse childValue
                    exact ⟨sourceBeforeDenotes,
                      ⟨relation, childEquiv.mpr targetChildDenotes⟩,
                      sourceAfterDenotes⟩

end AnchoredWireSoundness

end VisualProof.Rule
