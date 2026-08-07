import VisualProof.Refinement.Implementation.DoubleCutIntroPartition
import VisualProof.Diagram.RenamingIsomorphism
import VisualProof.Rule.DoubleCut

namespace VisualProof.Refinement.Implementation.DoubleCutIntroCompile

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutTransport
open VisualProof.Refinement.Implementation.DoubleCutIntroPartition

theorem region_zero_iso
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    {rels : RelCtx}
    {sourceItems : ItemSeq sourceWires rels}
    {targetItems : ItemSeq targetWires rels}
    (items : ItemSeqIso wire rels sourceItems targetItems) :
    RegionIso wire rels (.mk 0 sourceItems) (.mk 0 targetItems) := by
  apply RegionIso.mk (FiniteEquiv.refl (Fin 0))
  have extended : extendWireEquiv wire (FiniteEquiv.refl (Fin 0)) =
      wire := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    change (extendWireEquiv wire (FiniteEquiv.refl (Fin 0))
      (Fin.castAdd 0 index)).val = (wire index).val
    rw [extendWireEquiv_outer]
    rfl
  rw [extended]
  exact items

theorem singleton_iso
    {sourceWires targetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx} {sourceItem : Item sourceWires rels}
    {targetItem : Item targetWires rels}
    (item : ItemIso wire rels sourceItem targetItem) :
    ItemSeqIso wire rels (.cons sourceItem .nil) (.cons targetItem .nil) := by
  apply ItemSeqIso.permute (FiniteEquiv.finCast (by rfl))
  intro index
  have value : index.val = 0 := by
    have bound := index.isLt
    simp only [ItemSeq.length] at bound
    omega
  have zero : index = ⟨0, by simp [ItemSeq.length]⟩ := Fin.ext value
  subst index
  simpa [ItemSeq.get] using item

theorem splice_partition_eq
    (input : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount)
    {rels : RelCtx}
    (host material : ItemSeq
      (context.length +
        (Concrete.Elaboration.exactScopeWires input region).length) rels) :
    Region.spliceAt
        (Concrete.Elaboration.exactScopeWires input region).length host
        (.mk 0 material)
        id
        (identityRelationRenaming rels) =
      Concrete.Elaboration.finishRegion input context region
        ((host.append material).castWiresEq
          (Concrete.Elaboration.WireContext.length_extend context region).symm) := by
  unfold Region.spliceAt Region.adjoinAt
    Concrete.Elaboration.finishRegion identityRelationRenaming
  simp only [Region.renameWires, Region.renameRelations,
    ItemSeq.renameRelations_id, Nat.add_zero]
  congr 1
  simp only [ItemSeq.castWiresEq_trans]
  have proofEq :
      (Concrete.Elaboration.WireContext.length_extend context region).symm.trans
        (Concrete.Elaboration.WireContext.length_extend context region) = rfl :=
    Subsingleton.elim _ _
  rw [proofEq]
  simp only [ItemSeq.castWiresEq]
  have hostMap : Region.adjoinHostWire context.length
      (Concrete.Elaboration.exactScopeWires input region).length 0 = id := by
    funext index
    apply Fin.ext
    rfl
  have materialMap : Region.adjoinMaterialWire context.length
      (Concrete.Elaboration.exactScopeWires input region).length 0 = id := by
    funext index
    apply Fin.ext
    rfl
  have extendedId : extendWireRenaming
      (id : Fin (context.length +
        (Concrete.Elaboration.exactScopeWires input region).length) →
        Fin (context.length +
          (Concrete.Elaboration.exactScopeWires input region).length)) 0 =
      id := extendWireRenaming_id 0
  rw [hostMap, materialMap, extendedId,
    ItemSeq.renameWires_id, ItemSeq.renameWires_id]
  have castIdentity :
      (host.append material).castWiresEq
          ((Concrete.Elaboration.WireContext.length_extend
            context region).symm.trans
            (Concrete.Elaboration.WireContext.length_extend context region)) =
        host.append material := by
    rw [proofEq]
    rw [ItemSeq.castWiresEq_eq_renameWires]
    have castMap : Fin.cast
        ((Concrete.Elaboration.WireContext.length_extend
          context region).symm.trans
          (Concrete.Elaboration.WireContext.length_extend context region)) =
        (id : Fin (context.length +
          (Concrete.Elaboration.exactScopeWires input region).length) →
          Fin (context.length +
            (Concrete.Elaboration.exactScopeWires input region).length)) := by
      funext index
      apply Fin.ext
      rfl
    rw [castMap, ItemSeq.renameWires_id]
  have materialIdentity : ItemSeq.renameWires
      (id : Fin (context.length +
        (Concrete.Elaboration.exactScopeWires input region).length) →
        Fin (context.length +
          (Concrete.Elaboration.exactScopeWires input region).length))
      material = material := ItemSeq.renameWires_id material
  rw [materialIdentity]
  exact castIdentity.symm

def partitionBody
    (input : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount) {rels : RelCtx}
    (items : ItemSeq (context.extend region).length rels) :
    Region
      (context.length +
        (Concrete.Elaboration.exactScopeWires input region).length) rels :=
  .mk 0 (items.castWiresEq
    (Concrete.Elaboration.WireContext.length_extend context region))

def partitionBefore
    (input : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount) {rels : RelCtx}
    (kept selected : ItemSeq (context.extend region).length rels) :
    Region context.length rels :=
  Region.spliceAt
    (Concrete.Elaboration.exactScopeWires input region).length
    (kept.castWiresEq
      (Concrete.Elaboration.WireContext.length_extend context region))
    (partitionBody input context region selected) id
    (identityRelationRenaming rels)

def partitionAfter
    (input : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount) {rels : RelCtx}
    (kept selected : ItemSeq (context.extend region).length rels) :
    Region context.length rels :=
  Region.spliceAt
    (Concrete.Elaboration.exactScopeWires input region).length
    (kept.castWiresEq
      (Concrete.Elaboration.WireContext.length_extend context region))
    (Rule.DoubleCut.wrap (partitionBody input context region selected)) id
    (identityRelationRenaming rels)

theorem partition_local
    (input : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount) {rels : RelCtx}
    (kept selected : ItemSeq (context.extend region).length rels) :
    Rule.DoubleCut.Local
      (partitionBefore input context region kept selected)
      (partitionAfter input context region kept selected) := by
  exact Rule.DoubleCut.Local.introduce
    (Concrete.Elaboration.exactScopeWires input region).length
    (kept.castWiresEq
      (Concrete.Elaboration.WireContext.length_extend context region))
    (partitionBody input context region selected) id
    (identityRelationRenaming rels)

def wrappedItems {wires : Nat} {rels : RelCtx}
    (items : ItemSeq wires rels) : ItemSeq wires rels :=
  .cons (.cut (.mk 0 (.cons (.cut (.mk 0 items)) .nil))) .nil

private theorem cast_cancel_items
    (equality : source = target) (items : ItemSeq source rels) :
    (items.castWiresEq equality).castWiresEq equality.symm = items := by
  rw [ItemSeq.castWiresEq_trans]
  have proofEq : equality.trans equality.symm = rfl := Subsingleton.elim _ _
  rw [proofEq, ItemSeq.castWiresEq_eq_renameWires]
  have castMap : Fin.cast (equality.trans equality.symm) =
      (id : Fin source → Fin source) := by
    funext index
    apply Fin.ext
    rfl
  rw [castMap, ItemSeq.renameWires_id]

private theorem wrappedItems_cast
    (equality : source = target) (items : ItemSeq source rels) :
    wrappedItems (items.castWiresEq equality) =
      (wrappedItems items).castWiresEq equality := by
  subst target
  rfl

theorem partitionBefore_eq_finish
    (input : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount) {rels : RelCtx}
    (kept selected : ItemSeq (context.extend region).length rels) :
    partitionBefore input context region kept selected =
      Concrete.Elaboration.finishRegion input context region
        (kept.append selected) := by
  unfold partitionBefore partitionBody
  rw [splice_partition_eq]
  apply congrArg
  rw [← ItemSeq.castWiresEq_append]
  exact cast_cancel_items
    (Concrete.Elaboration.WireContext.length_extend context region)
    (kept.append selected)

theorem partitionAfter_eq_finish
    (input : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext input)
    (region : Fin input.regionCount) {rels : RelCtx}
    (kept selected : ItemSeq (context.extend region).length rels) :
    partitionAfter input context region kept selected =
      Concrete.Elaboration.finishRegion input context region
        (kept.append (wrappedItems selected)) := by
  unfold partitionAfter Rule.DoubleCut.wrap partitionBody
  rw [splice_partition_eq]
  apply congrArg
  change
    (((kept.castWiresEq
      (Concrete.Elaboration.WireContext.length_extend context region)).append
      (wrappedItems (selected.castWiresEq
        (Concrete.Elaboration.WireContext.length_extend context region)))).castWiresEq
      (Concrete.Elaboration.WireContext.length_extend context region).symm) =
        kept.append (wrappedItems selected)
  rw [wrappedItems_cast]
  rw [← ItemSeq.castWiresEq_append]
  apply cast_cancel_items

theorem finishRegion_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    (region : Fin input.regionCount)
    {rels : RelCtx}
    {sourceItems : ItemSeq (sourceContext.extend region).length rels}
    {targetItems : ItemSeq
      (targetContext.extend (Fin.castAdd 2 region)).length rels}
    (items : ItemSeqIso
      (FiniteEquiv.finCast (congrArg List.length
        (context.extend region).equality)) rels sourceItems targetItems) :
    RegionIso
      (FiniteEquiv.finCast (congrArg List.length context.equality)) rels
      (Concrete.Elaboration.finishRegion input sourceContext region sourceItems)
      (Concrete.Elaboration.finishRegion (doubleCutIntroRaw input selection)
        targetContext (Fin.castAdd 2 region) targetItems) := by
  have wireEquivEq :
      Concrete.Elaboration.castFinEquiv
        (Concrete.Elaboration.WireContext.length_extend sourceContext region)
        (Concrete.Elaboration.WireContext.length_extend targetContext
          (Fin.castAdd 2 region))
        (extendWireEquiv
          (FiniteEquiv.finCast (congrArg List.length context.equality))
          (FiniteEquiv.finCast (congrArg List.length
            (exactScopeWires input selection region).symm))) =
      FiniteEquiv.finCast (congrArg List.length
        (context.extend region).equality) := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    change
      (extendWireEquiv
        (FiniteEquiv.finCast (congrArg List.length context.equality))
        (FiniteEquiv.finCast (congrArg List.length
          (exactScopeWires input selection region).symm))
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend sourceContext region)
          index)).val = index.val
    have castVal :
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend sourceContext region)
          index).val = index.val := rfl
    rw [← castVal]
    refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_)
      (Fin.cast
        (Concrete.Elaboration.WireContext.length_extend sourceContext region)
        index)
    · rw [extendWireEquiv_outer]
      change outerIndex.val = outerIndex.val
      rfl
    · rw [extendWireEquiv_local]
      change targetContext.length + localIndex.val =
        sourceContext.length + localIndex.val
      exact congrArg (fun length => length + localIndex.val)
        (congrArg List.length context.equality).symm
  apply Concrete.Elaboration.regionIso_of_cast
    (Concrete.Elaboration.WireContext.length_extend sourceContext region)
    (Concrete.Elaboration.WireContext.length_extend targetContext
      (Fin.castAdd 2 region))
    (FiniteEquiv.finCast (congrArg List.length context.equality))
    (FiniteEquiv.finCast (congrArg List.length
      (exactScopeWires input selection region).symm))
    sourceItems targetItems
  rw [wireEquivEq]
  exact items

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

theorem node_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    (node : Fin input.nodeCount)
    (regionMap : Fin input.regionCount → Fin (input.regionCount + 2))
    (shape : (doubleCutIntroRaw input selection).nodes node =
      match input.nodes node with
      | .atom owner binder => .atom (regionMap owner) (Fin.castAdd 2 binder)
      | .identity owner arity => .identity (regionMap owner) arity)
    {sourceItem : Item sourceContext.length sourceRels}
    {targetItem : Item targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileNode? input sourceContext
      sourceBinders node = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileNode?
      (doubleCutIntroRaw input selection) targetContext targetBinders node =
        some targetItem) :
    ItemIso
      (FiniteEquiv.finCast (congrArg List.length context.equality))
      sourceRels sourceItem
      (binders.rels ▸ targetItem) := by
  cases binders.rels
  let wireMap : Fin sourceContext.length → Fin targetContext.length :=
    Fin.cast (congrArg List.length context.equality)
  have mapped := Concrete.Elaboration.compileNode?_map
    sourceContext targetContext sourceBinders targetBinders node node
    regionMap (Fin.castAdd 2) wireMap (identityRelationRenaming sourceRels)
    shape
    (by
      intro port
      exact resolvePort input selection sourceContext targetContext context
        node port)
    (by
      intro owner binder sourceAtom
      have lookup := eq_of_heq (binders.equality binder)
      simpa [identityRelationRenaming] using lookup.symm)
  rw [sourceCompiled, targetCompiled] at mapped
  simp only [Option.map_some, Option.some.injEq] at mapped
  rw [mapped]
  have identityMap :
      (fun {arity} => identityRelationRenaming sourceRels :
        RelationRenaming sourceRels sourceRels) =
      (fun {arity} relation => relation) := rfl
  rw [identityMap, Item.renameRelations_id]
  simpa [wireMap, identityRelationRenaming] using
    ItemIso.renameWiresEquiv sourceItem
      (FiniteEquiv.finCast (congrArg List.length context.equality))

theorem occurrence_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    {sourceFuel targetFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount)
    (regionMap : Fin input.regionCount → Fin (input.regionCount + 2))
    (nodeMap : ∀ node, occurrence = .node node →
      (doubleCutIntroRaw input selection).nodes node =
        match input.nodes node with
        | .atom owner binder => .atom (regionMap owner) (Fin.castAdd 2 binder)
        | .identity owner arity => .identity (regionMap owner) arity)
    (childMap : ∀ child, occurrence = .child child →
      (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
        match input.regions child with
        | .sheet => .sheet
        | .cut parent => .cut (regionMap parent)
        | .bubble parent arity => .bubble (regionMap parent) arity)
    (recurse : ∀ {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : Concrete.Elaboration.BinderContext input childSourceRels}
      {childTargetBinders : Concrete.Elaboration.BinderContext
        (doubleCutIntroRaw input selection) childTargetRels}
      (childBinders : Binders input selection childSourceBinders
        childTargetBinders)
      (child : Fin input.regionCount)
      (_occurrenceEq : occurrence = .child child)
      {sourceBody : Region sourceContext.length childSourceRels}
      {targetBody : Region targetContext.length childTargetRels},
      Concrete.Elaboration.compileRegion? input sourceFuel child sourceContext
          childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion? (doubleCutIntroRaw input selection)
          targetFuel (Fin.castAdd 2 child) targetContext childTargetBinders =
        some targetBody →
      RegionIso
        (FiniteEquiv.finCast (congrArg List.length context.equality))
        childSourceRels sourceBody (childBinders.rels ▸ targetBody))
    {sourceItem : Item sourceContext.length sourceRels}
    {targetItem : Item targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith? input
      (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
      sourceBinders occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input selection) targetFuel)
      targetContext targetBinders (liftOccurrence input occurrence) =
        some targetItem) :
    ItemIso (FiniteEquiv.finCast (congrArg List.length context.equality))
      sourceRels sourceItem (binders.rels ▸ targetItem) := by
  cases binders.rels
  cases occurrence with
  | node node =>
      apply node_iso input selection sourceContext targetContext context
        sourceBinders targetBinders binders node regionMap
        (nodeMap node rfl)
      · simpa [Concrete.Elaboration.compileOccurrenceWith?] using sourceCompiled
      · simpa [Concrete.Elaboration.compileOccurrenceWith?, liftOccurrence]
          using targetCompiled
  | child child =>
      simp only [Concrete.Elaboration.compileOccurrenceWith?, liftOccurrence]
        at sourceCompiled targetCompiled
      have shape := childMap child rfl
      cases childKind : input.regions child with
      | sheet => simp [childKind] at sourceCompiled
      | cut parent =>
          rw [childKind] at shape
          rw [childKind] at sourceCompiled
          simp only at shape
          rw [shape] at targetCompiled
          simp only at sourceCompiled targetCompiled
          cases sourceResult : Concrete.Elaboration.compileRegion? input
              sourceFuel child sourceContext sourceBinders with
          | none => simp [sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : Concrete.Elaboration.compileRegion?
                  (doubleCutIntroRaw input selection) targetFuel
                  (Fin.castAdd 2 child) targetContext targetBinders with
              | none => simp [targetResult] at targetCompiled
              | some targetBody =>
                  simp [targetResult] at targetCompiled
                  subst targetItem
                  exact ItemIso.cut
                    (recurse binders child rfl sourceResult targetResult)
      | bubble parent arity =>
          rw [childKind] at shape
          rw [childKind] at sourceCompiled
          simp only at shape
          rw [shape] at targetCompiled
          simp only at sourceCompiled targetCompiled
          cases sourceResult : Concrete.Elaboration.compileRegion? input
              sourceFuel child sourceContext (sourceBinders.push child arity) with
          | none => simp [sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : Concrete.Elaboration.compileRegion?
                  (doubleCutIntroRaw input selection) targetFuel
                  (Fin.castAdd 2 child) targetContext
                  (targetBinders.push (Fin.castAdd 2 child) arity) with
              | none => simp [targetResult] at targetCompiled
              | some targetBody =>
                  simp [targetResult] at targetCompiled
                  subst targetItem
                  exact ItemIso.bubble
                    (recurse (binders.push child arity) child rfl
                      sourceResult targetResult)

theorem occurrences_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    {sourceFuel targetFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount))
    (regionMap : Fin input.regionCount → Fin (input.regionCount + 2))
    (nodeMap : ∀ node, .node node ∈ occurrences →
      (doubleCutIntroRaw input selection).nodes node =
        match input.nodes node with
        | .atom owner binder => .atom (regionMap owner) (Fin.castAdd 2 binder)
        | .identity owner arity => .identity (regionMap owner) arity)
    (childMap : ∀ child, .child child ∈ occurrences →
      (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
        match input.regions child with
        | .sheet => .sheet
        | .cut parent => .cut (regionMap parent)
        | .bubble parent arity => .bubble (regionMap parent) arity)
    (recurse : ∀ {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : Concrete.Elaboration.BinderContext input childSourceRels}
      {childTargetBinders : Concrete.Elaboration.BinderContext
        (doubleCutIntroRaw input selection) childTargetRels}
      (childBinders : Binders input selection childSourceBinders
        childTargetBinders)
      (child : Fin input.regionCount),
      .child child ∈ occurrences →
      ∀ {sourceBody : Region sourceContext.length childSourceRels}
        {targetBody : Region targetContext.length childTargetRels},
      Concrete.Elaboration.compileRegion? input sourceFuel child sourceContext
          childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion? (doubleCutIntroRaw input selection)
          targetFuel (Fin.castAdd 2 child) targetContext childTargetBinders =
        some targetBody →
      RegionIso
        (FiniteEquiv.finCast (congrArg List.length context.equality))
        childSourceRels sourceBody (childBinders.rels ▸ targetBody))
    {sourceItems : ItemSeq sourceContext.length sourceRels}
    {targetItems : ItemSeq targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith? input
      (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
      sourceBinders occurrences = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input selection) targetFuel)
      targetContext targetBinders (occurrences.map (liftOccurrence input)) =
        some targetItems) :
    ItemSeqIso (FiniteEquiv.finCast
        (congrArg List.length context.equality))
      sourceRels sourceItems (binders.rels ▸ targetItems) := by
  cases binders.rels
  let positions : FiniteEquiv (Fin occurrences.length)
      (Fin (occurrences.map (liftOccurrence input)).length) :=
    FiniteEquiv.finCast
      (List.length_map (as := occurrences) (liftOccurrence input)).symm
  apply Concrete.Elaboration.compileOccurrencesWith?_iso
    (Concrete.Elaboration.compileRegion? input sourceFuel)
    (Concrete.Elaboration.compileRegion?
      (doubleCutIntroRaw input selection) targetFuel)
    sourceContext targetContext sourceBinders targetBinders
    occurrences (occurrences.map (liftOccurrence input))
    sourceCompiled targetCompiled positions
    (FiniteEquiv.finCast (congrArg List.length context.equality))
  intro index
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? input sourceFuel)
    sourceContext sourceBinders sourceCompiled index
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion?
      (doubleCutIntroRaw input selection) targetFuel)
    targetContext targetBinders targetCompiled (positions index)
  have targetGet' :
      Concrete.Elaboration.compileOccurrenceWith?
        (doubleCutIntroRaw input selection)
        (Concrete.Elaboration.compileRegion?
          (doubleCutIntroRaw input selection) targetFuel)
        targetContext targetBinders
        (liftOccurrence input (occurrences.get index)) =
      some (targetItems.get
        (Fin.cast
          (Concrete.Elaboration.compileOccurrencesWith?_length
            (Concrete.Elaboration.compileRegion?
              (doubleCutIntroRaw input selection) targetFuel)
            targetContext targetBinders targetCompiled).symm
          (positions index))) := by
    simpa [positions] using targetGet
  have member : occurrences.get index ∈ occurrences := List.get_mem _ _
  apply occurrence_iso input selection sourceContext targetContext context
    sourceBinders targetBinders binders (occurrences.get index) regionMap
  · intro node equality
    rw [equality] at member
    exact nodeMap node member
  · intro child equality
    rw [equality] at member
    exact childMap child member
  · intro childSourceRels childTargetRels childSourceBinders
      childTargetBinders childBinders child equality sourceBody targetBody
      childSourceCompiled childTargetCompiled
    rw [equality] at member
    exact recurse childBinders child member childSourceCompiled
      childTargetCompiled
  · exact sourceGet
  · exact targetGet'

theorem away_region_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {sourceFuel targetFuel : Nat}
    (region : Fin input.regionCount)
    (away : ¬ input.Encloses region selection.val.anchor)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    {sourceBody : Region sourceContext.length sourceRels}
    {targetBody : Region targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileRegion? input sourceFuel
      region sourceContext sourceBinders = some sourceBody)
    (targetCompiled : Concrete.Elaboration.compileRegion?
      (doubleCutIntroRaw input selection) targetFuel (Fin.castAdd 2 region)
      targetContext targetBinders = some targetBody) :
    RegionIso
      (FiniteEquiv.finCast (congrArg List.length context.equality))
      sourceRels sourceBody (binders.rels ▸ targetBody) := by
  induction sourceFuel generalizing targetFuel region sourceContext
      targetContext sourceRels targetRels sourceBinders targetBinders
      sourceBody targetBody with
  | zero => simp [Concrete.Elaboration.compileRegion?] at sourceCompiled
  | succ sourceFuel induction =>
      cases targetFuel with
      | zero => simp [Concrete.Elaboration.compileRegion?] at targetCompiled
      | succ targetFuel =>
          simp only [Concrete.Elaboration.compileRegion?] at sourceCompiled
          simp only [Concrete.Elaboration.compileRegion?] at targetCompiled
          cases sourceItemsResult : Concrete.Elaboration.compileOccurrencesWith?
              input (Concrete.Elaboration.compileRegion? input sourceFuel)
              (sourceContext.extend region) sourceBinders
              (Concrete.Elaboration.localOccurrences input region) with
          | none => simp [sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              simp [sourceItemsResult] at sourceCompiled
              subst sourceBody
              have regular : region ≠ selection.val.anchor := by
                intro equality
                apply away
                subst region
                exact Concrete.Diagram.Encloses.refl input selection.val.anchor
              let extendedContext := context.extend region
              rw [regular_localOccurrences input selection region regular]
                at targetCompiled
              change (do
                let items ← Concrete.Elaboration.compileOccurrencesWith?
                  (doubleCutIntroRaw input selection)
                  (Concrete.Elaboration.compileRegion?
                    (doubleCutIntroRaw input selection) targetFuel)
                  (targetContext.extend (Fin.castAdd 2 region)) targetBinders
                  ((Concrete.Elaboration.localOccurrences input region).map
                    (liftOccurrence input))
                pure (Concrete.Elaboration.finishRegion
                  (doubleCutIntroRaw input selection) targetContext
                  (Fin.castAdd 2 region) items)) = some targetBody
                at targetCompiled
              cases targetItemsResult : Concrete.Elaboration.compileOccurrencesWith?
                  (doubleCutIntroRaw input selection)
                  (Concrete.Elaboration.compileRegion?
                    (doubleCutIntroRaw input selection) targetFuel)
                  (targetContext.extend (Fin.castAdd 2 region)) targetBinders
                  ((Concrete.Elaboration.localOccurrences input region).map
                    (liftOccurrence input)) with
              | none =>
                  rw [targetItemsResult] at targetCompiled
                  simp at targetCompiled
              | some targetItems =>
                  rw [targetItemsResult] at targetCompiled
                  have targetBodyEq := Option.some.inj targetCompiled
                  subst targetBody
                  let occurrences :=
                    Concrete.Elaboration.localOccurrences input region
                  let occurrenceEquiv : FiniteEquiv (Fin occurrences.length)
                      (Fin (occurrences.map (liftOccurrence input)).length) :=
                    FiniteEquiv.finCast
                      (List.length_map (as := occurrences)
                        (liftOccurrence input)).symm
                  have itemsIso : ItemSeqIso
                      (FiniteEquiv.finCast
                        (congrArg List.length extendedContext.equality))
                      sourceRels sourceItems (binders.rels ▸ targetItems) := by
                    cases binders.rels
                    apply Concrete.Elaboration.compileOccurrencesWith?_iso
                      (Concrete.Elaboration.compileRegion? input sourceFuel)
                      (Concrete.Elaboration.compileRegion?
                        (doubleCutIntroRaw input selection) targetFuel)
                      (sourceContext.extend region)
                      (targetContext.extend (Fin.castAdd 2 region))
                      sourceBinders targetBinders
                      (Concrete.Elaboration.localOccurrences input region)
                      ((Concrete.Elaboration.localOccurrences input region).map
                        (liftOccurrence input))
                      sourceItemsResult targetItemsResult occurrenceEquiv
                      (FiniteEquiv.finCast
                        (congrArg List.length extendedContext.equality))
                    intro index
                    have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
                      (Concrete.Elaboration.compileRegion? input sourceFuel)
                      (sourceContext.extend region) sourceBinders
                      sourceItemsResult index
                    have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
                      (Concrete.Elaboration.compileRegion?
                        (doubleCutIntroRaw input selection) targetFuel)
                      (targetContext.extend (Fin.castAdd 2 region)) targetBinders
                      targetItemsResult (occurrenceEquiv index)
                    have targetGet' :
                        Concrete.Elaboration.compileOccurrenceWith?
                          (doubleCutIntroRaw input selection)
                          (Concrete.Elaboration.compileRegion?
                            (doubleCutIntroRaw input selection) targetFuel)
                          (targetContext.extend (Fin.castAdd 2 region))
                          targetBinders
                          (liftOccurrence input
                            ((Concrete.Elaboration.localOccurrences input
                              region).get index)) =
                        some (targetItems.get
                          (Fin.cast
                            (Concrete.Elaboration.compileOccurrencesWith?_length
                              (Concrete.Elaboration.compileRegion?
                                (doubleCutIntroRaw input selection) targetFuel)
                              (targetContext.extend (Fin.castAdd 2 region))
                              targetBinders targetItemsResult).symm
                            (occurrenceEquiv index))) := by
                      simpa [occurrenceEquiv, occurrences] using targetGet
                    let occurrence :=
                      (Concrete.Elaboration.localOccurrences input region).get index
                    have member : occurrence ∈
                        Concrete.Elaboration.localOccurrences input region :=
                      List.get_mem _ _
                    apply occurrence_iso input selection
                      (sourceContext.extend region)
                      (targetContext.extend (Fin.castAdd 2 region))
                      extendedContext sourceBinders targetBinders binders
                      occurrence (Fin.castAdd 2)
                    · intro node occurrenceEq
                      rw [occurrenceEq] at member
                      exact regular_node input selection region regular node
                        ((Concrete.Elaboration.mem_localOccurrences_node input
                          region node).1 member)
                    · intro child occurrenceEq
                      rw [occurrenceEq] at member
                      exact regular_region input selection region child regular
                        ((Concrete.Elaboration.mem_localOccurrences_child input
                          region child).1 member)
                    · intro childSourceRels childTargetRels childSourceBinders
                        childTargetBinders childBinders child occurrenceEq
                        childSourceBody childTargetBody childSourceCompiled
                        childTargetCompiled
                      rw [occurrenceEq] at member
                      have parent :=
                        (Concrete.Elaboration.mem_localOccurrences_child input
                          region child).1 member
                      have childAway : ¬ input.Encloses child
                          selection.val.anchor := by
                        intro childEncloses
                        apply away
                        exact Concrete.Elaboration.checked_encloses_trans
                          wellFormed (direct_child_encloses parent) childEncloses
                      exact induction child childAway
                        (sourceContext.extend region)
                        (targetContext.extend (Fin.castAdd 2 region))
                        extendedContext childSourceBinders childTargetBinders
                        childBinders childSourceCompiled childTargetCompiled
                    · exact sourceGet
                    · exact targetGet'
                  cases binders.rels
                  have wireEquivEq :
                      Concrete.Elaboration.castFinEquiv
                        (Concrete.Elaboration.WireContext.length_extend
                          sourceContext region)
                        (Concrete.Elaboration.WireContext.length_extend
                          targetContext (Fin.castAdd 2 region))
                        (extendWireEquiv
                          (FiniteEquiv.finCast
                            (congrArg List.length context.equality))
                          (FiniteEquiv.finCast (congrArg List.length
                            (exactScopeWires input selection region).symm))) =
                      FiniteEquiv.finCast
                        (congrArg List.length extendedContext.equality) := by
                    apply FiniteEquiv.ext
                    intro index
                    apply Fin.ext
                    change
                      (extendWireEquiv
                        (FiniteEquiv.finCast
                          (congrArg List.length context.equality))
                        (FiniteEquiv.finCast (congrArg List.length
                          (exactScopeWires input selection region).symm))
                        (Fin.cast
                          (Concrete.Elaboration.WireContext.length_extend
                            sourceContext region) index)).val = index.val
                    have castVal :
                        (Fin.cast
                          (Concrete.Elaboration.WireContext.length_extend
                            sourceContext region) index).val = index.val := rfl
                    rw [← castVal]
                    refine Fin.addCases (fun outerIndex => ?_)
                      (fun localIndex => ?_)
                      (Fin.cast
                        (Concrete.Elaboration.WireContext.length_extend
                          sourceContext region) index)
                    · rw [extendWireEquiv_outer]
                      change outerIndex.val = outerIndex.val
                      rfl
                    · rw [extendWireEquiv_local]
                      change targetContext.length + localIndex.val =
                        sourceContext.length + localIndex.val
                      have lengths := congrArg List.length context.equality
                      exact congrArg (fun length => length + localIndex.val)
                        lengths.symm
                  apply Concrete.Elaboration.regionIso_of_cast
                    (Concrete.Elaboration.WireContext.length_extend
                      sourceContext region)
                    (Concrete.Elaboration.WireContext.length_extend
                      targetContext (Fin.castAdd 2 region))
                    (FiniteEquiv.finCast
                      (congrArg List.length context.equality))
                    (FiniteEquiv.finCast (congrArg List.length
                      (exactScopeWires input selection region).symm))
                    sourceItems targetItems
                  rw [wireEquivEq]
                  exact itemsIso

theorem kept_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {sourceFuel targetFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    {sourceItems : ItemSeq sourceContext.length sourceRels}
    {targetItems : ItemSeq targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith? input
      (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
      sourceBinders (keptOccurrences input selection) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input selection) targetFuel)
      targetContext targetBinders
      ((keptOccurrences input selection).map (liftOccurrence input)) =
        some targetItems) :
    ItemSeqIso (FiniteEquiv.finCast
        (congrArg List.length context.equality))
      sourceRels sourceItems (binders.rels ▸ targetItems) := by
  apply occurrences_iso input selection sourceContext targetContext context
    sourceBinders targetBinders binders (keptOccurrences input selection)
    (Fin.castAdd 2)
  · intro node member
    exact unselected_node input selection node
      (kept_node_iff (input := input) (selection := selection) node |>.1
        member).2
  · intro child member
    exact unselected_region input selection child
      (kept_child_iff (input := input) (selection := selection) child |>.1
        member).2
  · intro childSourceRels childTargetRels childSourceBinders
      childTargetBinders childBinders child member sourceBody targetBody
      childSourceCompiled childTargetCompiled
    have parent := (kept_child_iff (input := input) (selection := selection)
      child |>.1 member).1
    have away := Concrete.Elaboration.checked_direct_child_not_encloses_parent
      wellFormed parent
    exact away_region_iso input selection wellFormed child away sourceContext
      targetContext context childSourceBinders childTargetBinders childBinders
      childSourceCompiled childTargetCompiled
  · exact sourceCompiled
  · exact targetCompiled

theorem selected_iso
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {sourceFuel targetFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (context : Context input selection sourceContext targetContext)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binders : Binders input selection sourceBinders targetBinders)
    {sourceItems : ItemSeq sourceContext.length sourceRels}
    {targetItems : ItemSeq targetContext.length targetRels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith? input
      (Concrete.Elaboration.compileRegion? input sourceFuel) sourceContext
      sourceBinders (selectedOccurrences input selection) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input selection) targetFuel)
      targetContext targetBinders
      ((selectedOccurrences input selection).map (liftOccurrence input)) =
        some targetItems) :
    ItemSeqIso (FiniteEquiv.finCast
        (congrArg List.length context.equality))
      sourceRels sourceItems (binders.rels ▸ targetItems) := by
  apply occurrences_iso input selection sourceContext targetContext context
    sourceBinders targetBinders binders (selectedOccurrences input selection)
    (fun _ => inner input)
  · intro node member
    exact selected_node input selection node
      (selected_node_iff (input := input) (selection := selection) node |>.1
        member)
  · intro child member
    exact selected_region input selection child
      (selected_child_iff (input := input) (selection := selection) child |>.1
        member)
  · intro childSourceRels childTargetRels childSourceBinders
      childTargetBinders childBinders child member sourceBody targetBody
      childSourceCompiled childTargetCompiled
    have parent := selection.property.childRoots_direct child
      (selected_child_iff (input := input) (selection := selection) child |>.1
        member)
    have away := Concrete.Elaboration.checked_direct_child_not_encloses_parent
      wellFormed parent
    exact away_region_iso input selection wellFormed child away sourceContext
      targetContext context childSourceBinders childTargetBinders childBinders
      childSourceCompiled childTargetCompiled
  · exact sourceCompiled
  · exact targetCompiled

theorem target_partition
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    {rels : RelCtx}
    (context : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (binders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) rels)
    {fuel : Nat} {body : Region context.length rels}
    (compiled : Concrete.Elaboration.compileRegion?
      (doubleCutIntroRaw input selection) fuel
      (Fin.castAdd 2 selection.val.anchor) context binders = some body) :
    ∃ (kept : ItemSeq
        (context.extend (Fin.castAdd 2 selection.val.anchor)).length rels)
      (selected : ItemSeq
        (((context.extend (Fin.castAdd 2 selection.val.anchor)).extend
          (outer input)).extend (inner input)).length rels)
      (keptFuel selectedFuel : Nat),
      Concrete.Elaboration.compileOccurrencesWith?
          (doubleCutIntroRaw input selection)
          (Concrete.Elaboration.compileRegion?
            (doubleCutIntroRaw input selection) keptFuel)
          (context.extend (Fin.castAdd 2 selection.val.anchor)) binders
          ((keptOccurrences input selection).map (liftOccurrence input)) =
        some kept ∧
      Concrete.Elaboration.compileOccurrencesWith?
          (doubleCutIntroRaw input selection)
          (Concrete.Elaboration.compileRegion?
            (doubleCutIntroRaw input selection) selectedFuel)
          (((context.extend (Fin.castAdd 2 selection.val.anchor)).extend
            (outer input)).extend (inner input)) binders
          ((selectedOccurrences input selection).map (liftOccurrence input)) =
        some selected ∧
      body = Concrete.Elaboration.finishRegion
        (doubleCutIntroRaw input selection) context
        (Fin.castAdd 2 selection.val.anchor)
        (kept.append (.cons (.cut
          (Concrete.Elaboration.finishRegion
            (doubleCutIntroRaw input selection)
            (context.extend (Fin.castAdd 2 selection.val.anchor))
            (outer input) (.cons (.cut
              (Concrete.Elaboration.finishRegion
                (doubleCutIntroRaw input selection)
                ((context.extend (Fin.castAdd 2 selection.val.anchor)).extend
                  (outer input))
                (inner input) selected)) .nil))) .nil)) := by
  cases fuel with
  | zero => simp [Concrete.Elaboration.compileRegion?] at compiled
  | succ anchorFuel =>
      simp only [Concrete.Elaboration.compileRegion?] at compiled
      rw [anchor_localOccurrences] at compiled
      obtain ⟨anchorItems, anchorItemsCompiled, bodyEq⟩ :=
        Option.bind_eq_some_iff.mp compiled
      have bodyEq' := Option.some.inj bodyEq
      subst body
      obtain ⟨kept, outerItems, keptCompiled, outerCompiled,
          anchorItemsEq⟩ :=
        Concrete.Elaboration.compileOccurrencesWith?_append_split
          (d := doubleCutIntroRaw input selection)
          (Concrete.Elaboration.compileRegion?
            (doubleCutIntroRaw input selection) anchorFuel)
          (context.extend (Fin.castAdd 2 selection.val.anchor)) binders
          ((keptOccurrences input selection).map (liftOccurrence input))
          [Concrete.Elaboration.LocalOccurrence.child (outer input)]
          anchorItems anchorItemsCompiled
      rw [anchorItemsEq]
      simp only [Concrete.Elaboration.compileOccurrencesWith?,
        Concrete.Elaboration.compileOccurrenceWith?, outer_region]
        at outerCompiled
      cases outerResult : Concrete.Elaboration.compileRegion?
          (doubleCutIntroRaw input selection) anchorFuel (outer input)
          (context.extend (Fin.castAdd 2 selection.val.anchor)) binders with
      | none => simp [outerResult] at outerCompiled
      | some outerBody =>
          simp [outerResult] at outerCompiled
          subst outerItems
          cases anchorFuel with
          | zero =>
              simp [Concrete.Elaboration.compileRegion?] at outerResult
          | succ outerFuel =>
              simp only [Concrete.Elaboration.compileRegion?] at outerResult
              rw [outer_localOccurrences] at outerResult
              obtain ⟨outerItems, outerItemsCompiled, outerBodyEq⟩ :=
                Option.bind_eq_some_iff.mp outerResult
              have outerBodyEq' := Option.some.inj outerBodyEq
              subst outerBody
              simp only [Concrete.Elaboration.compileOccurrencesWith?,
                Concrete.Elaboration.compileOccurrenceWith?, inner_region]
                at outerItemsCompiled
              cases innerResult : Concrete.Elaboration.compileRegion?
                  (doubleCutIntroRaw input selection) outerFuel (inner input)
                  ((context.extend (Fin.castAdd 2 selection.val.anchor)).extend
                    (outer input)) binders with
              | none => simp [innerResult] at outerItemsCompiled
              | some innerBody =>
                  simp [innerResult] at outerItemsCompiled
                  subst outerItems
                  cases outerFuel with
                  | zero =>
                      simp [Concrete.Elaboration.compileRegion?] at innerResult
                  | succ innerFuel =>
                      simp only [Concrete.Elaboration.compileRegion?]
                        at innerResult
                      rw [inner_localOccurrences] at innerResult
                      obtain ⟨selected, selectedCompiled, innerBodyEq⟩ :=
                        Option.bind_eq_some_iff.mp innerResult
                      have innerBodyEq' := Option.some.inj innerBodyEq
                      subst innerBody
                      exact ⟨kept, selected, innerFuel + 1 + 1, innerFuel,
                        keptCompiled, selectedCompiled, rfl⟩

end VisualProof.Refinement.Implementation.DoubleCutIntroCompile
