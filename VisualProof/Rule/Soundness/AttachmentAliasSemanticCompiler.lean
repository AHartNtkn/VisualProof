import VisualProof.Rule.Soundness.AttachmentAliasSemanticGraph

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) = (allFin n).map (Fin.castAdd 1) ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun values : List (Fin (n + 1)) =>
    values ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  apply Fin.ext
  rfl

theorem allFin_add (n m : Nat) :
    allFin (n + m) =
      (allFin n).map (Fin.castAdd m) ++
        (allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, allFin, List.map_nil, List.append_nil]
      have hfun : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        apply Fin.ext
        rfl
      rw [hfun, List.map_id]
  | succ m ih =>
      change allFin ((n + m) + 1) = _
      rw [allFin_succ_last (n + m), ih, List.map_append,
        allFin_succ_last m, List.map_append, List.map_map,
        List.append_assoc]
      simp only [List.map_map]
      have hleft :
          (Fin.castAdd 1 ∘ Fin.castAdd m : Fin n → Fin ((n + m) + 1)) =
            Fin.castAdd (m + 1) := by
        funext index
        apply Fin.ext
        rfl
      have hmiddle :
          (Fin.castAdd 1 ∘ Fin.natAdd n : Fin m → Fin ((n + m) + 1)) =
            (Fin.natAdd n ∘ Fin.castAdd 1) := by
        funext index
        apply Fin.ext
        rfl
      have hlast : Fin.last (n + m) = Fin.natAdd n (Fin.last m) := by
        apply Fin.ext
        rfl
      rw [hleft, hmiddle, hlast]
      rfl

def liftOccurrence (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    ConcreteElaboration.LocalOccurrence pattern.diagram.regionCount
        pattern.diagram.nodeCount →
      ConcreteElaboration.LocalOccurrence pattern.diagram.regionCount
        (pattern.diagram.nodeCount + aliasCount pattern attachment)
  | .node node => .node (liftOldNode pattern attachment node)
  | .child child => .child child

def sourceNodeOccurrences (pattern : OpenConcreteDiagram)
    (region : Fin pattern.diagram.regionCount) :
    List (ConcreteElaboration.LocalOccurrence pattern.diagram.regionCount
      pattern.diagram.nodeCount) :=
  (filterFin fun node => decide ((pattern.diagram.nodes node).region = region)).map
    ConcreteElaboration.LocalOccurrence.node

def sourceChildOccurrences (pattern : OpenConcreteDiagram)
    (region : Fin pattern.diagram.regionCount) :
    List (ConcreteElaboration.LocalOccurrence pattern.diagram.regionCount
      pattern.diagram.nodeCount) :=
  (filterFin fun child =>
    decide ((pattern.diagram.regions child).parent? = some region)).map
      ConcreteElaboration.LocalOccurrence.child

def aliasOccurrences (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host) :
    List (ConcreteElaboration.LocalOccurrence pattern.diagram.regionCount
      (pattern.diagram.nodeCount + aliasCount pattern attachment)) :=
  (allFin (aliasCount pattern attachment)).map fun aliasIndex =>
    .node (aliasNode pattern attachment aliasIndex)

theorem source_localOccurrences (pattern : OpenConcreteDiagram)
    (region : Fin pattern.diagram.regionCount) :
    ConcreteElaboration.localOccurrences pattern.diagram region =
      sourceNodeOccurrences pattern region ++
        sourceChildOccurrences pattern region := rfl

theorem materialized_regular_localOccurrences
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer region : Fin pattern.diagram.regionCount)
    (regular : region ≠ bodyContainer) :
    ConcreteElaboration.localOccurrences
        (materializedDiagram pattern attachment bodyContainer) region =
      (ConcreteElaboration.localOccurrences pattern.diagram region).map
        (liftOccurrence pattern attachment) := by
  unfold ConcreteElaboration.localOccurrences filterFin
  change
    (List.filter _ (allFin (pattern.diagram.nodeCount +
      aliasCount pattern attachment))).map
        (@ConcreteElaboration.LocalOccurrence.node pattern.diagram.regionCount
          (pattern.diagram.nodeCount + aliasCount pattern attachment)) ++
      (List.filter _ (allFin pattern.diagram.regionCount)).map
        (@ConcreteElaboration.LocalOccurrence.child pattern.diagram.regionCount
          (pattern.diagram.nodeCount + aliasCount pattern attachment)) = _
  rw [allFin_add pattern.diagram.nodeCount (aliasCount pattern attachment),
    List.filter_append]
  simp only [List.filter_map, List.map_append, List.map_map]
  have freshEmpty :
      List.filter
        ((fun node => decide
          (((materializedDiagram pattern attachment bodyContainer).nodes
            node).region = region)) ∘ Fin.natAdd pattern.diagram.nodeCount)
        (allFin (aliasCount pattern attachment)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro aliasIndex _ member
    apply regular
    simpa [materializedDiagram] using (of_decide_eq_true member).symm
  have oldFilter :
      List.filter
        ((fun node => decide
          (((materializedDiagram pattern attachment bodyContainer).nodes
            node).region = region)) ∘
              Fin.castAdd (aliasCount pattern attachment))
        (allFin pattern.diagram.nodeCount) =
      List.filter
        (fun node => decide ((pattern.diagram.nodes node).region = region))
        (allFin pattern.diagram.nodeCount) := by
    apply congrArg (fun predicate =>
      List.filter predicate (allFin pattern.diagram.nodeCount))
    funext node
    simp [materializedDiagram, liftOldNode]
  dsimp only [materializedDiagram] at freshEmpty oldFilter ⊢
  rw [freshEmpty, oldFilter]
  simp only [List.map_nil, List.append_nil, List.map_map]
  congr 1

theorem materialized_focused_localOccurrences
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount) :
    ConcreteElaboration.localOccurrences
        (materializedDiagram pattern attachment bodyContainer) bodyContainer =
      (sourceNodeOccurrences pattern bodyContainer).map
          (liftOccurrence pattern attachment) ++
        aliasOccurrences pattern attachment ++
        (sourceChildOccurrences pattern bodyContainer).map
          (liftOccurrence pattern attachment) := by
  unfold ConcreteElaboration.localOccurrences filterFin sourceNodeOccurrences
    sourceChildOccurrences aliasOccurrences
  change
    (List.filter _ (allFin (pattern.diagram.nodeCount +
      aliasCount pattern attachment))).map
        (@ConcreteElaboration.LocalOccurrence.node pattern.diagram.regionCount
          (pattern.diagram.nodeCount + aliasCount pattern attachment)) ++
      (List.filter _ (allFin pattern.diagram.regionCount)).map
        (@ConcreteElaboration.LocalOccurrence.child pattern.diagram.regionCount
          (pattern.diagram.nodeCount + aliasCount pattern attachment)) = _
  rw [allFin_add pattern.diagram.nodeCount (aliasCount pattern attachment),
    List.filter_append]
  simp only [List.filter_map, List.map_append, List.map_map]
  have oldFilter :
      List.filter
        ((fun node => decide
          (((materializedDiagram pattern attachment bodyContainer).nodes
            node).region = bodyContainer)) ∘
              Fin.castAdd (aliasCount pattern attachment))
        (allFin pattern.diagram.nodeCount) =
      List.filter
        (fun node => decide
          ((pattern.diagram.nodes node).region = bodyContainer))
        (allFin pattern.diagram.nodeCount) := by
    apply congrArg (fun predicate =>
      List.filter predicate (allFin pattern.diagram.nodeCount))
    funext node
    simp [materializedDiagram, liftOldNode]
  have aliasFilter :
      List.filter
        ((fun node => decide
          (((materializedDiagram pattern attachment bodyContainer).nodes
            node).region = bodyContainer)) ∘
              Fin.natAdd pattern.diagram.nodeCount)
        (allFin (aliasCount pattern attachment)) =
      allFin (aliasCount pattern attachment) := by
    apply List.filter_eq_self.mpr
    intro aliasIndex _
    simp only [Function.comp_apply, materializedDiagram, Fin.addCases_right,
      CNode.region, decide_true]
  dsimp only [materializedDiagram] at oldFilter aliasFilter ⊢
  rw [oldFilter, aliasFilter]
  simp [liftOccurrence, liftOldNode, aliasNode, filterFin, Function.comp_def,
    List.append_assoc]
  rfl

/-- Retained nodes compile with exactly the materialized-wire collapse
relation on their resolved ports. -/
theorem oldNode_itemSimulation
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext
      sourceContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceNode : Fin pattern.val.diagram.nodeCount)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      pattern.val.diagram sourceContext sourceBinders sourceNode =
        some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetContext targetBinders
      (liftOldNode pattern.val attachment sourceNode) = some targetItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.backwardMap collapse.indexMap)
      sourceItem targetItem := by
  cases bindersEqual
  have simulation :=
    ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      (source := pattern.val.diagram)
      (target := materializedDiagram pattern.val attachment spine.bodyContainer)
      model named direction sourceContext targetContext
      (ConcreteElaboration.ContextIndexRelation.backwardMap collapse.indexMap)
      sourceBinders sourceBinders
      (ConcreteElaboration.identityRelationRenaming rels)
      (sourceNode := sourceNode)
      (targetNode := liftOldNode pattern.val attachment sourceNode)
      (regionMap := id) (binderMap := id)
      (nodeShape := by
        cases shape : pattern.val.diagram.nodes sourceNode <;>
          simp [materializedDiagram, liftOldNode, shape])
      (portsRelated := by
        intro port sourceIndex targetIndex sourceResolved targetResolved
        obtain ⟨sourceOwner, sourceOccurs, sourceGet⟩ :=
          ConcreteElaboration.resolvePort?_sound sourceResolved
        obtain ⟨targetOwner, targetOccurs, targetGet⟩ :=
          ConcreteElaboration.resolvePort?_sound targetResolved
        obtain ⟨origin, originEq, originOccurs⟩ :=
          oldEndpointOccurs_backward pattern.val attachment spine.bodyContainer
            targetOwner { node := sourceNode, port := port } (by
              simpa [liftOldEndpoint, liftOldNode] using targetOccurs)
        have ownerEq : origin = sourceOwner :=
          ConcreteElaboration.endpoint_wire_unique
            pattern.property.diagram_well_formed.wire_endpoints_are_disjoint
            originOccurs sourceOccurs
        have sourceGetList : sourceContext.get sourceIndex = sourceOwner := by
          simpa only [List.get_eq_getElem] using sourceGet
        have targetGetList : targetContext.get targetIndex = targetOwner := by
          simpa only [List.get_eq_getElem] using targetGet
        change collapse.indexMap targetIndex = sourceIndex
        apply Fin.ext
        exact (List.getElem_inj sourceNodup).mp (by
          have mappedGet := collapse.get targetIndex
          rw [targetGetList, ← originEq, collapseWire_old, ownerEq] at mappedGet
          have sourceGetSymm := sourceGetList.symm
          have valuesEq := Eq.trans mappedGet sourceGetSymm
          simpa only [List.get_eq_getElem] using valuesEq))
      (bindersRelated := by
        intro region binder arity sourceRelation nodeShape binderLookup
        simpa [ConcreteElaboration.identityRelationRenaming] using binderLookup)
      (sourceItem := sourceItem) (targetItem := targetItem)
      sourceCompiled targetCompiled
  have relationMapEq :
      (ConcreteElaboration.identityRelationRenaming rels :
        RelationRenaming rels rels) =
      (fun {arity} (relation : RelVar rels arity) => relation) := rfl
  rw [relationMapEq, Item.renameRelations_id] at simulation
  exact simulation

/-- Retained nodes also admit the embedding-oriented relation that selects
the canonical lifted-old target position.  This orientation deliberately
ignores fresh alias positions until the distinguished identity block. -/
theorem oldNode_itemSimulation_oldIndex
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (collapse : ContextCollapse pattern attachment spine targetContext
      sourceContext)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext pattern.val.diagram rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceNode : Fin pattern.val.diagram.nodeCount)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      pattern.val.diagram sourceContext sourceBinders sourceNode =
        some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer)
      targetContext targetBinders
      (liftOldNode pattern.val attachment sourceNode) = some targetItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
      sourceItem targetItem := by
  cases bindersEqual
  have simulation :=
    ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      (source := pattern.val.diagram)
      (target := materializedDiagram pattern.val attachment spine.bodyContainer)
      model named direction sourceContext targetContext
      (ConcreteElaboration.ContextIndexRelation.forwardMap collapse.oldIndex)
      sourceBinders sourceBinders
      (ConcreteElaboration.identityRelationRenaming rels)
      (sourceNode := sourceNode)
      (targetNode := liftOldNode pattern.val attachment sourceNode)
      (regionMap := id) (binderMap := id)
      (nodeShape := by
        cases shape : pattern.val.diagram.nodes sourceNode <;>
          simp [materializedDiagram, liftOldNode, shape])
      (portsRelated := by
        intro port sourceIndex targetIndex sourceResolved targetResolved
        obtain ⟨sourceOwner, sourceOccurs, sourceGet⟩ :=
          ConcreteElaboration.resolvePort?_sound sourceResolved
        obtain ⟨targetOwner, targetOccurs, targetGet⟩ :=
          ConcreteElaboration.resolvePort?_sound targetResolved
        obtain ⟨origin, originEq, originOccurs⟩ :=
          oldEndpointOccurs_backward pattern.val attachment spine.bodyContainer
            targetOwner { node := sourceNode, port := port } (by
              simpa [liftOldEndpoint, liftOldNode] using targetOccurs)
        have ownerEq : origin = sourceOwner :=
          ConcreteElaboration.endpoint_wire_unique
            pattern.property.diagram_well_formed.wire_endpoints_are_disjoint
            originOccurs sourceOccurs
        change collapse.oldIndex sourceIndex = targetIndex
        apply Fin.ext
        exact (List.getElem_inj targetNodup).mp (by
          have sourceGetList : sourceContext.get sourceIndex = sourceOwner := by
            simpa only [List.get_eq_getElem] using sourceGet
          have targetGetList : targetContext.get targetIndex = targetOwner := by
            simpa only [List.get_eq_getElem] using targetGet
          have oldGet := collapse.old_get sourceIndex
          rw [sourceGetList, ← ownerEq, originEq] at oldGet
          simpa only [List.get_eq_getElem] using oldGet.trans targetGetList.symm))
      (bindersRelated := by
        intro region binder arity sourceRelation nodeShape binderLookup
        simpa [ConcreteElaboration.identityRelationRenaming] using binderLookup)
      (sourceItem := sourceItem) (targetItem := targetItem)
      sourceCompiled targetCompiled
  have relationMapEq :
      (ConcreteElaboration.identityRelationRenaming rels :
        RelationRenaming rels rels) =
      (fun {arity} (relation : RelVar rels arity) => relation) := rfl
  rw [relationMapEq, Item.renameRelations_id] at simulation
  exact simulation

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
