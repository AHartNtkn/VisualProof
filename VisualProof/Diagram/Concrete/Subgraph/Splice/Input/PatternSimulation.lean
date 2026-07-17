import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Presentation.Transport

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace PlugLayout

/-- Total region map for the input-local pattern simulation.  Retained
material maps to its actual plug body region; regions removed by the binder
spine are sent to the plug root and are never admitted by `AtRegion`. -/
def patternSimulationRegionMap (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount) :
    Fin layout.plugRaw.regionCount :=
  if input.binderSpine.IsMaterialRegion region then
    layout.bodyRegion region
  else
    layout.plugRaw.root

theorem patternSimulationRegionMap_material
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    layout.patternSimulationRegionMap region = layout.bodyRegion region := by
  simp [patternSimulationRegionMap, hregion]

theorem patternSimulationRegionMap_nonmaterial
    (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : ¬ input.binderSpine.IsMaterialRegion region) :
    layout.patternSimulationRegionMap region = layout.plugRaw.root := by
  simp [patternSimulationRegionMap, hregion]

/-- A context pair may be unavailable at opaque nonmaterial regions.  At a
material region it carries the concrete pattern-to-plug index map. -/
abbrev PatternContextWitness
    (layout : PlugLayout input)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw) : Type :=
  Option (Fin sourceContext.length → Fin targetContext.length)

def PatternAtRegion
    (layout : PlugLayout input)
    {sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram}
    {targetContext : ConcreteElaboration.WireContext layout.plugRaw}
    (witness : layout.PatternContextWitness sourceContext targetContext)
    (region : Fin input.pattern.val.diagram.regionCount) : Prop :=
  input.binderSpine.IsMaterialRegion region ∧
    ∃ indexMap : Fin sourceContext.length → Fin targetContext.length,
      witness = some indexMap ∧
      (∀ index, targetContext.get (indexMap index) =
        layout.patternPlugWire (sourceContext.get index)) ∧
      (∀ wire, layout.patternPlugWire wire ∈ targetContext ↔
        wire ∈ sourceContext)

def patternContextIndexRelation
    (layout : PlugLayout input)
    {sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram}
    {targetContext : ConcreteElaboration.WireContext layout.plugRaw}
    (witness : layout.PatternContextWitness sourceContext targetContext) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length :=
  match witness with
  | none => { Rel := fun _ _ => False }
  | some indexMap =>
      ConcreteElaboration.ContextIndexRelation.forwardMap indexMap

noncomputable def patternExtendedWireMapAt
    (layout : PlugLayout input)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (targetRegion : Fin layout.plugRaw.regionCount)
    (targetEq : targetRegion = layout.bodyRegion region)
    (indexMap : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.extend targetRegion).length := by
  subst targetRegion
  exact layout.materialExtendedWireMap region hregion sourceContext
    targetContext indexMap

noncomputable def patternExtendedWireMap
    (layout : PlugLayout input)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (indexMap : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.extend
        (layout.patternSimulationRegionMap region)).length :=
  layout.patternExtendedWireMapAt sourceContext targetContext region hregion
    (layout.patternSimulationRegionMap region)
    (layout.patternSimulationRegionMap_material region hregion) indexMap

noncomputable def extendPatternContext
    (layout : PlugLayout input)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (witness : layout.PatternContextWitness sourceContext targetContext)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region) :
    layout.PatternContextWitness (sourceContext.extend region)
      (targetContext.extend (layout.patternSimulationRegionMap region)) :=
  witness.map fun indexMap =>
    layout.patternExtendedWireMap sourceContext targetContext region hregion
      indexMap

theorem patternExtendedWireMapAt_spec
    (layout : PlugLayout input)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (targetRegion : Fin layout.plugRaw.regionCount)
    (targetEq : targetRegion = layout.bodyRegion region)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (indexSpec : ∀ index, targetContext.get (indexMap index) =
      layout.patternPlugWire (sourceContext.get index)) :
    ∀ index,
      (targetContext.extend targetRegion).get
          (layout.patternExtendedWireMapAt sourceContext targetContext region
            hregion targetRegion targetEq indexMap index) =
        layout.patternPlugWire ((sourceContext.extend region).get index) := by
  subst targetRegion
  simpa [patternExtendedWireMapAt] using
    layout.materialExtendedWireMap_spec region hregion sourceContext
      targetContext indexMap indexSpec

theorem patternExtendedWireMap_spec
    (layout : PlugLayout input)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (indexSpec : ∀ index, targetContext.get (indexMap index) =
      layout.patternPlugWire (sourceContext.get index)) :
    ∀ index,
      (targetContext.extend (layout.patternSimulationRegionMap region)).get
          (layout.patternExtendedWireMap sourceContext targetContext region
            hregion indexMap index) =
        layout.patternPlugWire ((sourceContext.extend region).get index) := by
  exact layout.patternExtendedWireMapAt_spec sourceContext targetContext region
    hregion (layout.patternSimulationRegionMap region)
    (layout.patternSimulationRegionMap_material region hregion) indexMap
    indexSpec

theorem patternPlugWire_mem_extendedContext_iff
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (layout.patternSimulationRegionMap region)).Exact
        (layout.patternSimulationRegionMap region)) :
    ∀ wire, layout.patternPlugWire wire ∈
        targetContext.extend (layout.patternSimulationRegionMap region) ↔
      wire ∈ sourceContext.extend region := by
  simpa [patternSimulationRegionMap, hregion] using
    layout.patternPlugWire_mem_materialContext_iff hadmissible region hregion
      (sourceContext.extend region)
      (targetContext.extend (layout.bodyRegion region)) sourceExact
      (by simpa [patternSimulationRegionMap, hregion] using targetExact)

theorem patternLocalSelection
    (layout : PlugLayout input)
    (direction : ConcreteElaboration.SimulationDirection)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin sourceContext.length → model.Carrier)
      (targetOuter : Fin targetContext.length → model.Carrier),
      (ConcreteElaboration.ContextIndexRelation.forwardMap indexMap)
          |>.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (layout.materialExtendedWireMap region hregion sourceContext
                  targetContext indexMap)).EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (layout.bodyRegion region) targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (layout.materialExtendedWireMap region hregion sourceContext
                  targetContext indexMap)).EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (layout.bodyRegion region) targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgrees
  rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
    at outerAgrees
  let localEquiv := layout.materialLocalWireEquiv region hregion
  cases direction with
  | forward =>
      intro sourceLocal
      refine ⟨fun targetLocal => sourceLocal (localEquiv.symm targetLocal), ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).2
      funext index
      let split := Fin.cast
        (ConcreteElaboration.WireContext.length_extend sourceContext region) index
      have recover : Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
          split = index := by
        apply Fin.ext
        rfl
      rw [← recover]
      refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
      · simpa [ConcreteElaboration.extendedEnvironment,
          materialExtendedWireMap, split, Function.comp_def, extendWireEnv] using
          congrFun outerAgrees outer
      · simpa [ConcreteElaboration.extendedEnvironment,
          materialExtendedWireMap, split, localEquiv, extendWireEnv] using
          congrArg sourceLocal (localEquiv.left_inv localIndex).symm
  | backward =>
      intro targetLocal
      refine ⟨fun sourceLocal => targetLocal (localEquiv sourceLocal), ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).2
      funext index
      let split := Fin.cast
        (ConcreteElaboration.WireContext.length_extend sourceContext region) index
      have recover : Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
          split = index := by
        apply Fin.ext
        rfl
      rw [← recover]
      refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
      · simpa [ConcreteElaboration.extendedEnvironment,
          materialExtendedWireMap, split, Function.comp_def, extendWireEnv] using
          congrFun outerAgrees outer
      · simp [ConcreteElaboration.extendedEnvironment,
          materialExtendedWireMap, split, localEquiv, extendWireEnv,
          FiniteEquiv.symm_apply_apply]

theorem patternLocalSelectionAt
    (layout : PlugLayout input)
    (direction : ConcreteElaboration.SimulationDirection)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (targetRegion : Fin layout.plugRaw.regionCount)
    (targetEq : targetRegion = layout.bodyRegion region)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin sourceContext.length → model.Carrier)
      (targetOuter : Fin targetContext.length → model.Carrier),
      (ConcreteElaboration.ContextIndexRelation.forwardMap indexMap)
          |>.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (layout.patternExtendedWireMapAt sourceContext targetContext
                  region hregion targetRegion targetEq indexMap))
                |>.EnvironmentsAgree
                  (ConcreteElaboration.extendedEnvironment sourceContext region
                    sourceOuter sourceLocal)
                  (ConcreteElaboration.extendedEnvironment targetContext
                    targetRegion targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (layout.patternExtendedWireMapAt sourceContext targetContext
                  region hregion targetRegion targetEq indexMap))
                |>.EnvironmentsAgree
                  (ConcreteElaboration.extendedEnvironment sourceContext region
                    sourceOuter sourceLocal)
                  (ConcreteElaboration.extendedEnvironment targetContext
                    targetRegion targetOuter targetLocal) := by
  subst targetRegion
  simpa [patternExtendedWireMapAt] using
    layout.patternLocalSelection direction region hregion sourceContext
      targetContext indexMap model

theorem patternLocalSelectionMapped
    (layout : PlugLayout input)
    (direction : ConcreteElaboration.SimulationDirection)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceContext : ConcreteElaboration.WireContext input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin sourceContext.length → model.Carrier)
      (targetOuter : Fin targetContext.length → model.Carrier),
      (ConcreteElaboration.ContextIndexRelation.forwardMap indexMap)
          |>.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (layout.patternExtendedWireMap sourceContext targetContext
                  region hregion indexMap)).EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (layout.patternSimulationRegionMap region) targetOuter
                  targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (layout.patternExtendedWireMap sourceContext targetContext
                  region hregion indexMap)).EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  (layout.patternSimulationRegionMap region) targetOuter
                  targetLocal) := by
  exact layout.patternLocalSelectionAt direction region hregion
    (layout.patternSimulationRegionMap region)
    (layout.patternSimulationRegionMap_material region hregion) sourceContext
    targetContext indexMap model

/-- The input-local authoritative simulation from the intrinsic pattern graph
to the corresponding retained material inside the concrete plug. -/
noncomputable def patternConcreteSemanticSimulation
    {signature : List Nat}
    {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature
      input.pattern.val.diagram layout.plugRaw model named where
  source_wellFormed := input.pattern.property.diagram_well_formed
  target_wellFormed := layout.plugRaw_wellFormed signature input hadmissible
  regionMap := layout.patternSimulationRegionMap
  binderMap := layout.binderRegion
  Distinguished := fun region =>
    ¬ input.binderSpine.IsMaterialRegion region
  occurrenceMap := fun _region _regular occurrence =>
    match occurrence with
    | .node node => .node (layout.patternNode node)
    | .child child => .child (layout.patternSimulationRegionMap child)
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨layout.patternNode node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := by
    rw [layout.patternSimulationRegionMap_nonmaterial
      input.pattern.val.diagram.root (by
        simp [BinderSpine.IsMaterialRegion])]
  region_shape := by
    intro parent regular child childParent
    have hparent : input.binderSpine.IsMaterialRegion parent :=
      Classical.byContradiction fun absent => regular absent
    have hchild := PlugLayout.directChildOfMaterial_material input parent child
      hparent childParent
    rw [layout.patternSimulationRegionMap_material child hchild]
    cases kind : input.pattern.val.diagram.regions child with
    | sheet => simp [kind, CRegion.parent?] at childParent
    | cut actualParent =>
        have equality : actualParent = parent := by
          rw [kind] at childParent
          exact Option.some.inj childParent
        subst actualParent
        simpa [kind, layout.patternSimulationRegionMap_material parent hparent]
          using layout.plugRaw_bodyRegion_cut child parent hchild kind
    | bubble actualParent arity =>
        have equality : actualParent = parent := by
          rw [kind] at childParent
          exact Option.some.inj childParent
        subst actualParent
        simpa [kind, layout.patternSimulationRegionMap_material parent hparent]
          using layout.plugRaw_bodyRegion_bubble child parent arity hchild kind
  localOccurrences_map := by
    intro region regular
    have hregion : input.binderSpine.IsMaterialRegion region :=
      Classical.byContradiction fun absent => regular absent
    rw [layout.patternSimulationRegionMap_material region hregion,
      TwoInputPresentation.PlugLayout.localOccurrences_bodyRegion layout region
        hregion]
    apply List.map_congr_left
    intro occurrence member
    cases occurrence with
    | node node => rfl
    | child child =>
        have parent :=
          (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 member
        have hchild := PlugLayout.directChildOfMaterial_material input region
          child hregion parent
        simp [layout.patternSimulationRegionMap_material child hchild,
          mapPatternOccurrence]
  BinderWitness := fun sourceBinders targetBinders =>
    PatternBinderWitness layout sourceBinders targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := PatternBinderWitness.empty layout
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    have hparent : input.binderSpine.IsMaterialRegion parent :=
      Classical.byContradiction fun absent => regular absent
    have childParent :
        (input.pattern.val.diagram.regions child).parent? = some parent := by
      simp [childKind, CRegion.parent?]
    have hchild := PlugLayout.directChildOfMaterial_material input parent child
      hparent childParent
    refine {
      relationMap := RelationRenaming.lift witness.relationMap arity
      lookup := ?_ }
    intro binder relationArity relation sourceLookup
    by_cases hbinder : binder = child
    · subst binder
      rw [ConcreteElaboration.BinderContext.push_self] at sourceLookup
      have payload := Option.some.inj sourceLookup
      cases payload
      simp [layout.binderRegion_material child hchild,
        patternSimulationRegionMap, hchild,
        ConcreteElaboration.BinderContext.push_self,
        ConcreteElaboration.BinderContext.head, RelationRenaming.lift]
    · rw [ConcreteElaboration.BinderContext.push_other sourceBinders arity
          hbinder] at sourceLookup
      cases hsource : sourceBinders binder with
      | none => simp [hsource] at sourceLookup
      | some payload =>
          rcases payload with ⟨sourceArity, sourceRelation⟩
          simp only [hsource, Option.map_some] at sourceLookup
          have targetNe : layout.binderRegion binder ≠
              layout.patternSimulationRegionMap child := by
            simpa [patternSimulationRegionMap, hchild] using
              layout.binderRegion_ne_bodyRegion_of_ne_material binder child
                hchild hbinder
          rw [ConcreteElaboration.BinderContext.push_other targetBinders arity
            targetNe]
          rw [witness.lookup binder sourceRelation hsource]
          cases sourceLookup
          rfl
  relationMap_push := by
    intros
    rfl
  Allowed := fun _direction _region => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := fun sourceContext targetContext =>
    layout.PatternContextWitness sourceContext targetContext
  AtRegion := fun witness region => layout.PatternAtRegion witness region
  indexRelation := fun witness => layout.patternContextIndexRelation witness
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    have hregion : input.binderSpine.IsMaterialRegion region :=
      Classical.byContradiction fun absent => regular absent
    exact layout.extendPatternContext sourceContext targetContext witness region
      hregion
  extendFocusedContext := by
    intro sourceContext targetContext witness region focused sourceExact
      targetExact
    exact none
  at_child := by
    intro sourceContext targetContext witness parent regular sourceExact
      targetExact child atParent childParent
    rcases atParent with ⟨hparent, indexMap, witnessEq, indexSpec, memberSpec⟩
    subst witness
    have hchild := PlugLayout.directChildOfMaterial_material input parent child
      hparent childParent
    refine ⟨hchild, layout.patternExtendedWireMap sourceContext targetContext
      parent hparent indexMap, ?_, ?_, ?_⟩
    · simp [extendPatternContext, patternExtendedWireMap]
    · exact layout.patternExtendedWireMap_spec sourceContext targetContext
        parent hparent indexMap indexSpec
    · exact layout.patternPlugWire_mem_extendedContext_iff hadmissible
        sourceContext targetContext parent hparent sourceExact targetExact
  at_extended := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact atRegion
    rcases atRegion with ⟨hregion, indexMap, witnessEq, indexSpec, memberSpec⟩
    subst witness
    refine ⟨hregion, layout.patternExtendedWireMap sourceContext targetContext
      region hregion indexMap, ?_, ?_, ?_⟩
    · simp [extendPatternContext, patternExtendedWireMap]
    · exact layout.patternExtendedWireMap_spec sourceContext targetContext
        region hregion indexMap indexSpec
    · exact layout.patternPlugWire_mem_extendedContext_iff hadmissible
        sourceContext targetContext region hregion sourceExact targetExact
  at_focused_child := by
    intro sourceContext targetContext witness parent focused sourceExact
      targetExact child atParent sourceParent targetParent
    exact False.elim (focused atParent.1)
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext witness sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact _ _ _ _ sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics
    rcases atRegion with ⟨hregion, indexMap, witnessEq, indexSpec, memberSpec⟩
    subst witness
    refine ConcreteElaboration.directionalLocalTransport_of_agreement direction
      sourceContext targetContext region
      (layout.patternSimulationRegionMap region)
      (ConcreteElaboration.ContextIndexRelation.forwardMap indexMap)
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (layout.patternExtendedWireMap sourceContext targetContext region
          hregion indexMap)) model named
      (sourceItems.renameRelations binderWitness.relationMap) targetItems ?_
      itemSemantics
    exact layout.patternLocalSelectionMapped direction region hregion
      sourceContext targetContext indexMap model
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    rcases atRegion with
      ⟨hregion, indexMap, contextEq, indexSpec, memberSpec⟩
    subst context
    have targetNodeEq := ConcreteElaboration.LocalOccurrence.node.inj mapped
    subst targetNode
    apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      (source := input.pattern.val.diagram)
      (target := layout.plugRaw)
      model named direction sourceContext targetContext
      (ConcreteElaboration.ContextIndexRelation.forwardMap indexMap)
      sourceBinders targetBinders binderWitness.relationMap sourceNode
      (layout.patternNode sourceNode)
      (regionMap := layout.bodyRegion)
      (binderMap := layout.binderRegion)
    · change layout.plugNode (layout.patternNode sourceNode) = _
      rw [layout.plugNode_patternNode]
      cases hsource : input.pattern.val.diagram.nodes sourceNode <;> rfl
    · intro port sourceIndex targetIndex sourceResolved targetResolved
      have resolved := ConcreteElaboration.resolvePort?_map_of_occurrence
        sourceContext targetContext sourceNode (layout.patternNode sourceNode)
        layout.patternPlugWire indexMap targetNodup indexSpec memberSpec
        (fun wire requested occurs => by
          simpa [mapPatternEndpoint] using
            layout.plugRaw_patternEndpoint_forward wire
              ⟨sourceNode, requested⟩ occurs)
        (fun targetWire requested occurs => by
          obtain ⟨sourceWire, wireEq, sourceOccurs⟩ :=
            layout.plugRaw_patternEndpoint_backward targetWire
              ⟨sourceNode, requested⟩ (by
                simpa [mapPatternEndpoint] using occurs)
          exact ⟨sourceWire, wireEq, sourceOccurs⟩)
        ((layout.plugRaw_wellFormed signature input hadmissible)
          |>.wire_endpoints_are_disjoint) port
      rw [targetResolved, sourceResolved] at resolved
      exact Option.some.inj resolved |>.symm
    · intro binderRegion binder arity sourceRelation sourceShape sourceLookup
      exact binderWitness.lookup binder sourceRelation sourceLookup
    · exact sourceCompiled
    · exact targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext context sourceBinders targetBinders atRegion
      focused
    exact False.elim (focused atRegion.1)

/-- Public material-region entry point for the intrinsic pattern simulation.
All recursive cut and bubble semantics are delegated to the generalized
compiler theorem; callers supply only the actual compiler contexts and
results reached at the enclosing splice site. -/
theorem compilePatternRegion_denote_at_material
    {signature : List Nat}
    {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {sourceRels targetRels : Theory.RelCtx}
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext
      input.pattern.val.diagram)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (indexMap : Fin sourceContext.length → Fin targetContext.length)
    (indexSpec : ∀ index, targetContext.get (indexMap index) =
      layout.patternPlugWire (sourceContext.get index))
    (memberSpec : ∀ wire, layout.patternPlugWire wire ∈ targetContext ↔
      wire ∈ sourceContext)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (binderWitness : PatternBinderWitness layout sourceBinders targetBinders)
    (region : Fin input.pattern.val.diagram.regionCount)
    (hregion : input.binderSpine.IsMaterialRegion region)
    (sourceBindersCover : sourceBinders.Covers region)
    (targetBindersCover : targetBinders.Covers (layout.bodyRegion region))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      layout.plugRaw targetBinders (layout.bodyRegion region))
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend (layout.bodyRegion region)).Exact
      (layout.bodyRegion region))
    (sourceBody : Region signature sourceContext.length sourceRels)
    (targetBody : Region signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileRegion? signature
      input.pattern.val.diagram fuelSource region sourceContext sourceBinders =
        some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRegion? signature
      layout.plugRaw fuelTarget (layout.bodyRegion region) targetContext
        targetBinders = some targetBody) :
    ConcreteElaboration.RegionSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap indexMap)
      (sourceBody.renameRelations binderWitness.relationMap) targetBody := by
  let simulation := layout.patternConcreteSemanticSimulation hadmissible model
    named
  have atRegion : simulation.AtRegion (some indexMap) region :=
    ⟨hregion, indexMap, rfl, indexSpec, memberSpec⟩
  have result := simulation.compileRegion_denote direction fuelSource fuelTarget
    region sourceContext targetContext (some indexMap) atRegion sourceBinders
    targetBinders (by trivial) binderWitness sourceBindersCover
    (by simpa [simulation, patternConcreteSemanticSimulation,
        patternSimulationRegionMap, hregion] using targetBindersCover)
    sourceEnumeration
    (by simpa [simulation, patternConcreteSemanticSimulation,
        patternSimulationRegionMap, hregion] using targetEnumeration)
    sourceExact
    (by simpa [simulation, patternConcreteSemanticSimulation,
        patternSimulationRegionMap, hregion] using targetExact)
    sourceBody targetBody sourceCompiled
    (by simpa [simulation, patternConcreteSemanticSimulation,
        patternSimulationRegionMap, hregion] using targetCompiled)
  simpa [simulation, patternConcreteSemanticSimulation,
    patternContextIndexRelation] using result

/-- Semantic transport of one intrinsic root occurrence into the actual
focused compiler context.  Root nodes use the public node kernel; every root
child is material for an empty proxy spine and therefore recurses through
`compilePatternRegion_denote_at_material`. -/
theorem compilePatternRootOccurrence_at_site_simulation
    {signature : List Nat}
    {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.pattern.val.diagram input.pattern.val.diagram.root)
    (sourceItem : Item signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
        input.pattern.val.diagram.regionCount)
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
        some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (layout.patternRootWireIndexMap hadmissible hzero outputWitness
          outputLeaf))
      (sourceItem.renameRelations
        (emptyRelationRenaming outputWitness.toFocus.holeRels)) targetItem := by
  let sourceContext :=
    input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires
  let targetContext :=
    outputLeaf.inheritedWires.extend (layout.frameRegion input.site)
  let indexMap := layout.patternRootWireIndexMap hadmissible hzero
    outputWitness outputLeaf
  have indexSpec : ∀ index, targetContext.get (indexMap index) =
      layout.patternPlugWire (sourceContext.get index) := by
    exact layout.patternRootWireIndexMap_spec hadmissible hzero outputWitness
      outputLeaf
  have memberSpec : ∀ wire, layout.patternPlugWire wire ∈ targetContext ↔
      wire ∈ sourceContext := by
    exact layout.patternPlugWire_mem_outputRootContext_iff hadmissible hzero
      outputWitness outputLeaf
  let rootWitness := PatternBinderWitness.root layout outputLeaf.binders
  cases occurrence with
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hoccurrence
      simp only [ConcreteElaboration.compileOccurrenceWith?] at hsource
      change ConcreteElaboration.compileNode? signature layout.plugRaw
          targetContext outputLeaf.binders (layout.patternNode node) =
        some targetItem at htarget
      apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
        (source := input.pattern.val.diagram) (target := layout.plugRaw)
        model named direction sourceContext targetContext
        (ConcreteElaboration.ContextIndexRelation.forwardMap indexMap)
        ConcreteElaboration.BinderContext.empty outputLeaf.binders
        (emptyRelationRenaming outputWitness.toFocus.holeRels) node
        (layout.patternNode node) (regionMap := layout.bodyRegion)
        (binderMap := layout.binderRegion)
      · change layout.plugNode (layout.patternNode node) = _
        rw [layout.plugNode_patternNode]
        cases hnode : input.pattern.val.diagram.nodes node <;> rfl
      · intro port sourceIndex targetIndex sourceResolved targetResolved
        have resolved := ConcreteElaboration.resolvePort?_map_of_occurrence
          sourceContext targetContext node (layout.patternNode node)
          layout.patternPlugWire indexMap outputLeaf.wiresExact.nodup indexSpec
          memberSpec
          (fun wire requested occurs => by
            simpa [mapPatternEndpoint] using
              layout.plugRaw_patternEndpoint_forward wire
                ⟨node, requested⟩ occurs)
          (fun targetWire requested occurs => by
            obtain ⟨sourceWire, wireEq, sourceOccurs⟩ :=
              layout.plugRaw_patternEndpoint_backward targetWire
                ⟨node, requested⟩ (by
                  simpa [mapPatternEndpoint] using occurs)
            exact ⟨sourceWire, wireEq, sourceOccurs⟩)
          ((layout.plugRaw_wellFormed signature input hadmissible)
            |>.wire_endpoints_are_disjoint) port
        rw [targetResolved, sourceResolved] at resolved
        exact Option.some.inj resolved |>.symm
      · intro region binder arity relation sourceShape sourceLookup
        simp [ConcreteElaboration.BinderContext.empty] at sourceLookup
      · exact hsource
      · exact htarget
  | child child =>
      have parentRoot :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hoccurrence
      have hbody := input.binderSpine.body_eq_root_of_empty hzero
      have parentBody : (input.pattern.val.diagram.regions child).parent? =
          some input.binderSpine.bodyContainer := by
        simpa [hbody] using parentRoot
      have hmaterial := directChildOfBody_material input child parentBody
      have sourceExact := (openRootWires_exact input.pattern).extend_child
        input.pattern.property.diagram_well_formed parentRoot
      have targetParent :=
        (layout.bodyRegion_parent_exact child
          input.binderSpine.bodyContainer hmaterial parentBody).trans
          (congrArg some layout.bodyRegion_bodyContainer)
      have targetExact := outputLeaf.wiresExact.extend_child
        (layout.plugRaw_wellFormed signature input hadmissible) targetParent
      cases childKind : input.pattern.val.diagram.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, childKind]
            at hsource
      | cut parent =>
          have parentEq : parent = input.pattern.val.diagram.root := by
            simpa [childKind, CRegion.parent?] using parentRoot
          subst parent
          have targetKind := layout.plugRaw_bodyRegion_cut child
            input.binderSpine.bodyContainer hmaterial (by
              simpa [hbody] using childKind)
          have targetKindAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                CRegion.cut (layout.frameRegion input.site) := by
            simpa only [layout.bodyRegion_bodyContainer] using targetKind
          cases sourceResult : ConcreteElaboration.compileRegion? signature
              input.pattern.val.diagram input.pattern.val.diagram.regionCount
              child sourceContext ConcreteElaboration.BinderContext.empty with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                sourceContext, sourceResult] at hsource
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                sourceContext, sourceResult] at hsource
              subst sourceItem
              cases targetResult : ConcreteElaboration.compileRegion? signature
                  layout.plugRaw outputLeaf.fuel (layout.bodyRegion child)
                  targetContext outputLeaf.binders with
              | none =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetContext, targetResult] at htarget
              | some targetBody =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetContext, targetResult] at htarget
                  subst targetItem
                  have bodies := layout.compilePatternRegion_denote_at_material
                    hadmissible model named direction.flip
                    input.pattern.val.diagram.regionCount outputLeaf.fuel
                    sourceContext targetContext indexMap indexSpec memberSpec
                    ConcreteElaboration.BinderContext.empty outputLeaf.binders
                    rootWitness child hmaterial
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      (ConcreteElaboration.BinderContext.empty_covers_root
                        input.pattern.property.diagram_well_formed) childKind)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      outputLeaf.bindersCover targetKindAtSite)
                    ((ConcreteElaboration.BinderContext.Enumeration.empty
                      input.pattern.val.diagram).cutChild
                        input.pattern.property.diagram_well_formed childKind)
                    (outputLeaf.binderEnumeration.cutChild
                      (layout.plugRaw_wellFormed signature input hadmissible)
                      targetKindAtSite)
                    sourceExact targetExact sourceBody targetBody sourceResult
                    targetResult
                  intro sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, cut_denotes_negation]
                  cases direction with
                  | forward =>
                      exact fun sourceNot targetDenotes =>
                        sourceNot (bodies sourceEnv targetEnv relEnv
                          environments targetDenotes)
                  | backward =>
                      exact fun targetNot sourceDenotes =>
                        targetNot (bodies sourceEnv targetEnv relEnv
                          environments sourceDenotes)
      | bubble parent arity =>
          have parentEq : parent = input.pattern.val.diagram.root := by
            simpa [childKind, CRegion.parent?] using parentRoot
          subst parent
          have targetKind := layout.plugRaw_bodyRegion_bubble child
            input.binderSpine.bodyContainer arity hmaterial (by
              simpa [hbody] using childKind)
          have targetKindAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                CRegion.bubble (layout.frameRegion input.site) arity := by
            simpa only [layout.bodyRegion_bodyContainer] using targetKind
          let sourcePushed := ConcreteElaboration.BinderContext.empty.push
            child arity
          let targetPushed := outputLeaf.binders.push
            (layout.bodyRegion child) arity
          let pushedWitness := PatternBinderWitness.pushMaterial layout
            rootWitness child arity hmaterial
          cases sourceResult : ConcreteElaboration.compileRegion? signature
              input.pattern.val.diagram input.pattern.val.diagram.regionCount
              child sourceContext sourcePushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                sourceContext, sourcePushed, sourceResult] at hsource
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                sourceContext, sourcePushed, sourceResult] at hsource
              subst sourceItem
              cases targetResult : ConcreteElaboration.compileRegion? signature
                  layout.plugRaw outputLeaf.fuel (layout.bodyRegion child)
                  targetContext targetPushed with
              | none =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetContext, targetPushed, targetResult] at htarget
              | some targetBody =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, targetKind,
                    targetContext, targetPushed, targetResult] at htarget
                  subst targetItem
                  have bodies := layout.compilePatternRegion_denote_at_material
                    hadmissible model named direction
                    input.pattern.val.diagram.regionCount outputLeaf.fuel
                    sourceContext targetContext indexMap indexSpec memberSpec
                    sourcePushed targetPushed pushedWitness child hmaterial
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      (ConcreteElaboration.BinderContext.empty_covers_root
                        input.pattern.property.diagram_well_formed) childKind)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      outputLeaf.bindersCover targetKindAtSite)
                    ((ConcreteElaboration.BinderContext.Enumeration.empty
                      input.pattern.val.diagram).bubbleChild
                        input.pattern.property.diagram_well_formed childKind)
                    (outputLeaf.binderEnumeration.bubbleChild
                      (layout.plugRaw_wellFormed signature input hadmissible)
                      targetKindAtSite)
                    sourceExact targetExact sourceBody targetBody sourceResult
                    targetResult
                  intro sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, bubble_denotes_exists]
                  cases direction with
                  | forward =>
                      rintro ⟨relationValue, sourceDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments sourceDenotes⟩
                  | backward =>
                      rintro ⟨relationValue, targetDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments targetDenotes⟩

/-- A retained-frame position in the semantic insertion order of an arbitrary
plug-layout witness for the same input. -/
def frameSiteSemanticIndexAt
    (input : Input signature)
    (layout : PlugLayout input)
    (index : Fin (ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw input.site).length) :
    Fin layout.semanticSiteOccurrences.length :=
  Fin.cast (by simp [PlugLayout.semanticSiteOccurrences])
    (Fin.castAdd
      (ConcreteElaboration.localOccurrences
        input.pattern.val.diagram input.binderSpine.bodyContainer).length
      index)

/-- The terminal-pattern position in semantic insertion order for an empty
proxy spine. -/
def patternSiteSemanticIndex
    (input : Input signature)
    (layout : PlugLayout input)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin (ConcreteElaboration.localOccurrences
      input.pattern.val.diagram input.pattern.val.diagram.root).length) :
    Fin layout.semanticSiteOccurrences.length :=
  Fin.cast (by
    rw [PlugLayout.semanticSiteOccurrences,
      input.binderSpine.body_eq_root_of_empty hzero]
    simp)
    (Fin.natAdd
      (ConcreteElaboration.localOccurrences
        input.coalesceFrameRaw input.site).length index)

/-- Inject one intrinsic empty-spine pattern-root occurrence through semantic
insertion order and the executable site permutation, then transport the item
returned by the actual focused compiler. -/
theorem focusedPatternOccurrence_itemSimulation
    {signature : List Nat}
    {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (patternIndex : Fin
      (compiledSpliceOpenRootItems input.pattern).items.length) :
    let pattern := compiledSpliceOpenRootItems input.pattern
    let occurrenceIndex := Fin.cast
      (ConcreteElaboration.compileOccurrencesWith?_length
        (ConcreteElaboration.compileRegion? signature
          input.pattern.val.diagram input.pattern.val.diagram.regionCount)
        (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty pattern.computation)
      patternIndex
    let targetOccurrenceIndex :=
      layout.siteOccurrenceEquiv
        (patternSiteSemanticIndex input layout hzero occurrenceIndex)
    ∃ targetIndex : Fin outputLeaf.items.length,
      targetIndex.val = targetOccurrenceIndex.val ∧
        ConcreteElaboration.ItemSimulation model named direction
          (ConcreteElaboration.ContextIndexRelation.forwardMap
            (layout.patternRootWireIndexMap hadmissible hzero
              outputWitness outputLeaf))
          ((pattern.items.get patternIndex).renameRelations
            (emptyRelationRenaming outputWitness.toFocus.holeRels))
          (outputLeaf.items.get targetIndex) := by
  dsimp only
  let pattern := compiledSpliceOpenRootItems input.pattern
  have patternLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature
        input.pattern.val.diagram input.pattern.val.diagram.regionCount)
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty pattern.computation
  let occurrenceIndex := Fin.cast patternLength patternIndex
  let semanticIndex :=
    patternSiteSemanticIndex input layout hzero occurrenceIndex
  let targetOccurrenceIndex := layout.siteOccurrenceEquiv semanticIndex
  have targetLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation
  let targetIndex := Fin.cast targetLength.symm targetOccurrenceIndex
  have sourceGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
      input.pattern.val.diagram.regionCount)
    (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
    ConcreteElaboration.BinderContext.empty pattern.computation occurrenceIndex
  have targetGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature layout.plugRaw
      outputLeaf.fuel)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
    outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
  rw [layout.siteOccurrenceEquiv_spec semanticIndex] at targetGet
  have targetGet' :
      ConcreteElaboration.compileOccurrenceWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders
        (layout.mapPatternOccurrence
          ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
            input.pattern.val.diagram.root).get occurrenceIndex)) =
          some (outputLeaf.items.get targetIndex) := by
    simpa [PlugLayout.semanticSiteOccurrences, semanticIndex,
      patternSiteSemanticIndex, input.binderSpine.body_eq_root_of_empty hzero,
      targetIndex] using targetGet
  refine ⟨targetIndex, rfl, ?_⟩
  exact layout.compilePatternRootOccurrence_at_site_simulation hadmissible
    outputWitness outputLeaf hzero model named direction
    ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
      input.pattern.val.diagram.root).get occurrenceIndex)
    (List.get_mem _ occurrenceIndex)
    (pattern.items.get patternIndex) (outputLeaf.items.get targetIndex)
    (by simpa [occurrenceIndex, patternLength] using sourceGet) targetGet'

/-- Reassemble the complete actual focused conjunction from its two semantic
blocks.  Retained-frame items are supplied by the caller; intrinsic pattern
items are transported through the authoritative pattern compiler simulation.
The executable node/child enumeration order is handled solely by
`siteOccurrenceEquiv`. -/
theorem denoteFocusedItems_of_patternRootItems_and_frame
    {signature : List Nat}
    {input : Input signature}
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (patternDenotes :
      let pattern := compiledSpliceOpenRootItems input.pattern
      denoteItemSeq (relCtx := []) model named
        (env ∘ layout.patternRootWireIndexMap hadmissible hzero
          outputWitness outputLeaf)
        (PUnit.unit : RelEnv model.Carrier []) pattern.items)
    (frameDenotes :
      ∀ frameIndex : Fin (ConcreteElaboration.localOccurrences
          input.coalesceFrameRaw input.site).length,
        let occurrenceIndex :=
          layout.siteOccurrenceEquiv
            (layout.frameSiteSemanticIndexAt input frameIndex)
        let itemIndex := Fin.cast
          (ConcreteElaboration.compileOccurrencesWith?_length
            (ConcreteElaboration.compileRegion? signature layout.plugRaw
              outputLeaf.fuel)
            (outputLeaf.inheritedWires.extend
              (layout.frameRegion input.site))
            outputLeaf.binders outputLeaf.itemsComputation).symm
          occurrenceIndex
        denoteItem model named env relEnv (outputLeaf.items.get itemIndex)) :
    denoteItemSeq model named env relEnv outputLeaf.items := by
  let pattern := compiledSpliceOpenRootItems input.pattern
  have targetLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation
  have patternLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature
        input.pattern.val.diagram input.pattern.val.diagram.regionCount)
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty pattern.computation
  apply (denoteItemSeq_iff_get model named env relEnv outputLeaf.items).mpr
  intro targetIndex
  let targetOccurrenceIndex := Fin.cast targetLength targetIndex
  let semanticIndex := layout.siteOccurrenceEquiv.symm targetOccurrenceIndex
  let split : Fin
      ((ConcreteElaboration.localOccurrences input.coalesceFrameRaw
          input.site).length +
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root).length) :=
    Fin.cast (by
      rw [PlugLayout.semanticSiteOccurrences,
        input.binderSpine.body_eq_root_of_empty hzero]
      simp) semanticIndex
  have semanticRecover :
      Fin.cast (by
        rw [PlugLayout.semanticSiteOccurrences,
          input.binderSpine.body_eq_root_of_empty hzero]
        simp) split = semanticIndex := by
    apply Fin.ext
    rfl
  revert semanticRecover
  refine Fin.addCases (fun frameIndex semanticRecover => ?_)
    (fun patternOccurrenceIndex semanticRecover => ?_) split
  · let frameSemanticIndex := layout.frameSiteSemanticIndexAt input frameIndex
    have semanticEq : semanticIndex = frameSemanticIndex := by
      apply Fin.ext
      exact congrArg Fin.val semanticRecover.symm
    let occurrenceIndex := layout.siteOccurrenceEquiv frameSemanticIndex
    let itemIndex := Fin.cast targetLength.symm occurrenceIndex
    have targetOccurrenceEq :
        targetOccurrenceIndex = occurrenceIndex := by
      change targetOccurrenceIndex =
        layout.siteOccurrenceEquiv frameSemanticIndex
      rw [← semanticEq]
      exact (layout.siteOccurrenceEquiv.right_inv targetOccurrenceIndex).symm
    have targetIndexEq : targetIndex = itemIndex := by
      apply Fin.ext
      change targetOccurrenceIndex.val = occurrenceIndex.val
      exact congrArg Fin.val targetOccurrenceEq
    subst targetIndex
    exact frameDenotes frameIndex
  · let occurrenceIndex : Fin
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root).length :=
      patternOccurrenceIndex
    let patternIndex := Fin.cast patternLength.symm occurrenceIndex
    have patternSemanticEq :
        semanticIndex =
          patternSiteSemanticIndex input layout hzero occurrenceIndex := by
      apply Fin.ext
      exact congrArg Fin.val semanticRecover.symm
    obtain ⟨actualIndex, actualIndexVal, simulation⟩ :=
      layout.focusedPatternOccurrence_itemSimulation hadmissible outputWitness
        outputLeaf hzero model named .forward patternIndex
    have actualIndexEq : actualIndex = targetIndex := by
      apply Fin.ext
      calc
        actualIndex.val =
            (layout.siteOccurrenceEquiv
              (patternSiteSemanticIndex input layout hzero
                (Fin.cast patternLength patternIndex))).val :=
          actualIndexVal
        _ = (layout.siteOccurrenceEquiv semanticIndex).val := by
          rw [Fin.cast_cast]
          simpa [patternIndex] using
            congrArg (fun index => (layout.siteOccurrenceEquiv index).val)
              patternSemanticEq.symm
        _ = targetOccurrenceIndex.val := by
          exact congrArg Fin.val
            (layout.siteOccurrenceEquiv.right_inv targetOccurrenceIndex)
        _ = targetIndex.val := rfl
    subst actualIndex
    have intrinsicDenotes :=
      (denoteItemSeq_iff_get (relCtx := []) model named
        (env ∘ layout.patternRootWireIndexMap hadmissible hzero
          outputWitness outputLeaf)
        (PUnit.unit : RelEnv model.Carrier []) pattern.items).mp
        patternDenotes patternIndex
    have relationAgrees : RelEnv.Agrees
        (emptyRelationRenaming outputWitness.toFocus.holeRels)
        (PUnit.unit : RelEnv model.Carrier []) relEnv := by
      simpa using RelEnv.pullback_agrees
        (emptyRelationRenaming outputWitness.toFocus.holeRels) relEnv
    have renamedDenotes :=
      (denoteItem_renameRelations model named
        (emptyRelationRenaming outputWitness.toFocus.holeRels)
        (PUnit.unit : RelEnv model.Carrier []) relEnv relationAgrees
        (env ∘ layout.patternRootWireIndexMap hadmissible hzero
          outputWitness outputLeaf)
        (pattern.items.get patternIndex)).mpr intrinsicDenotes
    exact simulation
      (env ∘ layout.patternRootWireIndexMap hadmissible hzero
        outputWitness outputLeaf)
      env relEnv (by
        intro sourceIndex mappedIndex related
        change layout.patternRootWireIndexMap hadmissible hzero
          outputWitness outputLeaf sourceIndex = mappedIndex at related
        subst mappedIndex
        rfl) renamedDenotes

/-- The actual focused item conjunction entails the intrinsic empty-spine
pattern-root conjunction under the canonical direct wire map.  Pattern
positions are selected by the executable site permutation, while individual
items are transported exclusively by the recursive semantic simulation. -/
theorem denotePatternRootItems_of_denoteFocusedItems
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (layout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (denotes : denoteItemSeq model named env relEnv outputLeaf.items) :
    let pattern := compiledSpliceOpenRootItems input.pattern
    denoteItemSeq (relCtx := []) model named
      (env ∘ layout.patternRootWireIndexMap hadmissible hzero
        outputWitness outputLeaf)
      (PUnit.unit : RelEnv model.Carrier []) pattern.items := by
  dsimp only
  let pattern := compiledSpliceOpenRootItems input.pattern
  have hpatternLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature
        input.pattern.val.diagram input.pattern.val.diagram.regionCount)
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty pattern.computation
  have htargetLength :=
    ConcreteElaboration.compileOccurrencesWith?_length
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation
  have hbody := input.binderSpine.body_eq_root_of_empty hzero
  apply (denoteItemSeq_iff_get (relCtx := []) model named
    (env ∘ layout.patternRootWireIndexMap hadmissible hzero
      outputWitness outputLeaf)
    (PUnit.unit : RelEnv model.Carrier []) pattern.items).mpr
  intro patternOriginalIndex
  let patternOccurrenceIndex := Fin.cast hpatternLength patternOriginalIndex
  have hpatternOccurrencesLength :
      (ConcreteElaboration.localOccurrences input.pattern.val.diagram
        input.pattern.val.diagram.root).length =
      (ConcreteElaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer).length := by
    rw [hbody]
  let patternOccurrenceAtBody :=
    Fin.cast hpatternOccurrencesLength patternOccurrenceIndex
  let occurrenceIndex : Fin layout.semanticSiteOccurrences.length :=
    Fin.cast (by simp [semanticSiteOccurrences])
      (Fin.natAdd
        (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
          input.site).length
        patternOccurrenceAtBody)
  let targetOccurrenceIndex := layout.siteOccurrenceEquiv occurrenceIndex
  let targetOriginalIndex := Fin.cast htargetLength.symm targetOccurrenceIndex
  have hsourceGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
      input.pattern.val.diagram.regionCount)
    (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
    ConcreteElaboration.BinderContext.empty pattern.computation
    patternOccurrenceIndex
  have htargetGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature layout.plugRaw
      outputLeaf.fuel)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
    outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
  rw [layout.siteOccurrenceEquiv_spec occurrenceIndex] at htargetGet
  have htargetGet' : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders
      (layout.mapPatternOccurrence
        ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root).get patternOccurrenceIndex)) =
        some (outputLeaf.items.get targetOriginalIndex) := by
    simpa [semanticSiteOccurrences, occurrenceIndex, hbody] using htargetGet
  have simulation := layout.compilePatternRootOccurrence_at_site_simulation
    hadmissible outputWitness outputLeaf hzero model named .backward
    ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
      input.pattern.val.diagram.root).get patternOccurrenceIndex)
    (List.get_mem _ patternOccurrenceIndex)
    (pattern.items.get patternOriginalIndex)
    (outputLeaf.items.get targetOriginalIndex) hsourceGet htargetGet'
  have targetDenotes :=
    (denoteItemSeq_iff_get model named env relEnv outputLeaf.items).mp
      denotes targetOriginalIndex
  have transformedDenotes := simulation
    (env ∘ layout.patternRootWireIndexMap hadmissible hzero
      outputWitness outputLeaf)
    env relEnv (by
      intro sourceIndex targetIndex related
      change layout.patternRootWireIndexMap hadmissible hzero
        outputWitness outputLeaf sourceIndex = targetIndex at related
      subst targetIndex
      rfl) targetDenotes
  have relationAgrees : RelEnv.Agrees
      (emptyRelationRenaming outputWitness.toFocus.holeRels)
      (PUnit.unit : RelEnv model.Carrier []) relEnv := by
    simpa using RelEnv.pullback_agrees
      (emptyRelationRenaming outputWitness.toFocus.holeRels) relEnv
  exact (denoteItem_renameRelations model named
    (emptyRelationRenaming outputWitness.toFocus.holeRels)
    (PUnit.unit : RelEnv model.Carrier []) relEnv relationAgrees
    (env ∘ layout.patternRootWireIndexMap hadmissible hzero
      outputWitness outputLeaf)
    (pattern.items.get patternOriginalIndex)).mp transformedDenotes

end PlugLayout

/-- An actual focused item conjunction for an empty proxy spine entails the
intrinsic checked pattern at the quotient valuation read from that exact
focused context.  Hidden pattern-root wires remain existential locals. -/
theorem pattern_denote_of_denoteFocusedItems
    (input : Input signature)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fallback : model.Carrier)
    (denotes : denoteItemSeq model named env relEnv outputLeaf.items) :
    input.pattern.denote model named (fun position =>
      siteQuotientEnvironment input
        (outputLeaf.inheritedWires.extend
          (input.plugLayout.frameRegion input.site))
        outputLeaf.wiresExact env fallback
        (input.quotientWire (input.attachment position))) := by
  apply pattern_denote_of_patternRootItems input hadmissible outputWitness
    outputLeaf hzero model named env fallback
  exact input.plugLayout.denotePatternRootItems_of_denoteFocusedItems input
    hadmissible outputWitness outputLeaf hzero model named env relEnv denotes

end VisualProof.Diagram.Splice.Input
