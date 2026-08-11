import VisualProof.Concrete.Elaboration.SpliceSiteCompiler

/-! Recursive compiler transport for the material children of a splice pattern. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private theorem get_of_eq {first second : List α}
    (equality : first = second)
    (firstIndex : Fin first.length) (secondIndex : Fin second.length)
    (indexEq : firstIndex.val = secondIndex.val) :
    first.get firstIndex = second.get secondIndex := by
  subst second
  have indices : firstIndex = secondIndex := Fin.ext indexEq
  subst secondIndex
  rfl

private theorem map_origin_allFin (domain : SurvivorDomain size) :
    (allFin domain.count).map domain.origin = domain.enumeration := by
  rw [allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  change List.ofFn (fun index : Fin domain.enumeration.length =>
    domain.enumeration.get index) = domain.enumeration
  exact List.ofFn_getElem

private theorem map_origin_filterFin (domain : SurvivorDomain size)
    (predicate : Fin size → Bool) :
    (filterFin fun index : domain.Carrier =>
      predicate (domain.origin index)).map domain.origin =
        domain.enumeration.filter predicate := by
  unfold filterFin
  change ((allFin domain.count).filter
      (predicate ∘ domain.origin)).map domain.origin = _
  rw [← List.filter_map, map_origin_allFin]

/-- Dense internal origins at a material region are exactly its source local
wire block, in source compiler order. -/
theorem materialLocalOrigins (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    (filterFin fun wire : layout.internalWires.Carrier =>
      decide ((input.pattern.val.diagram.wires
        (layout.internalWires.origin wire)).scope =
          layout.materialRegions.origin material)).map
            layout.internalWires.origin =
      exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin material) := by
  let predicate : Fin input.pattern.val.diagram.wireCount → Bool :=
    fun wire => decide ((input.pattern.val.diagram.wires wire).scope =
      layout.materialRegions.origin material)
  rw [map_origin_filterFin layout.internalWires predicate]
  unfold SurvivorDomain.enumeration exactScopeWires filterFin
  rw [List.filter_filter]
  apply List.filter_congr
  intro wire _
  rw [layout.internalWires_exact]
  by_cases scope : (input.pattern.val.diagram.wires wire).scope =
      layout.materialRegions.origin material
  · have notExposed : wire ∉ input.pattern.val.exposedWires := by
      intro exposed
      have rootScope := input.pattern.property.exposed_root_scoped exposed
      exact (layout.materialRegion_origin_isMaterial material).1
        (scope.symm.trans rootScope)
    simp [predicate, scope, notExposed]
  · have predicateFalse : predicate wire = false :=
      decide_eq_false_iff_not.mpr scope
    have scopeFalse : decide
        ((input.pattern.val.diagram.wires wire).scope =
          layout.materialRegions.origin material) = false :=
      decide_eq_false_iff_not.mpr scope
    rw [predicateFalse]
    rw [scopeFalse]
    rfl

/-- Source and target material-local blocks have the same stable length. -/
theorem materialLocalWires_length (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length =
        (layout.materialLocalWires material).length := by
  rw [← layout.materialLocalOrigins material]
  unfold materialLocalWires
  simp only [List.length_map]

/-- Stable local position transport at one material region. -/
noncomputable def materialLocalEquiv (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    FiniteEquiv
      (Fin (exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin material)).length)
      (Fin (layout.materialLocalWires material).length) :=
  FiniteEquiv.finCast (layout.materialLocalWires_length material)

/-- The material-local position equivalence names the same source survivor
and its target internal image. -/
theorem materialLocalEquiv_get (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (index : Fin (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length) :
    ∃ internal : layout.internalWires.Carrier,
      (exactScopeWires input.pattern.val.diagram
          (layout.materialRegions.origin material)).get index =
        layout.internalWires.origin internal ∧
      (layout.materialLocalWires material).get
          (layout.materialLocalEquiv material index) =
        layout.internalWire internal := by
  let positions := filterFin fun wire : layout.internalWires.Carrier =>
    decide ((input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        layout.materialRegions.origin material)
  have sourceEq : exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material) =
        positions.map layout.internalWires.origin :=
    (layout.materialLocalOrigins material).symm
  have targetEq : layout.materialLocalWires material =
      positions.map layout.internalWire := rfl
  have sourceLength :
      (exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin material)).length = positions.length := by
    rw [sourceEq, List.length_map]
  let position : Fin positions.length :=
    ⟨index.val, by rw [← sourceLength]; exact index.isLt⟩
  let internal := positions.get position
  refine ⟨internal, ?_, ?_⟩
  · have value := List.get_of_eq sourceEq index
    have mapped := List.getElem_map layout.internalWires.origin
      (l := positions) (i := index.val) (h := by
        exact Eq.mp (congrArg (fun length => index.val < length)
          (List.length_map layout.internalWires.origin).symm) position.isLt)
    exact value.trans (by
      simpa only [List.get_eq_getElem, position, internal] using mapped)
  · have value := List.get_of_eq targetEq
      (layout.materialLocalEquiv material index)
    have mapped := List.getElem_map layout.internalWire
      (l := positions)
      (i := (layout.materialLocalEquiv material index).val) (h := by
        change index.val < (positions.map layout.internalWire).length
        exact Eq.mp (congrArg (fun length => index.val < length)
          (List.length_map layout.internalWire).symm) position.isLt)
    exact value.trans (by
      simpa only [List.get_eq_getElem, materialLocalEquiv,
        FiniteEquiv.finCast, position, internal] using mapped)

/-- Extend an arbitrary inherited pattern-wire position map by the stable
local positions of one material region. -/
noncomputable def materialExtendedIndexMap (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (outer : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend
      (layout.materialRegions.origin material)).length →
      Fin (targetContext ++ layout.materialLocalWires material).length :=
  fun index =>
    Fin.cast (by simp)
      (Fin.addCases
        (fun inherited => Fin.castAdd
          (layout.materialLocalWires material).length (outer inherited))
        (fun localIndex => Fin.natAdd targetContext.length
          (layout.materialLocalEquiv material localIndex))
        (Fin.cast (by simp [WireContext.extend]) index))

/-- Extending the position map preserves the concrete source/target wire
lookup equation. -/
theorem materialExtendedIndexMap_get (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (outer : Fin sourceContext.length → Fin targetContext.length)
    (outerGet : ∀ index, targetContext.get (outer index) =
      layout.patternWireMap (sourceContext.get index))
    (index : Fin (sourceContext.extend
      (layout.materialRegions.origin material)).length) :
    (targetContext ++ layout.materialLocalWires material).get
        (layout.materialExtendedIndexMap material sourceContext
          targetContext outer index) =
      layout.patternWireMap ((sourceContext.extend
        (layout.materialRegions.origin material)).get index) := by
  let split : Fin (sourceContext.length +
      (exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin material)).length) :=
    Fin.cast (by simp [WireContext.extend]) index
  have indexEq : Fin.cast (by simp [WireContext.extend]) split = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · calc
      _ = (targetContext ++ layout.materialLocalWires material).get
          (Fin.cast (by simp)
            (Fin.castAdd (layout.materialLocalWires material).length
              (outer inherited))) := by
        congr 1
        apply Fin.ext
        simp [materialExtendedIndexMap]
      _ = targetContext.get (outer inherited) := by
        rw [get_append_castAdd]
      _ = layout.patternWireMap (sourceContext.get inherited) :=
        outerGet inherited
      _ = layout.patternWireMap
          ((sourceContext ++ exactScopeWires input.pattern.val.diagram
            (layout.materialRegions.origin material)).get
              (Fin.cast (by simp)
                (Fin.castAdd
                  (exactScopeWires input.pattern.val.diagram
                    (layout.materialRegions.origin material)).length
                  inherited))) := by
        rw [get_append_castAdd]
      _ = _ := by
        unfold WireContext.extend
        congr 2
  · obtain ⟨internal, sourceEq, targetEq⟩ :=
      layout.materialLocalEquiv_get material localIndex
    calc
      _ = (targetContext ++ layout.materialLocalWires material).get
          (Fin.cast (by simp)
            (Fin.natAdd targetContext.length
              (layout.materialLocalEquiv material localIndex))) := by
        congr 1
        apply Fin.ext
        simp [materialExtendedIndexMap]
      _ = (layout.materialLocalWires material).get
          (layout.materialLocalEquiv material localIndex) := by
        rw [get_append_natAdd]
      _ = layout.patternWireMap (layout.internalWires.origin internal) :=
        targetEq.trans (layout.patternWireMap_of_internal internal).symm
      _ = layout.patternWireMap
          ((exactScopeWires input.pattern.val.diagram
            (layout.materialRegions.origin material)).get localIndex) := by
        rw [sourceEq]
      _ = layout.patternWireMap
          ((sourceContext ++ exactScopeWires input.pattern.val.diagram
            (layout.materialRegions.origin material)).get
              (Fin.cast (by simp)
                (Fin.natAdd sourceContext.length localIndex))) := by
        rw [get_append_natAdd]
      _ = _ := by
        unfold WireContext.extend
        congr 2

/-- The same extended position map indexed by the target compiler's literal
`WireContext.extend` input. -/
noncomputable def materialCompilerIndexMap (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (outer : Fin sourceContext.length → Fin targetContext.length) :
    Fin (sourceContext.extend
      (layout.materialRegions.origin material)).length →
      Fin (targetContext.extend (layout.materialRegion material)).length :=
  fun index => Fin.cast (by
    unfold WireContext.extend
    rw [layout.exactScopeWires_materialRegion])
      (layout.materialExtendedIndexMap material sourceContext
        targetContext outer index)

theorem materialCompilerIndexMap_get (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (outer : Fin sourceContext.length → Fin targetContext.length)
    (outerGet : ∀ index, targetContext.get (outer index) =
      layout.patternWireMap (sourceContext.get index))
    (index : Fin (sourceContext.extend
      (layout.materialRegions.origin material)).length) :
    (targetContext.extend (layout.materialRegion material)).get
        (layout.materialCompilerIndexMap material sourceContext
          targetContext outer index) =
      layout.patternWireMap ((sourceContext.extend
        (layout.materialRegions.origin material)).get index) := by
  have targetEq : targetContext.extend (layout.materialRegion material) =
      targetContext ++ layout.materialLocalWires material := by
    unfold WireContext.extend
    rw [layout.exactScopeWires_materialRegion]
  calc
    _ = (targetContext ++ layout.materialLocalWires material).get
        (layout.materialExtendedIndexMap material sourceContext
          targetContext outer index) := by
      apply get_of_eq targetEq
      rfl
    _ = _ := layout.materialExtendedIndexMap_get material sourceContext
      targetContext outer outerGet index

/-- The material compiler map is the ordinary region wire renaming: inherited
positions use `outer`, and local positions retain their stable ordinal. -/
theorem materialCompilerIndexMap_eq_extendWireRenaming
    (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (outer : Fin sourceContext.length → Fin targetContext.length) :
    layout.materialCompilerIndexMap material sourceContext targetContext outer =
      fun index => Fin.cast (by
        unfold WireContext.extend
        rw [layout.exactScopeWires_materialRegion]
        simp only [List.length_append]
        rw [← layout.materialLocalWires_length material])
        (extendWireRenaming outer
          (exactScopeWires input.pattern.val.diagram
            (layout.materialRegions.origin material)).length
          (Fin.cast (WireContext.length_extend sourceContext
            (layout.materialRegions.origin material)) index)) := by
  funext index
  apply Fin.ext
  let split : Fin (sourceContext.length +
      (exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin material)).length) :=
    Fin.cast (WireContext.length_extend sourceContext
      (layout.materialRegions.origin material)) index
  have indexEq : Fin.cast (WireContext.length_extend sourceContext
      (layout.materialRegions.origin material)).symm split = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · simp [materialCompilerIndexMap, materialExtendedIndexMap,
      extendWireRenaming]
  · simp [materialCompilerIndexMap, materialExtendedIndexMap,
      materialLocalEquiv, FiniteEquiv.finCast, extendWireRenaming]

/-- Only the matching material source region maps to a fixed target material
binder region. -/
theorem binderRegion_eq_materialRegion_iff (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (material : layout.materialRegions.Carrier) :
    layout.binderRegion region = layout.materialRegion material ↔
      region = layout.materialRegions.origin material := by
  constructor
  · intro equality
    unfold binderRegion at equality
    cases proxyEq : layout.proxyIndex? region with
    | some proxy =>
        simp only [proxyEq] at equality
        exact (layout.frameRegion_ne_materialRegion
          (input.binderTarget proxy) material equality).elim
    | none =>
        simp only [proxyEq] at equality
        exact (layout.bodyRegion_eq_materialRegion_iff region material).1 equality
  · intro regionEq
    subst region
    have noProxy : layout.proxyIndex?
        (layout.materialRegions.origin material) = none := by
      unfold proxyIndex?
      cases found : indexOf? layout.proxies
          (layout.materialRegions.origin material) with
      | none => rfl
      | some index =>
          simp only [Option.map_some]
          exfalso
          have foundValue := indexOf?_sound found
          have member : layout.materialRegions.origin material ∈
              layout.proxies := by
            rw [← foundValue]
            exact List.get_mem _ _
          unfold proxies at member
          obtain ⟨proxy, _, proxyEq⟩ := List.mem_map.mp member
          exact (layout.materialRegion_origin_isMaterial material).2 proxy
            proxyEq.symm
    unfold binderRegion
    rw [noProxy, layout.bodyRegion_materialOrigin]

/-- Forward compiler binder lookup transport through the pattern embedding. -/
def PatternBindersForward (layout : PlugLayout input)
    (relation : RelationRenaming sourceRels targetRels)
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels) : Prop :=
  ∀ {binder arity} {sourceRelation : RelVar sourceRels arity},
    sourceBinders binder = some ⟨arity, sourceRelation⟩ →
      targetBinders (layout.binderRegion binder) =
        some ⟨arity, relation sourceRelation⟩

/-- A matched material bubble push preserves forward binder lookup under the
lifted relation renaming. -/
theorem PatternBindersForward.push (layout : PlugLayout input)
    (relation : RelationRenaming sourceRels targetRels)
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (forward : layout.PatternBindersForward relation
      sourceBinders targetBinders)
    (material : layout.materialRegions.Carrier) (arity : Nat) :
    layout.PatternBindersForward (RelationRenaming.lift relation arity)
      (sourceBinders.push (layout.materialRegions.origin material) arity)
      (targetBinders.push (layout.materialRegion material) arity) := by
  intro binder relationArity sourceRelation sourceLookup
  by_cases atChild : binder = layout.materialRegions.origin material
  · subst binder
    rw [BinderContext.push_self] at sourceLookup
    have targetBinderEq : layout.binderRegion
        (layout.materialRegions.origin material) =
          layout.materialRegion material :=
      (layout.binderRegion_eq_materialRegion_iff _ _).2 rfl
    rw [targetBinderEq, BinderContext.push_self]
    cases sourceLookup
    rfl
  · have targetNe : layout.binderRegion binder ≠
        layout.materialRegion material := by
      intro equality
      exact atChild ((layout.binderRegion_eq_materialRegion_iff
        binder material).1 equality)
    rw [BinderContext.push_other _ arity atChild] at sourceLookup
    rw [BinderContext.push_other _ arity targetNe]
    cases oldLookup : sourceBinders binder with
    | none => simp [oldLookup] at sourceLookup
    | some oldRelation =>
        cases oldRelation with
        | mk oldArity oldRelation =>
            simp only [oldLookup, Option.map_some] at sourceLookup
            cases sourceLookup
            rw [forward oldLookup]
            rfl

private theorem filterFin_eq_enumeration_filter
    (domain : SurvivorDomain size) (predicate : Fin size → Bool)
    (survives : ∀ original, predicate original = true →
      domain.survives original = true) :
    filterFin predicate = domain.enumeration.filter predicate := by
  unfold SurvivorDomain.enumeration filterFin
  rw [List.filter_filter]
  apply List.filter_congr
  intro original _
  cases predicateEq : predicate original with
  | false => rfl
  | true =>
      rw [survives original predicateEq]
      rfl

/-- Every direct child of a material pattern region is itself material. -/
theorem directMaterialChild_isMaterial (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (child : Fin input.pattern.val.diagram.regionCount)
    (parentEq : (input.pattern.val.diagram.regions child).parent? =
      some (layout.materialRegions.origin material)) :
    input.binderSpine.IsMaterialRegion child := by
  constructor
  · intro childRoot
    subst child
    rw [input.pattern.property.diagram_well_formed.root_is_sheet] at parentEq
    contradiction
  · intro proxy childProxy
    subst child
    rw [input.binderSpine.proxy_region] at parentEq
    simp only [CRegion.parent?, Option.some.injEq] at parentEq
    split at parentEq
    · exact (layout.materialRegion_origin_isMaterial material).1
        parentEq.symm
    · rename_i nonzero
      exact (layout.materialRegion_origin_isMaterial material).2
        ⟨proxy.val - 1, by omega⟩ parentEq.symm

/-- The direct source child stream of a material region maps to the target's
dense material-child stream, in compiler order. -/
theorem map_localChildOccurrences_material (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    (localChildOccurrences input.pattern.val.diagram
      (layout.materialRegions.origin material)).map
        layout.mapPatternOccurrence =
      layout.materialRegionChildOccurrences material := by
  let predicate : Fin input.pattern.val.diagram.regionCount → Bool :=
    fun child => decide
      ((input.pattern.val.diagram.regions child).parent? =
        some (layout.materialRegions.origin material))
  have survives : ∀ child, predicate child = true →
      layout.materialRegions.survives child = true := by
    intro child accepted
    rw [layout.materialRegions_exact]
    apply decide_eq_true
    apply layout.directMaterialChild_isMaterial material child
    exact of_decide_eq_true accepted
  have sourceFilter := filterFin_eq_enumeration_filter
    layout.materialRegions predicate survives
  have mappedOrigins := map_origin_filterFin layout.materialRegions predicate
  have origins : filterFin predicate =
      (filterFin fun child : layout.materialRegions.Carrier =>
        predicate (layout.materialRegions.origin child)).map
          layout.materialRegions.origin :=
    sourceFilter.trans mappedOrigins.symm
  have occurrences := congrArg
    (List.map fun child =>
      (LocalOccurrence.child (layout.bodyRegion child) :
        LocalOccurrence layout.regionCount layout.nodeCount)) origins
  unfold localChildOccurrences materialRegionChildOccurrences
    mapPatternOccurrence
  simp only [List.map_map]
  change (filterFin predicate).map (fun child =>
      (LocalOccurrence.child (layout.bodyRegion child) :
        LocalOccurrence layout.regionCount layout.nodeCount)) =
    (filterFin fun child : layout.materialRegions.Carrier =>
      predicate (layout.materialRegions.origin child)).map (fun child =>
        LocalOccurrence.child (layout.materialRegion child))
  calc
    _ = (filterFin fun child : layout.materialRegions.Carrier =>
          predicate (layout.materialRegions.origin child)).map (fun child =>
            (LocalOccurrence.child
              (layout.bodyRegion (layout.materialRegions.origin child)) :
                LocalOccurrence layout.regionCount layout.nodeCount)) := by
      simpa only [List.map_map, Function.comp_apply] using occurrences
    _ = _ := by
      apply List.map_congr_left
      intro child _
      rw [layout.bodyRegion_materialOrigin]

/-- The direct source node stream of a material region maps to the target's
pattern-node stream, in compiler order. -/
theorem map_localNodeOccurrences_material (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    (localNodeOccurrences input.pattern.val.diagram
      (layout.materialRegions.origin material)).map
      layout.mapPatternOccurrence =
      layout.materialNodeOccurrences material := by
  unfold localNodeOccurrences materialNodeOccurrences mapPatternOccurrence
  simp only [List.map_map]
  rfl

/-- A material target region has exactly the mapped source occurrence stream
used by recursive compilation. -/
theorem map_localOccurrences_material (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    (localOccurrences input.pattern.val.diagram
      (layout.materialRegions.origin material)).map
        layout.mapPatternOccurrence =
      localOccurrences layout.plugRaw
        (layout.materialRegion material) := by
  rw [localOccurrences_eq_node_child, List.map_append,
    layout.map_localNodeOccurrences_material material,
    layout.map_localChildOccurrences_material material,
    layout.localOccurrences_materialRegion material]

/-- Port resolution at any retained pattern node commutes with an arbitrary
exact lexical context map. -/
theorem resolvePort?_patternNode_map (layout : PlugLayout input)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (sourceRegion : Fin input.pattern.val.diagram.regionCount)
    (sourceExact : sourceContext.Exact sourceRegion)
    (targetNodup : targetContext.Nodup)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (nodeRegion : (input.pattern.val.diagram.nodes node).region = sourceRegion)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (getMapped : ∀ index, targetContext.get (wireMap index) =
      layout.patternWireMap (sourceContext.get index))
    (targetDisjoint : layout.plugRaw.WireEndpointsAreDisjoint)
    (port : CPort) :
    resolvePort? layout.plugRaw targetContext
        (layout.patternNode node) port =
      (resolvePort? input.pattern.val.diagram sourceContext node port).map
        wireMap := by
  unfold resolvePort?
  rw [endpointOwner?_map node (layout.patternNode node)
    layout.patternWireMap port
    (fun wire occurs =>
      layout.endpointOccurs_patternNode_forward wire node port occurs)
    (fun targetWire occurs =>
      layout.endpointOccurs_patternNode_backward targetWire node port occurs)
    targetDisjoint]
  cases sourceOwner : endpointOwner? input.pattern.val.diagram
      ⟨node, port⟩ with
  | none => rfl
  | some sourceWire =>
      simp only [Option.map_some]
      have sourceOccurs : input.pattern.val.diagram.EndpointOccurs sourceWire
          ⟨node, port⟩ := endpointOwner?_sound sourceOwner
      have sourceEncloses :=
        input.pattern.property.diagram_well_formed.wire_scopes_enclose
          sourceWire ⟨node, port⟩ sourceOccurs
      have sourceMember : sourceWire ∈ sourceContext :=
        (sourceExact.mem_iff sourceWire).2 (by
          simpa only [nodeRegion] using sourceEncloses)
      obtain ⟨sourceIndex, sourceLookup⟩ :=
        WireContext.lookup?_complete sourceMember
      have sourceGet : sourceContext.get sourceIndex = sourceWire := by
        simpa only [List.get_eq_getElem] using
          WireContext.lookup?_sound sourceLookup
      have mappedGet : targetContext.get (wireMap sourceIndex) =
          layout.patternWireMap sourceWire :=
        (getMapped sourceIndex).trans
          (congrArg layout.patternWireMap sourceGet)
      have targetMember : layout.patternWireMap sourceWire ∈
          targetContext := by
        rw [← mappedGet]
        exact List.get_mem _ _
      obtain ⟨targetIndex, targetLookup⟩ :=
        WireContext.lookup?_complete targetMember
      have targetGet : targetContext.get targetIndex =
          layout.patternWireMap sourceWire := by
        simpa only [List.get_eq_getElem] using
          WireContext.lookup?_sound targetLookup
      have indexEq : targetIndex = wireMap sourceIndex := by
        apply Fin.ext
        exact (List.getElem_inj targetNodup).mp (by
          simpa only [List.get_eq_getElem] using
            targetGet.trans mappedGet.symm)
      change targetContext.lookup? (layout.patternWireMap sourceWire) =
        (sourceContext.lookup? sourceWire).map wireMap
      rw [sourceLookup, targetLookup, indexEq]
      rfl

/-- Compile one retained pattern node in an arbitrary material-region
context through simultaneous wire and relation substitution. -/
theorem compileNode?_material_map (layout : PlugLayout input)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (sourceRegion : Fin input.pattern.val.diagram.regionCount)
    (sourceExact : sourceContext.Exact sourceRegion)
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (sourceCovers : sourceBinders.Covers sourceRegion)
    (relationMap : RelationRenaming sourceRels targetRels)
    (binderForward : layout.PatternBindersForward relationMap
      sourceBinders targetBinders)
    (node : Fin input.pattern.val.diagram.nodeCount)
    (nodeRegion : (input.pattern.val.diagram.nodes node).region = sourceRegion)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (targetNodup : targetContext.Nodup)
    (getMapped : ∀ index, targetContext.get (wireMap index) =
      layout.patternWireMap (sourceContext.get index))
    (targetWellFormed : layout.plugRaw.WellFormed) :
    compileNode? layout.plugRaw targetContext targetBinders
        (layout.patternNode node) =
      (compileNode? input.pattern.val.diagram sourceContext sourceBinders
        node).map (fun item =>
          (item.renameWires wireMap).renameRelations relationMap) := by
  apply compileNode?_map sourceContext targetContext sourceBinders targetBinders
    node (layout.patternNode node) layout.bodyRegion layout.binderRegion
    wireMap relationMap
  · cases nodeEq : input.pattern.val.diagram.nodes node <;>
      simp [PlugLayout.plugRaw, PlugLayout.plugNode,
        PlugLayout.patternNode, PlugLayout.mapPatternNode, nodeEq]
  · intro port
    exact layout.resolvePort?_patternNode_map sourceContext targetContext
      sourceRegion sourceExact targetNodup node nodeRegion wireMap getMapped
      targetWellFormed.wire_endpoints_are_disjoint port
  · intro region binder nodeEq
    have regionEq : region = sourceRegion :=
      (congrArg CNode.region nodeEq).symm.trans nodeRegion
    subst region
    obtain ⟨parent, arity, bubble⟩ :=
      BinderContext.checked_atom_binder_is_bubble
        input.pattern.property.diagram_well_formed nodeEq
    obtain ⟨sourceRelation, sourceLookup⟩ :=
      BinderContext.checked_atom_binder_available
        input.pattern.property.diagram_well_formed sourceCovers nodeEq bubble
    rw [sourceLookup, binderForward sourceLookup]
    rfl

/-- The terminal pattern compiler's retained binders map forward to the host
binder context selected by the splice relation substitution. -/
theorem compiledPattern_bindersForward
    (layout : PlugLayout input) (admissible : input.Admissible)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer)
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site) :
    layout.PatternBindersForward
      (compiled.spliceRelationMap input admissible hostBinders hostCovers)
      compiled.siteBinders (layout.mapFrameBinders hostBinders) := by
  intro binder arity sourceRelation sourceLookup
  obtain ⟨proxy, binderEq, hostLookup⟩ :=
    compiled.spliceRelationMap_of_lookup input admissible
      hostBinders hostCovers sourceLookup
  subst binder
  rw [layout.binderRegion_proxy, layout.mapFrameBinders_frameRegion]
  exact hostLookup

/-- Compare successful source and target sequence compilers pointwise through
simultaneous wire and relation renaming. -/
private theorem compileOccurrencesWith?_mapBoth_of_success
    {sourceDiagram targetDiagram : Concrete.Diagram}
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin sourceDiagram.regionCount) →
      (context : WireContext sourceDiagram) →
      BinderContext sourceDiagram rels → Option (Region context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin targetDiagram.regionCount) →
      (context : WireContext targetDiagram) →
      BinderContext targetDiagram rels → Option (Region context.length rels))
    (sourceContext : WireContext sourceDiagram)
    (targetContext : WireContext targetDiagram)
    (sourceBinders : BinderContext sourceDiagram sourceRels)
    (targetBinders : BinderContext targetDiagram targetRels)
    (mapOccurrence : LocalOccurrence sourceDiagram.regionCount
        sourceDiagram.nodeCount →
      LocalOccurrence targetDiagram.regionCount targetDiagram.nodeCount)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceOccurrences : List
      (LocalOccurrence sourceDiagram.regionCount sourceDiagram.nodeCount))
    (sourceItems : ItemSeq sourceContext.length sourceRels)
    (targetItems : ItemSeq targetContext.length targetRels)
    (sourceCompiled : compileOccurrencesWith? sourceDiagram sourceRecurse
      sourceContext sourceBinders sourceOccurrences = some sourceItems)
    (targetCompiled : compileOccurrencesWith? targetDiagram targetRecurse
      targetContext targetBinders (sourceOccurrences.map mapOccurrence) =
        some targetItems)
    (occurrenceMapped : ∀ occurrence,
      occurrence ∈ sourceOccurrences →
      ∀ sourceItem targetItem,
        compileOccurrenceWith? sourceDiagram sourceRecurse
            sourceContext sourceBinders occurrence = some sourceItem →
        compileOccurrenceWith? targetDiagram targetRecurse
            targetContext targetBinders (mapOccurrence occurrence) =
              some targetItem →
        targetItem = (sourceItem.renameWires wireMap).renameRelations
          relationMap) :
    targetItems = (sourceItems.renameWires wireMap).renameRelations
      relationMap := by
  induction sourceOccurrences generalizing sourceItems targetItems with
  | nil =>
      simp only [compileOccurrencesWith?] at sourceCompiled targetCompiled
      cases sourceCompiled
      cases targetCompiled
      rfl
  | cons occurrence tail inductionHypothesis =>
      simp only [compileOccurrencesWith?] at sourceCompiled
      simp only [List.map_cons, compileOccurrencesWith?] at targetCompiled
      cases sourceHead : compileOccurrenceWith? sourceDiagram sourceRecurse
          sourceContext sourceBinders occurrence with
      | none => simp [sourceHead] at sourceCompiled
      | some sourceItem =>
          cases sourceTail : compileOccurrencesWith? sourceDiagram sourceRecurse
              sourceContext sourceBinders tail with
          | none => simp [sourceHead, sourceTail] at sourceCompiled
          | some compiledSourceTail =>
              simp [sourceHead, sourceTail] at sourceCompiled
              subst sourceItems
              cases targetHead : compileOccurrenceWith? targetDiagram
                  targetRecurse targetContext targetBinders
                  (mapOccurrence occurrence) with
              | none => simp [targetHead] at targetCompiled
              | some targetItem =>
                  cases targetTail : compileOccurrencesWith? targetDiagram
                      targetRecurse targetContext targetBinders
                      (tail.map mapOccurrence) with
                  | none => simp [targetHead, targetTail] at targetCompiled
                  | some compiledTargetTail =>
                      simp [targetHead, targetTail] at targetCompiled
                      subst targetItems
                      have headEq := occurrenceMapped occurrence (by simp)
                        sourceItem targetItem sourceHead targetHead
                      have tailMapped : ∀ current, current ∈ tail →
                          ∀ sourceCurrent targetCurrent,
                            compileOccurrenceWith? sourceDiagram sourceRecurse
                                sourceContext sourceBinders current =
                              some sourceCurrent →
                            compileOccurrenceWith? targetDiagram targetRecurse
                                targetContext targetBinders
                                (mapOccurrence current) = some targetCurrent →
                            targetCurrent =
                              (sourceCurrent.renameWires wireMap).renameRelations
                                relationMap := by
                        intro current member
                        exact occurrenceMapped current (by simp [member])
                      have tailEq := inductionHypothesis compiledSourceTail
                        compiledTargetTail sourceTail targetTail tailMapped
                      simp only [ItemSeq.renameWires,
                        ItemSeq.renameRelations]
                      rw [headEq, tailEq]

private theorem ItemSeq.renameBoth_heq_of_val
    (items : ItemSeq source sourceRels)
    {first : Fin source → Fin firstTarget}
    {second : Fin source → Fin secondTarget}
    (relation : RelationRenaming sourceRels targetRels)
    (targetEq : firstTarget = secondTarget)
    (values : ∀ index, (first index).val = (second index).val) :
    (items.renameWires first).renameRelations relation ≍
      (items.renameWires second).renameRelations relation := by
  subst secondTarget
  have maps : first = second := by
    funext index
    exact Fin.ext (values index)
  subst second
  rfl

/-- Material `finishRegion` commutes with the standard inherited wire map and
relation substitution. -/
private theorem finishRegion_material_map
    (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceItems : ItemSeq
      (sourceContext.extend
        (layout.materialRegions.origin material)).length sourceRels) :
    finishRegion layout.plugRaw targetContext
        (layout.materialRegion material)
        ((sourceItems.renameWires
          (layout.materialCompilerIndexMap material sourceContext
            targetContext wireMap)).renameRelations relationMap) =
      ((finishRegion input.pattern.val.diagram sourceContext
          (layout.materialRegions.origin material) sourceItems).renameWires
            wireMap).renameRelations relationMap := by
  rw [layout.materialCompilerIndexMap_eq_extendWireRenaming]
  simp [finishRegion, Region.renameWires, Region.renameRelations,
    layout.exactScopeWires_materialRegion]
  constructor
  · exact (layout.materialLocalWires_length material).symm
  · rw [ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires,
      ← ItemSeq.renameWires_renameRelations,
      ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
    apply ItemSeq.renameBoth_heq_of_val sourceItems relationMap
    · apply congrArg (fun localCount =>
        targetContext.length + localCount)
      exact (congrArg List.length
        (layout.exactScopeWires_materialRegion material)).trans
          (layout.materialLocalWires_length material).symm
    · intro index
      simp [Function.comp_apply, extendWireRenaming]

/-- Successful recursive compilation of a material pattern region is exactly
the source computation renamed through the inherited wire and relation maps.
The successful source and target computations may use different fuels. -/
theorem compileRegion?_materialRegion_map
    (layout : PlugLayout input)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (material : layout.materialRegions.Carrier)
    (sourceContext : WireContext input.pattern.val.diagram)
    (targetContext : WireContext layout.plugRaw)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (getMapped : ∀ index, targetContext.get (wireMap index) =
      layout.patternWireMap (sourceContext.get index))
    (sourceExact : (sourceContext.extend
      (layout.materialRegions.origin material)).Exact
        (layout.materialRegions.origin material))
    (targetExact : (targetContext.extend
      (layout.materialRegion material)).Exact
        (layout.materialRegion material))
    (sourceBinders : BinderContext input.pattern.val.diagram sourceRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (sourceCovers : sourceBinders.Covers
      (layout.materialRegions.origin material))
    (relationMap : RelationRenaming sourceRels targetRels)
    (binderForward : layout.PatternBindersForward relationMap
      sourceBinders targetBinders)
    (sourceFuel targetFuel : Nat)
    (sourceBody : Region sourceContext.length sourceRels)
    (targetBody : Region targetContext.length targetRels)
    (sourceCompiled : compileRegion? input.pattern.val.diagram sourceFuel
      (layout.materialRegions.origin material) sourceContext sourceBinders =
        some sourceBody)
    (targetCompiled : compileRegion? layout.plugRaw targetFuel
      (layout.materialRegion material) targetContext targetBinders =
        some targetBody) :
    targetBody = (sourceBody.renameWires wireMap).renameRelations
      relationMap := by
  induction sourceFuel generalizing targetFuel material sourceContext
      targetContext wireMap sourceRels targetRels sourceBinders targetBinders
      relationMap sourceBody targetBody with
  | zero => simp [compileRegion?] at sourceCompiled
  | succ sourceFuel inductionHypothesis =>
      cases targetFuel with
      | zero => simp [compileRegion?] at targetCompiled
      | succ targetFuel =>
          let sourceRegion := layout.materialRegions.origin material
          let targetRegion := layout.materialRegion material
          let sourceExtended := sourceContext.extend sourceRegion
          let targetExtended := targetContext.extend targetRegion
          let extendedWireMap := layout.materialCompilerIndexMap material
            sourceContext targetContext wireMap
          have extendedGet : ∀ index,
              targetExtended.get (extendedWireMap index) =
                layout.patternWireMap (sourceExtended.get index) := by
            intro index
            exact layout.materialCompilerIndexMap_get material sourceContext
              targetContext wireMap getMapped index
          simp only [compileRegion?] at sourceCompiled targetCompiled
          cases sourceItemsResult : compileOccurrencesWith?
              input.pattern.val.diagram
              (compileRegion? input.pattern.val.diagram sourceFuel)
              sourceExtended sourceBinders
              (localOccurrences input.pattern.val.diagram sourceRegion) with
          | none =>
              obtain ⟨sourceItems, sourceItemsEq, _⟩ :=
                Option.bind_eq_some_iff.mp sourceCompiled
              rw [sourceItemsResult] at sourceItemsEq
              contradiction
          | some sourceItems =>
              obtain ⟨compiledItems, sourceItemsEq, sourceFinished⟩ :=
                Option.bind_eq_some_iff.mp sourceCompiled
              rw [sourceItemsResult] at sourceItemsEq
              simp only [Option.some.injEq] at sourceItemsEq
              subst compiledItems
              simp at sourceFinished
              subst sourceBody
              rw [← layout.map_localOccurrences_material material]
                at targetCompiled
              change (do
                let items ← compileOccurrencesWith? layout.plugRaw
                  (compileRegion? layout.plugRaw targetFuel) targetExtended
                  targetBinders
                  ((localOccurrences input.pattern.val.diagram
                    sourceRegion).map layout.mapPatternOccurrence)
                pure (finishRegion layout.plugRaw targetContext targetRegion
                  items)) = some targetBody at targetCompiled
              cases targetItemsResult : compileOccurrencesWith? layout.plugRaw
                  (compileRegion? layout.plugRaw targetFuel) targetExtended
                  targetBinders
                  ((localOccurrences input.pattern.val.diagram sourceRegion).map
                    layout.mapPatternOccurrence) with
              | none =>
                  obtain ⟨targetItems, targetItemsEq, _⟩ :=
                    Option.bind_eq_some_iff.mp targetCompiled
                  rw [targetItemsResult] at targetItemsEq
                  contradiction
              | some targetItems =>
                  obtain ⟨compiledItems, targetItemsEq, targetFinished⟩ :=
                    Option.bind_eq_some_iff.mp targetCompiled
                  rw [targetItemsResult] at targetItemsEq
                  simp only [Option.some.injEq] at targetItemsEq
                  subst compiledItems
                  simp at targetFinished
                  subst targetBody
                  have occurrenceMapped : ∀ occurrence,
                      occurrence ∈ localOccurrences
                        input.pattern.val.diagram sourceRegion →
                      ∀ sourceItem targetItem,
                        compileOccurrenceWith? input.pattern.val.diagram
                            (compileRegion? input.pattern.val.diagram sourceFuel)
                            sourceExtended sourceBinders occurrence =
                              some sourceItem →
                        compileOccurrenceWith? layout.plugRaw
                            (compileRegion? layout.plugRaw targetFuel)
                            targetExtended targetBinders
                            (layout.mapPatternOccurrence occurrence) =
                              some targetItem →
                        targetItem =
                          (sourceItem.renameWires extendedWireMap).renameRelations
                            relationMap := by
                    intro occurrence member sourceItem targetItem
                      sourceItemCompiled targetItemCompiled
                    cases occurrence with
                    | node node =>
                        have nodeRegion :
                            (input.pattern.val.diagram.nodes node).region =
                              sourceRegion :=
                          (mem_localOccurrences_node
                            input.pattern.val.diagram sourceRegion node).mp
                              member
                        have nodeMap := layout.compileNode?_material_map
                          sourceExtended targetExtended sourceRegion sourceExact
                          sourceBinders targetBinders sourceCovers relationMap
                          binderForward node nodeRegion extendedWireMap
                          targetExact.nodup extendedGet targetWellFormed
                        simp only [compileOccurrenceWith?, mapPatternOccurrence]
                          at sourceItemCompiled targetItemCompiled
                        rw [sourceItemCompiled] at nodeMap
                        simp only [Option.map_some] at nodeMap
                        exact Option.some.inj
                          (targetItemCompiled.symm.trans nodeMap)
                    | child child =>
                        have sourceParent :=
                          (mem_localOccurrences_child
                            input.pattern.val.diagram sourceRegion child).mp
                              member
                        have childSurvives :
                            layout.materialRegions.survives child = true := by
                          rw [layout.materialRegions_exact]
                          apply decide_eq_true
                          exact layout.directMaterialChild_isMaterial material
                            child sourceParent
                        let childMaterial := layout.materialRegions.index child
                          childSurvives
                        have childOrigin :
                            layout.materialRegions.origin childMaterial = child :=
                          layout.materialRegions.origin_index child childSurvives
                        have mappedChild : layout.bodyRegion child =
                            layout.materialRegion childMaterial := by
                          rw [← childOrigin,
                            layout.bodyRegion_materialOrigin]
                        have sourceChildExact := sourceExact.extend_child
                          input.pattern.property.diagram_well_formed sourceParent
                        have targetParent :
                            (layout.plugRaw.regions
                              (layout.materialRegion childMaterial)).parent? =
                                some targetRegion := by
                          rw [layout.plugRegion_materialRegion]
                          change CRegion.parent? (layout.mapPatternRegion
                              (input.pattern.val.diagram.regions
                                (layout.materialRegions.origin childMaterial))) =
                            some (layout.materialRegion material)
                          rw [layout.mapPatternRegion_parent_eq_some_material_iff]
                          simpa only [childOrigin] using sourceParent
                        have targetChildExact := targetExact.extend_child
                          targetWellFormed targetParent
                        simp only [compileOccurrenceWith?, mapPatternOccurrence]
                          at sourceItemCompiled targetItemCompiled
                        rw [mappedChild] at targetItemCompiled
                        cases childRegion :
                            input.pattern.val.diagram.regions child with
                        | sheet =>
                            simp [childRegion] at sourceItemCompiled
                        | cut parent =>
                            have parentEq : parent = sourceRegion := by
                              simpa [childRegion, CRegion.parent?] using
                                sourceParent
                            subst parent
                            have targetChildRegion :
                                layout.plugRaw.regions
                                    (layout.materialRegion childMaterial) =
                                  .cut targetRegion := by
                              rw [layout.plugRegion_materialRegion, childOrigin,
                                childRegion]
                              change CRegion.cut (layout.bodyRegion
                                (layout.materialRegions.origin material)) =
                                  CRegion.cut (layout.materialRegion material)
                              rw [layout.bodyRegion_materialOrigin]
                            cases sourceChildResult : compileRegion?
                                input.pattern.val.diagram sourceFuel child
                                sourceExtended sourceBinders with
                            | none => simp [childRegion, sourceChildResult]
                                at sourceItemCompiled
                            | some sourceChildBody =>
                                simp [childRegion, sourceChildResult]
                                  at sourceItemCompiled
                                subst sourceItem
                                cases targetChildResult : compileRegion?
                                    layout.plugRaw targetFuel
                                    (layout.materialRegion childMaterial)
                                    targetExtended targetBinders with
                                | none => simp [targetChildRegion,
                                    targetChildResult] at targetItemCompiled
                                | some targetChildBody =>
                                    simp [targetChildRegion, targetChildResult]
                                      at targetItemCompiled
                                    subst targetItem
                                    exact congrArg Item.cut
                                      (inductionHypothesis childMaterial sourceExtended
                                        targetExtended extendedWireMap extendedGet
                                        (by
                                          rw [childOrigin]
                                          exact sourceChildExact)
                                        targetChildExact
                                        sourceBinders targetBinders
                                        (BinderContext.covers_cut_child
                                          sourceCovers (by
                                            rw [childOrigin]
                                            exact childRegion))
                                        relationMap binderForward targetFuel
                                        sourceChildBody targetChildBody
                                        (by
                                          rw [childOrigin]
                                          exact sourceChildResult)
                                        targetChildResult)
                        | bubble parent arity =>
                            have parentEq : parent = sourceRegion := by
                              simpa [childRegion, CRegion.parent?] using
                                sourceParent
                            subst parent
                            have targetChildRegion :
                                layout.plugRaw.regions
                                    (layout.materialRegion childMaterial) =
                                  .bubble targetRegion arity := by
                              rw [layout.plugRegion_materialRegion, childOrigin,
                                childRegion]
                              change CRegion.bubble (layout.bodyRegion
                                (layout.materialRegions.origin material)) arity =
                                  CRegion.bubble
                                    (layout.materialRegion material) arity
                              rw [layout.bodyRegion_materialOrigin]
                            cases sourceChildResult : compileRegion?
                                input.pattern.val.diagram sourceFuel child
                                sourceExtended
                                (sourceBinders.push child arity) with
                            | none => simp [childRegion, sourceChildResult]
                                at sourceItemCompiled
                            | some sourceChildBody =>
                                simp [childRegion, sourceChildResult]
                                  at sourceItemCompiled
                                subst sourceItem
                                cases targetChildResult : compileRegion?
                                    layout.plugRaw targetFuel
                                    (layout.materialRegion childMaterial)
                                    targetExtended
                                    (targetBinders.push
                                      (layout.materialRegion childMaterial)
                                      arity) with
                                | none => simp [targetChildRegion,
                                    targetChildResult] at targetItemCompiled
                                | some targetChildBody =>
                                    simp [targetChildRegion, targetChildResult]
                                      at targetItemCompiled
                                    subst targetItem
                                    exact congrArg (Item.bubble arity)
                                      (inductionHypothesis childMaterial sourceExtended
                                        targetExtended extendedWireMap extendedGet
                                        (by
                                          rw [childOrigin]
                                          exact sourceChildExact)
                                        targetChildExact
                                        (sourceBinders.push
                                          (layout.materialRegions.origin
                                            childMaterial) arity)
                                        (targetBinders.push
                                          (layout.materialRegion childMaterial)
                                          arity)
                                        (BinderContext.push_covers_bubble_child
                                          sourceCovers (by
                                            rw [childOrigin]
                                            exact childRegion))
                                        (RelationRenaming.lift relationMap arity)
                                        (PatternBindersForward.push layout
                                          relationMap sourceBinders targetBinders
                                          binderForward childMaterial arity)
                                        targetFuel sourceChildBody
                                        targetChildBody
                                        (by
                                          rw [childOrigin]
                                          exact sourceChildResult)
                                        targetChildResult)
                  have itemsEq := compileOccurrencesWith?_mapBoth_of_success
                    (compileRegion? input.pattern.val.diagram sourceFuel)
                    (compileRegion? layout.plugRaw targetFuel)
                    sourceExtended targetExtended sourceBinders targetBinders
                    layout.mapPatternOccurrence extendedWireMap relationMap
                    (localOccurrences input.pattern.val.diagram sourceRegion)
                    sourceItems targetItems sourceItemsResult
                    targetItemsResult occurrenceMapped
                  rw [itemsEq]
                  exact layout.finishRegion_material_map material sourceContext
                    targetContext wireMap relationMap sourceItems

/-- Given the exact source child block and a successful target material-child
block computation, the target items are precisely the simultaneous wire and
relation transport of the source items. -/
theorem compilePatternChildBlock
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer)
    (kernel : compiled.Kernel) (blocks : kernel.Blocks)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (targetExact :
      (layout.patternSiteWires consistent hostContext).Exact
        (layout.frameRegion input.site))
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    (targetFuel : Nat)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (targetItems : ItemSeq
      (layout.patternSiteWires consistent hostContext).length hostRels)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      (layout.patternSiteWires consistent hostContext)
      (layout.mapFrameBinders hostBinders)
      layout.bodyChildOccurrences = some targetItems) :
    targetItems = (blocks.childItems.renameWires
      (layout.patternContextIndexMap consistent admissible compiled
        hostContext hostExact)).renameRelations
          (compiled.spliceRelationMap input admissible hostBinders
            hostCovers) := by
  have occurrencesEq :
      (localChildOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer).map layout.mapPatternOccurrence =
          layout.bodyChildOccurrences := by
    unfold localChildOccurrences mapPatternOccurrence
    simp only [List.map_map]
    exact layout.map_directBodyChildren
  rw [← occurrencesEq] at targetCompiled
  have sourceCompiled : compileOccurrencesWith?
      input.pattern.val.diagram
      (compileRegion? input.pattern.val.diagram kernel.recurseFuel)
      (compiled.siteContext ++ compiled.siteLocals) compiled.siteBinders
      (localChildOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer) = some blocks.childItems := by
    simpa [Splice.Input.patternState] using blocks.child_compiled
  apply compileOccurrencesWith?_mapBoth_of_success
    (compileRegion? input.pattern.val.diagram kernel.recurseFuel)
    (compileRegion? layout.plugRaw targetFuel)
    (compiled.siteContext ++ compiled.siteLocals)
    (layout.patternSiteWires consistent hostContext)
    compiled.siteBinders (layout.mapFrameBinders hostBinders)
    layout.mapPatternOccurrence
    (layout.patternContextIndexMap consistent admissible compiled
      hostContext hostExact)
    (compiled.spliceRelationMap input admissible hostBinders hostCovers)
    (localChildOccurrences input.pattern.val.diagram
      input.binderSpine.bodyContainer)
    blocks.childItems targetItems sourceCompiled targetCompiled
  intro occurrence member sourceItem targetItem sourceItemCompiled
    targetItemCompiled
  obtain ⟨child, childMember, occurrenceEq⟩ := List.mem_map.mp member
  subst occurrence
  have sourceParent :
      (input.pattern.val.diagram.regions child).parent? =
        some input.binderSpine.bodyContainer :=
    of_decide_eq_true (List.mem_filter.mp childMember).2
  have childSurvives : layout.materialRegions.survives child = true := by
    rw [layout.materialRegions_exact]
    apply decide_eq_true
    exact directBodyChild_isMaterial input child sourceParent
  let material := layout.materialRegions.index child childSurvives
  have materialOrigin : layout.materialRegions.origin material = child :=
    layout.materialRegions.origin_index child childSurvives
  have mappedChild : layout.bodyRegion child =
      layout.materialRegion material := by
    rw [← materialOrigin, layout.bodyRegion_materialOrigin]
  have sourceChildExact := compiled.completeContext_exact.extend_child
    input.pattern.property.diagram_well_formed sourceParent
  have targetParent :
      (layout.plugRaw.regions (layout.materialRegion material)).parent? =
        some (layout.frameRegion input.site) := by
    rw [layout.plugRegion_materialRegion]
    apply (layout.materialChild_parent_eq_some_frameRegion_iff
      admissible.terminal_body material input.site).2
    exact ⟨by simpa only [materialOrigin] using sourceParent, rfl⟩
  have targetChildExact := targetExact.extend_child targetWellFormed targetParent
  simp only [compileOccurrenceWith?, mapPatternOccurrence]
    at sourceItemCompiled targetItemCompiled
  rw [mappedChild] at targetItemCompiled
  cases childRegion : input.pattern.val.diagram.regions child with
  | sheet => simp [childRegion] at sourceItemCompiled
  | cut parent =>
      have parentEq : parent = input.binderSpine.bodyContainer := by
        simpa [childRegion, CRegion.parent?] using sourceParent
      subst parent
      have targetChildRegion :
          layout.plugRaw.regions (layout.materialRegion material) =
            .cut (layout.frameRegion input.site) := by
        rw [layout.plugRegion_materialRegion, materialOrigin, childRegion]
        simp only [PlugLayout.mapPatternRegion,
          layout.bodyRegion_bodyContainer]
        rfl
      cases sourceChildResult : compileRegion? input.pattern.val.diagram
          kernel.recurseFuel child
          (compiled.siteContext ++ compiled.siteLocals)
          compiled.siteBinders with
      | none => simp [childRegion, sourceChildResult] at sourceItemCompiled
      | some sourceChildBody =>
          simp [childRegion, sourceChildResult] at sourceItemCompiled
          subst sourceItem
          cases targetChildResult : compileRegion? layout.plugRaw targetFuel
              (layout.materialRegion material)
              (layout.patternSiteWires consistent hostContext)
              (layout.mapFrameBinders hostBinders) with
          | none =>
              simp [targetChildRegion, targetChildResult] at targetItemCompiled
          | some targetChildBody =>
              simp [targetChildRegion, targetChildResult] at targetItemCompiled
              subst targetItem
              exact congrArg Item.cut
                (layout.compileRegion?_materialRegion_map targetWellFormed
                  material (compiled.siteContext ++ compiled.siteLocals)
                  (layout.patternSiteWires consistent hostContext)
                  (layout.patternContextIndexMap consistent admissible compiled
                    hostContext hostExact)
                  (layout.patternContextIndexMap_get consistent admissible
                    compiled hostContext hostExact)
                  (by
                    rw [materialOrigin]
                    exact sourceChildExact)
                  targetChildExact compiled.siteBinders
                  (layout.mapFrameBinders hostBinders)
                  (BinderContext.covers_cut_child compiled.binder_covers (by
                    rw [materialOrigin]
                    exact childRegion))
                  (compiled.spliceRelationMap input admissible hostBinders
                    hostCovers)
                  (layout.compiledPattern_bindersForward admissible compiled
                    hostBinders hostCovers)
                  kernel.recurseFuel targetFuel sourceChildBody
                  targetChildBody
                  (by
                    rw [materialOrigin]
                    exact sourceChildResult)
                  targetChildResult)
  | bubble parent arity =>
      have parentEq : parent = input.binderSpine.bodyContainer := by
        simpa [childRegion, CRegion.parent?] using sourceParent
      subst parent
      have targetChildRegion :
          layout.plugRaw.regions (layout.materialRegion material) =
            .bubble (layout.frameRegion input.site) arity := by
        rw [layout.plugRegion_materialRegion, materialOrigin, childRegion]
        simp only [PlugLayout.mapPatternRegion,
          layout.bodyRegion_bodyContainer]
        rfl
      simp only [childRegion] at sourceItemCompiled
      cases sourceChildResult : compileRegion? input.pattern.val.diagram
          kernel.recurseFuel child
          (compiled.siteContext ++ compiled.siteLocals)
          (compiled.siteBinders.push child arity) with
      | none =>
          obtain ⟨sourceChildBody, sourceChildEq, _⟩ :=
            Option.bind_eq_some_iff.mp sourceItemCompiled
          have impossible := sourceChildResult.symm.trans sourceChildEq
          contradiction
      | some sourceChildBody =>
          obtain ⟨compiledBody, sourceChildEq, sourceItemEq⟩ :=
            Option.bind_eq_some_iff.mp sourceItemCompiled
          have sourceBodies : sourceChildBody = compiledBody :=
            Option.some.inj (sourceChildResult.symm.trans sourceChildEq)
          subst compiledBody
          simp at sourceItemEq
          subst sourceItem
          simp only [targetChildRegion] at targetItemCompiled
          cases targetChildResult : compileRegion? layout.plugRaw targetFuel
              (layout.materialRegion material)
              (layout.patternSiteWires consistent hostContext)
              ((layout.mapFrameBinders hostBinders).push
                (layout.materialRegion material) arity) with
          | none =>
              obtain ⟨targetChildBody, targetChildEq, _⟩ :=
                Option.bind_eq_some_iff.mp targetItemCompiled
              have impossible := targetChildResult.symm.trans targetChildEq
              contradiction
          | some targetChildBody =>
              obtain ⟨compiledBody, targetChildEq, targetItemEq⟩ :=
                Option.bind_eq_some_iff.mp targetItemCompiled
              have targetBodies : targetChildBody = compiledBody :=
                Option.some.inj (targetChildResult.symm.trans targetChildEq)
              subst compiledBody
              simp at targetItemEq
              subst targetItem
              exact congrArg (Item.bubble arity)
                (layout.compileRegion?_materialRegion_map targetWellFormed
                  material (compiled.siteContext ++ compiled.siteLocals)
                  (layout.patternSiteWires consistent hostContext)
                  (layout.patternContextIndexMap consistent admissible compiled
                    hostContext hostExact)
                  (layout.patternContextIndexMap_get consistent admissible
                    compiled hostContext hostExact)
                  (by
                    rw [materialOrigin]
                    exact sourceChildExact)
                  targetChildExact
                  (compiled.siteBinders.push
                    (layout.materialRegions.origin material) arity)
                  ((layout.mapFrameBinders hostBinders).push
                    (layout.materialRegion material) arity)
                  (BinderContext.push_covers_bubble_child
                    compiled.binder_covers (by
                      rw [materialOrigin]
                      exact childRegion))
                  (RelationRenaming.lift
                    (compiled.spliceRelationMap input admissible hostBinders
                      hostCovers) arity)
                  (PatternBindersForward.push layout
                    (compiled.spliceRelationMap input admissible hostBinders
                      hostCovers)
                    compiled.siteBinders (layout.mapFrameBinders hostBinders)
                    (layout.compiledPattern_bindersForward admissible compiled
                      hostBinders hostCovers)
                    material arity)
                  kernel.recurseFuel targetFuel sourceChildBody
                  targetChildBody
                  (by
                    rw [materialOrigin]
                    exact sourceChildResult)
                  targetChildResult)

/-- Every inserted material child in the terminal-body block is a direct
target occurrence at the splice site. -/
theorem bodyChildOccurrences_mem_localOccurrences_site
    (layout : PlugLayout input) (admissible : input.Admissible) :
    ∀ occurrence, occurrence ∈ layout.bodyChildOccurrences →
      occurrence ∈ localOccurrences layout.plugRaw
        (layout.frameRegion input.site) := by
  intro occurrence member
  rw [layout.localOccurrences_site admissible]
  exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr member)))

/-- Completeness constructs the terminal material-child block, and recursive
transport fixes its result to the canonical renamed source child items. -/
theorem compilePatternChildBlock_complete
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer)
    (kernel : compiled.Kernel) (blocks : kernel.Blocks)
    (hostContext : WireContext input.frame.val)
    (hostExact : hostContext.Exact input.site)
    (targetExact :
      (layout.patternSiteWires consistent hostContext).Exact
        (layout.frameRegion input.site))
    (hostBinders : BinderContext input.frame.val hostRels)
    (hostCovers : hostBinders.Covers input.site)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (targetDepth targetFuel : Nat)
    (targetClimb : layout.plugRaw.climb targetDepth
      (layout.frameRegion input.site) = some layout.plugRaw.root)
    (targetEnough : targetDepth + 1 + targetFuel =
      layout.plugRaw.regionCount + 1) :
    compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      (layout.patternSiteWires consistent hostContext)
      (layout.mapFrameBinders hostBinders)
      layout.bodyChildOccurrences =
        some ((blocks.childItems.renameWires
          (layout.patternContextIndexMap consistent admissible compiled
            hostContext hostExact)).renameRelations
              (compiled.spliceRelationMap input admissible hostBinders
                hostCovers)) := by
  obtain ⟨targetItems, targetCompiled⟩ :=
    compileDirectOccurrences?_complete targetWellFormed targetClimb
      targetEnough targetExact
      (layout.mapFrameBinders_covers_site hostCovers)
      layout.bodyChildOccurrences
      (layout.bodyChildOccurrences_mem_localOccurrences_site admissible)
  have itemsEq := layout.compilePatternChildBlock consistent admissible
    compiled kernel blocks hostContext hostExact targetExact hostBinders
    hostCovers targetFuel targetWellFormed targetItems targetCompiled
  rw [itemsEq] at targetCompiled
  exact targetCompiled

end Splice.Input.PlugLayout

end VisualProof.Concrete
