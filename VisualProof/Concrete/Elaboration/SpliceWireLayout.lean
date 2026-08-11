import VisualProof.Concrete.Elaboration.SpliceOccurrence

/-! Exact lexical wire blocks for a source-derived splice. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Elaboration

namespace Splice.Input.PlugLayout

private theorem allFin_add (left right : Nat) :
    allFin (left + right) =
      (allFin left).map (Fin.castAdd right) ++
        (allFin right).map (Fin.natAdd left) := by
  simp only [allFin_eq_finRange]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.length_finRange, List.length_append, List.length_map] at hright
    simp only [List.getElem_append, List.length_map, List.length_finRange]
    split
    · simp
    · simp
      omega

private theorem filterFin_add (predicate : Fin (left + right) → Bool) :
    filterFin predicate =
      (filterFin fun index : Fin left =>
        predicate (Fin.castAdd right index)).map (Fin.castAdd right) ++
      (filterFin fun index : Fin right =>
        predicate (Fin.natAdd left index)).map (Fin.natAdd left) := by
  unfold filterFin
  rw [allFin_add]
  simp only [List.filter_append, List.filter_map]
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

/-- Frame wires local to one source region, embedded in stable source order. -/
noncomputable def frameLocalWires (layout : PlugLayout input)
    (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount) :
    WireContext layout.plugRaw :=
  (exactScopeWires input.frame.val region).map
    (layout.frameWireEmbedding consistent)

/-- Pattern-internal wires local to the terminal body, in dense survivor order. -/
def bodyLocalWires (layout : PlugLayout input) :
    WireContext layout.plugRaw :=
  (filterFin fun wire : layout.internalWires.Carrier =>
    decide ((input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        input.binderSpine.bodyContainer)).map layout.internalWire

/-- Pattern-internal wires local to one surviving material region. -/
def materialLocalWires (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    WireContext layout.plugRaw :=
  (filterFin fun wire : layout.internalWires.Carrier =>
    decide ((input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        layout.materialRegions.origin material)).map layout.internalWire

/-- The source pattern wires represented by the terminal-body internal block. -/
def bodySourceLocalWires (layout : PlugLayout input) :
    WireContext input.pattern.val.diagram :=
  layout.internalWires.enumeration.filter fun wire =>
    decide ((input.pattern.val.diagram.wires wire).scope =
      input.binderSpine.bodyContainer)

/-- A non-boundary pattern wire can have nonmaterial scope only at the
designated terminal body. -/
theorem internalWire_not_material_iff_bodyContainer
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (wire : layout.internalWires.Carrier) :
    (¬input.binderSpine.IsMaterialRegion
        (input.pattern.val.diagram.wires
          (layout.internalWires.origin wire)).scope) ↔
      (input.pattern.val.diagram.wires
          (layout.internalWires.origin wire)).scope =
        input.binderSpine.bodyContainer := by
  let original := layout.internalWires.origin wire
  have internal : original ∉ input.pattern.val.exposedWires := by
    have survives := layout.internalWires.origin_survives wire
    rw [layout.internalWires_exact] at survives
    exact of_decide_eq_true survives
  have notBoundary : original ∉ input.pattern.val.boundary := by
    simpa only [OpenDiagram.mem_exposedWires] using internal
  let owner := (input.pattern.val.diagram.wires original).scope
  constructor
  · intro notMaterial
    by_cases empty : input.binderSpine.proxyCount = 0
    · by_cases rootEq : owner = input.pattern.val.diagram.root
      · exact rootEq.trans
          (input.binderSpine.body_eq_root_of_empty empty).symm
      · have everyProxy : ∀ index,
            owner ≠ input.binderSpine.proxy index := by
          intro index
          have index' : Fin 0 := Fin.cast empty index
          exact Fin.elim0 index'
        exact (notMaterial ⟨rootEq, everyProxy⟩).elim
    · have rootNe : owner ≠ input.pattern.val.diagram.root :=
        terminal.root_has_no_nonboundary_wires empty original notBoundary
      have notEveryProxy :
          ¬∀ index, owner ≠ input.binderSpine.proxy index := by
        intro everyProxy
        exact notMaterial ⟨rootNe, everyProxy⟩
      obtain ⟨index, ownerNe⟩ := Classical.not_forall.mp notEveryProxy
      have ownerEq : owner = input.binderSpine.proxy index :=
        Classical.not_not.mp ownerNe
      by_cases nonterminal :
          index.val + 1 < input.binderSpine.proxyCount
      · exact (terminal.nonterminal_has_no_nonboundary_wires index
          nonterminal original notBoundary ownerEq).elim
      · let last : Fin input.binderSpine.proxyCount :=
          ⟨input.binderSpine.proxyCount - 1, by omega⟩
        have indexEq : index = last := by
          apply Fin.ext
          simp only [last]
          omega
        calc
          owner = input.binderSpine.proxy index := ownerEq
          _ = input.binderSpine.proxy last := congrArg _ indexEq
          _ = input.binderSpine.bodyContainer :=
            (input.binderSpine.body_eq_terminal_of_nonempty empty).symm
  · intro ownerEq
    rw [ownerEq]
    exact bodyContainer_not_material input

@[simp] theorem internalWire_materialIndex_eq_none_iff_bodyContainer
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (wire : layout.internalWires.Carrier) :
    layout.materialRegions.index?
        (input.pattern.val.diagram.wires
          (layout.internalWires.origin wire)).scope = none ↔
      (input.pattern.val.diagram.wires
          (layout.internalWires.origin wire)).scope =
        input.binderSpine.bodyContainer := by
  rw [layout.materialRegions.index?_eq_none_iff,
    layout.materialRegions_exact]
  simpa using layout.internalWire_not_material_iff_bodyContainer
    terminal wire

/-- The quotient-carrier half of a target local-wire traversal is exactly the
source frame's local block under the no-coalescence embedding. -/
theorem quotientLocalWires_eq_frameLocalWires
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (region : Fin input.frame.val.regionCount) :
    (filterFin fun quotient : input.wireQuotient.Carrier =>
      decide (input.coalescedScope quotient = region)).map layout.frameWire =
        layout.frameLocalWires consistent region := by
  let predicate : Fin input.frame.val.wireCount → Bool :=
    fun wire => decide ((input.frame.val.wires wire).scope = region)
  have allSurvive : ∀ wire, predicate wire = true →
      input.wireQuotient.survives wire = true := by
    intro wire _
    change input.attachmentPartition.quotientDomain.survives wire = true
    rw [FinitePartition.quotientDomain_survives_iff]
    apply input.attachmentPartition_related_eq consistent
    apply (FinitePartition.related_eq_true_iff _ _ _).2
    exact input.attachmentPartition_normalized wire
  have sourceFilter := filterFin_eq_enumeration_filter
    input.wireQuotient predicate allSurvive
  have mappedOrigins := map_origin_filterFin
    input.wireQuotient predicate
  have quotientFilter :
      filterFin (fun quotient : input.wireQuotient.Carrier =>
        decide (input.coalescedScope quotient = region)) =
      filterFin (fun quotient : input.wireQuotient.Carrier =>
        predicate (input.wireQuotient.origin quotient)) := by
    unfold filterFin
    apply List.filter_congr
    intro quotient _
    have scope := coalescedScope_quotientWire input consistent
      (input.wireQuotient.origin quotient)
    rw [input.quotientWire_wireQuotient_origin] at scope
    simp only [predicate]
    rw [scope]
  unfold frameLocalWires frameWireEmbedding exactScopeWires
  rw [quotientFilter, sourceFilter, ← mappedOrigins]
  simp only [List.map_map]
  apply List.map_congr_left
  intro quotient _
  change layout.frameWire quotient =
    layout.frameWire
      (input.quotientWire (input.wireQuotient.origin quotient))
  rw [input.quotientWire_wireQuotient_origin]

/-- The internal-carrier half of a frame-region traversal is empty away from
the insertion site and is exactly the terminal body's local block at the site. -/
theorem internalLocalWires_frameRegion
    (layout : PlugLayout input) (terminal : input.TerminalBody)
    (region : Fin input.frame.val.regionCount) :
    (filterFin fun wire : layout.internalWires.Carrier =>
      decide (layout.bodyRegion
        (input.pattern.val.diagram.wires
          (layout.internalWires.origin wire)).scope =
            layout.frameRegion region)).map layout.internalWire =
      if region = input.site then layout.bodyLocalWires else [] := by
  by_cases atSite : region = input.site
  · rw [if_pos atSite]
    subst region
    unfold bodyLocalWires
    apply congrArg (List.map layout.internalWire)
    unfold filterFin
    apply List.filter_congr
    intro wire _
    simp only [bodyRegion_eq_frameRegion_iff,
      layout.internalWire_materialIndex_eq_none_iff_bodyContainer terminal,
      and_true]
  · rw [if_neg atSite]
    have empty :
        filterFin (fun wire : layout.internalWires.Carrier =>
          decide (layout.bodyRegion
            (input.pattern.val.diagram.wires
              (layout.internalWires.origin wire)).scope =
                layout.frameRegion region)) = [] := by
      unfold filterFin
      apply List.filter_eq_nil_iff.2
      intro wire _ accepted
      have equality := of_decide_eq_true accepted
      have siteEq := (layout.bodyRegion_eq_frameRegion_iff
        (input.pattern.val.diagram.wires
          (layout.internalWires.origin wire)).scope region).1 equality |>.2
      exact atSite siteEq.symm
    rw [empty]
    rfl

/-- Exact target local-wire order at every retained frame region.  Stable
frame wires precede the terminal body's internal wires at the insertion site. -/
theorem exactScopeWires_frameRegion
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (region : Fin input.frame.val.regionCount) :
    exactScopeWires layout.plugRaw (layout.frameRegion region) =
      layout.frameLocalWires consistent region ++
        if region = input.site then layout.bodyLocalWires else [] := by
  unfold exactScopeWires
  simp only [PlugLayout.plugRaw, PlugLayout.wireCount]
  rw [filterFin_add]
  simp only [PlugLayout.plugWire, Fin.addCases_left, Fin.addCases_right]
  have frameBlock :=
    layout.quotientLocalWires_eq_frameLocalWires consistent region
  have internalBlock := layout.internalLocalWires_frameRegion terminal region
  rw [show
      (filterFin fun index : input.wireQuotient.Carrier =>
        decide (layout.frameRegion (input.coalescedScope index) =
          layout.frameRegion region)).map (Fin.castAdd layout.internalWires.count) =
        layout.frameLocalWires consistent region by
      simpa only [frameRegion_eq_frameRegion_iff, PlugLayout.frameWire] using
        frameBlock,
    show
      (filterFin fun index : layout.internalWires.Carrier =>
        decide ((layout.mapPatternWire (input.pattern.val.diagram.wires
          (layout.internalWires.origin index))).scope =
            layout.frameRegion region)).map
              (Fin.natAdd input.wireQuotient.count) =
        (if region = input.site then layout.bodyLocalWires else []) by
      simpa only [PlugLayout.mapPatternWire, PlugLayout.internalWire] using
        internalBlock]
  rfl

/-- Exact target local-wire order at a surviving material region. -/
theorem exactScopeWires_materialRegion
    (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    exactScopeWires layout.plugRaw (layout.materialRegion material) =
      layout.materialLocalWires material := by
  unfold exactScopeWires
  simp only [PlugLayout.plugRaw, PlugLayout.wireCount]
  rw [filterFin_add]
  simp only [PlugLayout.plugWire, Fin.addCases_left, Fin.addCases_right]
  have noFrame :
      filterFin (fun quotient : input.wireQuotient.Carrier =>
        decide (layout.frameRegion (input.coalescedScope quotient) =
          layout.materialRegion material)) = [] := by
    unfold filterFin
    apply List.filter_eq_nil_iff.2
    intro quotient _ accepted
    exact layout.frameRegion_ne_materialRegion
      (input.coalescedScope quotient) material (of_decide_eq_true accepted)
  rw [noFrame]
  simp only [List.map_nil, List.nil_append]
  unfold materialLocalWires
  apply congrArg (List.map layout.internalWire)
  unfold filterFin
  apply List.filter_congr
  intro wire _
  simp only [PlugLayout.mapPatternWire,
    bodyRegion_eq_materialRegion_iff]

/-- The terminal source compiler's local-wire block is exactly the stable
non-boundary block represented by the plug layout. -/
theorem compiledPattern_siteLocals
    (layout : PlugLayout input)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer) :
    compiled.siteLocals = layout.bodySourceLocalWires := by
  by_cases atRoot : input.binderSpine.bodyContainer =
      input.pattern.val.diagram.root
  · have locals := compiled.siteLocals_eq
    change compiled.siteLocals =
      if input.binderSpine.bodyContainer = input.pattern.val.diagram.root then
        input.pattern.val.hiddenWires
      else exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer at locals
    rw [if_pos atRoot] at locals
    rw [locals]
    unfold bodySourceLocalWires SurvivorDomain.enumeration
      OpenDiagram.hiddenWires exactScopeWires filterFin
    rw [atRoot]
    simp only [List.filter_filter]
    apply List.filter_congr
    intro wire _
    rw [layout.internalWires_exact]
    by_cases scope :
        (input.pattern.val.diagram.wires wire).scope =
          input.pattern.val.diagram.root <;>
      by_cases internal : wire ∉ input.pattern.val.exposedWires <;>
        simp [scope, internal]
  · have locals := compiled.siteLocals_eq
    change compiled.siteLocals =
      if input.binderSpine.bodyContainer = input.pattern.val.diagram.root then
        input.pattern.val.hiddenWires
      else exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer at locals
    rw [if_neg atRoot] at locals
    rw [locals]
    unfold bodySourceLocalWires SurvivorDomain.enumeration
      exactScopeWires filterFin
    simp only [List.filter_filter]
    apply List.filter_congr
    intro wire _
    rw [layout.internalWires_exact]
    by_cases scope : (input.pattern.val.diagram.wires wire).scope =
        input.binderSpine.bodyContainer
    · have notExposed : wire ∉ input.pattern.val.exposedWires := by
        intro exposed
        have rootScope := input.pattern.property.exposed_root_scoped exposed
        exact atRoot (scope.symm.trans rootScope)
      simp [scope, notExposed]
    · simp [scope]

/-- Dense internal identifiers at the terminal body enumerate exactly the
source wires in `bodySourceLocalWires`. -/
theorem bodyLocalOrigins (layout : PlugLayout input) :
    (filterFin fun wire : layout.internalWires.Carrier =>
      decide ((input.pattern.val.diagram.wires
        (layout.internalWires.origin wire)).scope =
          input.binderSpine.bodyContainer)).map
            layout.internalWires.origin =
      layout.bodySourceLocalWires := by
  exact map_origin_filterFin layout.internalWires
    (fun wire => decide ((input.pattern.val.diagram.wires wire).scope =
      input.binderSpine.bodyContainer))

/-- The source terminal-body and target internal local blocks have the same
cardinality, position for position. -/
theorem compiledPattern_siteLocals_length
    (layout : PlugLayout input)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer) :
    compiled.siteLocals.length = layout.bodyLocalWires.length := by
  rw [layout.compiledPattern_siteLocals compiled]
  unfold bodyLocalWires
  rw [← layout.bodyLocalOrigins]
  let positions := filterFin fun wire : layout.internalWires.Carrier =>
    decide ((input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        input.binderSpine.bodyContainer)
  change (positions.map layout.internalWires.origin).length =
    (positions.map layout.internalWire).length
  exact (List.length_map layout.internalWires.origin).trans
    (List.length_map layout.internalWire).symm

/-- Stable local-wire position transport from the compiled terminal material
body to the target site's internal block. -/
noncomputable def bodyLocalEquiv
    (layout : PlugLayout input)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer) :
    FiniteEquiv (Fin compiled.siteLocals.length)
      (Fin layout.bodyLocalWires.length) :=
  FiniteEquiv.finCast (layout.compiledPattern_siteLocals_length compiled)

/-- Each transported terminal-body local position has one dense internal
identifier whose source origin and target image are the corresponding list
entries. -/
theorem bodyLocalEquiv_get
    (layout : PlugLayout input)
    (compiled : CompiledSite input.patternState
      input.binderSpine.bodyContainer)
    (index : Fin compiled.siteLocals.length) :
    ∃ internal : layout.internalWires.Carrier,
      compiled.siteLocals.get index = layout.internalWires.origin internal ∧
        layout.bodyLocalWires.get (layout.bodyLocalEquiv compiled index) =
          layout.internalWire internal := by
  let positions := filterFin fun wire : layout.internalWires.Carrier =>
    decide ((input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        input.binderSpine.bodyContainer)
  have sourceEq : compiled.siteLocals =
      positions.map layout.internalWires.origin := by
    exact (layout.compiledPattern_siteLocals compiled).trans
      layout.bodyLocalOrigins.symm
  have targetEq : layout.bodyLocalWires =
      positions.map layout.internalWire := by
    rfl
  have sourceLength : compiled.siteLocals.length = positions.length := by
    calc
      compiled.siteLocals.length =
          (positions.map layout.internalWires.origin).length :=
        congrArg List.length sourceEq
      _ = positions.length :=
        List.length_map layout.internalWires.origin
  let position : Fin positions.length :=
    ⟨index.val, by
      rw [← sourceLength]
      exact index.isLt⟩
  let internal := positions.get position
  refine ⟨internal, ?_, ?_⟩
  · have value := List.get_of_eq sourceEq index
    have mapped := List.getElem_map layout.internalWires.origin
      (l := positions) (i := index.val) (h := by
        exact Eq.mp (congrArg (fun length => index.val < length)
          (List.length_map layout.internalWires.origin).symm)
            position.isLt)
    exact value.trans (by
      simpa only [List.get_eq_getElem, position, internal] using mapped)
  · have value := List.get_of_eq targetEq
      (layout.bodyLocalEquiv compiled index)
    have mapped := List.getElem_map layout.internalWire
      (l := positions) (i := (layout.bodyLocalEquiv compiled index).val)
      (h := by
        change index.val < (positions.map layout.internalWire).length
        exact Eq.mp (congrArg (fun length => index.val < length)
          (List.length_map layout.internalWire).symm) position.isLt)
    exact value.trans (by
      simpa only [List.get_eq_getElem, bodyLocalEquiv,
        FiniteEquiv.finCast, position, internal] using mapped)

end Splice.Input.PlugLayout

end VisualProof.Concrete
