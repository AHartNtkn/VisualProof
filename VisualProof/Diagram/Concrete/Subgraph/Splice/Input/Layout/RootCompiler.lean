import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.PatternTransport

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace PlugLayout

/-! ## Ordered open-root contexts

The semantic boundary is a list of positions, not a set of wire identities.
These two views retain that list exactly while transporting its wire classes
through host coalescing and then through the frame embedding into the splice
output.  In particular, repeated source positions remain repeated positions.
-/

/-- A root-scoped host wire remains root-scoped after passing to its coalesced
class. -/
theorem quotientWire_scope_eq_root
    (input : Input signature)
    (hadmissible : input.Admissible)
    (wire : Fin input.frame.val.wireCount)
    (hroot : (input.frame.val.wires wire).scope = input.frame.val.root) :
    (input.coalesceFrameRaw.wires (input.quotientWire wire)).scope =
      input.coalesceFrameRaw.root := by
  change input.coalescedScope (input.quotientWire wire) = input.frame.val.root
  apply ConcreteElaboration.encloses_sheet_eq
    input.frame.property.root_is_sheet
  have hencloses := input.coalescedScope_encloses_member hadmissible
    (input.quotientWire wire) wire
    ((input.mem_classWires (input.quotientWire wire) wire).2 rfl)
  simpa only [hroot] using hencloses

/-- The coalesced host equipped with the caller's ordered open boundary. -/
def coalescedOpenRoot (input : Input signature)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    OpenConcreteDiagram where
  diagram := input.coalesceFrameRaw
  boundary := sourceBoundary.map input.quotientWire

theorem coalescedOpenRoot_wellFormed
    (input : Input signature)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (coalescedOpenRoot input sourceBoundary).WellFormed signature where
  diagram_well_formed := input.coalesceFrameRaw_wellFormed hadmissible
  boundary_is_root_scoped := by
    change ∀ quotient : input.wireQuotient.Carrier,
      quotient ∈ sourceBoundary.map input.quotientWire →
        input.coalescedScope quotient = input.frame.val.root
    intro quotient hquotient
    rw [List.mem_map] at hquotient
    obtain ⟨wire, hwire, rfl⟩ := hquotient
    exact quotientWire_scope_eq_root input hadmissible wire
      (sourceRoot wire hwire)

def checkedCoalescedOpenRoot
    (input : Input signature)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    CheckedOpenDiagram signature :=
  ⟨coalescedOpenRoot input sourceBoundary,
    coalescedOpenRoot_wellFormed input hadmissible sourceBoundary sourceRoot⟩

/-- The plugged output equipped with the same ordered positions, transported
through quotienting and the frame-wire embedding. -/
def outputOpenRoot (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    OpenConcreteDiagram where
  diagram := layout.plugRaw
  boundary := sourceBoundary.map (layout.frameWire ∘ input.quotientWire)

theorem outputOpenRoot_wellFormed
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    (outputOpenRoot input layout sourceBoundary).WellFormed signature where
  diagram_well_formed := plugRaw_wellFormed signature input layout hadmissible
  boundary_is_root_scoped := by
    change ∀ outputWire : Fin layout.wireCount,
      outputWire ∈
          sourceBoundary.map (layout.frameWire ∘ input.quotientWire) →
        (layout.plugWire outputWire).scope =
          layout.frameRegion input.frame.val.root
    intro outputWire houtput
    rw [List.mem_map] at houtput
    obtain ⟨wire, hwire, rfl⟩ := houtput
    have hcoalesced := quotientWire_scope_eq_root input hadmissible wire
      (sourceRoot wire hwire)
    simp only [Function.comp_apply]
    change (layout.plugWire
      (layout.quotientBlockWire (input.quotientWire wire))).scope =
        layout.frameRegion input.frame.val.root
    rw [plugWire_quotientBlockWire]
    change layout.frameRegion (input.coalescedScope
      (input.quotientWire wire)) = layout.frameRegion input.frame.val.root
    exact congrArg layout.frameRegion hcoalesced

def checkedOutputOpenRoot
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    CheckedOpenDiagram signature :=
  ⟨outputOpenRoot input layout sourceBoundary,
    outputOpenRoot_wellFormed input layout hadmissible sourceBoundary sourceRoot⟩

theorem frameWire_mem_rootExposed_iff
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (quotient : input.wireQuotient.Carrier) :
    layout.frameWire quotient ∈
        (outputOpenRoot input layout sourceBoundary).exposedWires ↔
      quotient ∈ (coalescedOpenRoot input sourceBoundary).exposedWires := by
  change layout.frameWire quotient ∈
      (sourceBoundary.map
        (layout.frameWire ∘ input.quotientWire)).eraseDups ↔
    quotient ∈ (sourceBoundary.map input.quotientWire).eraseDups
  simp only [List.mem_eraseDups]
  constructor
  · intro houtput
    obtain ⟨wire, hwire, heq⟩ := List.mem_map.mp houtput
    have hquotient : input.quotientWire wire = quotient := by
      apply layout.frameWire_injective
      simpa only [Function.comp_apply] using heq
    exact List.mem_map.mpr ⟨wire, hwire, hquotient⟩
  · intro hcoalesced
    obtain ⟨wire, hwire, heq⟩ := List.mem_map.mp hcoalesced
    exact List.mem_map.mpr ⟨wire, hwire, by
      simpa only [Function.comp_apply, heq]⟩

/-- The external wire classes of the coalesced and plugged open roots are in
canonical bijection, independently of repeated boundary positions. -/
noncomputable def rootExposedWireEquiv
    (input : Input signature)
    (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    FiniteEquiv
      (Fin (coalescedOpenRoot input sourceBoundary).exposedWires.length)
      (Fin (outputOpenRoot input layout sourceBoundary).exposedWires.length) :=
  listEmbeddingEquiv layout.frameWire
    (coalescedOpenRoot input sourceBoundary).exposedWires
    (outputOpenRoot input layout sourceBoundary).exposedWires
    (coalescedOpenRoot input sourceBoundary).exposedWires_nodup
    (outputOpenRoot input layout sourceBoundary).exposedWires_nodup
    (by
      intro quotient hquotient
      exact (frameWire_mem_rootExposed_iff input layout sourceBoundary
        quotient).2 hquotient)
    (by
      intro outputWire houtput
      have hboundary := (OpenConcreteDiagram.mem_exposedWires
        (outputOpenRoot input layout sourceBoundary) outputWire).1 houtput
      change outputWire ∈
        sourceBoundary.map (layout.frameWire ∘ input.quotientWire) at hboundary
      obtain ⟨wire, hwire, heq⟩ := List.mem_map.mp hboundary
      refine ⟨input.quotientWire wire, ?_, heq⟩
      apply (OpenConcreteDiagram.mem_exposedWires
        (coalescedOpenRoot input sourceBoundary) _).2
      change input.quotientWire wire ∈ sourceBoundary.map input.quotientWire
      exact List.mem_map.mpr ⟨wire, hwire, rfl⟩)
    (fun left _ right _ heq => layout.frameWire_injective heq)

theorem rootExposedWireEquiv_spec
    (input : Input signature)
    (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (index : Fin
      (coalescedOpenRoot input sourceBoundary).exposedWires.length) :
    (outputOpenRoot input layout sourceBoundary).exposedWires.get
        (rootExposedWireEquiv input layout sourceBoundary index) =
      layout.frameWire
        ((coalescedOpenRoot input sourceBoundary).exposedWires.get index) := by
  exact listEmbeddingEquiv_spec layout.frameWire
    (coalescedOpenRoot input sourceBoundary).exposedWires
    (outputOpenRoot input layout sourceBoundary).exposedWires
    (coalescedOpenRoot input sourceBoundary).exposedWires_nodup
    (outputOpenRoot input layout sourceBoundary).exposedWires_nodup
    (by
      intro quotient hquotient
      exact (frameWire_mem_rootExposed_iff input layout sourceBoundary
        quotient).2 hquotient)
    (by
      intro outputWire houtput
      have hboundary := (OpenConcreteDiagram.mem_exposedWires
        (outputOpenRoot input layout sourceBoundary) outputWire).1 houtput
      change outputWire ∈
        sourceBoundary.map (layout.frameWire ∘ input.quotientWire) at hboundary
      obtain ⟨wire, hwire, heq⟩ := List.mem_map.mp hboundary
      refine ⟨input.quotientWire wire, ?_, heq⟩
      apply (OpenConcreteDiagram.mem_exposedWires
        (coalescedOpenRoot input sourceBoundary) _).2
      change input.quotientWire wire ∈ sourceBoundary.map input.quotientWire
      exact List.mem_map.mpr ⟨wire, hwire, rfl⟩)
    (fun left _ right _ heq => layout.frameWire_injective heq) index

/-- The external-class equivalence preserves every ordered boundary
position, including repeated positions that denote the same wire class. -/
theorem rootExposedWireEquiv_boundaryClass
    (input : Input signature)
    (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (position : Fin sourceBoundary.length) :
    rootExposedWireEquiv input layout sourceBoundary
        ((coalescedOpenRoot input sourceBoundary).boundaryClass
          (Fin.cast (by simp [coalescedOpenRoot]) position)) =
      (outputOpenRoot input layout sourceBoundary).boundaryClass
        (Fin.cast (by simp [outputOpenRoot]) position) := by
  apply OpenConcreteDiagram.boundaryClass_complete
  rw [rootExposedWireEquiv_spec,
    OpenConcreteDiagram.boundaryClass_sound]
  simp [coalescedOpenRoot, outputOpenRoot, Function.comp_apply]

/-- Away from a sheet-root splice, hidden root wires are exactly the mapped
hidden frame wires; every pattern-internal wire remains below the root. -/
theorem frameWire_mem_rootHidden_iff_of_nested
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hnested : input.site ≠ input.frame.val.root)
    (quotient : input.wireQuotient.Carrier) :
    layout.frameWire quotient ∈
        (outputOpenRoot input layout sourceBoundary).hiddenWires ↔
      quotient ∈ (coalescedOpenRoot input sourceBoundary).hiddenWires := by
  constructor
  · intro htarget
    have hhidden := (OpenConcreteDiagram.mem_hiddenWires
      (outputOpenRoot input layout sourceBoundary)
      (layout.frameWire quotient)).1 htarget
    apply (OpenConcreteDiagram.mem_hiddenWires
      (coalescedOpenRoot input sourceBoundary) quotient).2
    constructor
    · have hscope := hhidden.1
      change (layout.plugWire
        (layout.quotientBlockWire quotient)).scope =
          layout.frameRegion input.frame.val.root at hscope
      rw [plugWire_quotientBlockWire] at hscope
      exact layout.frameRegion_injective hscope
    · intro hexposed
      exact hhidden.2 ((frameWire_mem_rootExposed_iff input layout
        sourceBoundary quotient).2 hexposed)
  · intro hsource
    have hhidden := (OpenConcreteDiagram.mem_hiddenWires
      (coalescedOpenRoot input sourceBoundary) quotient).1 hsource
    apply (OpenConcreteDiagram.mem_hiddenWires
      (outputOpenRoot input layout sourceBoundary)
      (layout.frameWire quotient)).2
    constructor
    · change (layout.plugWire
        (layout.quotientBlockWire quotient)).scope =
          layout.frameRegion input.frame.val.root
      rw [plugWire_quotientBlockWire]
      exact congrArg layout.frameRegion hhidden.1
    · intro hexposed
      exact hhidden.2 ((frameWire_mem_rootExposed_iff input layout
        sourceBoundary quotient).1 hexposed)

theorem outputRootHidden_frame_complete_of_nested
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hnested : input.site ≠ input.frame.val.root)
    (wire : Fin layout.plugRaw.wireCount)
    (hwire : wire ∈ (outputOpenRoot input layout sourceBoundary).hiddenWires) :
    ∃ quotient ∈ (coalescedOpenRoot input sourceBoundary).hiddenWires,
      layout.frameWire quotient = wire := by
  revert hwire
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun quotient => ?_)
    (fun internal => ?_) wire
  · intro hwire
    exact ⟨quotient,
      (frameWire_mem_rootHidden_iff_of_nested input layout sourceBoundary
        hnested quotient).1 hwire, rfl⟩
  · intro hwire
    have hscope := (OpenConcreteDiagram.mem_hiddenWires
      (outputOpenRoot input layout sourceBoundary)
      (layout.internalWire internal)).1 hwire |>.1
    change (layout.plugWire
      (layout.internalBlockWire internal)).scope =
        layout.frameRegion input.frame.val.root at hscope
    rw [plugWire_internalBlockWire] at hscope
    simp only [mapPatternWire] at hscope
    let original := layout.internalWires.origin internal
    have hinternal : original ∉ input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff original).1
        (layout.internalWires.origin_survives internal)
    rcases patternInternalWire_scope_material_or_bodyContainer input original
        hinternal with hmaterial | hbody
    · rw [layout.bodyRegion_material _ hmaterial] at hscope
      exact False.elim (layout.frameRegion_ne_materialRegion
        input.frame.val.root _ hscope.symm)
    · rw [hbody, layout.bodyRegion_bodyContainer] at hscope
      exact False.elim (hnested (layout.frameRegion_injective hscope))

/-- The local component of the open-root frame equivalence at a proper
nested splice site. -/
noncomputable def nestedRootHiddenWireEquiv
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hnested : input.site ≠ input.frame.val.root) :
    FiniteEquiv
      (Fin (coalescedOpenRoot input sourceBoundary).hiddenWires.length)
      (Fin (outputOpenRoot input layout sourceBoundary).hiddenWires.length) :=
  listEmbeddingEquiv layout.frameWire
    (coalescedOpenRoot input sourceBoundary).hiddenWires
    (outputOpenRoot input layout sourceBoundary).hiddenWires
    (coalescedOpenRoot input sourceBoundary).hiddenWires_nodup
    (outputOpenRoot input layout sourceBoundary).hiddenWires_nodup
    (fun quotient hquotient =>
      (frameWire_mem_rootHidden_iff_of_nested input layout sourceBoundary
        hnested quotient).2 hquotient)
    (outputRootHidden_frame_complete_of_nested input layout sourceBoundary
      hnested)
    (fun left _ right _ heq => layout.frameWire_injective heq)

theorem nestedRootHiddenWireEquiv_spec
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hnested : input.site ≠ input.frame.val.root)
    (index : Fin
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length) :
    (outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (nestedRootHiddenWireEquiv input layout sourceBoundary hnested index) =
      layout.frameWire
        ((coalescedOpenRoot input sourceBoundary).hiddenWires.get index) := by
  exact listEmbeddingEquiv_spec layout.frameWire
    (coalescedOpenRoot input sourceBoundary).hiddenWires
    (outputOpenRoot input layout sourceBoundary).hiddenWires
    (coalescedOpenRoot input sourceBoundary).hiddenWires_nodup
    (outputOpenRoot input layout sourceBoundary).hiddenWires_nodup
    (fun quotient hquotient =>
      (frameWire_mem_rootHidden_iff_of_nested input layout sourceBoundary
        hnested quotient).2 hquotient)
    (outputRootHidden_frame_complete_of_nested input layout sourceBoundary
      hnested)
    (fun left _ right _ heq => layout.frameWire_injective heq) index

/-- The complete open-root wire transport at a proper nested splice site. -/
noncomputable def nestedRootWireEquiv
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hnested : input.site ≠ input.frame.val.root) :
    FiniteEquiv
      (Fin (coalescedOpenRoot input sourceBoundary).rootWires.length)
      (Fin (outputOpenRoot input layout sourceBoundary).rootWires.length) :=
  let sourceEq :
      (coalescedOpenRoot input sourceBoundary).rootWires.length =
        (coalescedOpenRoot input sourceBoundary).exposedWires.length +
          (coalescedOpenRoot input sourceBoundary).hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let targetEq :
      (outputOpenRoot input layout sourceBoundary).rootWires.length =
        (outputOpenRoot input layout sourceBoundary).exposedWires.length +
          (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  (FiniteEquiv.finCast sourceEq).trans
    ((extendWireEquiv
      (rootExposedWireEquiv input layout sourceBoundary)
      (nestedRootHiddenWireEquiv input layout sourceBoundary hnested)).trans
      (FiniteEquiv.finCast targetEq.symm))

theorem nestedRootWireEquiv_spec
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hnested : input.site ≠ input.frame.val.root)
    (index : Fin
      (coalescedOpenRoot input sourceBoundary).rootWires.length) :
    (outputOpenRoot input layout sourceBoundary).rootWires.get
        (nestedRootWireEquiv input layout sourceBoundary hnested index) =
      layout.frameWire
        ((coalescedOpenRoot input sourceBoundary).rootWires.get index) := by
  let sourceEq :
      (coalescedOpenRoot input sourceBoundary).rootWires.length =
        (coalescedOpenRoot input sourceBoundary).exposedWires.length +
          (coalescedOpenRoot input sourceBoundary).hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let targetEq :
      (outputOpenRoot input layout sourceBoundary).rootWires.length =
        (outputOpenRoot input layout sourceBoundary).exposedWires.length +
          (outputOpenRoot input layout sourceBoundary).hiddenWires.length := by
    simp [OpenConcreteDiagram.rootWires]
  let split := Fin.cast sourceEq index
  change (outputOpenRoot input layout sourceBoundary).rootWires.get
      (Fin.cast targetEq.symm
        ((extendWireEquiv
          (rootExposedWireEquiv input layout sourceBoundary)
          (nestedRootHiddenWireEquiv input layout sourceBoundary hnested))
            split)) = _
  have hindex : index = Fin.cast sourceEq.symm split := by
    apply Fin.ext
    rfl
  rw [hindex]
  refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
  ·
    simp only [extendWireEquiv_outer]
    simpa [OpenConcreteDiagram.rootWires] using
      rootExposedWireEquiv_spec input layout sourceBoundary exposed
  ·
    simp only [extendWireEquiv_local]
    simpa [OpenConcreteDiagram.rootWires] using
      nestedRootHiddenWireEquiv_spec input layout sourceBoundary hnested hidden

/-- Hidden output-root wires in semantic splice order: hidden coalesced-frame
classes followed by the terminal pattern's internal wire carriers. -/
def semanticOpenRootHiddenWires
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    List (Fin layout.plugRaw.wireCount) :=
  (coalescedOpenRoot input sourceBoundary).hiddenWires.map layout.frameWire ++
    layout.bodyInternalCarriers.map layout.internalWire

theorem semanticOpenRootHiddenWires_subset
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root) :
    ∀ wire, wire ∈
        semanticOpenRootHiddenWires input layout sourceBoundary →
      wire ∈ (outputOpenRoot input layout sourceBoundary).hiddenWires := by
  intro wire hwire
  change wire ∈
    (coalescedOpenRoot input sourceBoundary).hiddenWires.map layout.frameWire ++
      layout.bodyInternalCarriers.map layout.internalWire at hwire
  have hparts := List.mem_append.mp hwire
  apply (OpenConcreteDiagram.mem_hiddenWires
    (outputOpenRoot input layout sourceBoundary) wire).2
  rcases hparts with hframe | hinternal
  · obtain ⟨quotient, hquotient, rfl⟩ := List.mem_map.mp hframe
    have hsource := (OpenConcreteDiagram.mem_hiddenWires
      (coalescedOpenRoot input sourceBoundary) quotient).1 hquotient
    constructor
    · change (layout.plugWire
        (layout.quotientBlockWire quotient)).scope =
          layout.frameRegion input.frame.val.root
      rw [plugWire_quotientBlockWire]
      exact congrArg layout.frameRegion hsource.1
    · intro hexposed
      exact hsource.2 ((frameWire_mem_rootExposed_iff input layout
        sourceBoundary quotient).1 hexposed)
  · obtain ⟨internal, hcarrier, heq⟩ := List.mem_map.mp hinternal
    subst wire
    have hbody : (input.pattern.val.diagram.wires
        (layout.internalWires.origin internal)).scope =
          input.binderSpine.bodyContainer :=
      decide_eq_true_iff.mp ((mem_filterFin internal).1 hcarrier)
    constructor
    · change (layout.plugWire
        (layout.internalBlockWire internal)).scope =
          layout.frameRegion input.frame.val.root
      rw [plugWire_internalBlockWire]
      simp only [mapPatternWire, hbody, layout.bodyRegion_bodyContainer, hsite]
    · intro hexposed
      have hboundary := (OpenConcreteDiagram.mem_exposedWires
        (outputOpenRoot input layout sourceBoundary)
        (layout.internalWire internal)).1 hexposed
      change layout.internalWire internal ∈
        sourceBoundary.map (layout.frameWire ∘ input.quotientWire) at hboundary
      obtain ⟨source, _, heq⟩ := List.mem_map.mp hboundary
      exact layout.frameWire_ne_internalWire (input.quotientWire source)
        internal (by simpa only [Function.comp_apply] using heq)

theorem semanticOpenRootHiddenWires_complete
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root) :
    ∀ wire, wire ∈ (outputOpenRoot input layout sourceBoundary).hiddenWires →
      wire ∈ semanticOpenRootHiddenWires input layout sourceBoundary := by
  intro wire hwire
  have hhidden := (OpenConcreteDiagram.mem_hiddenWires
    (outputOpenRoot input layout sourceBoundary) wire).1 hwire
  revert hhidden
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun quotient => ?_)
    (fun internal => ?_) wire
  · intro hhidden
    apply List.mem_append_left
    apply List.mem_map_of_mem
    apply (OpenConcreteDiagram.mem_hiddenWires
      (coalescedOpenRoot input sourceBoundary) quotient).2
    constructor
    · have hscope := hhidden.1
      change (layout.plugWire
        (layout.quotientBlockWire quotient)).scope =
          layout.frameRegion input.frame.val.root at hscope
      rw [plugWire_quotientBlockWire] at hscope
      exact layout.frameRegion_injective hscope
    · intro hexposed
      exact hhidden.2 ((frameWire_mem_rootExposed_iff input layout
        sourceBoundary quotient).2 hexposed)
  · intro hhidden
    apply List.mem_append_right
    apply List.mem_map_of_mem
    apply (mem_filterFin internal).2
    apply decide_eq_true_iff.mpr
    have hscope := hhidden.1
    change (layout.plugWire
      (layout.internalBlockWire internal)).scope =
        layout.frameRegion input.frame.val.root at hscope
    rw [plugWire_internalBlockWire] at hscope
    simp only [mapPatternWire] at hscope
    let original := layout.internalWires.origin internal
    have hinternal : original ∉ input.pattern.val.exposedWires :=
      (layout.internalWires_survives_iff original).1
        (layout.internalWires.origin_survives internal)
    rcases patternInternalWire_scope_material_or_bodyContainer input original
        hinternal with hmaterial | hbody
    · rw [layout.bodyRegion_material _ hmaterial] at hscope
      exact False.elim (layout.frameRegion_ne_materialRegion
        input.frame.val.root _ hscope.symm)
    · exact hbody

theorem semanticOpenRootHiddenWires_nodup
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    (semanticOpenRootHiddenWires input layout sourceBoundary).Nodup := by
  change ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
      layout.frameWire ++
    layout.bodyInternalCarriers.map layout.internalWire).Nodup
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact (coalescedOpenRoot input sourceBoundary).hiddenWires_nodup.map
      layout.frameWire
      (fun left right hne heq => hne (layout.frameWire_injective heq))
  · exact (filterFin_nodup _).map layout.internalWire
      (fun left right hne heq => hne (layout.internalWire_injective heq))
  · intro frame hframe internal hinternal heq
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp hframe
    obtain ⟨target, _, rfl⟩ := List.mem_map.mp hinternal
    exact layout.frameWire_ne_internalWire source target heq

noncomputable def rootHiddenWireEquiv
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root) :
    FiniteEquiv
      (Fin (semanticOpenRootHiddenWires input layout sourceBoundary).length)
      (Fin (outputOpenRoot input layout sourceBoundary).hiddenWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    (semanticOpenRootHiddenWires input layout sourceBoundary)
    (outputOpenRoot input layout sourceBoundary).hiddenWires
    (semanticOpenRootHiddenWires_nodup input layout sourceBoundary)
    (outputOpenRoot input layout sourceBoundary).hiddenWires_nodup
    (fun wire => ⟨
      semanticOpenRootHiddenWires_complete input layout sourceBoundary hsite wire,
      semanticOpenRootHiddenWires_subset input layout sourceBoundary hsite wire⟩)

theorem rootHiddenWireEquiv_spec
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (index : Fin
      (semanticOpenRootHiddenWires input layout sourceBoundary).length) :
    (outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (rootHiddenWireEquiv input layout sourceBoundary hsite index) =
      (semanticOpenRootHiddenWires input layout sourceBoundary).get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    (semanticOpenRootHiddenWires input layout sourceBoundary)
    (outputOpenRoot input layout sourceBoundary).hiddenWires _ _ _ index

@[simp] theorem semanticOpenRootHiddenWires_length
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount)) :
    (semanticOpenRootHiddenWires input layout sourceBoundary).length =
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length +
        layout.bodyInternalCarriers.length := by
  change ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
      layout.frameWire ++
    layout.bodyInternalCarriers.map layout.internalWire).length = _
  rw [List.length_append, List.length_map, List.length_map]
  rfl

/-- Open-root local-wire equivalence for a nonempty proxy spine.  Exposed
coalesced classes have been moved to the ambient block; the remaining host
classes precede the terminal pattern locals. -/
noncomputable def rootLocalWireEquivOfNonempty
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    FiniteEquiv
      (Fin ((coalescedOpenRoot input sourceBoundary).hiddenWires.length +
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length))
      (Fin (outputOpenRoot input layout sourceBoundary).hiddenWires.length) :=
  (extendWireEquiv
      (FiniteEquiv.refl (Fin
        (coalescedOpenRoot input sourceBoundary).hiddenWires.length))
      (layout.bodyInternalExactEquiv hnonempty).symm).trans
    ((FiniteEquiv.finCast
      (semanticOpenRootHiddenWires_length input layout sourceBoundary).symm).trans
        (rootHiddenWireEquiv input layout sourceBoundary hsite))

/-- Empty-spine local-wire equivalence; the pattern's hidden sheet-root wires
are the terminal internal block. -/
noncomputable def rootLocalWireEquivOfEmpty
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0) :
    FiniteEquiv
      (Fin ((coalescedOpenRoot input sourceBoundary).hiddenWires.length +
        input.pattern.val.hiddenWires.length))
      (Fin (outputOpenRoot input layout sourceBoundary).hiddenWires.length) :=
  (extendWireEquiv
      (FiniteEquiv.refl (Fin
        (coalescedOpenRoot input sourceBoundary).hiddenWires.length))
      (layout.bodyInternalHiddenEquiv hzero).symm).trans
    ((FiniteEquiv.finCast
      (semanticOpenRootHiddenWires_length input layout sourceBoundary).symm).trans
        (rootHiddenWireEquiv input layout sourceBoundary hsite))

theorem rootLocalWireEquivOfNonempty_host_spec
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length) :
    (outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (rootLocalWireEquivOfNonempty input layout sourceBoundary hsite
          hnonempty (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
              input.binderSpine.bodyContainer).length index)) =
      layout.frameWire
        ((coalescedOpenRoot input sourceBoundary).hiddenWires.get index) := by
  rw [rootLocalWireEquivOfNonempty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, rootHiddenWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticOpenRootHiddenWires, extendWireEquiv]
  have hlt : index.val <
      ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
        layout.frameWire).length := by
    rw [List.length_map]
    exact index.isLt
  exact (List.getElem_append_left hlt).trans
    (List.getElem_map layout.frameWire)

theorem rootLocalWireEquivOfEmpty_host_spec
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length) :
    (outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (rootLocalWireEquivOfEmpty input layout sourceBoundary hsite hzero
          (Fin.castAdd input.pattern.val.hiddenWires.length index)) =
      layout.frameWire
        ((coalescedOpenRoot input sourceBoundary).hiddenWires.get index) := by
  rw [rootLocalWireEquivOfEmpty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, rootHiddenWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticOpenRootHiddenWires, extendWireEquiv]
  have hlt : index.val <
      ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
        layout.frameWire).length := by
    rw [List.length_map]
    exact index.isLt
  exact (List.getElem_append_left hlt).trans
    (List.getElem_map layout.frameWire)

theorem rootLocalWireEquivOfNonempty_pattern_spec
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (index : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length) :
    (outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (rootLocalWireEquivOfNonempty input layout sourceBoundary hsite
          hnonempty (Fin.natAdd
            (coalescedOpenRoot input sourceBoundary).hiddenWires.length
            index)) =
      layout.internalWire
        (layout.bodyInternalCarriers.get
          ((layout.bodyInternalExactEquiv hnonempty).symm index)) := by
  rw [rootLocalWireEquivOfNonempty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, rootHiddenWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticOpenRootHiddenWires, extendWireEquiv]
  have hright :
      ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
          layout.frameWire).length ≤
        (coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          (layout.bodyInternalExactEquiv hnonempty).invFun index := by
    rw [List.length_map]
    exact Nat.le_add_right _ _
  refine (List.getElem_append_right hright).trans ?_
  have hindex :
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          (layout.bodyInternalExactEquiv hnonempty).invFun index -
        ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
          layout.frameWire).length =
      (layout.bodyInternalExactEquiv hnonempty).invFun index := by
    rw [List.length_map]
    exact Nat.add_sub_cancel_left _ _
  have hvalid :
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length +
            (layout.bodyInternalExactEquiv hnonempty).invFun index -
          ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
            layout.frameWire).length <
        (layout.bodyInternalCarriers.map layout.internalWire).length := by
    rw [hindex, List.length_map]
    exact ((layout.bodyInternalExactEquiv hnonempty).invFun index).isLt
  exact (getElem_congr rfl hindex hvalid).trans
    (List.getElem_map layout.internalWire)

theorem rootLocalWireEquivOfEmpty_pattern_spec
    (input : Input signature) (layout : PlugLayout input)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
    (index : Fin input.pattern.val.hiddenWires.length) :
    (outputOpenRoot input layout sourceBoundary).hiddenWires.get
        (rootLocalWireEquivOfEmpty input layout sourceBoundary hsite hzero
          (Fin.natAdd
            (coalescedOpenRoot input sourceBoundary).hiddenWires.length
            index)) =
      layout.internalWire
        (layout.bodyInternalCarriers.get
          ((layout.bodyInternalHiddenEquiv hzero).symm index)) := by
  rw [rootLocalWireEquivOfEmpty, FiniteEquiv.trans_apply,
    FiniteEquiv.trans_apply, rootHiddenWireEquiv_spec]
  simp [FiniteEquiv.finCast, semanticOpenRootHiddenWires, extendWireEquiv]
  have hright :
      ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
          layout.frameWire).length ≤
        (coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          (layout.bodyInternalHiddenEquiv hzero).invFun index := by
    rw [List.length_map]
    exact Nat.le_add_right _ _
  refine (List.getElem_append_right hright).trans ?_
  have hindex :
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length +
          (layout.bodyInternalHiddenEquiv hzero).invFun index -
        ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
          layout.frameWire).length =
      (layout.bodyInternalHiddenEquiv hzero).invFun index := by
    rw [List.length_map]
    exact Nat.add_sub_cancel_left _ _
  have hvalid :
      (coalescedOpenRoot input sourceBoundary).hiddenWires.length +
            (layout.bodyInternalHiddenEquiv hzero).invFun index -
          ((coalescedOpenRoot input sourceBoundary).hiddenWires.map
            layout.frameWire).length <
        (layout.bodyInternalCarriers.map layout.internalWire).length := by
    rw [hindex, List.length_map]
    exact ((layout.bodyInternalHiddenEquiv hzero).invFun index).isLt
  exact (getElem_congr rfl hindex hvalid).trans
    (List.getElem_map layout.internalWire)

/-- Reorder the plugged diagram's closed root context into the canonical
open-root context determined by the caller's ordered boundary. -/
noncomputable def outputExactContextToOpenRootWireEquiv
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (context : ConcreteElaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root) :
    FiniteEquiv (Fin context.length)
      (Fin (outputOpenRoot input layout sourceBoundary).rootWires.length) :=
  FiniteEquiv.restrictLists (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    context (outputOpenRoot input layout sourceBoundary).rootWires
    exact.nodup (outputOpenRoot input layout sourceBoundary).rootWires_nodup
    (fun wire => by
      simp only [FiniteEquiv.refl_apply]
      rw [exact.mem_iff]
      constructor
      · intro hmember
        have hscope :
            (layout.plugRaw.wires wire).scope = layout.plugRaw.root := by
          change ((outputOpenRoot input layout sourceBoundary).diagram.wires
              wire).scope =
            (outputOpenRoot input layout sourceBoundary).diagram.root
          exact (OpenConcreteDiagram.mem_rootWires_iff
            (outputOpenRoot input layout sourceBoundary)
            (outputOpenRoot_wellFormed input layout hadmissible sourceBoundary
              sourceRoot) wire).1 hmember
        rw [hscope]
        exact ConcreteDiagram.Encloses.refl _ _
      · intro hencloses
        apply (OpenConcreteDiagram.mem_rootWires_iff
          (outputOpenRoot input layout sourceBoundary)
          (outputOpenRoot_wellFormed input layout hadmissible sourceBoundary
            sourceRoot) wire).2
        change (layout.plugRaw.wires wire).scope = layout.plugRaw.root
        exact ConcreteElaboration.encloses_sheet_eq
          (layout.plugRaw_wellFormed signature input hadmissible).root_is_sheet
          hencloses
      )

theorem outputExactContextToOpenRootWireEquiv_spec
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (context : ConcreteElaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root) (index : Fin context.length) :
    (outputOpenRoot input layout sourceBoundary).rootWires.get
        (outputExactContextToOpenRootWireEquiv input layout hadmissible
          sourceBoundary sourceRoot context exact index) = context.get index :=
  FiniteEquiv.restrictLists_spec _ _ _ _ _ _ index

theorem compiledOutputRootItemsIsoFromExactContext
    (signature : List Nat) (input : Input signature)
    (layout : PlugLayout input) (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (context : ConcreteElaboration.WireContext layout.plugRaw)
    (exact : context.Exact layout.plugRaw.root)
    {closedItems : ItemSeq signature context.length []}
    {openItems : ItemSeq signature
      (outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ConcreteElaboration.compileOccurrencesWith? signature
      layout.plugRaw (ConcreteElaboration.compileRegion? signature
        layout.plugRaw layout.plugRaw.regionCount) context
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences layout.plugRaw layout.plugRaw.root) =
        some closedItems)
    (hopen : ConcreteElaboration.compileOccurrencesWith? signature
      layout.plugRaw (ConcreteElaboration.compileRegion? signature
        layout.plugRaw layout.plugRaw.regionCount)
      (outputOpenRoot input layout sourceBoundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences layout.plugRaw layout.plugRaw.root) =
        some openItems) :
    ItemSeqIso signature
      (outputExactContextToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot context exact) [] closedItems openItems := by
  apply ConcreteElaboration.compileRootItems?_equivariant
    (ConcreteIso.refl layout.plugRaw)
    (layout.plugRaw_wellFormed signature input hadmissible) context
    (outputOpenRoot input layout sourceBoundary).rootWires
    (outputExactContextToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot context exact)
  · exact outputExactContextToOpenRootWireEquiv_spec input layout hadmissible
      sourceBoundary sourceRoot context exact
  · exact openRootWires_exact
      (checkedOutputOpenRoot input layout hadmissible sourceBoundary sourceRoot)
  · exact hclosed
  · exact hopen

noncomputable def outputClosedToOpenRootWireEquiv
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root) :
    FiniteEquiv
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length)
      (Fin (outputOpenRoot input layout sourceBoundary).rootWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    (ConcreteElaboration.exactScopeWires layout.plugRaw layout.plugRaw.root)
    (outputOpenRoot input layout sourceBoundary).rootWires
    (ConcreteElaboration.exactScopeWires_nodup layout.plugRaw
      layout.plugRaw.root)
    (outputOpenRoot input layout sourceBoundary).rootWires_nodup
    (fun wire => by
      simp only [FiniteEquiv.refl_apply]
      rw [ConcreteElaboration.mem_exactScopeWires]
      exact OpenConcreteDiagram.mem_rootWires_iff
        (outputOpenRoot input layout sourceBoundary)
        (outputOpenRoot_wellFormed input layout hadmissible sourceBoundary
          sourceRoot) wire)

theorem outputClosedToOpenRootWireEquiv_spec
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (index : Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
      layout.plugRaw.root).length) :
    (outputOpenRoot input layout sourceBoundary).rootWires.get
        (outputClosedToOpenRootWireEquiv input layout hadmissible
          sourceBoundary sourceRoot index) =
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin layout.plugRaw.wireCount))
    (ConcreteElaboration.exactScopeWires layout.plugRaw layout.plugRaw.root)
    (outputOpenRoot input layout sourceBoundary).rootWires _ _ _ index

/-- The output compiler's closed-root item sequence and its actual open-root
item sequence differ only by the canonical root-context reordering above. -/
theorem compiledOutputRootItemsIso
    (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    {closedItems : ItemSeq signature
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length []}
    {openItems : ItemSeq signature
      (outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ConcreteElaboration.compileOccurrencesWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        layout.plugRaw.regionCount)
      (ConcreteElaboration.exactScopeWires layout.plugRaw layout.plugRaw.root)
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences layout.plugRaw
        layout.plugRaw.root) = some closedItems)
    (hopen : ConcreteElaboration.compileOccurrencesWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        layout.plugRaw.regionCount)
      (outputOpenRoot input layout sourceBoundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences layout.plugRaw
        layout.plugRaw.root) = some openItems) :
    ItemSeqIso signature
      (outputClosedToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot) [] closedItems openItems := by
  apply ConcreteElaboration.compileRootItems?_equivariant
    (ConcreteIso.refl layout.plugRaw)
    (layout.plugRaw_wellFormed signature input hadmissible)
    (ConcreteElaboration.exactScopeWires layout.plugRaw layout.plugRaw.root)
    (outputOpenRoot input layout sourceBoundary).rootWires
    (outputClosedToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot)
  · intro index
    simpa using outputClosedToOpenRootWireEquiv_spec input layout hadmissible
      sourceBoundary sourceRoot index
  · exact openRootWires_exact
      (checkedOutputOpenRoot input layout hadmissible sourceBoundary sourceRoot)
  · exact hclosed
  · exact hopen

/-- Canonical reindexing of a closed commuting source into a requested open
ambient/local split.  It is defined from the already-proved closed map and
the compiler's closed-to-open transport, so no parallel wire authority is
introduced. -/
noncomputable def closedSourceToOpenRootReindex
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin closedTargetWires))
    (outputTransport : FiniteEquiv (Fin closedTargetWires)
      (Fin (targetOuter + targetLocal)))
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal)) :
    FiniteEquiv (Fin closedSourceWires) (Fin (sourceOuter + sourceLocal)) :=
  (closedWire.trans outputTransport).trans
    (extendWireEquiv ambient localEquiv).symm

theorem closedSourceToOpenRootReindex_composes
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin closedTargetWires))
    (outputTransport : FiniteEquiv (Fin closedTargetWires)
      (Fin (targetOuter + targetLocal)))
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal)) :
    ((closedSourceToOpenRootReindex closedWire outputTransport ambient
          localEquiv).symm
        |>.trans closedWire |>.trans outputTransport) =
      extendWireEquiv ambient localEquiv := by
  apply FiniteEquiv.ext
  intro index
  change (closedWire.trans outputTransport)
      ((closedWire.trans outputTransport).symm
        (extendWireEquiv ambient localEquiv index)) =
    extendWireEquiv ambient localEquiv index
  exact (closedWire.trans outputTransport).right_inv _

/-- Repackage a closed root item simulation as an intrinsically split open
region simulation.  The source items are renamed once into the requested
open ordering; the resulting `RegionIso` is governed exactly by the supplied
ambient and local equivalences. -/
theorem openRootRegionIso_of_closedItems
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin closedTargetWires))
    (outputTransport : FiniteEquiv (Fin closedTargetWires)
      (Fin (targetOuter + targetLocal)))
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (closedSourceItems : ItemSeq signature closedSourceWires [])
    (closedTargetItems : ItemSeq signature closedTargetWires [])
    (openTargetItems : ItemSeq signature (targetOuter + targetLocal) [])
    (hclosed : ItemSeqIso signature closedWire []
      closedSourceItems closedTargetItems)
    (hopen : ItemSeqIso signature outputTransport []
      closedTargetItems openTargetItems) :
    RegionIso signature ambient []
      (Region.mk sourceLocal
        (closedSourceItems.renameWires
          (closedSourceToOpenRootReindex closedWire outputTransport
            ambient localEquiv)))
      (Region.mk targetLocal openTargetItems) := by
  let reindex := closedSourceToOpenRootReindex closedWire outputTransport
    ambient localEquiv
  have hrename := ItemSeqIso.renameWiresEquiv closedSourceItems reindex
  have hitems := hrename.symm.trans hclosed |>.trans hopen
  have hmap := closedSourceToOpenRootReindex_composes closedWire
    outputTransport ambient localEquiv
  rw [hmap] at hitems
  exact RegionIso.mk localEquiv hitems

/-- Version of `openRootRegionIso_of_closedItems` for an open compiler item
sequence whose carrier is only propositionally the ambient/local sum used by
`Region.mk`.  This is the canonical bridge between `OpenConcreteDiagram`'s
list-shaped `rootWires` context and an intrinsic region's split context. -/
theorem openRootRegionIso_of_closedItems_cast
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin closedTargetWires))
    (outputTransport : FiniteEquiv (Fin closedTargetWires)
      (Fin openTargetWires))
    (targetEq : openTargetWires = targetOuter + targetLocal)
    (ambient : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localEquiv : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (closedSourceItems : ItemSeq signature closedSourceWires [])
    (closedTargetItems : ItemSeq signature closedTargetWires [])
    (openTargetItems : ItemSeq signature openTargetWires [])
    (hclosed : ItemSeqIso signature closedWire []
      closedSourceItems closedTargetItems)
    (hopen : ItemSeqIso signature outputTransport []
      closedTargetItems openTargetItems) :
    let castTransport := outputTransport.trans
      (FiniteEquiv.finCast targetEq)
    RegionIso signature ambient []
      (Region.mk sourceLocal
        (closedSourceItems.renameWires
          (closedSourceToOpenRootReindex closedWire castTransport
            ambient localEquiv)))
      (Region.mk targetLocal (openTargetItems.castWiresEq targetEq)) := by
  dsimp only
  have hopenCast : ItemSeqIso signature
      (outputTransport.trans (FiniteEquiv.finCast targetEq)) []
      closedTargetItems (openTargetItems.castWiresEq targetEq) := by
    rw [ItemSeq.castWiresEq_eq_renameWires]
    exact hopen.trans
      (ItemSeqIso.renameWiresEquiv openTargetItems
        (FiniteEquiv.finCast targetEq))
  exact openRootRegionIso_of_closedItems closedWire
    (outputTransport.trans (FiniteEquiv.finCast targetEq)) ambient localEquiv
    closedSourceItems closedTargetItems
    (openTargetItems.castWiresEq targetEq) hclosed hopenCast

/-- Specialize the closed/open item bridge to the executable splice output.
The target is the actual elaborated body of `outputOpenRoot`; callers supply
only the already-established closed commuting item isomorphism and the
intrinsic source split they intend to expose. -/
theorem compiledOpenRootRegionIso_of_closedItems
    (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length))
    (closedSourceItems : ItemSeq signature closedSourceWires [])
    {closedOutputItems : ItemSeq signature
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length []}
    {openOutputItems : ItemSeq signature
      (outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ItemSeqIso signature closedWire []
      closedSourceItems closedOutputItems)
    (closedOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          layout.plugRaw.root)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some closedOutputItems)
    (openOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (outputOpenRoot input layout sourceBoundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some openOutputItems) :
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length :=
      by simp [OpenConcreteDiagram.rootWires]
    let outputTransport :=
      (outputClosedToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot).trans (FiniteEquiv.finCast targetEq)
    RegionIso signature
      (rootExposedWireEquiv input layout sourceBoundary) []
      (Region.mk sourceLocal
        (closedSourceItems.renameWires
          (closedSourceToOpenRootReindex closedWire outputTransport
            (rootExposedWireEquiv input layout sourceBoundary) localEquiv)))
      (checkedOutputOpenRoot input layout hadmissible sourceBoundary
        sourceRoot).elaborate.body := by
  dsimp only
  have hopen := compiledOutputRootItemsIso signature input layout hadmissible
    sourceBoundary sourceRoot closedOutputComputation openOutputComputation
  have hiso := openRootRegionIso_of_closedItems_cast closedWire
    (outputClosedToOpenRootWireEquiv input layout hadmissible
      sourceBoundary sourceRoot)
    (by simp [OpenConcreteDiagram.rootWires])
    (rootExposedWireEquiv input layout sourceBoundary) localEquiv
    closedSourceItems closedOutputItems openOutputItems hclosed hopen
  have hbody :
      (checkedOutputOpenRoot input layout hadmissible sourceBoundary
          sourceRoot).elaborate.body =
        ConcreteElaboration.finishRoot
          (outputOpenRoot input layout sourceBoundary).exposedWires
          (outputOpenRoot input layout sourceBoundary).hiddenWires
          openOutputItems := by
    have hitemsExpanded :
        ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
          (ConcreteElaboration.compileRegion? signature layout.plugRaw
            layout.plugRaw.regionCount)
          ((outputOpenRoot input layout sourceBoundary).exposedWires ++
            (outputOpenRoot input layout sourceBoundary).hiddenWires)
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences layout.plugRaw
            layout.plugRaw.root) = some openOutputItems := by
      simpa only [OpenConcreteDiagram.rootWires] using openOutputComputation
    have hitemsOutput :
        ConcreteElaboration.compileOccurrencesWith? signature
          (outputOpenRoot input layout sourceBoundary).diagram
          (ConcreteElaboration.compileRegion? signature
            (outputOpenRoot input layout sourceBoundary).diagram
            (outputOpenRoot input layout sourceBoundary).diagram.regionCount)
          ((outputOpenRoot input layout sourceBoundary).exposedWires ++
            (outputOpenRoot input layout sourceBoundary).hiddenWires)
          ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences
            (outputOpenRoot input layout sourceBoundary).diagram
            (outputOpenRoot input layout sourceBoundary).diagram.root) =
          some openOutputItems := by
      simpa only [outputOpenRoot] using hitemsExpanded
    have hroot :
        ConcreteElaboration.compileRoot? signature
          (outputOpenRoot input layout sourceBoundary).diagram
          (outputOpenRoot input layout sourceBoundary).exposedWires
          (outputOpenRoot input layout sourceBoundary).hiddenWires =
        some (ConcreteElaboration.finishRoot
          (outputOpenRoot input layout sourceBoundary).exposedWires
          (outputOpenRoot input layout sourceBoundary).hiddenWires
          openOutputItems) := by
      simp [ConcreteElaboration.compileRoot?, hitemsOutput] <;> rfl
    unfold checkedOutputOpenRoot
    unfold CheckedOpenDiagram.elaborate
    dsimp only
    exact Option.get_of_eq_some _ hroot
  rw [hbody]
  simpa only [ConcreteElaboration.finishRoot] using hiso

/-- Ordered-interface form of `compiledOpenRootRegionIso_of_closedItems`.
This packages the commuting body result with its canonical external-class
map, so clients receive the complete open-diagram semantics and never have to
reconstruct boundary compatibility from list indices. -/
noncomputable def compiledOpenRootIso_of_closedItems
    (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (sourceLocal : Nat)
    (localEquiv : FiniteEquiv (Fin sourceLocal)
      (Fin (outputOpenRoot input layout sourceBoundary).hiddenWires.length))
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length))
    (closedSourceItems : ItemSeq signature closedSourceWires [])
    {closedOutputItems : ItemSeq signature
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length []}
    {openOutputItems : ItemSeq signature
      (outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ItemSeqIso signature closedWire []
      closedSourceItems closedOutputItems)
    (closedOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          layout.plugRaw.root)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some closedOutputItems)
    (openOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (outputOpenRoot input layout sourceBoundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some openOutputItems) :
    let targetEq :
        (outputOpenRoot input layout sourceBoundary).rootWires.length =
          (outputOpenRoot input layout sourceBoundary).exposedWires.length +
            (outputOpenRoot input layout sourceBoundary).hiddenWires.length :=
      by simp [OpenConcreteDiagram.rootWires]
    let outputTransport :=
      (outputClosedToOpenRootWireEquiv input layout hadmissible
        sourceBoundary sourceRoot).trans (FiniteEquiv.finCast targetEq)
    let sourceBody := Region.mk sourceLocal
      (closedSourceItems.renameWires
        (closedSourceToOpenRootReindex closedWire outputTransport
          (rootExposedWireEquiv input layout sourceBoundary) localEquiv))
    let arityEq :
        (checkedCoalescedOpenRoot input hadmissible sourceBoundary
            sourceRoot).val.boundary.length =
          (checkedOutputOpenRoot input layout hadmissible sourceBoundary
            sourceRoot).val.boundary.length := by
      simp [checkedCoalescedOpenRoot, checkedOutputOpenRoot,
        coalescedOpenRoot, outputOpenRoot]
    OpenDiagramIso
      (replaceOpenBody
        (checkedCoalescedOpenRoot input hadmissible sourceBoundary
          sourceRoot).elaborate sourceBody)
      ((checkedOutputOpenRoot input layout hadmissible sourceBoundary
        sourceRoot).elaborate.castArity arityEq.symm) := by
  dsimp only
  apply OpenDiagramIso.ofArityEq
    (by simp [checkedCoalescedOpenRoot, checkedOutputOpenRoot,
      coalescedOpenRoot, outputOpenRoot])
    (rootExposedWireEquiv input layout sourceBoundary)
  · intro position
    simpa only [replaceOpenBody, CheckedOpenDiagram.elaborate_boundary] using
      rootExposedWireEquiv_boundaryClass input layout sourceBoundary
        (Fin.cast (by
          simp [checkedCoalescedOpenRoot, coalescedOpenRoot]) position)
  · exact compiledOpenRootRegionIso_of_closedItems signature input layout
      hadmissible sourceBoundary sourceRoot sourceLocal localEquiv closedWire
      closedSourceItems hclosed closedOutputComputation openOutputComputation

/-- Nonempty-spine root specialization.  The source-local carrier is the
hidden coalesced host block followed by the terminal pattern's exact block;
the canonical local map is fixed by the splice layout. -/
noncomputable def compiledOpenRootIsoOfNonempty
    (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length))
    (closedSourceItems : ItemSeq signature closedSourceWires [])
    {closedOutputItems : ItemSeq signature
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length []}
    {openOutputItems : ItemSeq signature
      (outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ItemSeqIso signature closedWire []
      closedSourceItems closedOutputItems)
    (closedOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          layout.plugRaw.root)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some closedOutputItems)
    (openOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (outputOpenRoot input layout sourceBoundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some openOutputItems) :=
  compiledOpenRootIso_of_closedItems signature input layout hadmissible
    sourceBoundary sourceRoot
    ((coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
        input.binderSpine.bodyContainer).length)
    (rootLocalWireEquivOfNonempty input layout sourceBoundary hsite hnonempty)
    closedWire closedSourceItems hclosed closedOutputComputation
    openOutputComputation

/-- Empty-spine root specialization.  The terminal pattern's hidden sheet
wires form the second source-local block. -/
noncomputable def compiledOpenRootIsoOfEmpty
    (signature : List Nat)
    (input : Input signature) (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hsite : input.site = input.frame.val.root)
    (hzero : input.binderSpine.proxyCount = 0)
    {closedSourceWires : Nat}
    (closedWire : FiniteEquiv (Fin closedSourceWires)
      (Fin (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length))
    (closedSourceItems : ItemSeq signature closedSourceWires [])
    {closedOutputItems : ItemSeq signature
      (ConcreteElaboration.exactScopeWires layout.plugRaw
        layout.plugRaw.root).length []}
    {openOutputItems : ItemSeq signature
      (outputOpenRoot input layout sourceBoundary).rootWires.length []}
    (hclosed : ItemSeqIso signature closedWire []
      closedSourceItems closedOutputItems)
    (closedOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          layout.plugRaw.root)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some closedOutputItems)
    (openOutputComputation :
      ConcreteElaboration.compileOccurrencesWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          layout.plugRaw.regionCount)
        (outputOpenRoot input layout sourceBoundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences layout.plugRaw
          layout.plugRaw.root) = some openOutputItems) :=
  compiledOpenRootIso_of_closedItems signature input layout hadmissible
    sourceBoundary sourceRoot
    ((coalescedOpenRoot input sourceBoundary).hiddenWires.length +
      input.pattern.val.hiddenWires.length)
    (rootLocalWireEquivOfEmpty input layout sourceBoundary hsite hzero)
    closedWire closedSourceItems hclosed closedOutputComputation
    openOutputComputation

/-- A coalesced-host endpoint has exactly one representation in the plugged
diagram.  Pattern material cannot become an alternative owner because the
node injections occupy disjoint finite blocks. -/
theorem plugRaw_frameEndpoint_forward
    (layout : PlugLayout input)
    (wire : Fin input.coalesceFrameRaw.wireCount)
    (endpoint : CEndpoint input.coalesceFrameRaw.nodeCount)
    (hoccurs : input.coalesceFrameRaw.EndpointOccurs wire endpoint) :
    layout.plugRaw.EndpointOccurs (layout.frameWire wire)
      (layout.mapFrameEndpoint endpoint) := by
  change endpoint ∈ input.coalescedEndpoints wire at hoccurs
  unfold ConcreteDiagram.EndpointOccurs
  simp only [plugRaw]
  rw [show layout.frameWire wire = layout.quotientBlockWire wire by rfl,
    plugWire_quotientBlockWire]
  exact List.mem_append_left _ (List.mem_map_of_mem hoccurs)

theorem plugRaw_frameEndpoint_backward
    (layout : PlugLayout input)
    (targetWire : Fin layout.plugRaw.wireCount)
    (endpoint : CEndpoint input.coalesceFrameRaw.nodeCount)
    (hoccurs : layout.plugRaw.EndpointOccurs targetWire
      (layout.mapFrameEndpoint endpoint)) :
    ∃ sourceWire : Fin input.coalesceFrameRaw.wireCount,
      layout.frameWire sourceWire = targetWire ∧
        input.coalesceFrameRaw.EndpointOccurs sourceWire endpoint := by
  revert hoccurs
  refine Fin.addCases (m := input.wireQuotient.count)
    (n := layout.internalWires.count) (fun quotient => ?_)
    (fun internal => ?_) targetWire
  · intro hquotient
    rcases quotient_endpoint_provenance _ input layout quotient
        (layout.mapFrameEndpoint endpoint) hquotient with
      ⟨original, horiginal, heq⟩ |
        ⟨external, _, original, _, heq⟩
    · have horiginalEq : original = endpoint :=
        layout.mapFrameEndpoint_injective heq
      subst original
      exact ⟨quotient, rfl, horiginal⟩
    · exact False.elim
        (layout.mapFrameEndpoint_ne_mapPatternEndpoint endpoint original
          heq.symm)
  · intro hinternal
    obtain ⟨original, _, heq⟩ :=
      internal_endpoint_provenance _ input layout internal
        (layout.mapFrameEndpoint endpoint) hinternal
    exact False.elim
      (layout.mapFrameEndpoint_ne_mapPatternEndpoint endpoint original
        heq.symm)

/-- Choice-independent node-kernel transport for any retained host region.
The contracts are exactly the concrete wire and binder lookups carried by the
recursive compiler. -/
theorem compileFrameNode_at_region_of_maps
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact (layout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders region)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      layout.frameWire (sourceContext.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (node : Fin input.coalesceFrameRaw.nodeCount)
    (hnodeAtRegion : (input.coalesceFrameRaw.nodes node).region = region) :
    ConcreteElaboration.compileNode? signature layout.plugRaw targetContext
        targetBinders (layout.frameNode node) =
      (ConcreteElaboration.compileNode? signature input.coalesceFrameRaw
        sourceContext sourceBinders node).map
          (fun item : Item signature sourceContext.length sourceRels =>
            (item.renameWires wireMap).renameRelations relationMap) := by
  apply ConcreteElaboration.compileNode?_map
    (regionMap := layout.frameRegion)
    (binderMap := layout.frameRegion)
    (wireMap := wireMap)
    (relationMap := relationMap)
  · change layout.plugNode (layout.frameNode node) = _
    rw [layout.plugNode_frameNode]
    cases hsource : input.coalesceFrameRaw.nodes node with
    | term region freePorts term =>
        change input.frame.val.nodes node = .term region freePorts term
          at hsource
        rw [hsource]
        rfl
    | atom region binder =>
        change input.frame.val.nodes node = .atom region binder at hsource
        rw [hsource]
        rfl
    | named region definition arity =>
        change input.frame.val.nodes node = .named region definition arity
          at hsource
        rw [hsource]
        rfl
  · intro port
    apply ConcreteElaboration.resolvePort?_map_of_occurrence
      (concreteWireMap := layout.frameWire)
      (targetNodup := targetExact.nodup)
      (hget := wireSpec)
      (hmem := layout.frameWire_mem_context_iff region sourceContext
        targetContext sourceExact targetExact)
      (targetDisjoint :=
        (layout.plugRaw_wellFormed signature input hadmissible)
          |>.wire_endpoints_are_disjoint)
    · intro wire requested hoccurs
      simpa [mapFrameEndpoint] using
        layout.plugRaw_frameEndpoint_forward wire
          ⟨node, requested⟩ hoccurs
    · intro targetWire requested hoccurs
      obtain ⟨sourceWire, hwire, hsource⟩ :=
        layout.plugRaw_frameEndpoint_backward targetWire
          ⟨node, requested⟩ (by
            simpa [mapFrameEndpoint] using hoccurs)
      exact ⟨sourceWire, hwire, hsource⟩
  · intro nodeRegion binder hnode
    have hactualRegion : nodeRegion = region :=
      (congrArg CNode.region hnode).symm.trans hnodeAtRegion
    obtain ⟨parent, arity, hbubble⟩ :=
      ConcreteElaboration.BinderContext.checked_atom_binder_is_bubble
        (input.coalesceFrameRaw_wellFormed hadmissible) hnode
    have hencloses : input.coalesceFrameRaw.Encloses binder region := by
      have hraw := (input.coalesceFrameRaw_wellFormed hadmissible)
        |>.atom_binders_enclose node
      simp only [hnode] at hraw
      rw [hactualRegion] at hraw
      exact hraw
    obtain ⟨relation, hrelation⟩ :=
      sourceCover binder parent arity hbubble hencloses
    rw [hrelation]
    simp only [Option.map_some]
    have howner := sourceEnumeration.lookup_owner relation hrelation
    rw [← howner]
    exact relationSpec relation

theorem compileFrameNode_at_region_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (sourceExact : (sourceOuter.extend region).Exact region)
    (targetExact :
      (targetOuter.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (sourceEnumeration :
      ConcreteElaboration.BinderContext.Enumeration
        input.coalesceFrameRaw sourceBinders region)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      layout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (node : Fin input.coalesceFrameRaw.nodeCount)
    (hnodeAtRegion : (input.coalesceFrameRaw.nodes node).region = region)
    (sourceItem : Item signature (sourceOuter.extend region).length sourceRels)
    (targetItem : Item signature
      (targetOuter.extend (layout.frameRegion region)).length targetRels)
    (hsource : ConcreteElaboration.compileNode? signature
      input.coalesceFrameRaw (sourceOuter.extend region) sourceBinders node =
        some sourceItem)
    (htarget : ConcreteElaboration.compileNode? signature layout.plugRaw
      (targetOuter.extend (layout.frameRegion region)) targetBinders
        (layout.frameNode node) = some targetItem) :
    ItemIso signature
      (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
        (layout.frameLocalWireEquiv region hne)) targetRels
      ((sourceItem.renameWires
        (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
          outerMap)).renameRelations relationMap)
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion region))) := by
  let extendedMap := layout.frameExtendedWireMap region hne
    sourceOuter targetOuter outerMap
  have hextendedSpec := layout.frameExtendedWireMap_spec region hne
    sourceOuter targetOuter outerMap outerSpec
  have htransport := layout.compileFrameNode_at_region_of_maps signature input
    hadmissible region (sourceOuter.extend region)
    (targetOuter.extend (layout.frameRegion region)) sourceExact targetExact
    sourceBinders targetBinders sourceCover sourceEnumeration extendedMap
    hextendedSpec relationMap relationSpec node hnodeAtRegion
  rw [hsource, htarget] at htransport
  simp only [Option.map_some, Option.some.injEq] at htransport
  subst targetItem
  have hiso := ItemIso.renameWiresEquiv
    ((sourceItem.renameWires
      (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
        outerMap)).renameRelations relationMap)
    (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
      (layout.frameLocalWireEquiv region hne))
  have hfactor :
      (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
          (layout.frameLocalWireEquiv region hne)).toFun ∘
          layout.frameSourceExtendedWireMap region sourceOuter targetOuter
            outerMap =
        Fin.cast
            (ConcreteElaboration.WireContext.length_extend targetOuter
              (layout.frameRegion region)) ∘
          extendedMap := by
    funext index
    have h := congrFun
      (layout.frameExtendedWireMap_factor region hne sourceOuter targetOuter
        outerMap) index
    apply Fin.ext
    simpa using congrArg (fun mapped => mapped.val) h
  simpa only [Item.castWiresEq_eq_renameWires,
    Item.renameWires_renameRelations, Item.renameWires_comp,
    hfactor] using hiso

theorem frameRecursiveRegionIso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (hne : region ≠ input.site)
    (sourceOuter : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext layout.plugRaw)
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceBody : Region signature (sourceOuter.extend region).length sourceRels)
    (targetBody : Region signature
      (targetOuter.extend (layout.frameRegion region)).length targetRels)
    (hrecursive : RegionIso signature
      (FiniteEquiv.refl
        (Fin (targetOuter.extend (layout.frameRegion region)).length)) targetRels
      ((sourceBody.renameWires
        (layout.frameExtendedWireMap region hne sourceOuter targetOuter
          outerMap)).renameRelations relationMap)
      targetBody) :
    RegionIso signature
      (extendWireEquiv (FiniteEquiv.refl (Fin targetOuter.length))
        (layout.frameLocalWireEquiv region hne)) targetRels
      ((sourceBody.renameWires
        (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
          outerMap)).renameRelations relationMap)
      (targetBody.castWiresEq
        (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion region))) := by
  let extended := extendWireEquiv
    (FiniteEquiv.refl (Fin targetOuter.length))
    (layout.frameLocalWireEquiv region hne)
  let targetEq := ConcreteElaboration.WireContext.length_extend targetOuter
    (layout.frameRegion region)
  let toTargetContext := extended.trans (FiniteEquiv.finCast targetEq.symm)
  let sourcePrepared :=
    (sourceBody.renameWires
      (layout.frameSourceExtendedWireMap region sourceOuter targetOuter
        outerMap)).renameRelations relationMap
  have hmap : toTargetContext.toFun ∘
        layout.frameSourceExtendedWireMap region sourceOuter targetOuter
          outerMap =
      layout.frameExtendedWireMap region hne sourceOuter targetOuter
        outerMap := by
    simpa only [toTargetContext, extended, FiniteEquiv.trans_apply,
      FiniteEquiv.finCast] using
      layout.frameExtendedWireMap_factor region hne sourceOuter targetOuter
        outerMap
  have hfirstRaw := RegionIso.renameWiresEquiv sourcePrepared toTargetContext
  have hfirst : RegionIso signature toTargetContext targetRels sourcePrepared
      ((sourceBody.renameWires
        (layout.frameExtendedWireMap region hne sourceOuter targetOuter
          outerMap)).renameRelations relationMap) := by
    simpa only [sourcePrepared, toTargetContext,
      Region.renameWires_renameRelations,
      Region.renameWires_comp, hmap] using hfirstRaw
  have hlastRaw := RegionIso.renameWiresEquiv targetBody
    (FiniteEquiv.finCast targetEq)
  have hlast : RegionIso signature (FiniteEquiv.finCast targetEq) targetRels
      targetBody (targetBody.castWiresEq targetEq) := by
    simpa only [Region.castWiresEq_eq_renameWires,
      FiniteEquiv.finCast] using hlastRaw
  have hcombined := (hfirst.trans hrecursive).trans hlast
  have hextended :
      (toTargetContext.trans
        (FiniteEquiv.refl
          (Fin (targetOuter.extend (layout.frameRegion region)).length))).trans
          (FiniteEquiv.finCast targetEq) = extended := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  rw [hextended] at hcombined
  exact hcombined

end PlugLayout

end VisualProof.Diagram.Splice.Input
