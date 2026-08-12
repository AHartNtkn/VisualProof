import VisualProof.Concrete.Elaboration.SpliceLayout

/-! Exact lexical wire blocks for a source-derived splice. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Elaboration

namespace Splice.Input.PlugLayout

private theorem eraseDups_map_of_injective [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (map : α → β) (injective : Function.Injective map)
    (values : List α) :
    (values.map map).eraseDups = values.eraseDups.map map := by
  cases values with
  | nil => rfl
  | cons head tail =>
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      have filterEq :
          (tail.map map).filter (fun value => !value == map head) =
            (tail.filter (fun value => !value == head)).map map := by
        rw [List.filter_map]
        apply congrArg (List.map map)
        apply List.filter_congr
        intro value _
        by_cases equality : value = head
        · subst value
          simp
        · have mappedNe : map value ≠ map head := fun mappedEq =>
            equality (injective mappedEq)
          change (!(map value == map head)) = !(value == head)
          rw [beq_false_of_ne mappedNe, beq_false_of_ne equality]
      rw [filterEq, eraseDups_map_of_injective map injective]
termination_by values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem filter_map_of_predicate_map
    (map : α → β) (sourcePredicate : α → Bool)
    (targetPredicate : β → Bool)
    (commutes : ∀ value, targetPredicate (map value) = sourcePredicate value)
    (values : List α) :
    (values.map map).filter targetPredicate =
      (values.filter sourcePredicate).map map := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      cases predicateEq : sourcePredicate head <;>
        simp [predicateEq, commutes head, ih]

private theorem filter_append_exact (predicate : α → Bool)
    (first second : List α) :
    (first ++ second).filter predicate =
      first.filter predicate ++ second.filter predicate := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      cases predicateEq : predicate head <;>
        simp [predicateEq, ih]

private theorem append_assoc_exact (first second third : List α) :
    first ++ (second ++ third) = (first ++ second) ++ third := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, ih]

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

/-- The source frame equipped with an arbitrary ordered open boundary. -/
def frameOpen (input : Input)
    (boundary : List (Fin input.frame.val.wireCount)) : OpenDiagram where
  diagram := input.frame.val
  boundary := boundary

/-- No-coalescence preserves the stable exposed-class enumeration of an
arbitrary frame boundary. -/
theorem outputOpenRoot_exposedWires
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount)) :
    (layout.outputOpenRoot input boundary).exposedWires =
      (frameOpen input boundary).exposedWires.map
        (layout.frameWireMap) := by
  unfold OpenDiagram.exposedWires PlugLayout.outputOpenRoot frameOpen
  exact eraseDups_map_of_injective
    (layout.frameWireMap)
    (layout.frameWireMap_injective consistent) boundary

/-- The internal carrier and retained frame carrier occupy disjoint halves of
the raw plug wire space. -/
theorem internalWire_ne_frameWireMap
    (layout : PlugLayout input)
    (internal : layout.internalWires.Carrier)
    (frame : Fin input.frame.val.wireCount) :
    layout.internalWire internal ≠
      layout.frameWireMap frame := by
  intro equality
  have values := congrArg Fin.val equality
  change input.wireQuotient.count + internal.val =
    (input.quotientWire frame).val at values
  have quotientLt := (input.quotientWire frame).isLt
  omega

/-- Frame wires local to one source region, embedded in stable source order. -/
noncomputable def frameLocalWires (layout : PlugLayout input)
    (region : Fin input.frame.val.regionCount) :
    WireContext layout.plugRaw :=
  (exactScopeWires input.frame.val region).map
    (layout.frameWireMap)

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
    exact input.binderSpine.bodyContainer_not_material

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
        layout.frameLocalWires region := by
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
  unfold frameLocalWires frameWireMap exactScopeWires
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
      layout.frameLocalWires region ++
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
        layout.frameLocalWires region by
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

/-- The target root's hidden block consists of the source frame hidden block,
followed by the terminal body's internal block exactly when insertion is at
the frame root. -/
theorem outputOpenRoot_hiddenWires
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount)) :
    (layout.outputOpenRoot input boundary).hiddenWires =
      ((frameOpen input boundary).hiddenWires.map
          (layout.frameWireMap) :
            WireContext layout.plugRaw) ++
        (if input.frame.val.root = input.site then
          layout.bodyLocalWires
        else []) := by
  change (exactScopeWires layout.plugRaw
      (layout.frameRegion input.frame.val.root)).filter
        (fun wire => decide
          (wire ∉ (layout.outputOpenRoot input boundary).exposedWires)) = _
  rw [layout.exactScopeWires_frameRegion consistent terminal
      input.frame.val.root,
    layout.outputOpenRoot_exposedWires consistent boundary]
  have frameBlock :
      (layout.frameLocalWires input.frame.val.root).filter
          (fun targetWire => decide
            (targetWire ∉
              (frameOpen input boundary).exposedWires.map
                (layout.frameWireMap))) =
        (frameOpen input boundary).hiddenWires.map
          (layout.frameWireMap) := by
    change
      ((exactScopeWires input.frame.val input.frame.val.root).map
          (layout.frameWireMap)).filter
        (fun targetWire => decide
          (targetWire ∉
            (frameOpen input boundary).exposedWires.map
              (layout.frameWireMap))) =
      ((exactScopeWires input.frame.val input.frame.val.root).filter
          (fun wire => decide
            (wire ∉ (frameOpen input boundary).exposedWires))).map
        (layout.frameWireMap)
    apply filter_map_of_predicate_map
    intro wire
    have membership :
        layout.frameWireMap wire ∈
            (frameOpen input boundary).exposedWires.map
              (layout.frameWireMap) ↔
          wire ∈ (frameOpen input boundary).exposedWires := by
      constructor
      · intro member
        obtain ⟨sourceWire, sourceMember, equality⟩ := List.mem_map.mp member
        have sourceEq : sourceWire = wire :=
          layout.frameWireMap_injective consistent equality
        simpa [sourceEq] using sourceMember
      · intro member
        exact List.mem_map.mpr ⟨wire, member, rfl⟩
    by_cases sourceMember :
        wire ∈ (frameOpen input boundary).exposedWires
    · have targetMember := membership.mpr sourceMember
      have targetFalse : decide
          (layout.frameWireMap wire ∉
            (frameOpen input boundary).exposedWires.map
              (layout.frameWireMap)) = false :=
        decide_eq_false_iff_not.mpr (fun absent => absent targetMember)
      have sourceFalse : decide
          (wire ∉ (frameOpen input boundary).exposedWires) = false :=
        decide_eq_false_iff_not.mpr (fun absent => absent sourceMember)
      exact targetFalse.trans sourceFalse.symm
    · have targetMember :
          layout.frameWireMap wire ∉
              (frameOpen input boundary).exposedWires.map
                (layout.frameWireMap) := by
        intro member
        exact sourceMember (membership.mp member)
      have targetTrue : decide
          (layout.frameWireMap wire ∉
            (frameOpen input boundary).exposedWires.map
              (layout.frameWireMap)) = true :=
        decide_eq_true targetMember
      have sourceTrue : decide
          (wire ∉ (frameOpen input boundary).exposedWires) = true :=
        decide_eq_true sourceMember
      exact targetTrue.trans sourceTrue.symm
  have bodyBlock :
      layout.bodyLocalWires.filter (fun targetWire => decide
        (targetWire ∉
          (frameOpen input boundary).exposedWires.map
            (layout.frameWireMap))) =
        layout.bodyLocalWires := by
    apply List.filter_eq_self.mpr
    intro targetWire member
    obtain ⟨internal, _, equality⟩ := List.mem_map.mp member
    subst targetWire
    apply decide_eq_true
    intro exposed
    obtain ⟨frame, _, mapped⟩ := List.mem_map.mp exposed
    exact layout.internalWire_ne_frameWireMap internal frame
      mapped.symm
  by_cases atRoot : input.frame.val.root = input.site
  · rw [if_pos atRoot]
    calc
      _ =
          (layout.frameLocalWires
              input.frame.val.root).filter (fun targetWire => decide
                (targetWire ∉
                  (frameOpen input boundary).exposedWires.map
                    (layout.frameWireMap))) ++
            layout.bodyLocalWires.filter (fun targetWire => decide
              (targetWire ∉
                (frameOpen input boundary).exposedWires.map
                  (layout.frameWireMap))) :=
        filter_append_exact _ _ _
      _ = (frameOpen input boundary).hiddenWires.map
              (layout.frameWireMap) ++
            layout.bodyLocalWires.filter (fun targetWire => decide
              (targetWire ∉
                (frameOpen input boundary).exposedWires.map
                  (layout.frameWireMap))) :=
        congrArg (fun first => first ++
          layout.bodyLocalWires.filter (fun targetWire => decide
            (targetWire ∉
              (frameOpen input boundary).exposedWires.map
                (layout.frameWireMap)))) frameBlock
      _ = _ := congrArg (fun second =>
        (frameOpen input boundary).hiddenWires.map
            (layout.frameWireMap) ++ second) bodyBlock
  · rw [if_neg atRoot, List.append_nil]
    simpa only [List.append_nil] using frameBlock

/-- The complete target root compiler context is the stable source root
context, followed only at a root insertion by the terminal body's internal
local block. -/
theorem outputOpenRoot_rootWires
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (boundary : List (Fin input.frame.val.wireCount)) :
    (layout.outputOpenRoot input boundary).rootWires =
      ((frameOpen input boundary).rootWires.map
          (layout.frameWireMap) :
            WireContext layout.plugRaw) ++
        (if input.frame.val.root = input.site then
          layout.bodyLocalWires
        else []) := by
  change
    (layout.outputOpenRoot input boundary).exposedWires ++
        (layout.outputOpenRoot input boundary).hiddenWires =
      (((frameOpen input boundary).exposedWires ++
          (frameOpen input boundary).hiddenWires).map
            (layout.frameWireMap) :
              WireContext layout.plugRaw) ++
        (if input.frame.val.root = input.site then
          layout.bodyLocalWires
        else [])
  rw [layout.outputOpenRoot_exposedWires consistent boundary,
    layout.outputOpenRoot_hiddenWires consistent terminal boundary]
  calc
    _ = (((frameOpen input boundary).exposedWires.map
            (layout.frameWireMap) :
              WireContext layout.plugRaw) ++
          ((frameOpen input boundary).hiddenWires.map
            (layout.frameWireMap) :
              WireContext layout.plugRaw)) ++
        (if input.frame.val.root = input.site then
          layout.bodyLocalWires
        else []) := append_assoc_exact _ _ _
    _ = _ := congrArg (fun rootContext => rootContext ++
      if input.frame.val.root = input.site then
        layout.bodyLocalWires
      else []) List.map_append.symm

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

/-- Dense target identifiers preserve the terminal body's source-local wire
order. -/
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
  have survives : ∀ wire, predicate wire = true →
      layout.internalWires.survives wire = true := by
    intro wire accepted
    rw [layout.internalWires_exact]
    apply decide_eq_true
    intro exposed
    have rootScope := input.pattern.property.exposed_root_scoped exposed
    have materialScope := of_decide_eq_true accepted
    exact (layout.materialRegion_origin_isMaterial material).1
      (materialScope.symm.trans rootScope)
  have filtered := filterFin_eq_enumeration_filter
    layout.internalWires predicate survives
  have origins := map_origin_filterFin layout.internalWires predicate
  exact origins.trans filtered.symm

theorem materialLocalWires_length (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length =
        (layout.materialLocalWires material).length := by
  rw [← layout.materialLocalOrigins material]
  unfold materialLocalWires
  simp

def materialLocalIndex (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    Fin (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length →
      Fin (layout.materialLocalWires material).length :=
  Fin.cast (layout.materialLocalWires_length material)

theorem materialLocalIndex_get (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (index : Fin (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length) :
    (layout.materialLocalWires material).get
        (layout.materialLocalIndex material index) =
      layout.patternWireMap
        ((exactScopeWires input.pattern.val.diagram
          (layout.materialRegions.origin material)).get index) := by
  let positions := filterFin fun wire : layout.internalWires.Carrier =>
    decide ((input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        layout.materialRegions.origin material)
  have sourceEq : positions.map layout.internalWires.origin =
      exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin material) :=
    layout.materialLocalOrigins material
  have targetEq : positions.map layout.internalWire =
      layout.materialLocalWires material := rfl
  let position : Fin positions.length :=
    ⟨index.val, by
      rw [← List.length_map layout.internalWires.origin, sourceEq]
      exact index.isLt⟩
  let internal := positions.get position
  have sourceGet :
      (exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin material)).get index =
          layout.internalWires.origin internal := by
    have value := List.get_of_eq sourceEq.symm index
    have mapped := List.getElem_map layout.internalWires.origin
      (l := positions) (i := index.val) (h := by
        exact Eq.mp (congrArg (fun length => index.val < length)
          (List.length_map layout.internalWires.origin).symm)
            position.isLt)
    exact value.trans (by
      simpa only [List.get_eq_getElem, position, internal] using mapped)
  have targetGet :
      (layout.materialLocalWires material).get
          (layout.materialLocalIndex material index) =
        layout.internalWire internal := by
    have value := List.get_of_eq targetEq.symm
      (layout.materialLocalIndex material index)
    have mapped := List.getElem_map layout.internalWire
      (l := positions)
      (i := (layout.materialLocalIndex material index).val)
      (h := by
        change index.val < (positions.map layout.internalWire).length
        exact Eq.mp (congrArg (fun length => index.val < length)
          (List.length_map layout.internalWire).symm) position.isLt)
    exact value.trans (by
      simpa only [List.get_eq_getElem, materialLocalIndex, Fin.cast,
        position, internal] using mapped)
  rw [sourceGet, layout.patternWireMap_internal]
  exact targetGet

theorem materialExactScope_length (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length =
      (exactScopeWires layout.plugRaw
        (layout.materialRegion material)).length := by
  rw [layout.exactScopeWires_materialRegion]
  exact layout.materialLocalWires_length material

def materialExactScopeIndex (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier) :
    Fin (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length →
      Fin (exactScopeWires layout.plugRaw
        (layout.materialRegion material)).length :=
  Fin.cast (layout.materialExactScope_length material)

theorem materialExactScopeIndex_get (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (index : Fin (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin material)).length) :
    (exactScopeWires layout.plugRaw
      (layout.materialRegion material)).get
        (layout.materialExactScopeIndex material index) =
      layout.patternWireMap
        ((exactScopeWires input.pattern.val.diagram
          (layout.materialRegions.origin material)).get index) := by
  have targetEq := layout.exactScopeWires_materialRegion material
  have value := List.get_of_eq targetEq
    (layout.materialExactScopeIndex material index)
  exact value.trans (by
    simpa only [materialExactScopeIndex, materialExactScope_length,
      materialLocalIndex, Fin.cast] using
        layout.materialLocalIndex_get material index)

theorem materialSourceExactScope_length (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (material : input.binderSpine.IsMaterialRegion region) :
    (exactScopeWires input.pattern.val.diagram region).length =
      (exactScopeWires layout.plugRaw
        (layout.bodyRegion region)).length := by
  let carrier := layout.materialCarrier region material
  have origin : layout.materialRegions.origin carrier = region :=
    layout.materialCarrier_origin region material
  calc
    (exactScopeWires input.pattern.val.diagram region).length =
        (exactScopeWires input.pattern.val.diagram
          (layout.materialRegions.origin carrier)).length := by rw [origin]
    _ = (exactScopeWires layout.plugRaw
          (layout.materialRegion carrier)).length :=
      layout.materialExactScope_length carrier
    _ = (exactScopeWires layout.plugRaw
          (layout.bodyRegion region)).length := by
      rw [layout.materialRegion_materialCarrier region material]

def materialSourceExactScopeIndex (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (material : input.binderSpine.IsMaterialRegion region) :
    Fin (exactScopeWires input.pattern.val.diagram region).length →
      Fin (exactScopeWires layout.plugRaw
        (layout.bodyRegion region)).length :=
  Fin.cast (layout.materialSourceExactScope_length region material)

theorem materialSourceExactScopeIndex_get (layout : PlugLayout input)
    (region : Fin input.pattern.val.diagram.regionCount)
    (material : input.binderSpine.IsMaterialRegion region)
    (index : Fin (exactScopeWires input.pattern.val.diagram region).length) :
    (exactScopeWires layout.plugRaw (layout.bodyRegion region)).get
        (layout.materialSourceExactScopeIndex region material index) =
      layout.patternWireMap
        ((exactScopeWires input.pattern.val.diagram region).get index) := by
  let carrier := layout.materialCarrier region material
  have origin : layout.materialRegions.origin carrier = region :=
    layout.materialCarrier_origin region material
  let sourceIndex : Fin (exactScopeWires input.pattern.val.diagram
      (layout.materialRegions.origin carrier)).length :=
    Fin.cast (by rw [origin]) index
  let targetIndex : Fin (exactScopeWires layout.plugRaw
      (layout.materialRegion carrier)).length :=
    layout.materialExactScopeIndex carrier sourceIndex
  have targetIndexEq : targetIndex.val =
      (layout.materialSourceExactScopeIndex region material index).val := rfl
  have sourceGet :
      (exactScopeWires input.pattern.val.diagram
        (layout.materialRegions.origin carrier)).get sourceIndex =
      (exactScopeWires input.pattern.val.diagram region).get index := by
    simpa only [sourceIndex, Fin.cast] using
      List.get_of_eq (congrArg
        (exactScopeWires input.pattern.val.diagram) origin) sourceIndex
  have targetGet :
      (exactScopeWires layout.plugRaw (layout.materialRegion carrier)).get
          targetIndex =
      (exactScopeWires layout.plugRaw (layout.bodyRegion region)).get
          (layout.materialSourceExactScopeIndex region material index) := by
    have values := List.get_of_eq (congrArg
      (exactScopeWires layout.plugRaw)
      (layout.materialRegion_materialCarrier region material)) targetIndex
    simpa only [targetIndex, materialSourceExactScopeIndex, Fin.cast]
      using values
  calc
    (exactScopeWires layout.plugRaw (layout.bodyRegion region)).get
        (layout.materialSourceExactScopeIndex region material index) =
      (exactScopeWires layout.plugRaw
        (layout.materialRegion carrier)).get targetIndex := targetGet.symm
    _ = layout.patternWireMap
        ((exactScopeWires input.pattern.val.diagram
          (layout.materialRegions.origin carrier)).get sourceIndex) := by
      exact layout.materialExactScopeIndex_get carrier sourceIndex
    _ = layout.patternWireMap
        ((exactScopeWires input.pattern.val.diagram region).get index) :=
      congrArg layout.patternWireMap sourceGet

end Splice.Input.PlugLayout

end VisualProof.Concrete
