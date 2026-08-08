import VisualProof.Refinement.Implementation.DoubleCutElimCompile

namespace VisualProof.Refinement.Implementation.DoubleCutElimRoot

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutElimTransport
open VisualProof.Refinement.Implementation.DoubleCutElimCompiler
open VisualProof.Refinement.Implementation.DoubleCutElimOccurrence
open VisualProof.Refinement.Implementation.DoubleCutElimCompile
open VisualProof.Refinement.Implementation.DoubleCutIntroCompile

/-- Canonical promoted open result.  The dense wire carrier is unchanged, so
the ordered source boundary can be retained literally. -/
def targetOpen
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    Concrete.OpenDiagram where
  diagram := Target trace
  boundary := source.val.boundary

theorem target_root_eq
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root) :
    (Target trace).root =
      promotedTarget source.val.diagram
        source.property.diagram_well_formed trace := by
  apply (Domain source.val.diagram outer trace.inner).origin_injective
  change (Domain source.val.diagram outer trace.inner).origin
      trace.promotion.root = _
  rw [trace.promotion.root_origin,
    promotedTarget_origin source.val.diagram
      source.property.diagram_well_formed trace, root]

def targetOpenWellFormed
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed) :
    (targetOpen source trace).WellFormed where
  diagram_well_formed := targetWellFormed
  boundary_is_root_scoped := by
    intro wire member
    change ((Target trace).wires wire).scope = (Target trace).root
    rw [target_root_eq source trace root]
    apply (target_scope_iff source.val.diagram
      source.property.diagram_well_formed trace wire).2
    exact Or.inl (by
      rw [root]
      exact source.property.boundary_is_root_scoped wire member)

def checkedTarget
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed) : Concrete.CheckedOpen :=
  ⟨targetOpen source trace,
    targetOpenWellFormed source trace root targetWellFormed⟩

@[simp] theorem targetOpen_exposedWires
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    (targetOpen source trace).exposedWires = source.val.exposedWires := rfl

private def sourceRootLocal
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    Concrete.Elaboration.WireContext source.val.diagram :=
  source.val.hiddenWires ++ sourceInnerWires trace

private theorem sourceRootLocal_nodup
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root) :
    (sourceRootLocal source trace).Nodup := by
  rw [sourceRootLocal, List.nodup_append]
  refine ⟨source.val.hiddenWires_nodup,
    Concrete.Elaboration.exactScopeWires_nodup source.val.diagram trace.inner,
    ?_⟩
  intro host hostMember inner innerMember equality
  subst inner
  have hostScope := (Concrete.OpenDiagram.mem_hiddenWires source.val host).1
    hostMember |>.1
  have innerScope := (Concrete.Elaboration.mem_exactScopeWires
    source.val.diagram trace.inner host).1 innerMember
  exact target_ne_inner source.val.diagram
    source.property.diagram_well_formed trace.outer_eq trace.inner_eq
    (root.trans (hostScope.symm.trans innerScope))

private theorem sourceRootLocal_mem_iff_targetHidden
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (wire : Fin source.val.diagram.wireCount) :
    wire ∈ sourceRootLocal source trace ↔
      wire ∈ (targetOpen source trace).hiddenWires := by
  simp only [sourceRootLocal, List.mem_append,
    Concrete.OpenDiagram.mem_hiddenWires,
    sourceInnerWires, Concrete.Elaboration.mem_exactScopeWires]
  constructor
  · intro member
    apply (Concrete.OpenDiagram.mem_hiddenWires
      (targetOpen source trace) wire).2
    change ((Target trace).wires wire).scope = (Target trace).root ∧
      wire ∉ source.val.exposedWires
    rw [target_root_eq source trace root,
      target_scope_iff source.val.diagram
        source.property.diagram_well_formed trace wire, root]
    rcases member with ⟨scope, notExposed⟩ | scope
    · exact ⟨Or.inl scope, by simpa [targetOpen] using notExposed⟩
    · refine ⟨Or.inr scope, ?_⟩
      intro exposed
      have exposedSource : wire ∈ source.val.exposedWires := by
        simpa [targetOpen] using exposed
      have exposedScope := source.property.exposed_root_scoped exposedSource
      exact target_ne_inner source.val.diagram
        source.property.diagram_well_formed trace.outer_eq trace.inner_eq
        (root.trans (exposedScope.symm.trans scope))
  · intro member
    have facts := (Concrete.OpenDiagram.mem_hiddenWires
      (targetOpen source trace) wire).1 member
    change ((Target trace).wires wire).scope = (Target trace).root ∧
      wire ∉ source.val.exposedWires at facts
    rw [target_root_eq source trace root,
      target_scope_iff source.val.diagram
        source.property.diagram_well_formed trace wire, root] at facts
    rcases facts with ⟨scope, notExposed⟩
    rcases scope with host | inner
    · exact Or.inl ⟨host, by simpa [targetOpen] using notExposed⟩
    · exact Or.inr inner

private noncomputable def rootLocalEquiv
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root) :
    FiniteEquiv (Fin (sourceRootLocal source trace).length)
      (Fin (targetOpen source trace).hiddenWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin source.val.diagram.wireCount))
    (sourceRootLocal source trace) (targetOpen source trace).hiddenWires
    (sourceRootLocal_nodup source trace root)
    (targetOpen source trace).hiddenWires_nodup (by
      intro wire
      simpa using
        (sourceRootLocal_mem_iff_targetHidden source trace root wire).symm)

private theorem rootLocalEquiv_spec
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (index : Fin (sourceRootLocal source trace).length) :
    (targetOpen source trace).hiddenWires.get
        (rootLocalEquiv source trace root index) =
      (sourceRootLocal source trace).get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin source.val.diagram.wireCount))
    (sourceRootLocal source trace) (targetOpen source trace).hiddenWires
    (sourceRootLocal_nodup source trace root)
    (targetOpen source trace).hiddenWires_nodup (by
      intro wire
      simpa using
        (sourceRootLocal_mem_iff_targetHidden source trace root wire).symm)
    index

private theorem sourceRootWires_nodup
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root) :
    (source.val.exposedWires ++ sourceRootLocal source trace).Nodup := by
  rw [List.nodup_append]
  refine ⟨source.val.exposedWires_nodup,
    sourceRootLocal_nodup source trace root, ?_⟩
  intro exposed exposedMember localWire localMember equality
  subst localWire
  rcases List.mem_append.mp localMember with hidden | inner
  · exact (Concrete.OpenDiagram.mem_hiddenWires source.val exposed).1 hidden
      |>.2 exposedMember
  · have exposedScope := source.property.exposed_root_scoped exposedMember
    have innerScope := (Concrete.Elaboration.mem_exactScopeWires
      source.val.diagram trace.inner exposed).1 inner
    exact target_ne_inner source.val.diagram
      source.property.diagram_well_formed trace.outer_eq trace.inner_eq
      (root.trans (exposedScope.symm.trans innerScope))

private theorem sourceRootWires_mem_iff_target
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed)
    (wire : Fin source.val.diagram.wireCount) :
    wire ∈ (targetOpen source trace).rootWires ↔
      wire ∈ source.val.exposedWires ++ sourceRootLocal source trace := by
  constructor
  · intro member
    have scope := (Concrete.OpenDiagram.mem_rootWires_iff
      (targetOpen source trace)
      (targetOpenWellFormed source trace root targetWellFormed) wire).1 member
    change ((Target trace).wires wire).scope = (Target trace).root at scope
    rw [target_root_eq source trace root,
      target_scope_iff source.val.diagram
        source.property.diagram_well_formed trace wire, root] at scope
    rcases scope with host | inner
    · by_cases exposed : wire ∈ source.val.exposedWires
      · exact List.mem_append_left _ exposed
      · exact List.mem_append_right _ (List.mem_append_left _
          ((Concrete.OpenDiagram.mem_hiddenWires source.val wire).2
            ⟨host, exposed⟩))
    · exact List.mem_append_right _ (List.mem_append_right _
        ((Concrete.Elaboration.mem_exactScopeWires
          source.val.diagram trace.inner wire).2 inner))
  · intro member
    apply (Concrete.OpenDiagram.mem_rootWires_iff
      (targetOpen source trace)
      (targetOpenWellFormed source trace root targetWellFormed) wire).2
    change ((Target trace).wires wire).scope = (Target trace).root
    rw [target_root_eq source trace root,
      target_scope_iff source.val.diagram
        source.property.diagram_well_formed trace wire, root]
    rcases List.mem_append.mp member with exposed | localMember
    · exact Or.inl (source.property.exposed_root_scoped exposed)
    · rcases List.mem_append.mp localMember with hidden | inner
      · exact Or.inl
          ((Concrete.OpenDiagram.mem_hiddenWires source.val wire).1 hidden |>.1)
      · exact Or.inr ((Concrete.Elaboration.mem_exactScopeWires
          source.val.diagram trace.inner wire).1 inner)

private noncomputable def rootWireEquiv
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed) :
    FiniteEquiv
      (Fin (source.val.exposedWires ++ sourceRootLocal source trace).length)
      (Fin (targetOpen source trace).rootWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin source.val.diagram.wireCount))
    (source.val.exposedWires ++ sourceRootLocal source trace)
    (targetOpen source trace).rootWires
    (sourceRootWires_nodup source trace root)
    (targetOpen source trace).rootWires_nodup (by
      intro wire
      simpa using sourceRootWires_mem_iff_target source trace root
        targetWellFormed wire)

private theorem rootWireEquiv_spec
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed)
    (index : Fin
      (source.val.exposedWires ++ sourceRootLocal source trace).length) :
    (targetOpen source trace).rootWires.get
        (rootWireEquiv source trace root targetWellFormed index) =
      (source.val.exposedWires ++ sourceRootLocal source trace).get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin source.val.diagram.wireCount))
    (source.val.exposedWires ++ sourceRootLocal source trace)
    (targetOpen source trace).rootWires
    (sourceRootWires_nodup source trace root)
    (targetOpen source trace).rootWires_nodup (by
      intro wire
      simpa using sourceRootWires_mem_iff_target source trace root
        targetWellFormed wire)
    index

private theorem rootWireEquiv_eq_cast
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed) :
    rootWireEquiv source trace root targetWellFormed =
      Concrete.Elaboration.castFinEquiv (by simp)
        (by
          simp only [Concrete.OpenDiagram.rootWires, List.length_append,
            targetOpen_exposedWires]
          rfl)
        (extendWireEquiv
          (FiniteEquiv.refl (Fin source.val.exposedWires.length))
          (rootLocalEquiv source trace root)) := by
  apply FiniteEquiv.ext
  intro index
  have values : (targetOpen source trace).rootWires.get
        (rootWireEquiv source trace root targetWellFormed index) =
      (targetOpen source trace).rootWires.get
        (Concrete.Elaboration.castFinEquiv (by simp)
          (by
            simp only [Concrete.OpenDiagram.rootWires, List.length_append,
              targetOpen_exposedWires]
            rfl)
          (extendWireEquiv
            (FiniteEquiv.refl (Fin source.val.exposedWires.length))
            (rootLocalEquiv source trace root)) index) := by
    rw [rootWireEquiv_spec source trace root targetWellFormed index]
    let split : Fin
        (source.val.exposedWires.length +
          (sourceRootLocal source trace).length) := Fin.cast (by simp) index
    have indexEq : Fin.cast (by simp) split = index := by
      apply Fin.ext
      rfl
    rw [← indexEq]
    refine Fin.addCases (fun exposedIndex => ?_) (fun localIndex => ?_) split
    · simpa [Concrete.Elaboration.castFinEquiv, extendWireEquiv,
        Concrete.OpenDiagram.rootWires, targetOpen] using
        (Concrete.Elaboration.get_append_castAdd
          (targetOpen source trace).exposedWires
          (targetOpen source trace).hiddenWires exposedIndex).symm
    · simp only [Concrete.Elaboration.castFinEquiv]
      have localSpec := rootLocalEquiv_spec source trace root localIndex
      rw [show
        (source.val.exposedWires ++ sourceRootLocal source trace).get
            (Fin.cast (by simp)
              (Fin.natAdd source.val.exposedWires.length localIndex)) =
          (sourceRootLocal source trace).get localIndex by
        simp]
      calc
        _ = (targetOpen source trace).hiddenWires.get
            (rootLocalEquiv source trace root localIndex) := localSpec.symm
        _ = _ := by
          simpa [extendWireEquiv, Concrete.OpenDiagram.rootWires, targetOpen]
            using (Concrete.Elaboration.get_append_natAdd
              (targetOpen source trace).exposedWires
              (targetOpen source trace).hiddenWires
              (rootLocalEquiv source trace root localIndex)).symm
  apply Fin.ext
  exact (List.getElem_inj
    (targetOpen source trace).rootWires_nodup).mp values

/-- Whole-open root elimination against the canonical promoted target. -/
theorem root_rule
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (root : trace.target = source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed) :
    Rule.DoubleCut source.elaborate
      (checkedTarget source trace root targetWellFormed).elaborate := by
  let target := checkedTarget source trace root targetWellFormed
  obtain ⟨sourceBody, sourceRootCompiled, sourceBodyEq⟩ :=
    source.elaborate_body_computation
  obtain ⟨targetBody, targetRootCompiled, targetBodyEq⟩ :=
    target.elaborate_body_computation
  obtain ⟨sourceItems, sourceItemsCompiled, sourceFinish⟩ :=
    Option.bind_eq_some_iff.mp sourceRootCompiled
  obtain ⟨targetItems, targetItemsCompiled, targetFinish⟩ :=
    Option.bind_eq_some_iff.mp targetRootCompiled
  have sourceFinishEq :
      Concrete.Elaboration.finishRoot source.val.exposedWires
        source.val.hiddenWires sourceItems = sourceBody :=
    Option.some.inj sourceFinish
  have targetFinishEq :
      Concrete.Elaboration.finishRoot target.val.exposedWires
        target.val.hiddenWires targetItems = targetBody :=
    Option.some.inj targetFinish
  let sourceRoot : Concrete.Elaboration.WireContext source.val.diagram :=
    source.val.rootWires
  let targetRoot : Concrete.Elaboration.WireContext (Target trace) :=
    (targetOpen source trace).rootWires
  have sourceItemsCompiled' : Concrete.Elaboration.compileOccurrencesWith?
      source.val.diagram
      (Concrete.Elaboration.compileRegion? source.val.diagram
        source.val.diagram.regionCount)
      sourceRoot Concrete.Elaboration.BinderContext.empty
      (Concrete.Elaboration.localOccurrences source.val.diagram trace.target) =
        some sourceItems := by
    simpa [sourceRoot, root] using sourceItemsCompiled
  have targetItemsCompiled' : Concrete.Elaboration.compileOccurrencesWith?
      (Target trace)
      (Concrete.Elaboration.compileRegion? (Target trace)
        (Target trace).regionCount)
      targetRoot Concrete.Elaboration.BinderContext.empty
      (Concrete.Elaboration.localOccurrences (Target trace)
        (promotedTarget source.val.diagram
          source.property.diagram_well_formed trace)) = some targetItems := by
    simpa [target, checkedTarget, targetOpen, targetRoot,
      target_root_eq source trace root] using targetItemsCompiled
  obtain ⟨sourceOrdered, sourceOrderedCompiled, sourceOrderedIso⟩ :=
    compileOccurrences_of_perm source.val.diagram
      (Concrete.Elaboration.compileRegion? source.val.diagram
        source.val.diagram.regionCount)
      sourceRoot Concrete.Elaboration.BinderContext.empty
      (target_occurrences_partition trace).symm
      (Concrete.Elaboration.localOccurrences_nodup source.val.diagram
        trace.target)
      ((Concrete.Elaboration.localOccurrences_nodup source.val.diagram
        trace.target).perm (target_occurrences_partition trace).symm)
      sourceItemsCompiled'
  obtain ⟨sourceHostItems, sourceOuterItems, sourceHostCompiled,
      sourceOuterCompiled, sourceOrderedEq⟩ :=
    Concrete.Elaboration.compileOccurrencesWith?_append_split
      (Concrete.Elaboration.compileRegion? source.val.diagram
        source.val.diagram.regionCount)
      sourceRoot Concrete.Elaboration.BinderContext.empty
      (hostOccurrences trace) [.child outer]
      sourceOrdered sourceOrderedCompiled
  rw [sourceOrderedEq] at sourceOrderedIso
  rcases sourceOrderedIso with ⟨sourceOrderedIso⟩
  simp only [Concrete.Elaboration.compileOccurrencesWith?,
    Concrete.Elaboration.compileOccurrenceWith?, trace.outer_eq]
    at sourceOuterCompiled
  cases sourceOuterResult : Concrete.Elaboration.compileRegion?
      source.val.diagram source.val.diagram.regionCount outer sourceRoot
      Concrete.Elaboration.BinderContext.empty with
  | none => simp [sourceOuterResult] at sourceOuterCompiled
  | some sourceOuterBody =>
      simp [sourceOuterResult] at sourceOuterCompiled
      subst sourceOuterItems
      have countNe : source.val.diagram.regionCount ≠ 0 := by
        intro countEq
        exact Fin.elim0 (Fin.cast countEq outer)
      obtain ⟨innerFuel, countEq⟩ := Nat.exists_eq_succ_of_ne_zero countNe
      rw [countEq] at sourceOuterResult
      simp only [Concrete.Elaboration.compileRegion?] at sourceOuterResult
      rw [outer_localOccurrences trace] at sourceOuterResult
      obtain ⟨sourceOuterItems, sourceOuterItemsCompiled,
          sourceOuterFinish⟩ := Option.bind_eq_some_iff.mp sourceOuterResult
      have sourceOuterFinishEq := Option.some.inj sourceOuterFinish
      subst sourceOuterBody
      simp only [Concrete.Elaboration.compileOccurrencesWith?,
        Concrete.Elaboration.compileOccurrenceWith?, trace.inner_eq]
        at sourceOuterItemsCompiled
      cases sourceInnerResult : Concrete.Elaboration.compileRegion?
          source.val.diagram innerFuel trace.inner
          (sourceRoot.extend outer) Concrete.Elaboration.BinderContext.empty with
      | none => simp [sourceInnerResult] at sourceOuterItemsCompiled
      | some sourceInnerBody =>
          simp [sourceInnerResult] at sourceOuterItemsCompiled
          subst sourceOuterItems
          cases innerFuel with
          | zero =>
              exact False.elim
                ((outer_ne_inner source.val.diagram
                  source.property.diagram_well_formed trace.inner_eq)
                  (by
                    apply Fin.ext
                    have outerLt := outer.isLt
                    have innerLt := trace.inner.isLt
                    omega))
          | succ innerItemFuel =>
              simp only [Concrete.Elaboration.compileRegion?]
                at sourceInnerResult
              obtain ⟨sourceInnerItems, sourceInnerItemsCompiled,
                  sourceInnerFinish⟩ :=
                Option.bind_eq_some_iff.mp sourceInnerResult
              have sourceInnerFinishEq := Option.some.inj sourceInnerFinish
              subst sourceInnerBody
              obtain ⟨targetOrdered, targetOrderedCompiled,
                  targetOrderedIso⟩ :=
                compileOccurrences_of_perm (Target trace)
                  (Concrete.Elaboration.compileRegion? (Target trace)
                    (Target trace).regionCount)
                  targetRoot Concrete.Elaboration.BinderContext.empty
                  (promoted_occurrences_partition source.val.diagram
                    source.property.diagram_well_formed trace).symm
                  (Concrete.Elaboration.localOccurrences_nodup
                    (Target trace)
                    (promotedTarget source.val.diagram
                      source.property.diagram_well_formed trace))
                  ((Concrete.Elaboration.localOccurrences_nodup
                    (Target trace)
                    (promotedTarget source.val.diagram
                      source.property.diagram_well_formed trace)).perm
                    (promoted_occurrences_partition source.val.diagram
                      source.property.diagram_well_formed trace).symm)
                  targetItemsCompiled'
              obtain ⟨targetHostItems, targetInnerItems,
                  targetHostCompiled, targetInnerCompiled,
                  targetOrderedEq⟩ :=
                Concrete.Elaboration.compileOccurrencesWith?_append_split
                  (Concrete.Elaboration.compileRegion? (Target trace)
                    (Target trace).regionCount)
                  targetRoot Concrete.Elaboration.BinderContext.empty
                  ((hostOccurrences trace).map
                    (promoteOccurrence trace
                      (promotedTarget source.val.diagram
                        source.property.diagram_well_formed trace)))
                  ((innerOccurrences trace).map
                    (promoteOccurrence trace
                      (promotedTarget source.val.diagram
                        source.property.diagram_well_formed trace)))
                  targetOrdered targetOrderedCompiled
              rw [targetOrderedEq] at targetOrderedIso
              rcases targetOrderedIso with ⟨targetOrderedIso⟩
              let sourceOuter := sourceRoot.extend outer
              let sourceFull := sourceOuter.extend trace.inner
              let totalWire := rootWireEquiv source trace root targetWellFormed
              let hostPlacement : Fin sourceRoot.length →
                  Fin (source.val.exposedWires ++
                    sourceRootLocal source trace).length :=
                fun index => Fin.cast (by
                  simp [sourceRoot, sourceRootLocal,
                    Concrete.OpenDiagram.rootWires]
                  omega)
                  (Fin.castAdd (sourceInnerWires trace).length index)
              let innerPlacement : Fin sourceFull.length →
                  Fin (source.val.exposedWires ++
                    sourceRootLocal source trace).length :=
                fun index => Fin.cast (by
                  simp [sourceFull, sourceOuter, sourceRoot,
                    sourceRootLocal, Concrete.OpenDiagram.rootWires,
                    Concrete.Elaboration.WireContext.extend,
                    outer_exactScopeWires trace, sourceInnerWires]) index
              let hostMap : Fin sourceRoot.length → Fin targetRoot.length :=
                totalWire.toFun ∘ hostPlacement
              let fullMap : Fin sourceFull.length → Fin targetRoot.length :=
                totalWire.toFun ∘ innerPlacement
              have hostAgreement : ∀ index,
                  targetRoot.get (hostMap index) = sourceRoot.get index := by
                intro index
                change (targetOpen source trace).rootWires.get
                    (rootWireEquiv source trace root targetWellFormed
                      (hostPlacement index)) = sourceRoot.get index
                rw [rootWireEquiv_spec source trace root targetWellFormed]
                simpa [hostPlacement, sourceRoot, sourceRootLocal,
                  Concrete.OpenDiagram.rootWires, List.append_assoc] using
                  (Concrete.Elaboration.get_append_castAdd sourceRoot
                    (sourceInnerWires trace) index)
              have fullAgreement : ∀ index,
                  targetRoot.get (fullMap index) = sourceFull.get index := by
                intro index
                change (targetOpen source trace).rootWires.get
                    (rootWireEquiv source trace root targetWellFormed
                      (innerPlacement index)) = sourceFull.get index
                rw [rootWireEquiv_spec source trace root targetWellFormed]
                simp [innerPlacement, sourceFull, sourceOuter, sourceRoot,
                  sourceRootLocal, Concrete.OpenDiagram.rootWires,
                  Concrete.Elaboration.WireContext.extend,
                  outer_exactScopeWires trace, sourceInnerWires,
                  List.append_assoc]
              have sourceRootExact : sourceRoot.Exact trace.target := by
                simpa [sourceRoot, root] using
                  (Concrete.Elaboration.openRootWires_exact source.property)
              have sourceOuterExact : sourceOuter.Exact outer := by
                exact sourceRootExact.extend_child
                  source.property.diagram_well_formed (by
                    simp [trace.outer_eq, Concrete.CRegion.parent?])
              have sourceFullExact : sourceFull.Exact trace.inner := by
                exact sourceOuterExact.extend_child
                  source.property.diagram_well_formed (by
                    simp [trace.inner_eq, Concrete.CRegion.parent?])
              have targetRootExact : targetRoot.Exact
                  (promotedTarget source.val.diagram
                    source.property.diagram_well_formed trace) := by
                have exact :=
                  Concrete.Elaboration.openRootWires_exact target.property
                change targetRoot.Exact (Target trace).root at exact
                rw [target_root_eq source trace root] at exact
                exact exact
              have hostItemsIso := promotion_items_iso source.val.diagram
                source.property.diagram_well_formed trace targetWellFormed
                trace.target
                (target_ne_outer source.val.diagram
                  source.property.diagram_well_formed trace.outer_eq)
                sourceRoot targetRoot hostMap hostAgreement sourceRootExact
                (by
                  simpa [promoteRegionIndex,
                    target_ne_inner source.val.diagram
                      source.property.diagram_well_formed trace.outer_eq
                      trace.inner_eq] using targetRootExact)
                Concrete.Elaboration.BinderContext.empty
                Concrete.Elaboration.BinderContext.empty (by
                  intro binder
                  rfl)
                (hostOccurrences trace)
                (by
                  intro occurrence member
                  exact (List.mem_filter.mp member).1)
                (by
                  intro occurrence member child occurrenceEq
                  subst occurrence
                  exact focusOccurrence_survives source.val.diagram
                    source.property.diagram_well_formed trace (.child child)
                    (List.mem_append_left _ member))
                (by
                  intro occurrence member child occurrenceEq
                  subst occurrence
                  have parent :=
                    (Concrete.Elaboration.mem_localOccurrences_child
                      source.val.diagram trace.target child).1
                      (List.mem_filter.mp member).1
                  exact
                    Concrete.Elaboration.checked_direct_child_not_encloses_parent
                      source.property.diagram_well_formed parent)
                sourceHostCompiled targetHostCompiled
              have innerItemsIso := promotion_items_iso source.val.diagram
                source.property.diagram_well_formed trace targetWellFormed
                trace.inner
                (outer_ne_inner source.val.diagram
                  source.property.diagram_well_formed trace.inner_eq).symm
                sourceFull targetRoot fullMap fullAgreement sourceFullExact
                (by
                  simpa [promoteRegionIndex] using targetRootExact)
                Concrete.Elaboration.BinderContext.empty
                Concrete.Elaboration.BinderContext.empty (by
                  intro binder
                  rfl)
                (innerOccurrences trace)
                (by intro occurrence member; exact member)
                (by
                  intro occurrence member child occurrenceEq
                  subst occurrence
                  exact focusOccurrence_survives source.val.diagram
                    source.property.diagram_well_formed trace (.child child)
                    (List.mem_append_right _ member))
                (by
                  intro occurrence member child occurrenceEq
                  subst occurrence
                  have childParent :=
                    (Concrete.Elaboration.mem_localOccurrences_child
                      source.val.diagram trace.inner child).1 member
                  intro childEnclosesTarget
                  have targetEnclosesOuter :
                      source.val.diagram.Encloses trace.target outer :=
                    direct_child_encloses (input := source.val.diagram) (by
                      simp [trace.outer_eq, Concrete.CRegion.parent?])
                  have outerEnclosesInner :
                      source.val.diagram.Encloses outer trace.inner :=
                    direct_child_encloses (input := source.val.diagram) (by
                      simp [trace.inner_eq, Concrete.CRegion.parent?])
                  have childEnclosesInner :=
                    Concrete.Elaboration.checked_encloses_trans
                      source.property.diagram_well_formed childEnclosesTarget
                      (Concrete.Elaboration.checked_encloses_trans
                        source.property.diagram_well_formed
                        targetEnclosesOuter outerEnclosesInner)
                  exact
                    Concrete.Elaboration.checked_direct_child_not_encloses_parent
                      source.property.diagram_well_formed childParent
                      childEnclosesInner)
                sourceInnerItemsCompiled targetInnerCompiled
              let rootLayout : sourceRoot.length =
                  (source.val.exposedWires ++ source.val.hiddenWires).length := by
                simp [sourceRoot, Concrete.OpenDiagram.rootWires]
              let rootWire : FiniteEquiv (Fin sourceRoot.length)
                  (Fin (source.val.exposedWires ++
                    source.val.hiddenWires).length) :=
                FiniteEquiv.finCast rootLayout
              let outerWire : FiniteEquiv (Fin sourceOuter.length)
                  (Fin (source.val.exposedWires ++
                    source.val.hiddenWires).length) := FiniteEquiv.finCast (by
                simp [sourceOuter, sourceRoot,
                  Concrete.OpenDiagram.rootWires,
                  Concrete.Elaboration.WireContext.extend,
                  outer_exactScopeWires trace])
              let material : Region
                  (source.val.exposedWires ++ source.val.hiddenWires).length [] :=
                (Concrete.Elaboration.finishRegion source.val.diagram
                  sourceOuter trace.inner sourceInnerItems).renameWires
                    outerWire
              let hostItems : ItemSeq
                  (source.val.exposedWires ++ source.val.hiddenWires).length [] :=
                sourceHostItems.castWiresEq rootLayout
              let rootSumLayout :
                  (source.val.exposedWires ++ source.val.hiddenWires).length =
                    source.val.exposedWires.length +
                      source.val.hiddenWires.length := by simp
              let before : Region source.val.exposedWires.length [] :=
                Region.spliceAt source.val.hiddenWires.length
                  (hostItems.castWiresEq rootSumLayout)
                  (material.castWiresEq rootSumLayout) id
                  (DoubleCutTransport.identityRelationRenaming [])
              let wrapped : ItemSeq
                  (source.val.exposedWires ++
                    source.val.hiddenWires).length [] :=
                .cons (.cut (.mk 0 (.cons (.cut material) .nil))) .nil
              let after : Region source.val.exposedWires.length [] :=
                Region.spliceAt source.val.hiddenWires.length
                  (hostItems.castWiresEq rootSumLayout)
                  (.mk 0 (wrapped.castWiresEq rootSumLayout)) id
                  (DoubleCutTransport.identityRelationRenaming [])
              have localStep : Rule.DoubleCut.Local before after := by
                have wrapEq : Rule.DoubleCut.wrap
                    (material.castWiresEq rootSumLayout) =
                    .mk 0 (wrapped.castWiresEq rootSumLayout) := by
                  dsimp only [wrapped]
                  exact wrap_castWiresEq_explicit rootSumLayout material
                dsimp only [before, after]
                rw [← wrapEq]
                exact Rule.DoubleCut.Local.introduce
                  source.val.hiddenWires.length
                  (hostItems.castWiresEq rootSumLayout)
                  (material.castWiresEq rootSumLayout) id
                  (DoubleCutTransport.identityRelationRenaming [])
              have sourceBodyIso : RegionIso
                  (FiniteEquiv.refl
                    (Fin source.val.exposedWires.length)) []
                  source.elaborate.body after := by
                let innerBody := Concrete.Elaboration.finishRegion
                  source.val.diagram sourceOuter trace.inner sourceInnerItems
                have materialIso : RegionIso outerWire []
                    innerBody material :=
                  RegionIso.renameWiresEquiv innerBody outerWire
                have innerItemIso := singleton_iso
                  (ItemIso.cut materialIso.symm)
                have outerBodyIso := empty_finish_iso source.val.diagram
                  sourceRoot outer (outer_exactScopeWires trace)
                  outerWire.symm innerItemIso
                have wrappedIso := singleton_iso
                  (ItemIso.cut outerBodyIso.symm)
                have wrappedIso' : ItemSeqIso rootWire []
                    (.cons (.cut
                      (Concrete.Elaboration.finishRegion source.val.diagram
                        sourceRoot outer (.cons (.cut innerBody) .nil))) .nil)
                    wrapped := by
                  apply ItemSeqIso.changeWire _ wrappedIso
                  apply FiniteEquiv.ext
                  intro index
                  apply Fin.ext
                  rfl
                have hostIso : ItemSeqIso rootWire [] sourceHostItems
                    hostItems := by
                  dsimp only [hostItems]
                  rw [ItemSeq.castWiresEq_eq_renameWires]
                  apply ItemSeqIso.changeWire _
                    (ItemSeqIso.renameWiresEquiv sourceHostItems rootWire)
                  apply FiniteEquiv.ext
                  intro index
                  apply Fin.ext
                  rfl
                have combined := ItemSeqIso.append hostIso wrappedIso'
                have compiledToPartition := sourceOrderedIso.trans combined
                have compiledToPartition' : ItemSeqIso
                    (FiniteEquiv.refl
                      (Fin (source.val.exposedWires ++
                        source.val.hiddenWires).length)) []
                    sourceItems (hostItems.append wrapped) := by
                  apply ItemSeqIso.changeWire _ compiledToPartition
                  apply FiniteEquiv.ext
                  intro index
                  apply Fin.ext
                  rfl
                have canonical := finishRoot_iso source.val.exposedWires
                  source.val.hiddenWires compiledToPartition'
                have afterEq : after =
                    Concrete.Elaboration.finishRoot
                      source.val.exposedWires source.val.hiddenWires
                      (hostItems.append wrapped) := by
                  dsimp only [after]
                  exact root_splice_eq source.val.exposedWires
                    source.val.hiddenWires hostItems wrapped
                rw [sourceBodyEq, ← sourceFinishEq, afterEq]
                exact canonical
              have hostBack : totalWire.symm.toFun ∘ hostMap =
                  hostPlacement := by
                funext index
                exact totalWire.left_inv (hostPlacement index)
              have innerBack : totalWire.symm.toFun ∘ fullMap =
                  innerPlacement := by
                funext index
                exact totalWire.left_inv (innerPlacement index)
              have totalCommute : totalWire.toFun ∘ totalWire.symm.toFun =
                  id ∘ (FiniteEquiv.refl (Fin targetRoot.length)).toFun := by
                funext index
                exact totalWire.right_inv index
              have hostTransported := hostItemsIso.renameWires_commuting
                totalWire.symm.toFun id totalWire totalCommute
              have innerTransported := innerItemsIso.renameWires_commuting
                totalWire.symm.toFun id totalWire totalCommute
              have hostFinal : ItemSeqIso totalWire []
                  (sourceHostItems.renameWires hostPlacement)
                  targetHostItems := by
                rw [← hostBack]
                simpa only [← ItemSeq.renameWires_comp,
                  ItemSeq.renameWires_id] using hostTransported
              have innerFinal : ItemSeqIso totalWire []
                  (sourceInnerItems.renameWires innerPlacement)
                  targetInnerItems := by
                rw [← innerBack]
                simpa only [← ItemSeq.renameWires_comp,
                  ItemSeq.renameWires_id] using innerTransported
              have blocks := ItemSeqIso.append hostFinal innerFinal
              let sourcePartitionItems : ItemSeq
                  (source.val.exposedWires ++
                    sourceRootLocal source trace).length [] :=
                (sourceHostItems.renameWires hostPlacement).append
                  (sourceInnerItems.renameWires innerPlacement)
              let sourcePartitionLayout :
                  (source.val.exposedWires ++
                    sourceRootLocal source trace).length =
                    source.val.exposedWires.length +
                      (source.val.hiddenWires.length +
                        (sourceInnerWires trace).length) := by
                simp [sourceRootLocal]
              let sourceCanonical : Region
                  source.val.exposedWires.length [] :=
                .mk (source.val.hiddenWires.length +
                  (sourceInnerWires trace).length)
                  (sourcePartitionItems.castWiresEq sourcePartitionLayout)
              have beforeEq : before = sourceCanonical := by
                dsimp only [before]
                unfold Region.spliceAt Region.adjoinAt
                  DoubleCutTransport.identityRelationRenaming
                dsimp only [material, hostItems, sourceCanonical,
                  sourcePartitionItems]
                simp only [Region.castWiresEq_eq_renameWires,
                  Concrete.Elaboration.finishRegion,
                  Region.renameWires, Region.renameRelations,
                  ItemSeq.renameRelations_id,
                  ItemSeq.renameWires_comp,
                  ItemSeq.castWiresEq_eq_renameWires,
                  ItemSeq.renameWires_append]
                congr 1
                congr 2
                · funext index
                  apply Fin.ext
                  let split : Fin (sourceOuter.length +
                      (sourceInnerWires trace).length) := Fin.cast (by
                    change (sourceOuter.extend trace.inner).length =
                      sourceOuter.length +
                        (Concrete.Elaboration.exactScopeWires
                          source.val.diagram trace.inner).length
                    exact Concrete.Elaboration.WireContext.length_extend
                      sourceOuter trace.inner) index
                  have indexEq : Fin.cast (by
                      change sourceOuter.length +
                          (Concrete.Elaboration.exactScopeWires
                            source.val.diagram trace.inner).length =
                        (sourceOuter.extend trace.inner).length
                      exact (Concrete.Elaboration.WireContext.length_extend
                        sourceOuter trace.inner).symm) split = index := by
                    apply Fin.ext
                    rfl
                  rw [← indexEq]
                  refine Fin.addCases (fun outerIndex => ?_)
                    (fun innerIndex => ?_) split
                  · simp [innerPlacement, sourceFull, sourceOuter, sourceRoot,
                      outerWire, Region.adjoinMaterialWire,
                      extendWireRenaming, Concrete.OpenDiagram.rootWires,
                      Concrete.Elaboration.WireContext.extend,
                      sourceRootLocal, sourceInnerWires]
                    rfl
                  · simp [innerPlacement, sourceFull, sourceOuter, sourceRoot,
                      outerWire, Region.adjoinMaterialWire,
                      extendWireRenaming, Concrete.OpenDiagram.rootWires,
                      Concrete.Elaboration.WireContext.extend,
                      outer_exactScopeWires trace, sourceRootLocal,
                      sourceInnerWires]
              let localWire : FiniteEquiv
                  (Fin (source.val.hiddenWires.length +
                    (sourceInnerWires trace).length))
                  (Fin target.val.hiddenWires.length) :=
                (FiniteEquiv.finCast (by
                  simp [sourceRootLocal])).trans
                  (rootLocalEquiv source trace root)
              let targetLayout : targetRoot.length =
                  target.val.exposedWires.length +
                    target.val.hiddenWires.length := by
                dsimp only [targetRoot, target, checkedTarget]
                exact List.length_append
              have canonicalTarget : RegionIso
                  (FiniteEquiv.refl
                    (Fin source.val.exposedWires.length)) []
                  sourceCanonical
                  (Concrete.Elaboration.finishRoot
                    target.val.exposedWires target.val.hiddenWires
                    (targetHostItems.append targetInnerItems)) := by
                apply Concrete.Elaboration.regionIso_of_cast
                  sourcePartitionLayout targetLayout
                  (FiniteEquiv.refl
                    (Fin source.val.exposedWires.length))
                  localWire sourcePartitionItems
                  (targetHostItems.append targetInnerItems)
                apply ItemSeqIso.changeWire _ blocks
                dsimp only [totalWire]
                rw [rootWireEquiv_eq_cast source trace root targetWellFormed]
                apply FiniteEquiv.ext
                intro index
                apply Fin.ext
                let split : Fin (source.val.exposedWires.length +
                    (sourceRootLocal source trace).length) := Fin.cast (by
                  simp) index
                have indexEq : Fin.cast (by simp) split = index := by
                  apply Fin.ext
                  rfl
                rw [← indexEq]
                refine Fin.addCases (fun exposedIndex => ?_)
                  (fun localIndex => ?_) split
                · simp [Concrete.Elaboration.castFinEquiv, localWire,
                    FiniteEquiv.trans, FiniteEquiv.finCast,
                    extendWireEquiv, sourceRootLocal]
                · have placementEq : Fin.cast sourcePartitionLayout
                      (Fin.cast (by simp)
                        (Fin.natAdd source.val.exposedWires.length
                          localIndex)) =
                    Fin.natAdd source.val.exposedWires.length
                      (Fin.cast (by simp [sourceRootLocal]) localIndex) := by
                    apply Fin.ext
                    rfl
                  simp only [Concrete.Elaboration.castFinEquiv]
                  rw [placementEq]
                  simp [localWire,
                    FiniteEquiv.trans, FiniteEquiv.finCast,
                    extendWireEquiv, sourceRootLocal]
                  rfl
              have beforeTarget : RegionIso
                  (FiniteEquiv.refl
                    (Fin source.val.exposedWires.length)) []
                  before
                  (Concrete.Elaboration.finishRoot
                    target.val.exposedWires target.val.hiddenWires
                    (targetHostItems.append targetInnerItems)) := by
                rw [beforeEq]
                exact canonicalTarget
              have targetOrderedRoot := finishRoot_iso
                target.val.exposedWires target.val.hiddenWires targetOrderedIso
              have targetBodyIso : RegionIso
                  (FiniteEquiv.refl
                    (Fin source.val.exposedWires.length)) []
                  before target.elaborate.body := by
                rw [targetBodyEq, ← targetFinishEq]
                exact beforeTarget.trans targetOrderedRoot.symm
              let sourceHostIso : OpenDiagramIso source.elaborate
                  (source.elaborate.withBody after) := {
                external := FiniteEquiv.refl
                  (Fin source.elaborate.externalClasses)
                boundary := by intro position; rfl
                body := sourceBodyIso
              }
              let targetHostIso : OpenDiagramIso target.elaborate
                  (source.elaborate.withBody before) := {
                external := FiniteEquiv.refl
                  (Fin source.elaborate.externalClasses)
                boundary := by intro position; rfl
                body := targetBodyIso.symm
              }
              let occurrence : Occurrence after source.elaborate := {
                interface := source.elaborate
                context := .hole
                host_iso := sourceHostIso
              }
              refine ⟨_, _, after, before, occurrence, targetHostIso, ?_⟩
              exact Or.inr localStep

end VisualProof.Refinement.Implementation.DoubleCutElimRoot
