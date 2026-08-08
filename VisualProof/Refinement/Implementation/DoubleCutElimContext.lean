import VisualProof.Refinement.Implementation.DoubleCutElimRoot
import VisualProof.Concrete.Subgraph.Splice.Input.Route
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.Nested

namespace VisualProof.Refinement.Implementation.DoubleCutElimContext

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutElimTransport
open VisualProof.Refinement.Implementation.DoubleCutElimCompiler
open VisualProof.Refinement.Implementation.DoubleCutElimCompile

private theorem root_survives
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    (Domain source.val.diagram outer trace.inner).survives
        source.val.diagram.root = true := by
  rw [domain_survives_iff]
  constructor
  · intro equality
    have shape : source.val.diagram.regions source.val.diagram.root =
        .cut trace.target := by
      rw [equality]
      exact trace.outer_eq
    rw [source.property.diagram_well_formed.root_is_sheet] at shape
    cases shape
  · intro equality
    have shape : source.val.diagram.regions source.val.diagram.root =
        .cut outer := by
      rw [equality]
      exact trace.inner_eq
    rw [source.property.diagram_well_formed.root_is_sheet] at shape
    cases shape

theorem target_root_eq
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    (Target trace).root =
      (Domain source.val.diagram outer trace.inner).index
        source.val.diagram.root (root_survives source trace) := by
  apply (Domain source.val.diagram outer trace.inner).origin_injective
  change (Domain source.val.diagram outer trace.inner).origin
      trace.promotion.root = _
  rw [trace.promotion.root_origin,
    (Domain source.val.diagram outer trace.inner).origin_index]

def targetOpen
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    Concrete.OpenDiagram where
  diagram := Target trace
  boundary := source.val.boundary

def targetOpenWellFormed
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed) :
    (targetOpen source trace).WellFormed where
  diagram_well_formed := targetWellFormed
  boundary_is_root_scoped := by
    intro wire member
    change ((Target trace).wires wire).scope = (Target trace).root
    rw [target_root_eq source trace,
      target_wire_scope source.val.diagram
        source.property.diagram_well_formed trace wire]
    have sourceScope := source.property.boundary_is_root_scoped wire member
    apply (Domain source.val.diagram outer trace.inner).origin_injective
    rw [promoteRegionIndex_origin,
      (Domain source.val.diagram outer trace.inner).origin_index]
    have rootNeInner :=
      (domain_survives_iff source.val.diagram outer trace.inner
        source.val.diagram.root).1 (root_survives source trace) |>.2
    have scopeNeInner : (source.val.diagram.wires wire).scope ≠
        trace.inner := by
      intro equality
      exact rootNeInner (sourceScope.symm.trans equality)
    rw [if_neg scopeNeInner, sourceScope]

def checkedTarget
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed) : Concrete.CheckedOpen :=
  ⟨targetOpen source trace,
    targetOpenWellFormed source trace targetWellFormed⟩

private theorem promote_survivor_eq
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (region : Fin source.val.diagram.regionCount)
    (survives : (Domain source.val.diagram outer trace.inner).survives
      region = true) :
    promoteRegionIndex source.val.diagram
        source.property.diagram_well_formed trace region
        ((domain_survives_iff source.val.diagram outer trace.inner region).1
          survives |>.1) =
      (Domain source.val.diagram outer trace.inner).index region survives := by
  apply (Domain source.val.diagram outer trace.inner).origin_injective
  rw [promoteRegionIndex_origin,
    (Domain source.val.diagram outer trace.inner).origin_index]
  have innerNe :=
    (domain_survives_iff source.val.diagram outer trace.inner region).1
      survives |>.2
  simp [innerNe]

private theorem route_start_ne_target
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {start child : Fin source.val.diagram.regionCount} {rest : List Nat}
    (parent : (source.val.diagram.regions child).parent? = some start)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      trace.target rest) :
    start ≠ trace.target := by
  intro equality
  subst start
  exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
    source.property.diagram_well_formed parent
    (Concrete.Splice.Input.RegionRoute.encloses tail
      source.property.diagram_well_formed)

private theorem route_start_survives
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {start child : Fin source.val.diagram.regionCount} {rest : List Nat}
    (parent : (source.val.diagram.regions child).parent? = some start)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      trace.target rest) :
    (Domain source.val.diagram outer trace.inner).survives start = true := by
  rw [domain_survives_iff]
  have startEnclosesTarget : source.val.diagram.Encloses start trace.target :=
    Concrete.Elaboration.checked_encloses_trans
      source.property.diagram_well_formed
      (DoubleCutElimCompile.direct_child_encloses parent)
      (Concrete.Splice.Input.RegionRoute.encloses tail
        source.property.diagram_well_formed)
  constructor
  · intro equality
    subst start
    have outerParent : (source.val.diagram.regions outer).parent? =
        some trace.target := by
      rw [trace.outer_eq]
      rfl
    exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
      source.property.diagram_well_formed outerParent startEnclosesTarget
  · intro equality
    subst start
    have innerParent : (source.val.diagram.regions trace.inner).parent? =
        some outer := by
      rw [trace.inner_eq]
      rfl
    have targetEnclosesOuter : source.val.diagram.Encloses trace.target outer :=
      DoubleCutElimCompile.direct_child_encloses (by
        rw [trace.outer_eq]
        rfl)
    have innerEnclosesOuter :=
      Concrete.Elaboration.checked_encloses_trans
        source.property.diagram_well_formed startEnclosesTarget
        targetEnclosesOuter
    exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
      source.property.diagram_well_formed innerParent innerEnclosesOuter

private theorem route_child_survives
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {start child : Fin source.val.diagram.regionCount} {rest : List Nat}
    (parent : (source.val.diagram.regions child).parent? = some start)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      trace.target rest) :
    (Domain source.val.diagram outer trace.inner).survives child = true := by
  rw [domain_survives_iff]
  have startSurvives := route_start_survives source trace parent tail
  have startCases :=
    (domain_survives_iff source.val.diagram outer trace.inner start).1
      startSurvives
  constructor
  · intro equality
    subst child
    have outerParent : (source.val.diagram.regions outer).parent? =
        some trace.target := by
      rw [trace.outer_eq]
      rfl
    exact (route_start_ne_target source trace parent tail)
      (Option.some.inj (parent.symm.trans outerParent))
  · intro equality
    subst child
    have innerParent : (source.val.diagram.regions trace.inner).parent? =
        some outer := by
      rw [trace.inner_eq]
      rfl
    exact startCases.1 (Option.some.inj (parent.symm.trans innerParent))

private theorem promoted_parent
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {start child : Fin source.val.diagram.regionCount}
    (startSurvives :
      (Domain source.val.diagram outer trace.inner).survives start = true)
    (childSurvives :
      (Domain source.val.diagram outer trace.inner).survives child = true)
    (parent : (source.val.diagram.regions child).parent? = some start) :
    ((Target trace).regions
      ((Domain source.val.diagram outer trace.inner).index child
        childSurvives)).parent? =
      some ((Domain source.val.diagram outer trace.inner).index start
        startSurvives) := by
  cases shape : source.val.diagram.regions child with
  | sheet => simp [shape, Concrete.CRegion.parent?] at parent
  | cut actualParent =>
      have actualEq : actualParent = start := by
        simpa [shape, Concrete.CRegion.parent?] using parent
      subst actualParent
      rw [promoted_cut source.val.diagram
        source.property.diagram_well_formed trace
        ((domain_survives_iff source.val.diagram outer trace.inner start).1
          startSurvives |>.1) childSurvives shape]
      simp only [Concrete.CRegion.parent?]
      exact congrArg some (promote_survivor_eq source trace start startSurvives)
  | bubble actualParent arity =>
      have actualEq : actualParent = start := by
        simpa [shape, Concrete.CRegion.parent?] using parent
      subst actualParent
      rw [promoted_bubble source.val.diagram
        source.property.diagram_well_formed trace
        ((domain_survives_iff source.val.diagram outer trace.inner start).1
          startSurvives |>.1) childSurvives shape]
      simp only [Concrete.CRegion.parent?]
      exact congrArg some (promote_survivor_eq source trace start startSurvives)

inductive RouteAlignment
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    {sourceStart : Fin source.val.diagram.regionCount} →
    {targetStart : Fin (Target trace).regionCount} →
    {sourcePath targetPath : List Nat} →
    (sourceRoute : Concrete.Splice.RegionRoute source.val.diagram sourceStart
      trace.target sourcePath) →
    (targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) targetPath) → Type
  | here : @RouteAlignment source outer raw trace trace.target
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) [] []
      (.here trace.target)
      (Concrete.Splice.RegionRoute.here (d := Target trace)
        (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace))
  | step
      {start child : Fin source.val.diagram.regionCount}
      {sourceRest targetRest : List Nat}
      {sourceParent : (source.val.diagram.regions child).parent? = some start}
      {sourcePosition : Fin (Concrete.Elaboration.localOccurrences
        source.val.diagram start).length}
      {sourcePositionEq : indexOf?
        (Concrete.Elaboration.localOccurrences source.val.diagram start)
        (.child child) = some sourcePosition}
      {sourceTail : Concrete.Splice.RegionRoute source.val.diagram child
        trace.target sourceRest}
      (startSurvives :
        (Domain source.val.diagram outer trace.inner).survives start = true)
      (childSurvives :
        (Domain source.val.diagram outer trace.inner).survives child = true)
      {targetParent : ((Target trace).regions
        ((Domain source.val.diagram outer trace.inner).index child
          childSurvives)).parent? =
        some ((Domain source.val.diagram outer trace.inner).index start
          startSurvives)}
      {targetPosition : Fin (Concrete.Elaboration.localOccurrences
        (Target trace)
        ((Domain source.val.diagram outer trace.inner).index start
          startSurvives)).length}
      {targetPositionEq : indexOf?
        (Concrete.Elaboration.localOccurrences (Target trace)
          ((Domain source.val.diagram outer trace.inner).index start
            startSurvives))
        (.child ((Domain source.val.diagram outer trace.inner).index child
          childSurvives)) = some targetPosition}
      {targetTail : Concrete.Splice.RegionRoute (Target trace)
        ((Domain source.val.diagram outer trace.inner).index child
          childSurvives)
        (promotedTarget source.val.diagram
          source.property.diagram_well_formed trace) targetRest}
      (positionEq : targetPosition =
        localOccurrenceEquiv source.val.diagram
          source.property.diagram_well_formed trace start startSurvives
          (route_start_ne_target source trace sourceParent sourceTail)
          sourcePosition)
      (tail : RouteAlignment source trace sourceTail targetTail) :
      RouteAlignment source trace
        (.step sourceParent sourcePosition sourcePositionEq sourceTail)
        (.step targetParent targetPosition targetPositionEq targetTail)

private noncomputable def route_complete_aux
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {start : Fin source.val.diagram.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute source.val.diagram start
      trace.target path) :
    Σ targetStart, Σ targetPath,
      Σ targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
        (promotedTarget source.val.diagram
          source.property.diagram_well_formed trace) targetPath,
        RouteAlignment source trace route targetRoute := by
  cases route with
  | here region =>
      exact ⟨promotedTarget source.val.diagram
        source.property.diagram_well_formed trace, [], .here _, .here⟩
  | @step start child target rest parent position positionEq tail =>
      let startSurvives := route_start_survives source trace parent tail
      let childSurvives := route_child_survives source trace parent tail
      let targetStart :=
        (Domain source.val.diagram outer trace.inner).index start startSurvives
      let targetChild :=
        (Domain source.val.diagram outer trace.inner).index child childSurvives
      let targetPosition := localOccurrenceEquiv source.val.diagram
        source.property.diagram_well_formed trace start startSurvives
        (route_start_ne_target source trace parent tail) position
      have targetGet : (Concrete.Elaboration.localOccurrences
          (Target trace) targetStart).get targetPosition =
          .child targetChild := by
        rw [localOccurrenceEquiv_spec source.val.diagram
          source.property.diagram_well_formed trace start startSurvives
          (route_start_ne_target source trace parent tail) position]
        have sourceGet := indexOf?_sound positionEq
        rw [show (Concrete.Elaboration.localOccurrences
          source.val.diagram start).get position = .child child by
            simpa only [List.get_eq_getElem] using sourceGet]
        simp only [promoteOccurrence, targetChild]
        rw [dif_pos childSurvives]
      have targetPositionEq : indexOf?
          (Concrete.Elaboration.localOccurrences (Target trace) targetStart)
          (.child targetChild) = some targetPosition := by
        rw [← targetGet]
        exact indexOf?_get_eq_some_of_nodup
          (Concrete.Elaboration.localOccurrences_nodup _ _) targetPosition
      have targetParent : ((Target trace).regions targetChild).parent? =
          some targetStart := promoted_parent source trace startSurvives
            childSurvives parent
      obtain ⟨targetEnd, targetRest, targetTail, tailAlignment⟩ :=
        route_complete_aux source trace tail
      have endEq : targetEnd = targetChild := by
        cases tailAlignment <;> rfl
      subst targetEnd
      refine ⟨targetStart, targetPosition.val :: targetRest,
        .step targetParent targetPosition targetPositionEq targetTail, ?_⟩
      refine .step (sourceParent := parent)
        (sourcePositionEq := positionEq)
        (sourceTail := tail)
        (targetParent := by simpa [targetStart, targetChild] using targetParent)
        (targetPositionEq := by
          simpa [targetStart, targetChild] using targetPositionEq)
        (targetTail := targetTail)
        startSurvives childSurvives rfl ?_
      exact tailAlignment

noncomputable def route_complete
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {start : Fin source.val.diagram.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute source.val.diagram start
      trace.target path) :
    Σ targetStart, Σ targetPath,
      Σ targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
        (promotedTarget source.val.diagram
          source.property.diagram_well_formed trace) targetPath,
        RouteAlignment source trace route targetRoute :=
  route_complete_aux source trace route

private theorem direct_child_survives
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {region child : Fin source.val.diagram.regionCount}
    (regionSurvives :
      (Domain source.val.diagram outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (parent : (source.val.diagram.regions child).parent? = some region) :
    (Domain source.val.diagram outer trace.inner).survives child = true := by
  rw [domain_survives_iff]
  have regionCases :=
    (domain_survives_iff source.val.diagram outer trace.inner region).1
      regionSurvives
  constructor
  · intro equality
    subst child
    have outerParent : (source.val.diagram.regions outer).parent? =
        some trace.target := by rw [trace.outer_eq]; rfl
    exact regionNeTarget (Option.some.inj (parent.symm.trans outerParent))
  · intro equality
    subst child
    have innerParent : (source.val.diagram.regions trace.inner).parent? =
        some outer := by rw [trace.inner_eq]; rfl
    exact regionCases.1 (Option.some.inj (parent.symm.trans innerParent))

private noncomputable def compilerRawFrame
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {region child : Fin source.val.diagram.regionCount} {rest : List Nat}
    (regionSurvives :
      (Domain source.val.diagram outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (childParent : (source.val.diagram.regions child).parent? = some region)
    (sourcePosition : Fin (Concrete.Elaboration.localOccurrences
      source.val.diagram region).length)
    (sourcePositionEq : indexOf?
      (Concrete.Elaboration.localOccurrences source.val.diagram region)
      (.child child) = some sourcePosition)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      trace.target rest)
    {rels : RelCtx} {sourceFuel targetFuel : Nat}
    (sourceContext : Concrete.Elaboration.WireContext source.val.diagram)
    (targetContext : Concrete.Elaboration.WireContext (Target trace))
    (ambient : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length))
    (wireAgreement : ∀ index,
      targetContext.get (ambient index) = sourceContext.get index)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact
      ((Domain source.val.diagram outer trace.inner).index region
        regionSurvives))
    (sourceBinders : Concrete.Elaboration.BinderContext source.val.diagram rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (binderAgreement : ∀ binder, targetBinders binder = sourceBinders
      ((Domain source.val.diagram outer trace.inner).origin binder))
    {sourceItems : ItemSeq sourceContext.length rels}
    {targetItems : ItemSeq targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      source.val.diagram
      (Concrete.Elaboration.compileRegion? source.val.diagram sourceFuel)
      sourceContext sourceBinders
      (Concrete.Elaboration.localOccurrences source.val.diagram region) =
        some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (Target trace)
      (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
      targetContext targetBinders
      (Concrete.Elaboration.localOccurrences (Target trace)
        ((Domain source.val.diagram outer trace.inner).index region
          regionSurvives)) = some targetItems)
    (sourceIndex : Fin sourceItems.length)
    (targetIndex : Fin targetItems.length)
    (sourceIndexVal : sourceIndex.val = sourcePosition.val)
    (targetIndexVal : targetIndex.val =
      (localOccurrenceEquiv source.val.diagram
        source.property.diagram_well_formed trace region regionSurvives
        regionNeTarget sourcePosition).val) :
    ItemSeqIso.Frame ambient sourceIndex targetIndex := by
  let occurrencePositions := localOccurrenceEquiv source.val.diagram
    source.property.diagram_well_formed trace region regionSurvives
      regionNeTarget
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? source.val.diagram sourceFuel)
    sourceContext sourceBinders sourceCompiled
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
    targetContext targetBinders targetCompiled
  let positions := (FiniteEquiv.finCast sourceLength).trans
    (occurrencePositions.trans (FiniteEquiv.finCast targetLength.symm))
  have mapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    have sourceEq : Fin.cast sourceLength sourceIndex = sourcePosition := by
      apply Fin.ext
      exact sourceIndexVal
    change (Fin.cast targetLength.symm
      (occurrencePositions (Fin.cast sourceLength sourceIndex))).val =
        targetIndex.val
    rw [sourceEq]
    simpa using targetIndexVal.symm
  refine { positions := positions, mapped := mapped, siblings := ?_ }
  intro index indexNe
  let occurrenceIndex : Fin
      (Concrete.Elaboration.localOccurrences source.val.diagram region).length :=
    Fin.cast sourceLength index
  have occurrenceNe : occurrenceIndex ≠ sourcePosition := by
    intro equality
    apply indexNe
    apply Fin.ext
    simpa [occurrenceIndex, sourceIndexVal] using congrArg Fin.val equality
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? source.val.diagram sourceFuel)
    sourceContext sourceBinders sourceCompiled occurrenceIndex
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
    targetContext targetBinders targetCompiled
      (occurrencePositions occurrenceIndex)
  rw [localOccurrenceEquiv_spec source.val.diagram
    source.property.diagram_well_formed trace region regionSurvives
    regionNeTarget occurrenceIndex] at targetGet
  let occurrence := (Concrete.Elaboration.localOccurrences
    source.val.diagram region).get occurrenceIndex
  have occurrenceMem : occurrence ∈ Concrete.Elaboration.localOccurrences
      source.val.diagram region := List.get_mem _ _
  have childrenSurvive : ∀ sibling, occurrence = .child sibling →
      (Domain source.val.diagram outer trace.inner).survives sibling = true := by
    intro sibling equality
    rw [equality] at occurrenceMem
    exact direct_child_survives source trace regionSurvives regionNeTarget
      ((Concrete.Elaboration.mem_localOccurrences_child
        source.val.diagram region sibling).1 occurrenceMem)
  have childrenAway : ∀ sibling, occurrence = .child sibling →
      ¬ source.val.diagram.Encloses sibling trace.target := by
    intro sibling equality
    rw [equality] at occurrenceMem
    have siblingParent :=
      (Concrete.Elaboration.mem_localOccurrences_child
        source.val.diagram region sibling).1 occurrenceMem
    have siblingNe : sibling ≠ child := by
      intro siblingEq
      subst sibling
      have found := indexOf?_get_eq_some_of_nodup
        (Concrete.Elaboration.localOccurrences_nodup
          source.val.diagram region) occurrenceIndex
      have foundChild : indexOf?
          (Concrete.Elaboration.localOccurrences source.val.diagram region)
          (.child child) = some occurrenceIndex := by
        rw [← equality]
        exact found
      apply occurrenceNe
      exact Option.some.inj (foundChild.symm.trans sourcePositionEq)
    exact Concrete.Splice.Input.PlugLayout.RegionRoute.distinctSibling_away
      source.property.diagram_well_formed tail childParent siblingParent
        siblingNe
  have sourceGet' : Concrete.Elaboration.compileOccurrenceWith?
      source.val.diagram
      (Concrete.Elaboration.compileRegion? source.val.diagram sourceFuel)
      sourceContext sourceBinders occurrence =
        some (sourceItems.get index) := by
    simpa [occurrence, occurrenceIndex] using sourceGet
  have targetGet' : Concrete.Elaboration.compileOccurrenceWith?
      (Target trace)
      (Concrete.Elaboration.compileRegion? (Target trace) targetFuel)
      targetContext targetBinders
      (promoteOccurrence trace
        (promotedTarget source.val.diagram
          source.property.diagram_well_formed trace) occurrence) =
        some (targetItems.get (positions index)) := by
    have promotedEq : promoteOccurrence trace
          ((Domain source.val.diagram outer trace.inner).index region
            regionSurvives) occurrence =
        promoteOccurrence trace
          (promotedTarget source.val.diagram
            source.property.diagram_well_formed trace) occurrence := by
      cases occurrenceEq : occurrence with
      | node node => rfl
      | child sibling =>
          simp [promoteOccurrence, childrenSurvive sibling occurrenceEq]
    rw [← promotedEq]
    simpa [positions, occurrencePositions, sourceLength, targetLength,
      occurrenceIndex] using targetGet
  have compiledIso := compileOccurrence_promotion source.val.diagram
    source.property.diagram_well_formed trace targetWellFormed region
    ((domain_survives_iff source.val.diagram outer trace.inner region).1
      regionSurvives |>.1)
    sourceContext targetContext ambient wireAgreement
    sourceExact
    (by
      rw [promote_survivor_eq source trace region regionSurvives]
      exact targetExact)
    sourceBinders targetBinders binderAgreement occurrence occurrenceMem
    childrenSurvive childrenAway sourceGet' targetGet'
  exact (ItemIso.renameWiresEquiv (sourceItems.get index) ambient).trans
    compiledIso

noncomputable def compilerBodyOuterWire
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf sourceDiagram
      sourceRegion (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf targetDiagram
      targetRegion (.here targetBody))
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length)) :
    FiniteEquiv (Fin sourceOuter) (Fin targetOuter) :=
  (FiniteEquiv.finCast sourceState.inheritedLength).symm |>.trans
    (inherited.trans (FiniteEquiv.finCast targetState.inheritedLength))

private theorem append_agreement
    {sourceAmbient sourceLocal targetAmbient targetLocal : List α}
    (ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length))
    (localEquiv : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length))
    (ambientAgreement : ∀ index,
      targetAmbient.get (ambient index) = sourceAmbient.get index)
    (localAgreement : ∀ index,
      targetLocal.get (localEquiv index) = sourceLocal.get index) :
    ∀ index,
      (targetAmbient ++ targetLocal).get
          (Concrete.Elaboration.appendContextEquiv ambient localEquiv index) =
        (sourceAmbient ++ sourceLocal).get index := by
  intro index
  let sumIndex : Fin (sourceAmbient.length + sourceLocal.length) :=
    Fin.cast (by simp) index
  have sourceIndex : Fin.cast (by simp) sumIndex = index := by
    apply Fin.ext
    rfl
  rw [← sourceIndex]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) sumIndex
  · simp only [Concrete.Elaboration.get_append_castAdd]
    calc
      _ = (targetAmbient ++ targetLocal).get
          (Fin.cast (by simp)
            (Fin.castAdd targetLocal.length (ambient outerIndex))) := by
        congr 1
        apply Fin.ext
        simp [Concrete.Elaboration.appendContextEquiv,
          Concrete.Elaboration.castFinEquiv, extendWireEquiv]
      _ = targetAmbient.get (ambient outerIndex) :=
        Concrete.Elaboration.get_append_castAdd targetAmbient targetLocal _
      _ = sourceAmbient.get outerIndex := ambientAgreement outerIndex
  · simp only [Concrete.Elaboration.get_append_natAdd]
    calc
      _ = (targetAmbient ++ targetLocal).get
          (Fin.cast (by simp)
            (Fin.natAdd targetAmbient.length (localEquiv localIndex))) := by
        congr 1
        apply Fin.ext
        simp [Concrete.Elaboration.appendContextEquiv,
          Concrete.Elaboration.castFinEquiv, extendWireEquiv]
      _ = targetLocal.get (localEquiv localIndex) :=
        Concrete.Elaboration.get_append_natAdd targetAmbient targetLocal _
      _ = sourceLocal.get localIndex := localAgreement localIndex

private noncomputable def compilerLeafFrame
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {region child : Fin source.val.diagram.regionCount} {rest : List Nat}
    (regionSurvives :
      (Domain source.val.diagram outer trace.inner).survives region = true)
    (regionNeTarget : region ≠ trace.target)
    (childParent : (source.val.diagram.regions child).parent? = some region)
    (sourcePosition : Fin (Concrete.Elaboration.localOccurrences
      source.val.diagram region).length)
    (sourcePositionEq : indexOf?
      (Concrete.Elaboration.localOccurrences source.val.diagram region)
      (.child child) = some sourcePosition)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      trace.target rest)
    {sourceOuter sourceLocal targetOuter targetLocal : Nat} {rels : RelCtx}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) rels}
    {targetItems : ItemSeq (targetOuter + targetLocal) rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      source.val.diagram region (.here (.mk sourceLocal sourceItems)))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Target trace)
      ((Domain source.val.diagram outer trace.inner).index region
        regionSurvives) (.here (.mk targetLocal targetItems)))
    (sourceLocalCanonical : sourceLocal =
      (Concrete.Elaboration.exactScopeWires source.val.diagram region).length)
    (targetLocalCanonical : targetLocal =
      (Concrete.Elaboration.exactScopeWires (Target trace)
        ((Domain source.val.diagram outer trace.inner).index region
          regionSurvives)).length)
    (sourceItemsCanonical : HEq sourceItems sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetItems targetState.canonicalBodyItems)
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length))
    (wireAgreement : ∀ index,
      targetState.inheritedWires.get (inherited index) =
        sourceState.inheritedWires.get index)
    (binderAgreement : ∀ binder, targetState.binders binder =
      sourceState.binders
        ((Domain source.val.diagram outer trace.inner).origin binder))
    (sourceIndex : Fin sourceItems.length)
    (targetIndex : Fin targetItems.length)
    (sourceIndexVal : sourceIndex.val = sourcePosition.val)
    (targetIndexVal : targetIndex.val =
      (localOccurrenceEquiv source.val.diagram
        source.property.diagram_well_formed trace region regionSurvives
        regionNeTarget sourcePosition).val) :
    let outerWire := compilerBodyOuterWire sourceState targetState inherited
    let localWire := (FiniteEquiv.finCast sourceLocalCanonical).trans
      ((localWireEquiv source.val.diagram
        source.property.diagram_well_formed trace region regionSurvives
          regionNeTarget).trans
        (FiniteEquiv.finCast targetLocalCanonical.symm))
    ItemSeqIso.Frame (source := sourceItems)
      (target := targetItems) (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex := by
  dsimp only
  subst sourceLocal
  subst targetLocal
  let targetRegion :=
    (Domain source.val.diagram outer trace.inner).index region regionSurvives
  let outerWire := compilerBodyOuterWire sourceState targetState inherited
  let localWire := localWireEquiv source.val.diagram
    source.property.diagram_well_formed trace region regionSurvives
      regionNeTarget
  let sourceExtended := sourceState.inheritedWires.extend region
  let targetExtended := targetState.inheritedWires.extend targetRegion
  let extendedEquiv := Concrete.Elaboration.appendContextEquiv inherited localWire
  have extendedAgreement : ∀ index,
      targetExtended.get (extendedEquiv index) =
        sourceExtended.get index := by
    exact append_agreement inherited localWire wireAgreement
      (localWireEquiv_spec source.val.diagram
        source.property.diagram_well_formed trace region regionSurvives
          regionNeTarget)
  let sourceCast : FiniteEquiv (Fin sourceExtended.length)
      (Fin (sourceOuter +
        (Concrete.Elaboration.exactScopeWires
          source.val.diagram region).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      sourceState.inheritedWires region)).trans
      (FiniteEquiv.finCast (congrArg
        (fun inheritedLength => inheritedLength +
          (Concrete.Elaboration.exactScopeWires
            source.val.diagram region).length)
        sourceState.inheritedLength))
  let targetCast : FiniteEquiv (Fin targetExtended.length)
      (Fin (targetOuter +
        (Concrete.Elaboration.exactScopeWires
          (Target trace) targetRegion).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      targetState.inheritedWires targetRegion)).trans
      (FiniteEquiv.finCast (congrArg
        (fun inheritedLength => inheritedLength +
          (Concrete.Elaboration.exactScopeWires
            (Target trace) targetRegion).length)
        targetState.inheritedLength))
  have sourceCanonicalEq : sourceItems =
      sourceState.items.renameWires sourceCast := by
    have core := eq_of_heq sourceItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    exact core.trans ((ItemSeq.renameWires_comp sourceState.items _ _).trans (by
      apply congrArg (sourceState.items.renameWires ·)
      funext index
      rfl))
  have targetCanonicalEq : targetItems =
      targetState.items.renameWires targetCast := by
    have core := eq_of_heq targetItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    exact core.trans ((ItemSeq.renameWires_comp targetState.items _ _).trans (by
      apply congrArg (targetState.items.renameWires ·)
      funext index
      rfl))
  let sourceRenamedIndex : Fin
      (sourceState.items.renameWires sourceCast).length :=
    Fin.cast (congrArg ItemSeq.length sourceCanonicalEq) sourceIndex
  let targetRenamedIndex : Fin
      (targetState.items.renameWires targetCast).length :=
    Fin.cast (congrArg ItemSeq.length targetCanonicalEq) targetIndex
  let rawSourceIndex :=
    (sourceState.items.renameWiresPositionEquiv sourceCast).symm
      sourceRenamedIndex
  let rawTargetIndex :=
    (targetState.items.renameWiresPositionEquiv targetCast).symm
      targetRenamedIndex
  have rawSourceVal : rawSourceIndex.val = sourcePosition.val := by
    simpa [rawSourceIndex, sourceRenamedIndex,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using sourceIndexVal
  have rawTargetVal : rawTargetIndex.val =
      (localOccurrenceEquiv source.val.diagram
        source.property.diagram_well_formed trace region regionSurvives
        regionNeTarget sourcePosition).val := by
    simpa [rawTargetIndex, targetRenamedIndex,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using targetIndexVal
  let rawFrame := compilerRawFrame source trace targetWellFormed
    regionSurvives regionNeTarget childParent sourcePosition sourcePositionEq
    tail sourceExtended targetExtended extendedEquiv extendedAgreement
    sourceState.wiresExact targetState.wiresExact sourceState.binders
    targetState.binders binderAgreement sourceState.itemsComputation
    targetState.itemsComputation rawSourceIndex rawTargetIndex rawSourceVal
    rawTargetVal
  have sourceUndo : sourceItems.renameWires sourceCast.symm =
      sourceState.items := by
    calc
      sourceItems.renameWires sourceCast.symm =
          (sourceState.items.renameWires sourceCast).renameWires
            sourceCast.symm := congrArg
              (fun items => items.renameWires sourceCast.symm) sourceCanonicalEq
      _ = sourceState.items.renameWires
          (sourceCast.symm.toFun ∘ sourceCast.toFun) :=
        ItemSeq.renameWires_comp sourceState.items sourceCast sourceCast.symm
      _ = sourceState.items := by
        have identity : sourceCast.symm.toFun ∘ sourceCast.toFun = id := by
          funext index
          exact sourceCast.left_inv index
        rw [identity]
        exact ItemSeq.renameWires_id sourceState.items
  have targetPush : targetState.items.renameWires targetCast = targetItems :=
    targetCanonicalEq.symm
  let finalWire := extendWireEquiv outerWire localWire
  have wireFactor :
      (sourceCast.symm.trans extendedEquiv).trans targetCast = finalWire := by
    have sourceChildExtended : sourceOuter +
          (Concrete.Elaboration.exactScopeWires
            source.val.diagram region).length = sourceExtended.length :=
      (congrArg
          (fun inheritedLength => inheritedLength +
            (Concrete.Elaboration.exactScopeWires
              source.val.diagram region).length)
          sourceState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region).symm
    have targetChildExtended : targetOuter +
          (Concrete.Elaboration.exactScopeWires
            (Target trace) targetRegion).length = targetExtended.length :=
      (congrArg
          (fun inheritedLength => inheritedLength +
            (Concrete.Elaboration.exactScopeWires
              (Target trace) targetRegion).length)
          targetState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires targetRegion).symm
    have algebra :=
      Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
        sourceChildExtended
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region)
        sourceState.inheritedLength
        (rfl : sourceOuter +
          (Concrete.Elaboration.exactScopeWires
            source.val.diagram region).length = _)
        (rfl : (Concrete.Elaboration.exactScopeWires
          source.val.diagram region).length = _)
        targetChildExtended
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires targetRegion)
        targetState.inheritedLength
        (rfl : targetOuter + (Concrete.Elaboration.exactScopeWires
          (Target trace) targetRegion).length = _)
        (rfl : (Concrete.Elaboration.exactScopeWires
          (Target trace) targetRegion).length = _)
        inherited localWire
    simpa [sourceCast, targetCast, extendedEquiv, finalWire, outerWire,
      sourceExtended, targetExtended] using algebra
  obtain ⟨sourceIndex', targetIndex', sourceVal, targetVal, frame⟩ :=
    ItemSeqIso.Frame.pullPush sourceCast.symm extendedEquiv targetCast
      finalWire sourceUndo targetPush wireFactor rawFrame
  have sourceIndexEq : sourceIndex' = sourceIndex := by
    apply Fin.ext
    exact sourceVal.trans (by
      change rawSourceIndex.val = sourceIndex.val
      simp [rawSourceIndex, sourceRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  have targetIndexEq : targetIndex' = targetIndex := by
    apply Fin.ext
    exact targetVal.trans (by
      change rawTargetIndex.val = targetIndex.val
      simp [rawTargetIndex, targetRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  subst sourceIndex'
  subst targetIndex'
  simpa only [finalWire] using frame

private theorem target_root_scope_iff
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root)
    (wire : Fin source.val.diagram.wireCount) :
    ((Target trace).wires wire).scope = (Target trace).root ↔
      (source.val.diagram.wires wire).scope = source.val.diagram.root := by
  rw [target_root_eq source trace,
    target_wire_scope source.val.diagram
      source.property.diagram_well_formed trace wire]
  have rootNeInner :=
    (domain_survives_iff source.val.diagram outer trace.inner
      source.val.diagram.root).1 (root_survives source trace) |>.2
  constructor
  · intro equality
    have origins := congrArg
      (Domain source.val.diagram outer trace.inner).origin equality
    rw [promoteRegionIndex_origin,
      (Domain source.val.diagram outer trace.inner).origin_index] at origins
    by_cases innerCase : (source.val.diagram.wires wire).scope = trace.inner
    · simp [innerCase] at origins
      exact False.elim (rootNe origins)
    · simpa [innerCase] using origins
  · intro equality
    have innerCase : (source.val.diagram.wires wire).scope ≠ trace.inner := by
      intro scopeInner
      exact rootNeInner (equality.symm.trans scopeInner)
    apply (Domain source.val.diagram outer trace.inner).origin_injective
    rw [promoteRegionIndex_origin,
      (Domain source.val.diagram outer trace.inner).origin_index]
    simpa [innerCase] using equality

@[simp] theorem targetOpen_exposedWires
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw) :
    (targetOpen source trace).exposedWires = source.val.exposedWires := rfl

private theorem target_root_exactScopeWires
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root) :
    Concrete.Elaboration.exactScopeWires (Target trace) (Target trace).root =
      Concrete.Elaboration.exactScopeWires source.val.diagram
        source.val.diagram.root := by
  unfold Concrete.Elaboration.exactScopeWires
  apply congrArg filterFin
  funext wire
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    target_root_scope_iff source trace rootNe wire

@[simp] theorem targetOpen_hiddenWires
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root) :
    (targetOpen source trace).hiddenWires = source.val.hiddenWires := by
  unfold Concrete.OpenDiagram.hiddenWires
  change (Concrete.Elaboration.exactScopeWires
      (Target trace) (Target trace).root).filter _ = _
  rw [target_root_exactScopeWires source trace rootNe]
  rfl

@[simp] theorem targetOpen_rootWires
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root) :
    (targetOpen source trace).rootWires = source.val.rootWires := by
  simp [Concrete.OpenDiagram.rootWires, targetOpen_hiddenWires source trace rootNe]
  rfl

private theorem list_get_cast
    {source target : List α} (equality : source = target)
    (index : Fin source.length) :
    target.get (Fin.cast (congrArg List.length equality) index) =
      source.get index := by
  subst target
  rfl

private noncomputable def openRootRawFrame
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed)
    {child : Fin source.val.diagram.regionCount} {rest : List Nat}
    (childParent : (source.val.diagram.regions child).parent? =
      some source.val.diagram.root)
    (sourcePosition : Fin (Concrete.Elaboration.localOccurrences
      source.val.diagram source.val.diagram.root).length)
    (sourcePositionEq : indexOf?
      (Concrete.Elaboration.localOccurrences source.val.diagram
        source.val.diagram.root) (.child child) = some sourcePosition)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      trace.target rest)
    {sourceBody targetBody : Region source.val.exposedWires.length []}
    (sourceState : Concrete.Splice.OpenRootCompilerState source sourceBody)
    (targetState : Concrete.Splice.OpenRootCompilerState
      (checkedTarget source trace targetWellFormed) targetBody)
    (sourceIndex : Fin sourceState.items.length)
    (targetIndex : Fin targetState.items.length)
    (sourceIndexVal : sourceIndex.val = sourcePosition.val)
    (targetIndexVal : targetIndex.val =
      (localOccurrenceEquiv source.val.diagram
        source.property.diagram_well_formed trace source.val.diagram.root
        (root_survives source trace) rootNe.symm sourcePosition).val) :
    ItemSeqIso.Frame
      (FiniteEquiv.finCast (congrArg List.length
        (targetOpen_rootWires source trace rootNe).symm))
      sourceIndex targetIndex := by
  let target := checkedTarget source trace targetWellFormed
  let equality := targetOpen_rootWires source trace rootNe
  let ambient := FiniteEquiv.finCast
    (congrArg List.length equality).symm
  have agreement : ∀ index,
      target.val.rootWires.get (ambient index) =
        source.val.rootWires.get index := by
    intro index
    exact list_get_cast equality.symm index
  have targetExact := Concrete.Elaboration.openRootWires_exact target.property
  change Concrete.Elaboration.WireContext.Exact
    (targetOpen source trace).rootWires (Target trace).root at targetExact
  rw [target_root_eq source trace] at targetExact
  apply compilerRawFrame source trace targetWellFormed
    (root_survives source trace) rootNe.symm childParent sourcePosition
    sourcePositionEq tail source.val.rootWires target.val.rootWires ambient
    agreement (Concrete.Elaboration.openRootWires_exact source.property)
    targetExact Concrete.Elaboration.BinderContext.empty
    Concrete.Elaboration.BinderContext.empty (by intro binder; rfl)
    sourceState.itemsComputation
    (by simpa [target, checkedTarget, targetOpen,
      target_root_eq source trace] using targetState.itemsComputation)
    sourceIndex targetIndex sourceIndexVal targetIndexVal

private noncomputable def openRootFrame
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed)
    {sourceLocal targetLocal : Nat}
    {sourceSeq : ItemSeq (source.val.exposedWires.length + sourceLocal) []}
    {targetSeq : ItemSeq
      ((targetOpen source trace).exposedWires.length + targetLocal) []}
    (sourceState : Concrete.Splice.OpenRootCompilerState source
      (.mk sourceLocal sourceSeq))
    (targetState : Concrete.Splice.OpenRootCompilerState
      (checkedTarget source trace targetWellFormed)
      (.mk targetLocal targetSeq))
    (sourceLocalCanonical : sourceLocal = source.val.hiddenWires.length)
    (targetLocalCanonical : targetLocal =
      (targetOpen source trace).hiddenWires.length)
    (sourceItemsCanonical : HEq sourceSeq sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetSeq targetState.canonicalBodyItems)
    {sourceIndex : Fin sourceState.items.length}
    {targetIndex : Fin targetState.items.length}
    (rawFrame : ItemSeqIso.Frame
      (FiniteEquiv.finCast (congrArg List.length
        (targetOpen_rootWires source trace rootNe).symm))
      sourceIndex targetIndex) :
    ItemSeqIso.Frame.Indexed sourceSeq targetSeq
      (extendWireEquiv
        (FiniteEquiv.finCast (congrArg List.length
          (targetOpen_exposedWires source trace).symm))
        ((FiniteEquiv.finCast sourceLocalCanonical).trans
          ((FiniteEquiv.finCast (congrArg List.length
            (targetOpen_hiddenWires source trace rootNe).symm)).trans
            (FiniteEquiv.finCast targetLocalCanonical.symm))))
      sourceIndex.val targetIndex.val := by
  subst sourceLocal
  subst targetLocal
  let target := checkedTarget source trace targetWellFormed
  let sourceEq : source.val.rootWires.length =
      source.val.exposedWires.length + source.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let targetEq : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let firstWire := FiniteEquiv.finCast sourceEq.symm
  let middleWire := FiniteEquiv.finCast (congrArg List.length
    (targetOpen_rootWires source trace rootNe).symm)
  let lastWire := FiniteEquiv.finCast targetEq
  let outerWire := FiniteEquiv.finCast (congrArg List.length
    (targetOpen_exposedWires source trace).symm)
  let localWire := FiniteEquiv.finCast (congrArg List.length
    (targetOpen_hiddenWires source trace rootNe).symm)
  let finalWire := extendWireEquiv outerWire localWire
  have sourcePull : sourceSeq.renameWires firstWire = sourceState.items := by
    have canonical : sourceSeq = sourceState.canonicalBodyItems :=
      eq_of_heq sourceItemsCanonical
    conv => lhs; rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    rw [ItemSeq.renameWires_comp]
    have identity : firstWire.toFun ∘
        Fin.cast (by simp [Concrete.OpenDiagram.rootWires]) = id := by
      funext index
      apply Fin.ext
      rfl
    rw [identity]
    exact ItemSeq.renameWires_id sourceState.items
  have targetPush : targetState.items.renameWires lastWire = targetSeq := by
    have canonical : targetSeq = targetState.canonicalBodyItems :=
      eq_of_heq targetItemsCanonical
    conv => rhs; rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    apply congrArg (targetState.items.renameWires ·)
    funext index
    apply Fin.ext
    rfl
  have wireFactor : (firstWire.trans middleWire).trans lastWire =
      finalWire := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    refine Fin.addCases (fun outerIndex => ?_)
      (fun localIndex => ?_) index
    · simp [firstWire, middleWire, lastWire, finalWire, outerWire,
        localWire, extendWireEquiv, FiniteEquiv.finCast]
    · simp [firstWire, middleWire, lastWire, finalWire, outerWire,
        localWire, extendWireEquiv, FiniteEquiv.finCast,
        targetOpen_exposedWires]
  simpa only [finalWire] using
    ItemSeqIso.Frame.pullPush firstWire middleWire lastWire finalWire
      sourcePull targetPush wireFactor rawFrame

structure CompilerTraceAlignment
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourcePath targetPath : List Nat}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (targetWitness : Region.ContextPath targetBody targetPath) where
  holeRelsEq : sourceWitness.toFocus.holeRels =
    targetWitness.toFocus.holeRels
  holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
    (Fin targetWitness.toFocus.holeWires)
  contexts : DiagramContextIso outerWire holeWire rels
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.context
    (holeRelsEq.symm ▸ targetWitness.toFocus.context)

structure TraceAlignmentResult
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourcePath targetPath : List Nat}
    {sourceStart : Fin source.val.diagram.regionCount}
    {sourceSite : Fin source.val.diagram.regionCount}
    {targetStart : Fin (Target trace).regionCount}
    {targetSite : Fin (Target trace).regionCount}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram sourceStart
      sourceSite sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
      targetSite targetPath}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      source.val.diagram sourceStart (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Target trace) targetStart (.here targetBody))
    (sourceTrace : Concrete.Splice.CompilerTrace source.val.diagram sourceRoute
      sourceWitness sourceState)
    (targetTrace : Concrete.Splice.CompilerTrace (Target trace) targetRoute
      targetWitness targetState)
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)) where
  alignment : CompilerTraceAlignment outerWire sourceWitness targetWitness
  leafWire : FiniteEquiv (Fin sourceTrace.leaf.inheritedWires.length)
    (Fin targetTrace.leaf.inheritedWires.length)
  holeWire_leaf : alignment.holeWire =
    (FiniteEquiv.finCast sourceTrace.leaf.inheritedLength).symm.trans
      (leafWire.trans (FiniteEquiv.finCast
        targetTrace.leaf.inheritedLength))
  leafWireAgreement : ∀ index,
    targetTrace.leaf.inheritedWires.get (leafWire index) =
      sourceTrace.leaf.inheritedWires.get index
  leafBinderAgreement : ∀ binder, targetTrace.leaf.binders binder =
    alignment.holeRelsEq ▸ sourceTrace.leaf.binders
      ((Domain source.val.diagram outer trace.inner).origin binder)

private theorem pushBinderAgreement
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (child : Fin source.val.diagram.regionCount)
    (childSurvives :
      (Domain source.val.diagram outer trace.inner).survives child = true)
    (sourceBinders : Concrete.Elaboration.BinderContext
      source.val.diagram rels)
    (targetBinders : Concrete.Elaboration.BinderContext (Target trace) rels)
    (agreement : ∀ binder, targetBinders binder = sourceBinders
      ((Domain source.val.diagram outer trace.inner).origin binder))
    (arity : Nat) : ∀ binder,
    (targetBinders.push
      ((Domain source.val.diagram outer trace.inner).index child childSurvives)
      arity) binder =
    (sourceBinders.push child arity)
      ((Domain source.val.diagram outer trace.inner).origin binder) := by
  intro binder
  by_cases equality : binder =
      (Domain source.val.diagram outer trace.inner).index child childSurvives
  · subst binder
    rw [(Domain source.val.diagram outer trace.inner).origin_index]
    simp
  · have originNe :
        (Domain source.val.diagram outer trace.inner).origin binder ≠ child := by
      intro originEq
      apply equality
      apply (Domain source.val.diagram outer trace.inner).origin_injective
      rw [(Domain source.val.diagram outer trace.inner).origin_index]
      exact originEq
    rw [Concrete.Elaboration.BinderContext.push_other _ _ equality,
      Concrete.Elaboration.BinderContext.push_other _ _ originNe,
      agreement]

private theorem childInheritedAgreement
    {sourceAmbient sourceLocal targetAmbient targetLocal : List α}
    {sourceChild targetChild : List α}
    (sourceEq : sourceChild = sourceAmbient ++ sourceLocal)
    (targetEq : targetChild = targetAmbient ++ targetLocal)
    (ambient : FiniteEquiv (Fin sourceAmbient.length)
      (Fin targetAmbient.length))
    (localWire : FiniteEquiv (Fin sourceLocal.length)
      (Fin targetLocal.length))
    (ambientAgreement : ∀ index,
      targetAmbient.get (ambient index) = sourceAmbient.get index)
    (localAgreement : ∀ index,
      targetLocal.get (localWire index) = sourceLocal.get index) :
    let childWire := (FiniteEquiv.finCast (congrArg List.length sourceEq)).trans
      ((Concrete.Elaboration.appendContextEquiv ambient localWire).trans
        (FiniteEquiv.finCast (congrArg List.length targetEq).symm))
    ∀ index, targetChild.get (childWire index) = sourceChild.get index := by
  subst sourceChild
  subst targetChild
  simpa using append_agreement ambient localWire ambientAgreement localAgreement

private noncomputable def compilerTraceContextIso_aux
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {sourceStart : Fin source.val.diagram.regionCount}
    {targetStart : Fin (Target trace).regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram sourceStart
      trace.target sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) targetPath}
    (routeAlignment : RouteAlignment source trace sourceRoute targetRoute) :
    ∀ {actualSourceStart : Fin source.val.diagram.regionCount}
      {actualTargetStart : Fin (Target trace).regionCount}
      {actualSourceSite : Fin source.val.diagram.regionCount}
      {actualTargetSite : Fin (Target trace).regionCount}
      {actualSourcePath actualTargetPath : List Nat}
      (_sourceStartEq : actualSourceStart = sourceStart)
      (_targetStartEq : actualTargetStart = targetStart)
      (_sourceSiteEq : actualSourceSite = trace.target)
      (_targetSiteEq : actualTargetSite = promotedTarget source.val.diagram
        source.property.diagram_well_formed trace)
      (_sourcePathEq : actualSourcePath = sourcePath)
      (_targetPathEq : actualTargetPath = targetPath)
      {actualSourceRoute : Concrete.Splice.RegionRoute source.val.diagram
        actualSourceStart actualSourceSite actualSourcePath}
      {actualTargetRoute : Concrete.Splice.RegionRoute (Target trace)
        actualTargetStart actualTargetSite actualTargetPath}
      {sourceOuter targetOuter : Nat} {rels : RelCtx}
      {sourceBody : Region sourceOuter rels}
      {targetBody : Region targetOuter rels}
      {sourceWitness : Region.ContextPath sourceBody actualSourcePath}
      {targetWitness : Region.ContextPath targetBody actualTargetPath}
      (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
        source.val.diagram actualSourceStart (.here sourceBody))
      (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
        (Target trace) actualTargetStart (.here targetBody))
      (sourceTrace : Concrete.Splice.CompilerTrace source.val.diagram
        actualSourceRoute sourceWitness sourceState)
      (targetTrace : Concrete.Splice.CompilerTrace (Target trace)
        actualTargetRoute targetWitness targetState)
      (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
        (Fin targetState.inheritedWires.length))
      (_wireAgreement : ∀ index,
        targetState.inheritedWires.get (inherited index) =
          sourceState.inheritedWires.get index)
      (_binderAgreement : ∀ binder, targetState.binders binder =
        sourceState.binders
          ((Domain source.val.diagram outer trace.inner).origin binder)),
      let outerWire := compilerBodyOuterWire sourceState targetState inherited
      TraceAlignmentResult source trace sourceWitness targetWitness
        sourceState targetState sourceTrace targetTrace outerWire := by
  induction routeAlignment with
  | here =>
      intro actualSourceStart actualTargetStart actualSourceSite actualTargetSite
        actualSourcePath actualTargetPath sourceStartEq targetStartEq
        sourceSiteEq targetSiteEq sourcePathEq targetPathEq actualSourceRoute
        actualTargetRoute sourceOuter targetOuter rels sourceBody targetBody
        sourceWitness targetWitness sourceState targetState sourceTrace
        targetTrace inherited wireAgreement binderAgreement
      subst actualSourceStart
      subst actualTargetStart
      subst actualSourcePath
      subst actualTargetPath
      cases sourceTrace using @Concrete.Splice.CompilerTrace.casesOn
          source.val.diagram with
      | here sourceState =>
          cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
              (Target trace) with
          | here targetState =>
              exact {
                alignment := {
                  holeRelsEq := rfl
                  holeWire := compilerBodyOuterWire sourceState targetState
                    inherited
                  contexts := .hole _
                }
                leafWire := inherited
                holeWire_leaf := rfl
                leafWireAgreement := wireAgreement
                leafBinderAgreement := binderAgreement
              }
  | @step start child alignedSourceRest alignedTargetRest sourceParent
      alignedSourcePosition alignedSourcePositionEq sourceTail startSurvives
      childSurvives targetParent alignedTargetPosition alignedTargetPositionEq
      targetTail positionEq tail induction =>
      intro actualSourceStart actualTargetStart actualSourceSite actualTargetSite
        actualSourcePath actualTargetPath sourceStartEq targetStartEq
        sourceSiteEq targetSiteEq sourcePathEq targetPathEq actualSourceRoute
        actualTargetRoute sourceOuter targetOuter rels sourceBody targetBody
        sourceWitness targetWitness sourceState targetState sourceTrace
        targetTrace inherited wireAgreement binderAgreement
      subst actualSourceStart
      subst actualTargetStart
      cases sourceTrace using @Concrete.Splice.CompilerTrace.casesOn
          source.val.diagram with
      | here => simp at sourcePathEq
      | @cut sourceStart sourceChild sourceEnd sourceRest sourceParent
          sourcePosition sourcePositionEq sourceTail sourceOuter sourceLocal
          sourceRels sourceSeq sourceFocus sourceChildBody sourceAt sourceIsCut
          sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
          sourceChildState sourceChildKind sourceInherited sourceBinders
          sourceFuel sourceTailTrace =>
          cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
              (Target trace) with
          | here => simp at targetPathEq
          | @cut targetStart targetChild targetEnd targetRest targetParent
              targetPosition targetPositionEq targetTail targetOuter targetLocal
              targetRels targetSeq targetFocus targetChildBody targetAt
              targetIsCut targetNested targetState targetLocalCanonical
              targetItemsCanonical targetChildState targetChildKind
              targetInherited targetBinders targetFuel targetTailTrace =>
              have sourcePositionVal : sourcePosition.val =
                  alignedSourcePosition.val := (List.cons.inj sourcePathEq).1
              have targetPositionVal : targetPosition.val =
                  alignedTargetPosition.val := (List.cons.inj targetPathEq).1
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext sourcePositionVal
              have targetPositionAlign : targetPosition =
                  alignedTargetPosition := Fin.ext targetPositionVal
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) =
                  .cut ((Domain source.val.diagram outer trace.inner).index
                    start startSurvives) := by
                rw [promoted_cut source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    start).1 startSurvives |>.1) childSurvives sourceChildKind,
                  promote_survivor_eq source trace start startSurvives]
              have targetKindEq := targetChildKind.symm.trans targetKind
              cases Concrete.CRegion.cut.inj targetKindEq
              have sourceTailCanonical : Concrete.Splice.RegionRoute
                  source.val.diagram child trace.target sourceRest :=
                sourceSiteEq ▸ sourceTail
              let rawLocalWire := localWireEquiv source.val.diagram
                source.property.diagram_well_formed trace start startSurvives
                (route_start_ne_target source trace sourceParent
                  sourceTailCanonical)
              let childWire :=
                (FiniteEquiv.finCast
                    (congrArg List.length sourceInherited)).trans
                  ((Concrete.Elaboration.appendContextEquiv inherited
                    rawLocalWire).trans
                    (FiniteEquiv.finCast
                      (congrArg List.length targetInherited).symm))
              have childWireAgreement : ∀ index,
                  targetChildState.inheritedWires.get (childWire index) =
                    sourceChildState.inheritedWires.get index := by
                exact childInheritedAgreement sourceInherited targetInherited
                  inherited rawLocalWire wireAgreement
                    (localWireEquiv_spec source.val.diagram
                      source.property.diagram_well_formed trace start
                      startSurvives
                      (route_start_ne_target source trace sourceParent
                        sourceTailCanonical))
              have childBinderAgreement : ∀ binder,
                  targetChildState.binders binder =
                    sourceChildState.binders
                      ((Domain source.val.diagram outer trace.inner).origin
                        binder) := by
                rw [sourceBinders, targetBinders]
                exact binderAgreement
              have sourceRestEq : sourceRest = alignedSourceRest :=
                (List.cons.inj sourcePathEq).2
              have targetRestEq : targetRest = alignedTargetRest :=
                (List.cons.inj targetPathEq).2
              let childResult := induction rfl rfl sourceSiteEq
                targetSiteEq sourceRestEq targetRestEq sourceChildState
                targetChildState sourceTailTrace targetTailTrace childWire
                childWireAgreement childBinderAgreement
              let outerWire := compilerBodyOuterWire sourceState targetState
                inherited
              let localWire :=
                (FiniteEquiv.finCast sourceLocalCanonical).trans
                  (rawLocalWire.trans
                    (FiniteEquiv.finCast targetLocalCanonical.symm))
              let sourceIndex : Fin sourceSeq.length :=
                ⟨alignedSourcePosition.val,
                  ItemSeq.focusAt?_index_lt sourceSeq
                    alignedSourcePosition.val sourceFocus sourceAt⟩
              let targetIndex : Fin targetSeq.length :=
                ⟨alignedTargetPosition.val,
                  ItemSeq.focusAt?_index_lt targetSeq
                    alignedTargetPosition.val targetFocus targetAt⟩
              let frame := compilerLeafFrame source trace
                targetWellFormed startSurvives
                (route_start_ne_target source trace sourceParent
                  sourceTailCanonical)
                sourceParent alignedSourcePosition alignedSourcePositionEq
                sourceTailCanonical sourceState targetState
                sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
                targetItemsCanonical inherited wireAgreement binderAgreement
                sourceIndex targetIndex rfl
                (congrArg Fin.val positionEq)
              have childOuterEq : compilerBodyOuterWire sourceChildState
                    targetChildState childWire =
                  extendWireEquiv outerWire localWire := by
                have algebra :=
                  Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
                    (sourceChildState.inheritedLength.symm.trans
                      (congrArg List.length sourceInherited))
                    (Concrete.Elaboration.WireContext.length_extend
                      sourceState.inheritedWires start)
                    sourceState.inheritedLength
                    (rfl : sourceOuter + sourceLocal = _)
                    sourceLocalCanonical
                    (targetChildState.inheritedLength.symm.trans
                      (congrArg List.length targetInherited))
                    (Concrete.Elaboration.WireContext.length_extend
                      targetState.inheritedWires
                        ((Domain source.val.diagram outer trace.inner).index
                          start startSurvives))
                    targetState.inheritedLength
                    (rfl : targetOuter + targetLocal = _)
                    targetLocalCanonical inherited rawLocalWire
                simpa [childWire, outerWire, localWire,
                  compilerBodyOuterWire,
                  Concrete.Elaboration.appendContextEquiv,
                  Concrete.Elaboration.castFinEquiv] using algebra
              have childContexts : DiagramContextIso
                  (extendWireEquiv outerWire localWire)
                  childResult.alignment.holeWire rels
                  sourceNested.toFocus.holeRels
                  sourceNested.toFocus.context
                  (childResult.alignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
                rw [← childOuterEq]
                exact childResult.alignment.contexts
              have targetContextTransport :
                  childResult.alignment.holeRelsEq.symm ▸
                      DiagramContext.cut targetLocal targetFocus.before
                        targetFocus.after targetNested.toFocus.context =
                    DiagramContext.cut targetLocal targetFocus.before
                      targetFocus.after
                      (childResult.alignment.holeRelsEq.symm ▸
                        targetNested.toFocus.context) :=
                DiagramContext.cut_transport_holeRels
                  childResult.alignment.holeRelsEq targetFocus.before
                    targetFocus.after targetNested.toFocus.context
              have contexts := DiagramContextIso.cutFrame localWire sourceFocus
                targetFocus sourceAt targetAt frame
                sourceNested.toFocus.context
                (childResult.alignment.holeRelsEq.symm ▸
                  targetNested.toFocus.context) childContexts
              exact {
                alignment := {
                  holeRelsEq := childResult.alignment.holeRelsEq
                  holeWire := childResult.alignment.holeWire
                  contexts := by
                    simpa only [Region.ContextPath.toFocus,
                      targetContextTransport] using contexts
                }
                leafWire := childResult.leafWire
                holeWire_leaf := childResult.holeWire_leaf
                leafWireAgreement := childResult.leafWireAgreement
                leafBinderAgreement := childResult.leafBinderAgreement
              }
          | @bubble targetStart targetChild targetEnd targetRest targetParent
              targetPosition targetPositionEq targetTail targetOuter targetLocal
              targetArity targetRels targetSeq targetFocus targetChildBody
              targetAt targetIsBubble targetNested targetState
              targetLocalCanonical targetItemsCanonical targetChildState
              targetChildKind targetInherited targetBinders targetFuel
              targetTailTrace =>
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext
                    (List.cons.inj sourcePathEq).1
              have targetPositionAlign : targetPosition =
                  alignedTargetPosition := Fin.ext
                    (List.cons.inj targetPathEq).1
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) =
                  .cut ((Domain source.val.diagram outer trace.inner).index
                    start startSurvives) := by
                rw [promoted_cut source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    start).1 startSurvives |>.1) childSurvives sourceChildKind,
                  promote_survivor_eq source trace start startSurvives]
              have impossible := targetChildKind.symm.trans targetKind
              cases impossible
      | @bubble sourceStart sourceChild sourceEnd sourceRest sourceParent
          sourcePosition sourcePositionEq sourceTail sourceOuter sourceLocal
          sourceArity sourceRels sourceSeq sourceFocus sourceChildBody sourceAt
          sourceIsBubble sourceNested sourceState sourceLocalCanonical
          sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
          sourceBinders sourceFuel sourceTailTrace =>
          cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
              (Target trace) with
          | here => simp at targetPathEq
          | @cut targetStart targetChild targetEnd targetRest targetParent
              targetPosition targetPositionEq targetTail targetOuter targetLocal
              targetRels targetSeq targetFocus targetChildBody targetAt
              targetIsCut targetNested targetState targetLocalCanonical
              targetItemsCanonical targetChildState targetChildKind
              targetInherited targetBinders targetFuel targetTailTrace =>
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext
                    (List.cons.inj sourcePathEq).1
              have targetPositionAlign : targetPosition =
                  alignedTargetPosition := Fin.ext
                    (List.cons.inj targetPathEq).1
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) =
                  .bubble
                    ((Domain source.val.diagram outer trace.inner).index
                      start startSurvives) sourceArity := by
                rw [promoted_bubble source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    start).1 startSurvives |>.1) childSurvives sourceChildKind,
                  promote_survivor_eq source trace start startSurvives]
              have impossible := targetChildKind.symm.trans targetKind
              cases impossible
          | @bubble targetStart targetChild targetEnd targetRest targetParent
              targetPosition targetPositionEq targetTail targetOuter targetLocal
              targetArity targetRels targetSeq targetFocus targetChildBody
              targetAt targetIsBubble targetNested targetState
              targetLocalCanonical targetItemsCanonical targetChildState
              targetChildKind targetInherited targetBinders targetFuel
              targetTailTrace =>
              have sourcePositionVal : sourcePosition.val =
                  alignedSourcePosition.val := (List.cons.inj sourcePathEq).1
              have targetPositionVal : targetPosition.val =
                  alignedTargetPosition.val := (List.cons.inj targetPathEq).1
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext sourcePositionVal
              have targetPositionAlign : targetPosition =
                  alignedTargetPosition := Fin.ext targetPositionVal
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) =
                  .bubble
                    ((Domain source.val.diagram outer trace.inner).index
                      start startSurvives) sourceArity := by
                rw [promoted_bubble source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    start).1 startSurvives |>.1) childSurvives sourceChildKind,
                  promote_survivor_eq source trace start startSurvives]
              have targetKindEq := targetChildKind.symm.trans targetKind
              have arityEq : targetArity = sourceArity := by
                injection targetKindEq
              subst targetArity
              have sourceTailCanonical : Concrete.Splice.RegionRoute
                  source.val.diagram child trace.target sourceRest :=
                sourceSiteEq ▸ sourceTail
              let rawLocalWire := localWireEquiv source.val.diagram
                source.property.diagram_well_formed trace start startSurvives
                (route_start_ne_target source trace sourceParent
                  sourceTailCanonical)
              let childWire :=
                (FiniteEquiv.finCast
                    (congrArg List.length sourceInherited)).trans
                  ((Concrete.Elaboration.appendContextEquiv inherited
                    rawLocalWire).trans
                    (FiniteEquiv.finCast
                      (congrArg List.length targetInherited).symm))
              have childWireAgreement : ∀ index,
                  targetChildState.inheritedWires.get (childWire index) =
                    sourceChildState.inheritedWires.get index := by
                exact childInheritedAgreement sourceInherited targetInherited
                  inherited rawLocalWire wireAgreement
                    (localWireEquiv_spec source.val.diagram
                      source.property.diagram_well_formed trace start
                      startSurvives
                      (route_start_ne_target source trace sourceParent
                        sourceTailCanonical))
              have childBinderAgreement : ∀ binder,
                  targetChildState.binders binder =
                    sourceChildState.binders
                      ((Domain source.val.diagram outer trace.inner).origin
                        binder) := by
                rw [sourceBinders, targetBinders]
                exact pushBinderAgreement source trace child childSurvives
                  sourceState.binders targetState.binders binderAgreement
                    sourceArity
              have sourceRestEq : sourceRest = alignedSourceRest :=
                (List.cons.inj sourcePathEq).2
              have targetRestEq : targetRest = alignedTargetRest :=
                (List.cons.inj targetPathEq).2
              let childResult := induction rfl rfl sourceSiteEq
                targetSiteEq sourceRestEq targetRestEq sourceChildState
                targetChildState sourceTailTrace targetTailTrace childWire
                childWireAgreement childBinderAgreement
              let outerWire := compilerBodyOuterWire sourceState targetState
                inherited
              let localWire :=
                (FiniteEquiv.finCast sourceLocalCanonical).trans
                  (rawLocalWire.trans
                    (FiniteEquiv.finCast targetLocalCanonical.symm))
              let sourceIndex : Fin sourceSeq.length :=
                ⟨alignedSourcePosition.val,
                  ItemSeq.focusAt?_index_lt sourceSeq
                    alignedSourcePosition.val sourceFocus sourceAt⟩
              let targetIndex : Fin targetSeq.length :=
                ⟨alignedTargetPosition.val,
                  ItemSeq.focusAt?_index_lt targetSeq
                    alignedTargetPosition.val targetFocus targetAt⟩
              let frame := compilerLeafFrame source trace
                targetWellFormed startSurvives
                (route_start_ne_target source trace sourceParent
                  sourceTailCanonical)
                sourceParent alignedSourcePosition alignedSourcePositionEq
                sourceTailCanonical sourceState targetState
                sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
                targetItemsCanonical inherited wireAgreement binderAgreement
                sourceIndex targetIndex rfl
                (congrArg Fin.val positionEq)
              have childOuterEq : compilerBodyOuterWire sourceChildState
                    targetChildState childWire =
                  extendWireEquiv outerWire localWire := by
                have algebra :=
                  Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
                    (sourceChildState.inheritedLength.symm.trans
                      (congrArg List.length sourceInherited))
                    (Concrete.Elaboration.WireContext.length_extend
                      sourceState.inheritedWires start)
                    sourceState.inheritedLength
                    (rfl : sourceOuter + sourceLocal = _)
                    sourceLocalCanonical
                    (targetChildState.inheritedLength.symm.trans
                      (congrArg List.length targetInherited))
                    (Concrete.Elaboration.WireContext.length_extend
                      targetState.inheritedWires
                        ((Domain source.val.diagram outer trace.inner).index
                          start startSurvives))
                    targetState.inheritedLength
                    (rfl : targetOuter + targetLocal = _)
                    targetLocalCanonical inherited rawLocalWire
                simpa [childWire, outerWire, localWire,
                  compilerBodyOuterWire,
                  Concrete.Elaboration.appendContextEquiv,
                  Concrete.Elaboration.castFinEquiv] using algebra
              have childContexts : DiagramContextIso
                  (extendWireEquiv outerWire localWire)
                  childResult.alignment.holeWire (sourceArity :: rels)
                  sourceNested.toFocus.holeRels
                  sourceNested.toFocus.context
                  (childResult.alignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
                rw [← childOuterEq]
                exact childResult.alignment.contexts
              have targetContextTransport :
                  childResult.alignment.holeRelsEq.symm ▸
                      DiagramContext.bubble targetLocal targetFocus.before
                        targetFocus.after sourceArity
                        targetNested.toFocus.context =
                    DiagramContext.bubble targetLocal targetFocus.before
                      targetFocus.after sourceArity
                      (childResult.alignment.holeRelsEq.symm ▸
                        targetNested.toFocus.context) :=
                DiagramContext.bubble_transport_holeRels
                  childResult.alignment.holeRelsEq targetFocus.before
                    targetFocus.after targetNested.toFocus.context
              have contexts := DiagramContextIso.bubbleFrame localWire
                sourceFocus targetFocus sourceAt targetAt frame
                sourceNested.toFocus.context
                (childResult.alignment.holeRelsEq.symm ▸
                  targetNested.toFocus.context) childContexts
              exact {
                alignment := {
                  holeRelsEq := childResult.alignment.holeRelsEq
                  holeWire := childResult.alignment.holeWire
                  contexts := by
                    simpa only [Region.ContextPath.toFocus,
                      targetContextTransport] using contexts
                }
                leafWire := childResult.leafWire
                holeWire_leaf := childResult.holeWire_leaf
                leafWireAgreement := childResult.leafWireAgreement
                leafBinderAgreement := childResult.leafBinderAgreement
              }

noncomputable def compilerTraceContextIso
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {sourceStart : Fin source.val.diagram.regionCount}
    {targetStart : Fin (Target trace).regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram sourceStart
      trace.target sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) targetPath}
    (routeAlignment : RouteAlignment source trace sourceRoute targetRoute)
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      source.val.diagram sourceStart (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Target trace) targetStart (.here targetBody))
    (sourceTrace : Concrete.Splice.CompilerTrace source.val.diagram sourceRoute
      sourceWitness sourceState)
    (targetTrace : Concrete.Splice.CompilerTrace (Target trace) targetRoute
      targetWitness targetState)
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length))
    (wireAgreement : ∀ index,
      targetState.inheritedWires.get (inherited index) =
        sourceState.inheritedWires.get index)
    (binderAgreement : ∀ binder, targetState.binders binder =
      sourceState.binders
        ((Domain source.val.diagram outer trace.inner).origin binder)) :
    let outerWire := compilerBodyOuterWire sourceState targetState inherited
    TraceAlignmentResult source trace sourceWitness targetWitness
      sourceState targetState sourceTrace targetTrace outerWire :=
  compilerTraceContextIso_aux source trace targetWellFormed routeAlignment
    rfl rfl rfl rfl rfl rfl sourceState targetState sourceTrace targetTrace
      inherited wireAgreement binderAgreement

structure RuleAlignment
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourcePath targetPath : List Nat}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (targetWitness : Region.ContextPath targetBody targetPath)
    extends CompilerTraceAlignment outerWire sourceWitness targetWitness where
  material : Region sourceWitness.toFocus.holeWires
    sourceWitness.toFocus.holeRels
  replacement : Region sourceWitness.toFocus.holeWires
    sourceWitness.toFocus.holeRels
  step : Rule.DoubleCut.Local replacement material
  source_iso : RegionIso
    (FiniteEquiv.refl (Fin sourceWitness.toFocus.holeWires))
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.body material
  target_iso : RegionIso holeWire.symm sourceWitness.toFocus.holeRels
    (holeRelsEq.symm ▸ targetWitness.toFocus.body) replacement

private theorem local_castWiresEq
    {sourceWires targetWires : Nat} {rels : RelCtx}
    (equality : sourceWires = targetWires)
    {before after : Region sourceWires rels}
    (step : Rule.DoubleCut.Local before after) :
    Rule.DoubleCut.Local (before.castWiresEq equality)
      (after.castWiresEq equality) := by
  cases equality
  simpa only [Region.castWiresEq] using step

private noncomputable def sourceIso_castWiresEq
    {sourceWires targetWires : Nat} {rels : RelCtx}
    (equality : sourceWires = targetWires)
    {source : Region targetWires rels}
    {before : Region sourceWires rels}
    (iso : RegionIso (FiniteEquiv.finCast equality.symm) rels source before) :
    RegionIso (FiniteEquiv.refl (Fin targetWires)) rels source
      (before.castWiresEq equality) := by
  cases equality
  have wireEq : FiniteEquiv.finCast rfl =
      FiniteEquiv.refl (Fin sourceWires) := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [wireEq] at iso
  simpa only [Region.castWiresEq] using iso

private noncomputable def compilerLeafPresentation
    {input : Concrete.Diagram} {site : Fin input.regionCount}
    {outerWires : Nat} {rels : RelCtx} {body : Region outerWires rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input site
      (.here body)) :
    RegionIso (FiniteEquiv.finCast leaf.inheritedLength.symm) rels body
      (Concrete.Elaboration.finishRegion input leaf.inheritedWires site
        leaf.items) := by
  let inherited := leaf.inheritedWires
  let lengthEq : inherited.length = outerWires := leaf.inheritedLength
  let items := leaf.items
  change RegionIso (FiniteEquiv.finCast lengthEq.symm) rels body
    (Concrete.Elaboration.finishRegion input inherited site items)
  have renamed := (RegionIso.renameWiresEquiv
    (Concrete.Elaboration.finishRegion input inherited site items)
      (FiniteEquiv.finCast lengthEq)).symm
  have wireEq : (FiniteEquiv.finCast lengthEq).symm =
      FiniteEquiv.finCast lengthEq.symm := by
    apply FiniteEquiv.ext
    intro index
    rfl
  rw [wireEq] at renamed
  have bodyEq : body = Region.castWiresEq lengthEq
      (Concrete.Elaboration.finishRegion input inherited site items) := by
    simpa [inherited, lengthEq, items] using leaf.bodyComputation
  rw [bodyEq]
  simpa only [Region.castWiresEq_eq_renameWires] using renamed

private noncomputable def compilerLeafPresentation_castRels
    {input : Concrete.Diagram} {site : Fin input.regionCount}
    {outerWires : Nat} {sourceRels targetRels : RelCtx}
    {body : Region outerWires targetRels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input site
      (.here body))
    (relsEq : sourceRels = targetRels) :
    RegionIso (FiniteEquiv.finCast leaf.inheritedLength.symm) sourceRels
      (Eq.mp (congrArg (Region outerWires) relsEq.symm) body)
      (Eq.mp (congrArg (Region leaf.inheritedWires.length) relsEq.symm)
        (Concrete.Elaboration.finishRegion input leaf.inheritedWires site
          leaf.items)) := by
  cases relsEq
  exact compilerLeafPresentation leaf

private theorem region_transport_eq_mp
    {sourceRels targetRels : RelCtx}
    (equality : sourceRels = targetRels)
    (body : Region wires sourceRels) :
    equality ▸ body =
      Eq.mp (congrArg (Region wires) equality) body := by
  cases equality
  rfl

private noncomputable def changeRegionIsoWire
    {first second : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (equality : first = second)
    {source : Region sourceWires rels}
    {target : Region targetWires rels}
    (iso : RegionIso first rels source target) :
    RegionIso second rels source target := by
  subst second
  exact iso

private def castBinderResult
    {sourceRels targetRels : RelCtx}
    (equality : sourceRels = targetRels) :
    Option ((arity : Nat) × RelVar sourceRels arity) →
      Option ((arity : Nat) × RelVar targetRels arity) :=
  Eq.mp (congrArg
    (fun rels => Option ((arity : Nat) × RelVar rels arity)) equality)

private theorem castBinderResult_eq_transport
    {sourceRels targetRels : RelCtx}
    (equality : sourceRels = targetRels)
    (value : Option ((arity : Nat) × RelVar sourceRels arity)) :
    castBinderResult equality value = equality ▸ value := by
  cases equality
  rfl

private theorem focusLeaves
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {sourceRels targetRels : RelCtx}
    (relsEq : sourceRels = targetRels) :
    ∀ {sourceWires targetWires : Nat}
      {sourceBody : Region sourceWires sourceRels}
      {targetBody : Region targetWires targetRels}
      (sourceLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
        source.val.diagram trace.target (.here sourceBody))
      (targetLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
        (Target trace)
        (promotedTarget source.val.diagram
          source.property.diagram_well_formed trace) (.here targetBody))
      (ambient : FiniteEquiv (Fin sourceLeaf.inheritedWires.length)
        (Fin targetLeaf.inheritedWires.length))
      (_wireAgreement : ∀ index,
        targetLeaf.inheritedWires.get (ambient index) =
          sourceLeaf.inheritedWires.get index)
      (_binderAgreement : ∀ binder, targetLeaf.binders binder =
        castBinderResult relsEq (sourceLeaf.binders
          ((Domain source.val.diagram outer trace.inner).origin binder))),
      ∃ before after : Region sourceLeaf.inheritedWires.length sourceRels,
        Rule.DoubleCut.Local before after ∧
        Nonempty (RegionIso (FiniteEquiv.refl
          (Fin sourceLeaf.inheritedWires.length)) sourceRels
          (Concrete.Elaboration.finishRegion source.val.diagram
            sourceLeaf.inheritedWires trace.target sourceLeaf.items) after) ∧
        Nonempty (RegionIso ambient sourceRels before
          (Eq.mp (congrArg (Region targetLeaf.inheritedWires.length)
            relsEq.symm)
            (Concrete.Elaboration.finishRegion (Target trace)
              targetLeaf.inheritedWires
              (promotedTarget source.val.diagram
                source.property.diagram_well_formed trace)
              targetLeaf.items))) := by
  cases relsEq
  intro sourceWires targetWires sourceBody targetBody sourceLeaf targetLeaf
    ambient wireAgreement binderAgreement
  have sourceCompiled : Concrete.Elaboration.compileRegion?
      source.val.diagram (sourceLeaf.fuel + 1) trace.target
      sourceLeaf.inheritedWires sourceLeaf.binders =
        some (Concrete.Elaboration.finishRegion source.val.diagram
          sourceLeaf.inheritedWires trace.target sourceLeaf.items) := by
    simp only [Concrete.Elaboration.compileRegion?]
    rw [sourceLeaf.itemsComputation]
    rfl
  have targetCompiled : Concrete.Elaboration.compileRegion?
      (Target trace) (targetLeaf.fuel + 1)
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace)
      targetLeaf.inheritedWires targetLeaf.binders =
        some (Concrete.Elaboration.finishRegion (Target trace)
          targetLeaf.inheritedWires
          (promotedTarget source.val.diagram
            source.property.diagram_well_formed trace) targetLeaf.items) := by
    simp only [Concrete.Elaboration.compileRegion?]
    rw [targetLeaf.itemsComputation]
    rfl
  exact DoubleCutElimCompile.focus source.val.diagram
    source.property.diagram_well_formed trace targetWellFormed
    sourceLeaf.inheritedWires targetLeaf.inheritedWires ambient wireAgreement
    sourceLeaf.wiresExact targetLeaf.wiresExact sourceLeaf.binders
    targetLeaf.binders binderAgreement sourceCompiled targetCompiled

private theorem focusRuleAlignment
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (targetWellFormed : (Target trace).WellFormed)
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourcePath targetPath : List Nat}
    {sourceStart : Fin source.val.diagram.regionCount}
    {targetStart : Fin (Target trace).regionCount}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram sourceStart
      trace.target sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) targetPath}
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (targetWitness : Region.ContextPath targetBody targetPath)
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      source.val.diagram sourceStart (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (Target trace) targetStart (.here targetBody))
    (sourceTrace : Concrete.Splice.CompilerTrace source.val.diagram sourceRoute
      sourceWitness sourceState)
    (targetTrace : Concrete.Splice.CompilerTrace (Target trace) targetRoute
      targetWitness targetState)
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (traceResult : TraceAlignmentResult source trace sourceWitness targetWitness
      sourceState targetState sourceTrace targetTrace outerWire) :
    Nonempty {result : RuleAlignment outerWire sourceWitness targetWitness //
      result.holeWire = traceResult.alignment.holeWire} := by
  let sourceLeaf := sourceTrace.leaf.atFocus
  let targetLeaf := targetTrace.leaf.atFocus
  let relsEq := traceResult.alignment.holeRelsEq
  have focusBinderAgreement : ∀ binder, targetLeaf.binders binder =
      castBinderResult relsEq (sourceLeaf.binders
        ((Domain source.val.diagram outer trace.inner).origin binder)) := by
    intro binder
    rw [castBinderResult_eq_transport]
    exact traceResult.leafBinderAgreement binder
  obtain ⟨before, after, localEvidence, sourceFocusIso,
      targetFocusIso⟩ := focusLeaves source trace targetWellFormed relsEq
    sourceLeaf targetLeaf traceResult.leafWire
    traceResult.leafWireAgreement focusBinderAgreement
  rcases sourceFocusIso with ⟨sourceFocusIso⟩
  rcases targetFocusIso with ⟨targetFocusIso⟩
  let before' := before.castWiresEq sourceLeaf.inheritedLength
  let after' := after.castWiresEq sourceLeaf.inheritedLength
  have localEvidence' : Rule.DoubleCut.Local before' after' :=
    local_castWiresEq sourceLeaf.inheritedLength localEvidence
  have sourcePresentation := compilerLeafPresentation sourceLeaf
  have sourceCombined := sourcePresentation.trans sourceFocusIso
  have sourceFocusIso' : RegionIso
      (FiniteEquiv.refl (Fin sourceWitness.toFocus.holeWires))
      sourceWitness.toFocus.holeRels sourceWitness.toFocus.body after' :=
    sourceIso_castWiresEq sourceLeaf.inheritedLength sourceCombined
  have targetPresentation := compilerLeafPresentation_castRels targetLeaf relsEq
  have targetCombined := targetPresentation.trans targetFocusIso.symm
  have renamed := targetCombined.trans
    (RegionIso.renameWiresEquiv before
      (FiniteEquiv.finCast sourceLeaf.inheritedLength))
  have wireFactor :
      ((FiniteEquiv.finCast targetLeaf.inheritedLength.symm).trans
        traceResult.leafWire.symm).trans
          (FiniteEquiv.finCast sourceLeaf.inheritedLength) =
        traceResult.alignment.holeWire.symm := by
    rw [traceResult.holeWire_leaf]
    apply FiniteEquiv.ext
    intro index
    rfl
  have targetFocusIso' : RegionIso traceResult.alignment.holeWire.symm
      sourceWitness.toFocus.holeRels
      (Eq.mp (congrArg (Region targetWitness.toFocus.holeWires) relsEq.symm)
        targetWitness.toFocus.body) before' := by
    have changed := changeRegionIsoWire wireFactor renamed
    dsimp only [before']
    rw [Region.castWiresEq_eq_renameWires]
    exact changed
  exact ⟨⟨{
    holeRelsEq := traceResult.alignment.holeRelsEq
    holeWire := traceResult.alignment.holeWire
    contexts := traceResult.alignment.contexts
    material := after'
    replacement := before'
    step := localEvidence'
    source_iso := sourceFocusIso'
    target_iso := by
      rw [region_transport_eq_mp]
      exact targetFocusIso'
  }, rfl⟩⟩

private theorem routeAlignment_start_origin
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    {sourceStart : Fin source.val.diagram.regionCount}
    {targetStart : Fin (Target trace).regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram
      sourceStart trace.target sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) targetPath}
    (alignment : RouteAlignment source trace sourceRoute targetRoute) :
    (Domain source.val.diagram outer trace.inner).origin targetStart =
      sourceStart := by
  cases alignment with
  | here =>
      exact promotedTarget_origin source.val.diagram
        source.property.diagram_well_formed trace
  | step startSurvives childSurvives positionEq tail =>
      exact (Domain source.val.diagram outer trace.inner).origin_index _ _

private theorem routeAlignment_root_start
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (_rootNe : trace.target ≠ source.val.diagram.root)
    {targetStart : Fin (Target trace).regionCount}
    {sourcePath targetPath : List Nat}
    {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram
      source.val.diagram.root trace.target sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute (Target trace) targetStart
      (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) targetPath}
    (alignment : RouteAlignment source trace sourceRoute targetRoute) :
    targetStart = (Target trace).root := by
  apply (Domain source.val.diagram outer trace.inner).origin_injective
  rw [routeAlignment_start_origin source trace alignment]
  exact trace.promotion.root_origin.symm

noncomputable def targetTrace_complete
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed)
    (sourceView : Concrete.Splice.OpenSiteView source trace.target) :
    let target := checkedTarget source trace targetWellFormed
    Σ targetPath,
      Σ targetRoute : Concrete.Splice.RegionRoute target.val.diagram
        target.val.diagram.root
        (promotedTarget source.val.diagram
          source.property.diagram_well_formed trace) targetPath,
        RouteAlignment source trace sourceView.route targetRoute ×
          Concrete.Splice.OpenCompilerTraceResult target targetRoute
            target.elaborate.body := by
  dsimp only
  let target := checkedTarget source trace targetWellFormed
  obtain ⟨targetStart, targetPath, targetRoute, alignment⟩ :=
    route_complete source trace sourceView.route
  have startEq := routeAlignment_root_start source trace rootNe alignment
  subst targetStart
  have compiled : Concrete.Elaboration.compileRoot? target.val.diagram
      target.val.exposedWires target.val.hiddenWires =
        some target.elaborate.body := by
    obtain ⟨body, bodyComputation, elaborates⟩ :=
      Concrete.CheckedOpen.elaborate_body_computation target
    subst body
    exact bodyComputation
  let result :=
    Concrete.Splice.compileOpenRoot_route_context_complete target targetRoute
      compiled
  exact ⟨targetPath, targetRoute, alignment, result⟩

private theorem localOccurrence_indexOf_cast
    (diagram : Concrete.Diagram)
    {sourceRegion targetRegion : Fin diagram.regionCount}
    (regionEq : sourceRegion = targetRegion)
    (occurrence : Concrete.Elaboration.LocalOccurrence diagram.regionCount
      diagram.nodeCount)
    (position : Fin (Concrete.Elaboration.localOccurrences diagram
      sourceRegion).length)
    (found : indexOf?
      (Concrete.Elaboration.localOccurrences diagram sourceRegion)
      occurrence = some position) :
    indexOf? (Concrete.Elaboration.localOccurrences diagram targetRegion)
      occurrence = some (Fin.cast (congrArg List.length
        (congrArg (Concrete.Elaboration.localOccurrences diagram) regionEq))
          position) := by
  cases regionEq
  exact found

private theorem cast_context_agreement
    {source target sourceChild targetChild : List α}
    (sourceEq : sourceChild = source)
    (targetEq : targetChild = target)
    (ambient : FiniteEquiv (Fin source.length) (Fin target.length))
    (agreement : ∀ index, target.get (ambient index) = source.get index) :
    let childWire :=
      (FiniteEquiv.finCast (congrArg List.length sourceEq)).trans
        (ambient.trans (FiniteEquiv.finCast
          (congrArg List.length targetEq).symm))
    ∀ index, targetChild.get (childWire index) =
      sourceChild.get index := by
  subst sourceChild
  subst targetChild
  exact agreement

private theorem openTraceRuleAlignment_aux
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed)
    {alignedSourceStart : Fin source.val.diagram.regionCount}
    {alignedTargetStart : Fin (Target trace).regionCount}
    {alignedSourcePath alignedTargetPath : List Nat}
    {alignedSourceRoute : Concrete.Splice.RegionRoute source.val.diagram
      alignedSourceStart trace.target alignedSourcePath}
    {alignedTargetRoute : Concrete.Splice.RegionRoute (Target trace)
      alignedTargetStart (promotedTarget source.val.diagram
        source.property.diagram_well_formed trace) alignedTargetPath}
    (routeAlignment : RouteAlignment source trace alignedSourceRoute
      alignedTargetRoute) :
    ∀ {actualSourceSite : Fin source.val.diagram.regionCount}
      {actualTargetSite : Fin (Target trace).regionCount}
      {actualSourcePath actualTargetPath : List Nat}
      (_sourceStartEq : source.val.diagram.root = alignedSourceStart)
      (_targetStartEq : (Target trace).root = alignedTargetStart)
      (_sourceSiteEq : actualSourceSite = trace.target)
      (_targetSiteEq : actualTargetSite = promotedTarget source.val.diagram
        source.property.diagram_well_formed trace)
      (_sourcePathEq : actualSourcePath = alignedSourcePath)
      (_targetPathEq : actualTargetPath = alignedTargetPath)
      {sourceRoute : Concrete.Splice.RegionRoute source.val.diagram
        source.val.diagram.root actualSourceSite actualSourcePath}
      {targetRoute : Concrete.Splice.RegionRoute (Target trace)
        (Target trace).root actualTargetSite actualTargetPath}
      {sourceBody : Region source.val.exposedWires.length []}
      {targetBody : Region (targetOpen source trace).exposedWires.length []}
      {sourceWitness : Region.ContextPath sourceBody actualSourcePath}
      {targetWitness : Region.ContextPath targetBody actualTargetPath}
      (sourceState : Concrete.Splice.OpenRootCompilerState source sourceBody)
      (targetState : Concrete.Splice.OpenRootCompilerState
        (checkedTarget source trace targetWellFormed) targetBody)
      (_sourceTrace : Concrete.Splice.OpenCompilerTrace source sourceRoute
        sourceWitness sourceState)
      (_targetTrace : Concrete.Splice.OpenCompilerTrace
        (checkedTarget source trace targetWellFormed) targetRoute
        targetWitness targetState),
      let outerWire := FiniteEquiv.finCast (congrArg List.length
        (targetOpen_exposedWires source trace).symm)
      Nonempty (RuleAlignment outerWire sourceWitness targetWitness) := by
  induction routeAlignment with
  | here =>
      intro actualSourceSite actualTargetSite actualSourcePath actualTargetPath
        sourceStartEq targetStartEq sourceSiteEq targetSiteEq sourcePathEq
        targetPathEq sourceRoute targetRoute sourceBody targetBody
        sourceWitness targetWitness sourceState targetState sourceTrace
        targetTrace
      exact False.elim (rootNe sourceStartEq.symm)
  | @step start child alignedSourceRest alignedTargetRest sourceParent
      alignedSourcePosition alignedSourcePositionEq sourceTail startSurvives
      childSurvives targetParent alignedTargetPosition alignedTargetPositionEq
      targetTail positionEq tail induction =>
      intro actualSourceSite actualTargetSite actualSourcePath actualTargetPath
        sourceStartEq targetStartEq sourceSiteEq targetSiteEq sourcePathEq
        targetPathEq sourceRoute targetRoute sourceBody targetBody
        sourceWitness targetWitness sourceState targetState sourceTrace
        targetTrace
      cases sourceStartEq
      cases sourceTrace using @Concrete.Splice.OpenCompilerTrace.casesOn source with
      | here => simp at sourcePathEq
      | @cut sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceSeq sourceFocus
          sourceChildBody sourceAt sourceIsCut sourceNested sourceState
          sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          cases targetTrace using @Concrete.Splice.OpenCompilerTrace.casesOn
              (checkedTarget source trace targetWellFormed) with
          | here => simp at targetPathEq
          | @cut targetChild targetEnd targetRest targetParent targetPosition
              targetPositionEq targetTail targetLocal targetSeq targetFocus
              targetChildBody targetAt targetIsCut targetNested targetState
              targetLocalCanonical targetItemsCanonical targetChildState
              targetChildKind targetInherited targetBinders targetFuel
              targetTailTrace =>
              let alignedTargetPositionAtRoot : Fin
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root).length :=
                Fin.cast (congrArg (fun region =>
                  (Concrete.Elaboration.localOccurrences
                    (Target trace) region).length) targetStartEq).symm
                  alignedTargetPosition
              have alignedTargetPositionEqAtRoot : indexOf?
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root)
                  (.child ((Domain source.val.diagram outer trace.inner).index
                    child childSurvives)) =
                    some alignedTargetPositionAtRoot := by
                exact localOccurrence_indexOf_cast (Target trace)
                  targetStartEq.symm _ alignedTargetPosition
                    alignedTargetPositionEq
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext
                    (List.cons.inj sourcePathEq).1
              have targetPositionAlign : targetPosition =
                  alignedTargetPositionAtRoot := Fin.ext
                    (List.cons.inj targetPathEq).1
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEqAtRoot
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) = .cut (Target trace).root := by
                rw [promoted_cut source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    source.val.diagram.root).1 startSurvives |>.1)
                  childSurvives sourceChildKind,
                  promote_survivor_eq source trace source.val.diagram.root
                    startSurvives, ← targetStartEq]
              have targetKindEq := targetChildKind.symm.trans targetKind
              cases Concrete.CRegion.cut.inj targetKindEq
              let rootWire := FiniteEquiv.finCast (congrArg List.length
                (targetOpen_rootWires source trace rootNe).symm)
              let childWire :=
                (FiniteEquiv.finCast
                  (congrArg List.length sourceInherited)).trans
                    (rootWire.trans (FiniteEquiv.finCast
                      (congrArg List.length targetInherited).symm))
              have rootWireAgreement : ∀ index,
                  (targetOpen source trace).rootWires.get (rootWire index) =
                    source.val.rootWires.get index := by
                intro index
                exact list_get_cast
                  (targetOpen_rootWires source trace rootNe).symm index
              have childWireAgreement : ∀ index,
                  targetChildState.inheritedWires.get (childWire index) =
                    sourceChildState.inheritedWires.get index := by
                exact cast_context_agreement sourceInherited targetInherited
                  rootWire rootWireAgreement
              have rootBinderAgreement : ∀ binder,
                  (Concrete.Elaboration.BinderContext.empty :
                    Concrete.Elaboration.BinderContext (Target trace) [])
                      binder =
                  (Concrete.Elaboration.BinderContext.empty :
                    Concrete.Elaboration.BinderContext
                      source.val.diagram [])
                    ((Domain source.val.diagram outer trace.inner).origin
                      binder) := by
                intro binder
                rfl
              have childBinderAgreement : ∀ binder,
                  targetChildState.binders binder =
                    sourceChildState.binders
                      ((Domain source.val.diagram outer trace.inner).origin
                        binder) := by
                rw [sourceBinders, targetBinders]
                exact rootBinderAgreement
              have sourceRestEq : sourceRest = alignedSourceRest :=
                (List.cons.inj sourcePathEq).2
              have targetRestEq : targetRest = alignedTargetRest :=
                (List.cons.inj targetPathEq).2
              let childResult := compilerTraceContextIso_aux source
                trace targetWellFormed tail rfl rfl sourceSiteEq targetSiteEq
                sourceRestEq targetRestEq sourceChildState targetChildState
                sourceTailTrace targetTailTrace childWire childWireAgreement
                childBinderAgreement
              let outerWire := FiniteEquiv.finCast (congrArg List.length
                (targetOpen_exposedWires source trace).symm)
              let localWire :=
                (FiniteEquiv.finCast sourceLocalCanonical).trans
                  ((FiniteEquiv.finCast (congrArg List.length
                    (targetOpen_hiddenWires source trace rootNe).symm)).trans
                    (FiniteEquiv.finCast targetLocalCanonical.symm))
              let sourceItemsLength :=
                Concrete.Elaboration.compileOccurrencesWith?_length
                  (Concrete.Elaboration.compileRegion? source.val.diagram
                    source.val.diagram.regionCount)
                  source.val.rootWires
                  Concrete.Elaboration.BinderContext.empty
                  sourceState.itemsComputation
              let targetItemsLength :=
                Concrete.Elaboration.compileOccurrencesWith?_length
                  (Concrete.Elaboration.compileRegion? (Target trace)
                    (Target trace).regionCount)
                  (targetOpen source trace).rootWires
                  Concrete.Elaboration.BinderContext.empty
                  targetState.itemsComputation
              let sourceIndex : Fin sourceState.items.length :=
                Fin.cast sourceItemsLength.symm alignedSourcePosition
              let targetIndex : Fin targetState.items.length :=
                Fin.cast targetItemsLength.symm alignedTargetPositionAtRoot
              have sourceTailCanonical : Concrete.Splice.RegionRoute
                  source.val.diagram child trace.target sourceRest :=
                sourceSiteEq ▸ sourceTail
              let rawFrame := openRootRawFrame source trace rootNe
                targetWellFormed sourceParent alignedSourcePosition
                alignedSourcePositionEq sourceTailCanonical sourceState
                targetState sourceIndex targetIndex (by simp [sourceIndex])
                (by
                  simp [targetIndex, alignedTargetPositionAtRoot,
                    positionEq])
              obtain ⟨sourceIndex', targetIndex', sourceIndexVal,
                  targetIndexVal, frame⟩ := openRootFrame source trace
                rootNe targetWellFormed sourceState targetState
                sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
                targetItemsCanonical rawFrame
              have childOuterEq : compilerBodyOuterWire sourceChildState
                    targetChildState childWire =
                  extendWireEquiv outerWire localWire := by
                apply FiniteEquiv.ext
                intro index
                apply Fin.ext
                have left : (compilerBodyOuterWire sourceChildState
                    targetChildState childWire index).val = index.val := by
                  simp [compilerBodyOuterWire, childWire, rootWire,
                    FiniteEquiv.finCast]
                have right : ((extendWireEquiv outerWire localWire) index).val =
                    index.val := by
                  refine Fin.addCases (fun inheritedIndex => ?_)
                    (fun localIndex => ?_) index
                  · simp [outerWire, extendWireEquiv, FiniteEquiv.finCast]
                  · simp [localWire, extendWireEquiv, FiniteEquiv.finCast,
                      targetOpen_exposedWires]
                exact left.trans right.symm
              have childContexts : DiagramContextIso
                  (extendWireEquiv outerWire localWire)
                  childResult.alignment.holeWire []
                  sourceNested.toFocus.holeRels
                  sourceNested.toFocus.context
                  (childResult.alignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
                rw [← childOuterEq]
                exact childResult.alignment.contexts
              have sourceAt' : sourceSeq.focusAt? sourceIndex'.val =
                  some sourceFocus := by
                simpa [sourceIndexVal, sourceIndex] using sourceAt
              have targetAt' : targetSeq.focusAt? targetIndex'.val =
                  some targetFocus := by
                simpa [targetIndexVal, targetIndex] using targetAt
              have targetContextTransport :
                  childResult.alignment.holeRelsEq.symm ▸
                      DiagramContext.cut targetLocal targetFocus.before
                        targetFocus.after targetNested.toFocus.context =
                    DiagramContext.cut targetLocal targetFocus.before
                      targetFocus.after
                      (childResult.alignment.holeRelsEq.symm ▸
                        targetNested.toFocus.context) :=
                DiagramContext.cut_transport_holeRels
                  childResult.alignment.holeRelsEq targetFocus.before
                    targetFocus.after targetNested.toFocus.context
              have contexts := DiagramContextIso.cutFrame
                (outerWire := outerWire)
                (holeWire := childResult.alignment.holeWire) localWire
                sourceFocus targetFocus sourceAt' targetAt' frame
                sourceNested.toFocus.context
                (childResult.alignment.holeRelsEq.symm ▸
                  targetNested.toFocus.context) childContexts
              cases sourceSiteEq
              cases targetSiteEq
              obtain ⟨⟨focusResult, focusWireEq⟩⟩ :=
                focusRuleAlignment source trace targetWellFormed
                  sourceNested targetNested sourceChildState targetChildState
                  sourceTailTrace targetTailTrace
                  (compilerBodyOuterWire sourceChildState targetChildState
                    childWire) childResult
              exact ⟨{
                holeRelsEq := focusResult.holeRelsEq
                holeWire := focusResult.holeWire
                contexts := by
                  rw [focusWireEq]
                  simpa only [Region.ContextPath.toFocus] using
                    (targetContextTransport.symm ▸ contexts)
                material := focusResult.material
                replacement := focusResult.replacement
                step := focusResult.step
                source_iso := focusResult.source_iso
                target_iso := focusResult.target_iso
              }⟩
          | @bubble targetChild targetEnd targetRest targetParent
              targetPosition targetPositionEq targetTail targetLocal
              targetArity targetSeq targetFocus targetChildBody targetAt
              targetIsBubble targetNested targetState targetLocalCanonical
              targetItemsCanonical targetChildState targetChildKind
              targetInherited targetBinders targetFuel targetTailTrace =>
              let alignedTargetPositionAtRoot : Fin
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root).length :=
                Fin.cast (congrArg (fun region =>
                  (Concrete.Elaboration.localOccurrences
                    (Target trace) region).length) targetStartEq).symm
                  alignedTargetPosition
              have alignedTargetPositionEqAtRoot : indexOf?
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root)
                  (.child ((Domain source.val.diagram outer trace.inner).index
                    child childSurvives)) =
                    some alignedTargetPositionAtRoot :=
                localOccurrence_indexOf_cast (Target trace)
                  targetStartEq.symm _ alignedTargetPosition
                    alignedTargetPositionEq
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext
                    (List.cons.inj sourcePathEq).1
              have targetPositionAlign : targetPosition =
                  alignedTargetPositionAtRoot := Fin.ext
                    (List.cons.inj targetPathEq).1
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEqAtRoot
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) = .cut (Target trace).root := by
                rw [promoted_cut source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    source.val.diagram.root).1 startSurvives |>.1)
                  childSurvives sourceChildKind,
                  promote_survivor_eq source trace source.val.diagram.root
                    startSurvives, ← targetStartEq]
              have impossible := targetChildKind.symm.trans targetKind
              cases impossible
      | @bubble sourceChild sourceEnd sourceRest sourceParent sourcePosition
          sourcePositionEq sourceTail sourceLocal sourceArity sourceSeq
          sourceFocus sourceChildBody sourceAt sourceIsBubble sourceNested
          sourceState sourceLocalCanonical sourceItemsCanonical sourceChildState
          sourceChildKind sourceInherited sourceBinders sourceFuel
          sourceTailTrace =>
          cases targetTrace using @Concrete.Splice.OpenCompilerTrace.casesOn
              (checkedTarget source trace targetWellFormed) with
          | here => simp at targetPathEq
          | @cut targetChild targetEnd targetRest targetParent targetPosition
              targetPositionEq targetTail targetLocal targetSeq targetFocus
              targetChildBody targetAt targetIsCut targetNested targetState
              targetLocalCanonical targetItemsCanonical targetChildState
              targetChildKind targetInherited targetBinders targetFuel
              targetTailTrace =>
              let alignedTargetPositionAtRoot : Fin
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root).length :=
                Fin.cast (congrArg (fun region =>
                  (Concrete.Elaboration.localOccurrences
                    (Target trace) region).length) targetStartEq).symm
                  alignedTargetPosition
              have alignedTargetPositionEqAtRoot : indexOf?
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root)
                  (.child ((Domain source.val.diagram outer trace.inner).index
                    child childSurvives)) =
                    some alignedTargetPositionAtRoot :=
                localOccurrence_indexOf_cast (Target trace)
                  targetStartEq.symm _ alignedTargetPosition
                    alignedTargetPositionEq
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext
                    (List.cons.inj sourcePathEq).1
              have targetPositionAlign : targetPosition =
                  alignedTargetPositionAtRoot := Fin.ext
                    (List.cons.inj targetPathEq).1
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEqAtRoot
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) =
                  .bubble (Target trace).root sourceArity := by
                rw [promoted_bubble source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    source.val.diagram.root).1 startSurvives |>.1)
                  childSurvives sourceChildKind,
                  promote_survivor_eq source trace source.val.diagram.root
                    startSurvives, ← targetStartEq]
              have impossible := targetChildKind.symm.trans targetKind
              cases impossible
          | @bubble targetChild targetEnd targetRest targetParent
              targetPosition targetPositionEq targetTail targetLocal
              targetArity targetSeq targetFocus targetChildBody targetAt
              targetIsBubble targetNested targetState targetLocalCanonical
              targetItemsCanonical targetChildState targetChildKind
              targetInherited targetBinders targetFuel targetTailTrace =>
              let alignedTargetPositionAtRoot : Fin
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root).length :=
                Fin.cast (congrArg (fun region =>
                  (Concrete.Elaboration.localOccurrences
                    (Target trace) region).length) targetStartEq).symm
                  alignedTargetPosition
              have alignedTargetPositionEqAtRoot : indexOf?
                  (Concrete.Elaboration.localOccurrences (Target trace)
                    (Target trace).root)
                  (.child ((Domain source.val.diagram outer trace.inner).index
                    child childSurvives)) =
                    some alignedTargetPositionAtRoot :=
                localOccurrence_indexOf_cast (Target trace)
                  targetStartEq.symm _ alignedTargetPosition
                    alignedTargetPositionEq
              have sourcePositionAlign : sourcePosition =
                  alignedSourcePosition := Fin.ext
                    (List.cons.inj sourcePathEq).1
              have targetPositionAlign : targetPosition =
                  alignedTargetPositionAtRoot := Fin.ext
                    (List.cons.inj targetPathEq).1
              subst sourcePosition
              subst targetPosition
              have sourceChildEq : sourceChild = child := by
                have first := indexOf?_sound sourcePositionEq
                have second := indexOf?_sound alignedSourcePositionEq
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              have targetChildEq : targetChild =
                  (Domain source.val.diagram outer trace.inner).index child
                    childSurvives := by
                have first := indexOf?_sound targetPositionEq
                have second := indexOf?_sound alignedTargetPositionEqAtRoot
                exact Concrete.Elaboration.LocalOccurrence.child.inj
                  (by simpa only [List.get_eq_getElem] using first.symm.trans second)
              subst sourceChild
              subst targetChild
              have targetKind : (Target trace).regions
                    ((Domain source.val.diagram outer trace.inner).index child
                      childSurvives) =
                  .bubble (Target trace).root sourceArity := by
                rw [promoted_bubble source.val.diagram
                  source.property.diagram_well_formed trace
                  ((domain_survives_iff source.val.diagram outer trace.inner
                    source.val.diagram.root).1 startSurvives |>.1)
                  childSurvives sourceChildKind,
                  promote_survivor_eq source trace source.val.diagram.root
                    startSurvives, ← targetStartEq]
              have targetKindEq := targetChildKind.symm.trans targetKind
              have arityEq : targetArity = sourceArity := by
                injection targetKindEq
              subst targetArity
              let rootWire := FiniteEquiv.finCast (congrArg List.length
                (targetOpen_rootWires source trace rootNe).symm)
              let childWire :=
                (FiniteEquiv.finCast
                  (congrArg List.length sourceInherited)).trans
                    (rootWire.trans (FiniteEquiv.finCast
                      (congrArg List.length targetInherited).symm))
              have rootWireAgreement : ∀ index,
                  (targetOpen source trace).rootWires.get (rootWire index) =
                    source.val.rootWires.get index := by
                intro index
                exact list_get_cast
                  (targetOpen_rootWires source trace rootNe).symm index
              have childWireAgreement : ∀ index,
                  targetChildState.inheritedWires.get (childWire index) =
                    sourceChildState.inheritedWires.get index := by
                exact cast_context_agreement sourceInherited targetInherited
                  rootWire rootWireAgreement
              have rootBinderAgreement : ∀ binder,
                  (Concrete.Elaboration.BinderContext.empty :
                    Concrete.Elaboration.BinderContext (Target trace) [])
                      binder =
                  (Concrete.Elaboration.BinderContext.empty :
                    Concrete.Elaboration.BinderContext
                      source.val.diagram [])
                    ((Domain source.val.diagram outer trace.inner).origin
                      binder) := by
                intro binder
                rfl
              have childBinderAgreement : ∀ binder,
                  targetChildState.binders binder =
                    sourceChildState.binders
                      ((Domain source.val.diagram outer trace.inner).origin
                        binder) := by
                rw [sourceBinders, targetBinders]
                exact pushBinderAgreement source trace child childSurvives
                  Concrete.Elaboration.BinderContext.empty
                  Concrete.Elaboration.BinderContext.empty
                  rootBinderAgreement sourceArity
              have sourceRestEq : sourceRest = alignedSourceRest :=
                (List.cons.inj sourcePathEq).2
              have targetRestEq : targetRest = alignedTargetRest :=
                (List.cons.inj targetPathEq).2
              let childResult := compilerTraceContextIso_aux source
                trace targetWellFormed tail rfl rfl sourceSiteEq targetSiteEq
                sourceRestEq targetRestEq sourceChildState targetChildState
                sourceTailTrace targetTailTrace childWire childWireAgreement
                childBinderAgreement
              let outerWire := FiniteEquiv.finCast (congrArg List.length
                (targetOpen_exposedWires source trace).symm)
              let localWire :=
                (FiniteEquiv.finCast sourceLocalCanonical).trans
                  ((FiniteEquiv.finCast (congrArg List.length
                    (targetOpen_hiddenWires source trace rootNe).symm)).trans
                    (FiniteEquiv.finCast targetLocalCanonical.symm))
              let sourceItemsLength :=
                Concrete.Elaboration.compileOccurrencesWith?_length
                  (Concrete.Elaboration.compileRegion? source.val.diagram
                    source.val.diagram.regionCount)
                  source.val.rootWires
                  Concrete.Elaboration.BinderContext.empty
                  sourceState.itemsComputation
              let targetItemsLength :=
                Concrete.Elaboration.compileOccurrencesWith?_length
                  (Concrete.Elaboration.compileRegion? (Target trace)
                    (Target trace).regionCount)
                  (targetOpen source trace).rootWires
                  Concrete.Elaboration.BinderContext.empty
                  targetState.itemsComputation
              let sourceIndex : Fin sourceState.items.length :=
                Fin.cast sourceItemsLength.symm alignedSourcePosition
              let targetIndex : Fin targetState.items.length :=
                Fin.cast targetItemsLength.symm alignedTargetPositionAtRoot
              have sourceTailCanonical : Concrete.Splice.RegionRoute
                  source.val.diagram child trace.target sourceRest :=
                sourceSiteEq ▸ sourceTail
              let rawFrame := openRootRawFrame source trace rootNe
                targetWellFormed sourceParent alignedSourcePosition
                alignedSourcePositionEq sourceTailCanonical sourceState
                targetState sourceIndex targetIndex (by simp [sourceIndex])
                (by
                  simp [targetIndex, alignedTargetPositionAtRoot,
                    positionEq])
              obtain ⟨sourceIndex', targetIndex', sourceIndexVal,
                  targetIndexVal, frame⟩ := openRootFrame source trace
                rootNe targetWellFormed sourceState targetState
                sourceLocalCanonical targetLocalCanonical sourceItemsCanonical
                targetItemsCanonical rawFrame
              have childOuterEq : compilerBodyOuterWire sourceChildState
                    targetChildState childWire =
                  extendWireEquiv outerWire localWire := by
                apply FiniteEquiv.ext
                intro index
                apply Fin.ext
                have left : (compilerBodyOuterWire sourceChildState
                    targetChildState childWire index).val = index.val := by
                  simp [compilerBodyOuterWire, childWire, rootWire,
                    FiniteEquiv.finCast]
                have right : ((extendWireEquiv outerWire localWire) index).val =
                    index.val := by
                  refine Fin.addCases (fun inheritedIndex => ?_)
                    (fun localIndex => ?_) index
                  · simp [outerWire, extendWireEquiv, FiniteEquiv.finCast]
                  · simp [localWire, extendWireEquiv, FiniteEquiv.finCast,
                      targetOpen_exposedWires]
                exact left.trans right.symm
              have childContexts : DiagramContextIso
                  (extendWireEquiv outerWire localWire)
                  childResult.alignment.holeWire (sourceArity :: [])
                  sourceNested.toFocus.holeRels
                  sourceNested.toFocus.context
                  (childResult.alignment.holeRelsEq.symm ▸
                    targetNested.toFocus.context) := by
                rw [← childOuterEq]
                exact childResult.alignment.contexts
              have sourceAt' : sourceSeq.focusAt? sourceIndex'.val =
                  some sourceFocus := by
                simpa [sourceIndexVal, sourceIndex] using sourceAt
              have targetAt' : targetSeq.focusAt? targetIndex'.val =
                  some targetFocus := by
                simpa [targetIndexVal, targetIndex] using targetAt
              have targetContextTransport :
                  childResult.alignment.holeRelsEq.symm ▸
                      DiagramContext.bubble targetLocal targetFocus.before
                        targetFocus.after sourceArity
                        targetNested.toFocus.context =
                    DiagramContext.bubble targetLocal targetFocus.before
                      targetFocus.after sourceArity
                      (childResult.alignment.holeRelsEq.symm ▸
                        targetNested.toFocus.context) :=
                DiagramContext.bubble_transport_holeRels
                  childResult.alignment.holeRelsEq targetFocus.before
                    targetFocus.after targetNested.toFocus.context
              have contexts := DiagramContextIso.bubbleFrame
                (outerWire := outerWire)
                (holeWire := childResult.alignment.holeWire) localWire
                sourceFocus targetFocus sourceAt' targetAt' frame
                sourceNested.toFocus.context
                (childResult.alignment.holeRelsEq.symm ▸
                  targetNested.toFocus.context) childContexts
              cases sourceSiteEq
              cases targetSiteEq
              obtain ⟨⟨focusResult, focusWireEq⟩⟩ :=
                focusRuleAlignment source trace targetWellFormed
                  sourceNested targetNested sourceChildState targetChildState
                  sourceTailTrace targetTailTrace
                  (compilerBodyOuterWire sourceChildState targetChildState
                    childWire) childResult
              exact ⟨{
                holeRelsEq := focusResult.holeRelsEq
                holeWire := focusResult.holeWire
                contexts := by
                  rw [focusWireEq]
                  simpa only [Region.ContextPath.toFocus] using
                    (targetContextTransport.symm ▸ contexts)
                material := focusResult.material
                replacement := focusResult.replacement
                step := focusResult.step
                source_iso := focusResult.source_iso
                target_iso := focusResult.target_iso
              }⟩

/-- Whole-open elimination below the root against the canonical promoted
target. -/
theorem nested_rule
    (source : Concrete.CheckedOpen)
    {outer : Fin source.val.diagram.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace source.val.diagram outer raw)
    (rootNe : trace.target ≠ source.val.diagram.root)
    (targetWellFormed : (Target trace).WellFormed) :
    Rule.DoubleCut source.elaborate
      (checkedTarget source trace targetWellFormed).elaborate := by
  let target := checkedTarget source trace targetWellFormed
  let sourceView := Concrete.Splice.openSiteView_complete source trace.target
  obtain ⟨targetPath, targetRoute, routeAlignment,
      targetResult⟩ := targetTrace_complete source trace rootNe
        targetWellFormed sourceView
  let outerWire := FiniteEquiv.finCast (congrArg List.length
    (targetOpen_exposedWires source trace).symm)
  obtain ⟨alignment⟩ := openTraceRuleAlignment_aux source trace rootNe
    targetWellFormed routeAlignment rfl rfl rfl rfl rfl rfl
    sourceView.result.state targetResult.state sourceView.result.trace
      targetResult.trace
  let sourceBodyIso : RegionIso
      (FiniteEquiv.refl (Fin source.elaborate.externalClasses)) []
      source.elaborate.body
      (sourceView.intrinsicPath.toFocus.context.fill alignment.material) := by
    have rebuildIso : RegionIso
        (FiniteEquiv.refl (Fin source.elaborate.externalClasses)) []
        source.elaborate.body
        (sourceView.intrinsicPath.toFocus.context.fill
          sourceView.intrinsicPath.toFocus.body) := by
      exact cast (congrArg
        (fun body => RegionIso
          (FiniteEquiv.refl (Fin source.elaborate.externalClasses)) [] body
          (sourceView.intrinsicPath.toFocus.context.fill
            sourceView.intrinsicPath.toFocus.body))
        sourceView.intrinsicPath.toFocus.rebuild)
        (RegionIso.refl
          (sourceView.intrinsicPath.toFocus.context.fill
            sourceView.intrinsicPath.toFocus.body))
    exact rebuildIso.trans
      (sourceView.intrinsicPath.toFocus.context.fillIso
        alignment.source_iso)
  let sourceHostIso : OpenDiagramIso source.elaborate
      (source.elaborate.withBody
        (sourceView.intrinsicPath.toFocus.context.fill
          alignment.material)) := {
    external := FiniteEquiv.refl (Fin source.elaborate.externalClasses)
    boundary := fun _ => rfl
    body := sourceBodyIso
  }
  let occurrence : Occurrence alignment.material source.elaborate := {
    interface := source.elaborate
    context := sourceView.intrinsicPath.toFocus.context
    host_iso := sourceHostIso
  }
  have targetHostIso : OpenDiagramIso target.elaborate
      (source.elaborate.withBody
        (sourceView.intrinsicPath.toFocus.context.fill
          alignment.replacement)) := by
    apply OpenDiagramIso.replaceContext sourceView.intrinsicPath
      targetResult.witness outerWire.symm alignment.holeWire.symm
        alignment.holeRelsEq.symm
    · intro position
      apply Fin.ext
      rfl
    · exact alignment.contexts.symm
    · exact alignment.target_iso
  refine ⟨_, _, alignment.material, alignment.replacement, occurrence,
    targetHostIso, ?_⟩
  cases polarityEq : occurrence.context.polarity <;>
      simp only [Rule.atPolarity, Rule.converse, Rule.symmetric]
  · exact Or.inr alignment.step
  · exact Or.inl alignment.step

end VisualProof.Refinement.Implementation.DoubleCutElimContext
