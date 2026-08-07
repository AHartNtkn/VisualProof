import VisualProof.Rule.Soundness.AttachmentAliasSemanticIdentity

namespace VisualProof.Concrete.Splice.AttachmentAliasMaterialization

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- Denotation of a compiled alias list exposes the equation belonging to
each member of that list.  The list order is retained throughout. -/
theorem compiledAliases_value_eq
    (pattern : Concrete.OpenDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (context : Concrete.Elaboration.WireContext
      (materializedDiagram pattern attachment bodyContainer))
    (binders : Concrete.Elaboration.BinderContext
      (materializedDiagram pattern attachment bodyContainer) rels)
    (recurse : ∀ {currentRels : RelCtx},
      Fin pattern.diagram.regionCount →
      (currentContext : Concrete.Elaboration.WireContext
        (materializedDiagram pattern attachment bodyContainer)) →
      Concrete.Elaboration.BinderContext
        (materializedDiagram pattern attachment bodyContainer) currentRels →
      Option (Region  currentContext.length currentRels))
    (aliases : List (Fin (aliasCount pattern attachment)))
    (items : ItemSeq  context.length rels)
    (compiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern attachment bodyContainer) recurse context
      binders (aliases.map fun aliasIndex =>
        .node (aliasNode pattern attachment aliasIndex)) = some items)
    (model : Model)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (denotes : denoteItemSeq model  env relEnv items) :
    ∀ aliasIndex, aliasIndex ∈ aliases → ∀ output input,
      Concrete.Elaboration.resolvePort?
          (materializedDiagram pattern attachment bodyContainer) context
          (aliasNode pattern attachment aliasIndex) (.arg 0) = some output →
      Concrete.Elaboration.resolvePort?
          (materializedDiagram pattern attachment bodyContainer) context
          (aliasNode pattern attachment aliasIndex) (.arg 1) = some input →
      env output = env input := by
  induction aliases generalizing items with
  | nil => simp
  | cons head tail induction =>
      simp only [List.map_cons,
        Concrete.Elaboration.compileOccurrencesWith?] at compiled
      cases headResult : Concrete.Elaboration.compileOccurrenceWith?
          (materializedDiagram pattern attachment bodyContainer) recurse context
          binders (.node (aliasNode pattern attachment head)) with
      | none =>
          rw [headResult] at compiled
          simp at compiled
      | some headItem =>
          cases tailResult : Concrete.Elaboration.compileOccurrencesWith?
               (materializedDiagram pattern attachment bodyContainer)
              recurse context binders
              (tail.map fun aliasIndex =>
                .node (aliasNode pattern attachment aliasIndex)) with
          | none =>
              rw [headResult, tailResult] at compiled
              simp at compiled
          | some tailItems =>
              rw [headResult, tailResult] at compiled
              injection compiled with itemsEq
              subst items
              rw [denoteItemSeq_cons] at denotes
              intro aliasIndex member output input outputResult inputResult
              by_cases current : aliasIndex = head
              · subst aliasIndex
                have singletonCompiled :
                    Concrete.Elaboration.compileOccurrencesWith?
                      (materializedDiagram pattern attachment bodyContainer)
                      recurse context binders
                      [.node (aliasNode pattern attachment head)] =
                        some (.cons headItem .nil) := by
                    simp only [Concrete.Elaboration.compileOccurrencesWith?]
                    rw [headResult]
                    rfl
                exact (aliasOccurrence_denotes_iff pattern attachment
                  bodyContainer context binders recurse head
                  (.cons headItem .nil) singletonCompiled model  env
                  relEnv).1 (by
                    simpa only [denoteItemSeq_cons, denoteItemSeq_nil,
                      and_true] using denotes.1)
                  output input outputResult inputResult
              · have tailMember : aliasIndex ∈ tail :=
                  (List.mem_cons.mp member).resolve_left current
                exact induction tailItems tailResult denotes.2 aliasIndex tailMember
                  output input outputResult inputResult

noncomputable def factoredSourceEnv
    {pattern : Concrete.CheckedOpen }
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    {targetContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer)}
    {sourceContext : Concrete.Elaboration.WireContext pattern.val.diagram}
    {D : Type}
    (collapse : ContextCollapse pattern attachment spine targetContext
      sourceContext)
    (targetEnv : Fin targetContext.length → D) :
    Fin sourceContext.length → D :=
  targetEnv ∘ collapse.oldIndex

/-- The inserted equations are complete for the collapse: once their block
denotes, every target context value factors through the source context. -/
theorem aliasOccurrences_factor_collapse
    (pattern : Concrete.CheckedOpen )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        )
    (targetContext : Concrete.Elaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (sourceContext : Concrete.Elaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (targetExact : targetContext.Exact spine.bodyContainer)
    (sourceNodup : sourceContext.Nodup)
    (binders : Concrete.Elaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (recurse : ∀ {currentRels : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (currentContext : Concrete.Elaboration.WireContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)) →
      Concrete.Elaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)
          currentRels →
      Option (Region  currentContext.length currentRels))
    (items : ItemSeq  targetContext.length rels)
    (compiled : Concrete.Elaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer) recurse
      targetContext binders (aliasOccurrences pattern.val attachment) = some items)
    (model : Model)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (denotes : denoteItemSeq model  targetEnv relEnv items) :
    targetEnv = factoredSourceEnv collapse targetEnv ∘ collapse.indexMap := by
  have aliasEquations := compiledAliases_value_eq pattern.val attachment
    spine.bodyContainer targetContext binders recurse
    (allFin (aliasCount pattern.val attachment)) items (by
      simpa only [aliasOccurrences] using compiled)
    model  targetEnv relEnv denotes
  funext targetIndex
  let targetWire := targetContext.get targetIndex
  refine Fin.addCases (motive := fun wire => targetWire = wire →
      targetEnv targetIndex =
        (factoredSourceEnv collapse targetEnv ∘ collapse.indexMap) targetIndex)
      ?_ ?_ targetWire rfl
  · intro old targetGet
    change targetContext.get targetIndex = liftOldWire pattern.val attachment old
      at targetGet
    have collapsed := collapse.get targetIndex
    rw [targetGet, collapseWire_old] at collapsed
    have oldGet := collapse.old_get (collapse.indexMap targetIndex)
    rw [collapsed] at oldGet
    have sameIndex : targetIndex =
        collapse.oldIndex (collapse.indexMap targetIndex) := by
      apply Fin.ext
      exact (List.getElem_inj targetExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using targetGet.trans oldGet.symm)
    change targetEnv targetIndex =
      targetEnv (collapse.oldIndex (collapse.indexMap targetIndex))
    exact congrArg targetEnv sameIndex
  · intro aliasIndex targetGet
    change targetContext.get targetIndex = aliasWire pattern.val attachment aliasIndex
      at targetGet
    have aliasMember : aliasIndex ∈ allFin (aliasCount pattern.val attachment) := by
      simp
    obtain ⟨output, outputResult⟩ :=
      Concrete.Elaboration.checked_resolvePort?_complete targetWellFormed
        (context := targetContext) (region := spine.bodyContainer)
        (node := aliasNode pattern.val attachment aliasIndex) (port := .arg 0)
        targetExact.covers (by
          rw [show (materializedDiagram pattern.val attachment
              spine.bodyContainer).nodes
                (aliasNode pattern.val attachment aliasIndex) =
              .identity spine.bodyContainer 2 by
            simp [materializedDiagram, aliasNode]]
          rfl) (by
          simp [Concrete.Diagram.RequiresPort, materializedDiagram, aliasNode])
    obtain ⟨input, inputResult⟩ :=
      Concrete.Elaboration.checked_resolvePort?_complete targetWellFormed
        (context := targetContext) (region := spine.bodyContainer)
        (node := aliasNode pattern.val attachment aliasIndex) (port := .arg 1)
        targetExact.covers (by
          rw [show (materializedDiagram pattern.val attachment
              spine.bodyContainer).nodes
                (aliasNode pattern.val attachment aliasIndex) =
              .identity spine.bodyContainer 2 by
            simp [materializedDiagram, aliasNode]]
          rfl) (by
          simp [Concrete.Diagram.RequiresPort, materializedDiagram, aliasNode])
    have valueEq := aliasEquations aliasIndex aliasMember output input
      outputResult inputResult
    obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
      Concrete.Elaboration.resolvePort?_sound outputResult
    obtain ⟨inputWire, inputOccurs, inputGet⟩ :=
      Concrete.Elaboration.resolvePort?_sound inputResult
    have inputWireEq : inputWire = aliasWire pattern.val attachment aliasIndex := by
      apply Concrete.Elaboration.endpoint_wire_unique
        targetWellFormed.wire_endpoints_are_disjoint inputOccurs
      unfold Concrete.Diagram.EndpointOccurs
      rw [show (materializedDiagram pattern.val attachment
          spine.bodyContainer).wires
            (aliasWire pattern.val attachment aliasIndex) = {
              scope := pattern.val.diagram.root
              endpoints := [⟨aliasNode pattern.val attachment aliasIndex,
                .arg 1⟩]
            } by simp [materializedDiagram, aliasWire]]
      simp
    have inputIndexEq : input = targetIndex := by
      apply Fin.ext
      exact (List.getElem_inj targetExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using inputGet.trans
          (inputWireEq.trans targetGet.symm))
    have outputWireEq : outputWire = liftOldWire pattern.val attachment
        (pattern.val.boundary.get
          (aliasOrigin pattern.val attachment aliasIndex)) := by
      apply Concrete.Elaboration.endpoint_wire_unique
        targetWellFormed.wire_endpoints_are_disjoint outputOccurs
      unfold Concrete.Diagram.EndpointOccurs
      rw [materialized_old_wire_endpoints]
      apply List.mem_append_right
      unfold aliasOutputs
      apply List.mem_filterMap.mpr
      refine ⟨aliasIndex, by simp, ?_⟩
      simp only [ite_true]
      rfl
    have collapsed := collapse.get targetIndex
    rw [targetGet, collapseWire_alias] at collapsed
    have oldGet := collapse.old_get (collapse.indexMap targetIndex)
    rw [collapsed] at oldGet
    have outputIndexEq : output =
        collapse.oldIndex (collapse.indexMap targetIndex) := by
      apply Fin.ext
      exact (List.getElem_inj targetExact.nodup).mp (by
        exact outputGet.trans (outputWireEq.trans oldGet.symm))
    change targetEnv targetIndex =
      targetEnv (collapse.oldIndex (collapse.indexMap targetIndex))
    exact (congrArg targetEnv inputIndexEq).symm.trans
      (valueEq.symm.trans (congrArg targetEnv outputIndexEq))

end Semantic

end VisualProof.Concrete.Splice.AttachmentAliasMaterialization
