import VisualProof.Rule.Soundness.AttachmentAliasSemanticIdentity

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- Denotation of a compiled alias list exposes the equation belonging to
each member of that list.  The list order is retained throughout. -/
theorem compiledAliases_value_eq
    (pattern : OpenConcreteDiagram)
    (attachment : Fin pattern.boundary.length → Host)
    (bodyContainer : Fin pattern.diagram.regionCount)
    (context : ConcreteElaboration.WireContext
      (materializedDiagram pattern attachment bodyContainer))
    (binders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern attachment bodyContainer) rels)
    (recurse : ∀ {currentRels : RelCtx},
      Fin pattern.diagram.regionCount →
      (currentContext : ConcreteElaboration.WireContext
        (materializedDiagram pattern attachment bodyContainer)) →
      ConcreteElaboration.BinderContext
        (materializedDiagram pattern attachment bodyContainer) currentRels →
      Option (Region signature currentContext.length currentRels))
    (aliases : List (Fin (aliasCount pattern attachment)))
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern attachment bodyContainer) recurse context
      binders (aliases.map fun aliasIndex =>
        .node (aliasNode pattern attachment aliasIndex)) = some items)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (denotes : denoteItemSeq model named env relEnv items) :
    ∀ aliasIndex, aliasIndex ∈ aliases → ∀ output input,
      ConcreteElaboration.resolvePort?
          (materializedDiagram pattern attachment bodyContainer) context
          (aliasNode pattern attachment aliasIndex) .output = some output →
      ConcreteElaboration.resolvePort?
          (materializedDiagram pattern attachment bodyContainer) context
          (aliasNode pattern attachment aliasIndex) (.free 0) = some input →
      env output = env input := by
  induction aliases generalizing items with
  | nil => simp
  | cons head tail induction =>
      simp only [List.map_cons,
        ConcreteElaboration.compileOccurrencesWith?] at compiled
      cases headResult : ConcreteElaboration.compileOccurrenceWith? signature
          (materializedDiagram pattern attachment bodyContainer) recurse context
          binders (.node (aliasNode pattern attachment head)) with
      | none =>
          rw [headResult] at compiled
          simp at compiled
      | some headItem =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith?
              signature (materializedDiagram pattern attachment bodyContainer)
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
                    ConcreteElaboration.compileOccurrencesWith? signature
                      (materializedDiagram pattern attachment bodyContainer)
                      recurse context binders
                      [.node (aliasNode pattern attachment head)] =
                        some (.cons headItem .nil) := by
                    simp only [ConcreteElaboration.compileOccurrencesWith?]
                    rw [headResult]
                    rfl
                exact (aliasOccurrence_denotes_iff pattern attachment
                  bodyContainer context binders recurse head
                  (.cons headItem .nil) singletonCompiled model named env
                  relEnv).1 (by
                    simpa only [denoteItemSeq_cons, denoteItemSeq_nil,
                      and_true] using denotes.1)
                  output input outputResult inputResult
              · have tailMember : aliasIndex ∈ tail :=
                  (List.mem_cons.mp member).resolve_left current
                exact induction tailItems tailResult denotes.2 aliasIndex tailMember
                  output input outputResult inputResult

noncomputable def factoredSourceEnv
    {signature : List Nat}
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    {targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer)}
    {sourceContext : ConcreteElaboration.WireContext pattern.val.diagram}
    {D : Type}
    (collapse : ContextCollapse pattern attachment spine targetContext
      sourceContext)
    (targetEnv : Fin targetContext.length → D) :
    Fin sourceContext.length → D :=
  targetEnv ∘ collapse.oldIndex

/-- The inserted equations are complete for the collapse: once their block
denotes, every target context value factors through the source context. -/
theorem aliasOccurrences_factor_collapse
    (pattern : CheckedOpenDiagram signature)
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        signature)
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (targetExact : targetContext.Exact spine.bodyContainer)
    (sourceNodup : sourceContext.Nodup)
    (binders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (recurse : ∀ {currentRels : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (currentContext : ConcreteElaboration.WireContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)) →
      ConcreteElaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)
          currentRels →
      Option (Region signature currentContext.length currentRels))
    (items : ItemSeq signature targetContext.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer) recurse
      targetContext binders (aliasOccurrences pattern.val attachment) = some items)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (denotes : denoteItemSeq model named targetEnv relEnv items) :
    targetEnv = factoredSourceEnv collapse targetEnv ∘ collapse.indexMap := by
  have aliasEquations := compiledAliases_value_eq pattern.val attachment
    spine.bodyContainer targetContext binders recurse
    (allFin (aliasCount pattern.val attachment)) items (by
      simpa only [aliasOccurrences] using compiled)
    model named targetEnv relEnv denotes
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
      ConcreteElaboration.checked_resolvePort?_complete targetWellFormed
        (context := targetContext) (region := spine.bodyContainer)
        (node := aliasNode pattern.val attachment aliasIndex) (port := .output)
        targetExact.covers (by
          rw [show (materializedDiagram pattern.val attachment
              spine.bodyContainer).nodes
                (aliasNode pattern.val attachment aliasIndex) =
              .term spine.bodyContainer 1 (.port 0) by
            simp [materializedDiagram, aliasNode]]
          rfl) (by
          simp [ConcreteDiagram.RequiresPort, materializedDiagram, aliasNode])
    obtain ⟨input, inputResult⟩ :=
      ConcreteElaboration.checked_resolvePort?_complete targetWellFormed
        (context := targetContext) (region := spine.bodyContainer)
        (node := aliasNode pattern.val attachment aliasIndex) (port := .free 0)
        targetExact.covers (by
          rw [show (materializedDiagram pattern.val attachment
              spine.bodyContainer).nodes
                (aliasNode pattern.val attachment aliasIndex) =
              .term spine.bodyContainer 1 (.port 0) by
            simp [materializedDiagram, aliasNode]]
          rfl) (by
          simp [ConcreteDiagram.RequiresPort, materializedDiagram, aliasNode])
    have valueEq := aliasEquations aliasIndex aliasMember output input
      outputResult inputResult
    obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
      ConcreteElaboration.resolvePort?_sound outputResult
    obtain ⟨inputWire, inputOccurs, inputGet⟩ :=
      ConcreteElaboration.resolvePort?_sound inputResult
    have inputWireEq : inputWire = aliasWire pattern.val attachment aliasIndex := by
      apply ConcreteElaboration.endpoint_wire_unique
        targetWellFormed.wire_endpoints_are_disjoint inputOccurs
      unfold ConcreteDiagram.EndpointOccurs
      rw [show (materializedDiagram pattern.val attachment
          spine.bodyContainer).wires
            (aliasWire pattern.val attachment aliasIndex) = {
              scope := pattern.val.diagram.root
              endpoints := [⟨aliasNode pattern.val attachment aliasIndex,
                .free 0⟩]
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
      apply ConcreteElaboration.endpoint_wire_unique
        targetWellFormed.wire_endpoints_are_disjoint outputOccurs
      unfold ConcreteDiagram.EndpointOccurs
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

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
