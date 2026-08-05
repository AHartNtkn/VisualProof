import VisualProof.Rule.Soundness.AttachmentAliasSemanticContext

namespace VisualProof.Diagram.Splice.AttachmentAliasMaterialization

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

variable {Host : Type} [DecidableEq Host]

namespace Semantic

/-- A compiled inserted alias occurrence is exactly an equality between its
old-wire output and its fresh-wire input. -/
theorem aliasOccurrence_denotes_iff
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
      Option (Region  currentContext.length currentRels))
    (aliasIndex : Fin (aliasCount pattern attachment))
    (items : ItemSeq  context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith?
      (materializedDiagram pattern attachment bodyContainer) recurse context
      binders [.node (aliasNode pattern attachment aliasIndex)] = some items)
    (model : Model)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItemSeq model  env relEnv items ↔
      ∀ output input,
        ConcreteElaboration.resolvePort?
            (materializedDiagram pattern attachment bodyContainer) context
            (aliasNode pattern attachment aliasIndex) (.arg 0) = some output →
        ConcreteElaboration.resolvePort?
            (materializedDiagram pattern attachment bodyContainer) context
            (aliasNode pattern attachment aliasIndex) (.arg 1) = some input →
        env output = env input := by
  simp only [ConcreteElaboration.compileOccurrencesWith?,
    ConcreteElaboration.compileOccurrenceWith?] at compiled
  unfold ConcreteElaboration.compileNode? at compiled
  have aliasShape :
      (materializedDiagram pattern attachment bodyContainer).nodes
          (aliasNode pattern attachment aliasIndex) =
        .identity bodyContainer 2 := by
    simp [materializedDiagram, aliasNode]
  rw [aliasShape] at compiled
  simp only at compiled
  cases argumentsResult : ConcreteElaboration.resolvePorts?
      (materializedDiagram pattern attachment bodyContainer) context
      (aliasNode pattern attachment aliasIndex) 2 with
  | none =>
      rw [argumentsResult] at compiled
      simp at compiled
  | some arguments =>
      rw [argumentsResult] at compiled
      injection compiled with itemsEq
      subst items
      simp only [denoteItemSeq_cons, denoteItem_identity,
        denoteItemSeq_nil, and_true]
      have portResult (index : Fin 2) :
          ConcreteElaboration.resolvePort?
              (materializedDiagram pattern attachment bodyContainer) context
              (aliasNode pattern attachment aliasIndex) (.arg index) =
            some (arguments index) :=
        sequenceFin_sound argumentsResult index
      constructor
      · intro equality output input outputResult inputResult
        have outputEq : output = arguments 0 := by
          have atZero :
              ConcreteElaboration.resolvePort?
                  (materializedDiagram pattern attachment bodyContainer) context
                  (aliasNode pattern attachment aliasIndex) (.arg 0) =
                some (arguments 0) := by
            simpa using portResult (0 : Fin 2)
          rw [outputResult] at atZero
          exact Option.some.inj atZero
        have inputEq : input = arguments 1 := by
          have atOne :
              ConcreteElaboration.resolvePort?
                  (materializedDiagram pattern attachment bodyContainer) context
                  (aliasNode pattern attachment aliasIndex) (.arg 1) =
                some (arguments 1) := by
            simpa using portResult (1 : Fin 2)
          rw [inputResult] at atOne
          exact Option.some.inj atOne
        simpa [outputEq, inputEq] using equality (0 : Fin 2) (1 : Fin 2)
      · intro property left right
        have equality : env (arguments 0) = env (arguments 1) :=
          property (arguments 0) (arguments 1) (portResult 0) (portResult 1)
        have leftCases : left = 0 ∨ left = 1 := by omega
        have rightCases : right = 0 ∨ right = 1 := by omega
        rcases leftCases with rfl | rfl <;>
          rcases rightCases with rfl | rfl
        · rfl
        · exact equality
        · exact equality.symm
        · rfl

/-- Under the collapse environment, every inserted identity block denotes. -/
theorem aliasOccurrences_denote_of_collapse
    (pattern : CheckedOpenDiagram )
    (attachment : Fin pattern.val.boundary.length → Host)
    (spine : BinderSpine pattern.val.diagram)
    (targetWellFormed :
      (materializedDiagram pattern.val attachment spine.bodyContainer).WellFormed
        )
    (targetContext : ConcreteElaboration.WireContext
      (materializedDiagram pattern.val attachment spine.bodyContainer))
    (sourceContext : ConcreteElaboration.WireContext pattern.val.diagram)
    (collapse : ContextCollapse pattern attachment spine targetContext sourceContext)
    (sourceNodup : sourceContext.Nodup)
    (targetExact : targetContext.Exact spine.bodyContainer)
    (binders : ConcreteElaboration.BinderContext
      (materializedDiagram pattern.val attachment spine.bodyContainer) rels)
    (recurse : ∀ {currentRels : RelCtx},
      Fin pattern.val.diagram.regionCount →
      (currentContext : ConcreteElaboration.WireContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)) →
      ConcreteElaboration.BinderContext
        (materializedDiagram pattern.val attachment spine.bodyContainer)
          currentRels →
      Option (Region  currentContext.length currentRels))
    (items : ItemSeq  targetContext.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith?
      (materializedDiagram pattern.val attachment spine.bodyContainer) recurse
      targetContext binders (aliasOccurrences pattern.val attachment) = some items)
    (model : Model)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (envEq : targetEnv = sourceEnv ∘ collapse.indexMap)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItemSeq model  targetEnv relEnv items := by
  subst targetEnv
  unfold aliasOccurrences at compiled
  have general : ∀ (aliases : List (Fin (aliasCount pattern.val attachment)))
      (items : ItemSeq  targetContext.length rels),
      ConcreteElaboration.compileOccurrencesWith?
          (materializedDiagram pattern.val attachment spine.bodyContainer) recurse
          targetContext binders
          (aliases.map fun current =>
            .node (aliasNode pattern.val attachment current)) = some items →
      denoteItemSeq model  (sourceEnv ∘ collapse.indexMap) relEnv items := by
    intro aliases
    induction aliases with
    | nil =>
      intro currentItems currentCompiled
      simp [ConcreteElaboration.compileOccurrencesWith?] at currentCompiled
      subst currentItems
      simp
    | cons aliasIndex rest induction =>
      intro currentItems currentCompiled
      simp only [List.map_cons, ConcreteElaboration.compileOccurrencesWith?]
        at currentCompiled
      cases headResult : ConcreteElaboration.compileOccurrenceWith?
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          recurse targetContext binders
          (.node (aliasNode pattern.val attachment aliasIndex)) with
      | none =>
          rw [headResult] at currentCompiled
          simp at currentCompiled
      | some head =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith?
              (materializedDiagram pattern.val attachment spine.bodyContainer)
              recurse targetContext binders
              (rest.map fun current =>
                .node (aliasNode pattern.val attachment current)) with
          | none =>
              rw [headResult, tailResult] at currentCompiled
              simp at currentCompiled
          | some tail =>
              rw [headResult, tailResult] at currentCompiled
              injection currentCompiled with itemsEq
              subst currentItems
              rw [denoteItemSeq_cons]
              constructor
              · have oneCompiled : ConcreteElaboration.compileOccurrencesWith?

                    (materializedDiagram pattern.val attachment spine.bodyContainer)
                    recurse targetContext binders
                    [.node (aliasNode pattern.val attachment aliasIndex)] =
                      some (.cons head .nil) := by
                  simp only [ConcreteElaboration.compileOccurrencesWith?]
                  rw [headResult]
                  rfl
                have blockDenotes := (aliasOccurrence_denotes_iff pattern.val attachment
                  spine.bodyContainer targetContext binders recurse aliasIndex
                  (.cons head .nil) oneCompiled model
                  (sourceEnv ∘ collapse.indexMap) relEnv).2 (by
                    intro output input outputResult inputResult
                    obtain ⟨outputWire, outputOccurs, outputGet⟩ :=
                      ConcreteElaboration.resolvePort?_sound outputResult
                    obtain ⟨inputWire, inputOccurs, inputGet⟩ :=
                      ConcreteElaboration.resolvePort?_sound inputResult
                    have inputWireEq : inputWire = aliasWire pattern.val attachment
                        aliasIndex := by
                      apply ConcreteElaboration.endpoint_wire_unique
                        targetWellFormed.wire_endpoints_are_disjoint inputOccurs
                      unfold ConcreteDiagram.EndpointOccurs
                      simp only [materializedDiagram, aliasWire,
                        Fin.addCases_right]
                      exact List.mem_cons_self
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
                    have outputMap := collapse.get output
                    have inputMap := collapse.get input
                    have outputGetList : targetContext.get output = outputWire := by
                      simpa only [List.get_eq_getElem] using outputGet
                    have inputGetList : targetContext.get input = inputWire := by
                      simpa only [List.get_eq_getElem] using inputGet
                    rw [outputGetList, outputWireEq, collapseWire_old] at outputMap
                    rw [inputGetList, inputWireEq, collapseWire_alias] at inputMap
                    have indexEq : collapse.indexMap output =
                        collapse.indexMap input := by
                      apply Fin.ext
                      exact (List.getElem_inj sourceNodup).mp (by
                        simpa only [List.get_eq_getElem] using
                          outputMap.trans inputMap.symm)
                    exact congrArg sourceEnv indexEq)
                simpa only [denoteItemSeq_cons, denoteItemSeq_nil, and_true]
                  using blockDenotes
              · exact induction tail tailResult
  apply general (allFin (aliasCount pattern.val attachment)) items
  simpa only using compiled

end Semantic

end VisualProof.Diagram.Splice.AttachmentAliasMaterialization
