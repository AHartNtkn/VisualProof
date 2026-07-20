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
      Option (Region signature currentContext.length currentRels))
    (aliasIndex : Fin (aliasCount pattern attachment))
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern attachment bodyContainer) recurse context
      binders [.node (aliasNode pattern attachment aliasIndex)] = some items)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItemSeq model named env relEnv items ↔
      ∀ output input,
        ConcreteElaboration.resolvePort?
            (materializedDiagram pattern attachment bodyContainer) context
            (aliasNode pattern attachment aliasIndex) .output = some output →
        ConcreteElaboration.resolvePort?
            (materializedDiagram pattern attachment bodyContainer) context
            (aliasNode pattern attachment aliasIndex) (.free 0) = some input →
        env output = env input := by
  simp only [ConcreteElaboration.compileOccurrencesWith?,
    ConcreteElaboration.compileOccurrenceWith?] at compiled
  unfold ConcreteElaboration.compileNode? at compiled
  have aliasShape :
      (materializedDiagram pattern attachment bodyContainer).nodes
          (aliasNode pattern attachment aliasIndex) =
        .term bodyContainer 1 (.port 0) := by
    simp [materializedDiagram, aliasNode]
  rw [aliasShape] at compiled
  cases outputResult : ConcreteElaboration.resolvePort?
      (materializedDiagram pattern attachment bodyContainer) context
      (aliasNode pattern attachment aliasIndex) .output with
  | none =>
      rw [outputResult] at compiled
      simp at compiled
  | some output =>
      rw [outputResult] at compiled
      simp only [Option.bind_some] at compiled
      cases freeResult : ConcreteElaboration.resolvePorts?
          (materializedDiagram pattern attachment bodyContainer) context
          (aliasNode pattern attachment aliasIndex) 1 (fun index => .free index) with
      | none =>
          rw [freeResult] at compiled
          simp at compiled
      | some free =>
          rw [freeResult] at compiled
          change some (ItemSeq.cons
            (Item.equation output ((Lambda.Term.port 0).mapFree free))
              ItemSeq.nil) = some items at compiled
          injection compiled with itemsEq
          subst items
          simp only [denoteItemSeq_cons, denoteItem_equation,
            denoteItemSeq_nil, and_true]
          rw [model.eval_mapFree]
          have evalPort : model.eval (Lambda.Term.port 0)
              (env ∘ free) = env (free 0) := by
            simpa using model.eval_port (0 : Fin 1) (env ∘ free)
          rw [evalPort]
          constructor
          · intro equality candidateOutput candidateInput candidateOutputResult
              candidateInputResult
            have outputEq : candidateOutput = output :=
              Option.some.inj candidateOutputResult.symm
            have inputResult : ConcreteElaboration.resolvePorts?
                (materializedDiagram pattern attachment bodyContainer) context
                (aliasNode pattern attachment aliasIndex) 1
                (fun index => .free index) = some free := freeResult
            have inputEq : candidateInput = free 0 := by
              have singleton := sequenceFin_sound inputResult (0 : Fin 1)
              change ConcreteElaboration.resolvePort?
                  (materializedDiagram pattern attachment bodyContainer) context
                  (aliasNode pattern attachment aliasIndex) (.free 0) =
                some (free 0) at singleton
              rw [candidateInputResult] at singleton
              exact Option.some.inj singleton
            simpa [outputEq, inputEq] using equality
          · intro property
            apply property output (free 0) rfl
            exact sequenceFin_sound freeResult (0 : Fin 1)

/-- Under the collapse environment, every inserted identity block denotes. -/
theorem aliasOccurrences_denote_of_collapse
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
      Option (Region signature currentContext.length currentRels))
    (items : ItemSeq signature targetContext.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (materializedDiagram pattern.val attachment spine.bodyContainer) recurse
      targetContext binders (aliasOccurrences pattern.val attachment) = some items)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (envEq : targetEnv = sourceEnv ∘ collapse.indexMap)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItemSeq model named targetEnv relEnv items := by
  subst targetEnv
  unfold aliasOccurrences at compiled
  have general : ∀ (aliases : List (Fin (aliasCount pattern.val attachment)))
      (items : ItemSeq signature targetContext.length rels),
      ConcreteElaboration.compileOccurrencesWith? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer) recurse
          targetContext binders
          (aliases.map fun current =>
            .node (aliasNode pattern.val attachment current)) = some items →
      denoteItemSeq model named (sourceEnv ∘ collapse.indexMap) relEnv items := by
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
      cases headResult : ConcreteElaboration.compileOccurrenceWith? signature
          (materializedDiagram pattern.val attachment spine.bodyContainer)
          recurse targetContext binders
          (.node (aliasNode pattern.val attachment aliasIndex)) with
      | none =>
          rw [headResult] at currentCompiled
          simp at currentCompiled
      | some head =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith? signature
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
                    signature
                    (materializedDiagram pattern.val attachment spine.bodyContainer)
                    recurse targetContext binders
                    [.node (aliasNode pattern.val attachment aliasIndex)] =
                      some (.cons head .nil) := by
                  simp only [ConcreteElaboration.compileOccurrencesWith?]
                  rw [headResult]
                  rfl
                have blockDenotes := (aliasOccurrence_denotes_iff pattern.val attachment
                  spine.bodyContainer targetContext binders recurse aliasIndex
                  (.cons head .nil) oneCompiled model named
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
