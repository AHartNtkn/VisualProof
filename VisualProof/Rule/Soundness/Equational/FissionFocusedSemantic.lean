import VisualProof.Rule.Soundness.Equational.FissionSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace FissionSoundness

def optionIndex : Option (Fin n) → Fin (n + 1)
  | none => Fin.last n
  | some wire => wire.castSucc

def optionEnvironment (environment : Option (Fin n) → D) : Fin (n + 1) → D :=
  Fin.lastCases (environment none) (fun wire => environment (some wire))

@[simp] theorem optionEnvironment_optionIndex
    (environment : Option (Fin n) → D) (value : Option (Fin n)) :
    optionEnvironment environment (optionIndex value) = environment value := by
  cases value <;> simp [optionEnvironment, optionIndex]

def optionSubstitution (producer : Lambda.Term 0 (Fin n)) :
    Fin (n + 1) → Lambda.Term 0 (Fin n) :=
  Fin.lastCases producer Lambda.Term.port

theorem mapOption_bind_optionSubstitution
    (residual : Lambda.Term 0 (Option (Fin n)))
    (producer : Lambda.Term 0 (Fin n)) :
    (residual.mapFree optionIndex).bindFree (optionSubstitution producer) =
      residual.bindFree (fillFresh 0 producer) := by
  rw [Lambda.Term.mapFree_eq_bindFree_ports,
    Lambda.Term.bindFree_assoc]
  apply congrArg (fun substitution => residual.bindFree substitution)
  funext value
  cases value with
  | none => simp [Lambda.Term.bindFree, optionIndex, optionSubstitution,
      fillFresh, liftClosedTo_zero]
  | some wire => simp [Lambda.Term.bindFree, optionIndex, optionSubstitution,
      fillFresh]

theorem eval_compact_option
    (model : Lambda.LambdaModel)
    (residual : Lambda.Term 0 (Option (Fin n)))
    (environment : Option (Fin n) → model.Carrier) :
    model.eval residual.compact (environment ∘ residual.freeSupport.get) =
      model.eval (residual.mapFree optionIndex)
        (optionEnvironment environment) := by
  calc
    model.eval residual.compact (environment ∘ residual.freeSupport.get) =
        model.eval residual.compact
          (optionEnvironment environment ∘ optionIndex ∘
            residual.freeSupport.get) := by
      apply congrArg (model.eval residual.compact)
      funext port
      simp [Function.comp_def]
    _ = model.eval
        (residual.compact.mapFree (optionIndex ∘ residual.freeSupport.get))
        (optionEnvironment environment) := by
      rw [model.eval_mapFree]
    _ = model.eval (residual.mapFree optionIndex)
        (optionEnvironment environment) := by
      apply congrArg (fun candidate => model.eval candidate
        (optionEnvironment environment))
      rw [← Lambda.Term.mapFree_comp]
      exact congrArg (Lambda.Term.mapFree optionIndex)
        residual.compact_reconstruct

noncomputable def wireValue
    (context : ConcreteElaboration.WireContext diagram)
    (fallback : D) (environment : Fin context.length → D)
    (wire : Fin diagram.wireCount) : D :=
  if member : wire ∈ context then
    environment (Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete member))
  else fallback

theorem wireValue_eq_of_get
    (context : ConcreteElaboration.WireContext diagram)
    (nodup : context.Nodup)
    (fallback : D) (environment : Fin context.length → D)
    (wire : Fin diagram.wireCount) (index : Fin context.length)
    (get : context.get index = wire) :
    wireValue context fallback environment wire = environment index := by
  unfold wireValue
  split
  · rename_i member
    let found := Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete member)
    have foundResult := Classical.choose_spec
      (ConcreteElaboration.WireContext.lookup?_complete member)
    have foundGet := ConcreteElaboration.WireContext.lookup?_sound foundResult
    have equality : found = index := by
      apply Fin.ext
      exact (List.getElem_inj nodup).mp (by
        simpa only [List.get_eq_getElem] using foundGet.trans get.symm)
    exact congrArg environment equality
  · rename_i absent
    exact False.elim (absent (get ▸ List.get_mem context index))

theorem targetOldValue_eq_of_get
    (embedding : ContextEmbedding input selected site producer residual
      sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (sourceEnvironment : Fin sourceContext.length → D)
    (targetEnvironment : Fin targetContext.length → D)
    (agrees : (ConcreteElaboration.ContextIndexRelation.forwardMap
      embedding.index).EnvironmentsAgree sourceEnvironment targetEnvironment)
    (fallback : D) (wire : Fin input.val.wireCount)
    (targetIndex : Fin targetContext.length)
    (targetGet : targetContext.get targetIndex = wire.castSucc) :
    targetEnvironment targetIndex =
      wireValue sourceContext fallback sourceEnvironment wire := by
  have targetMember : wire.castSucc ∈ targetContext :=
    targetGet ▸ List.get_mem targetContext targetIndex
  have sourceMember : wire ∈ sourceContext :=
    (embedding.mem_old wire).mp targetMember
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  have sourceGet : sourceContext.get sourceIndex = wire :=
    ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  have targetIndexEq : targetIndex = embedding.index sourceIndex :=
    embedding.index_eq_of_get targetNodup sourceIndex targetIndex (by
      rw [targetGet, sourceGet])
  rw [targetIndexEq]
  have environmentEq := agrees sourceIndex (embedding.index sourceIndex) rfl
  rw [← environmentEq]
  exact (wireValue_eq_of_get sourceContext sourceNodup fallback
    sourceEnvironment wire sourceIndex sourceGet).symm

theorem selectedProducer_item_denote_iff
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (portWire : Fin freePorts → Fin input.val.wireCount)
    (depth : Nat) (selectedTerm : Lambda.Term depth
      (Fin input.val.wireCount))
    (path : List Lambda.PathSegment)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (nodeShape : input.val.nodes selected = .term site freePorts term)
    (resolved : resolveNodeFreeWires? input selected freePorts = some portWire)
    (selectedResult : subtermAt? (term.mapFree portWire) path =
      some ⟨depth, selectedTerm⟩)
    (residualResult : replaceAtPort?
      ((term.mapFree portWire).mapFree some) path none = some residual)
    (producerResult : lowerToZero depth selectedTerm = some producer)
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (fissionRaw input selected site producer residual))
    (embedding : ContextEmbedding input selected site producer residual
      sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (sourceItem : Item signature sourceContext.length rels)
    (residualItem producerItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input.val
      sourceContext binders selected = some sourceItem)
    (residualCompiled : ConcreteElaboration.compileNode? signature
      (fissionRaw input selected site producer residual) targetContext binders
      selected.castSucc = some residualItem)
    (producerCompiled : ConcreteElaboration.compileNode? signature
      (fissionRaw input selected site producer residual) targetContext binders
      (Fin.last input.val.nodeCount) = some producerItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnvironment : Fin sourceContext.length → model.Carrier)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (relEnvironment : RelEnv model.Carrier rels)
    (agrees : (ConcreteElaboration.ContextIndexRelation.forwardMap
      embedding.index).EnvironmentsAgree sourceEnvironment targetEnvironment) :
    denoteItem model named targetEnvironment relEnvironment producerItem →
      (denoteItem model named sourceEnvironment relEnvironment sourceItem ↔
        denoteItem model named targetEnvironment relEnvironment residualItem) := by
  unfold ConcreteElaboration.compileNode? at sourceCompiled residualCompiled producerCompiled
  rw [nodeShape] at sourceCompiled
  have residualShape :
      (fissionRaw input selected site producer residual).nodes
          selected.castSucc =
        .term site residual.freeSupport.length residual.compact := by
    simp [fissionRaw, nodeShape]
  rw [residualShape] at residualCompiled
  rw [fissionRaw_producer_node] at producerCompiled
  cases sourceOutputResult : ConcreteElaboration.resolvePort? input.val
      sourceContext selected .output with
  | none => simp [sourceOutputResult] at sourceCompiled
  | some sourceOutput =>
    cases sourceFreeResult : ConcreteElaboration.resolvePorts? input.val
        sourceContext selected freePorts (fun port => .free port) with
    | none => simp [sourceOutputResult, sourceFreeResult] at sourceCompiled
    | some sourceFree =>
      simp [sourceOutputResult, sourceFreeResult] at sourceCompiled
      subst sourceItem
      cases residualOutputResult : ConcreteElaboration.resolvePort?
          (fissionRaw input selected site producer residual) targetContext
          selected.castSucc .output with
      | none => simp [residualOutputResult] at residualCompiled
      | some residualOutput =>
        cases residualFreeResult : ConcreteElaboration.resolvePorts?
            (fissionRaw input selected site producer residual) targetContext
            selected.castSucc residual.freeSupport.length
            (fun port => .free port) with
        | none =>
            simp [residualOutputResult, residualFreeResult] at residualCompiled
        | some residualFree =>
          simp [residualOutputResult, residualFreeResult] at residualCompiled
          subst residualItem
          cases producerOutputResult : ConcreteElaboration.resolvePort?
              (fissionRaw input selected site producer residual) targetContext
              (Fin.last input.val.nodeCount) .output with
          | none => simp [producerOutputResult] at producerCompiled
          | some producerOutput =>
            cases producerFreeResult : ConcreteElaboration.resolvePorts?
                (fissionRaw input selected site producer residual) targetContext
                (Fin.last input.val.nodeCount) producer.freeSupport.length
                (fun port => .free port) with
            | none =>
                simp [producerOutputResult, producerFreeResult]
                  at producerCompiled
            | some producerFree =>
              simp [producerOutputResult, producerFreeResult]
                at producerCompiled
              subst producerItem
              intro producerDenotes
              let fallback : model.Carrier := model.eval
                (Lambda.Term.lam (Lambda.Term.bvar 0) :
                  Lambda.Term 0 (Fin 0)) Fin.elim0
              let global : Fin input.val.wireCount → model.Carrier :=
                wireValue sourceContext fallback sourceEnvironment
              obtain ⟨sourceOutputOwner, sourceOutputOccurs, sourceOutputGet⟩ :=
                ConcreteElaboration.resolvePort?_sound sourceOutputResult
              obtain ⟨residualOutputOwner, residualOutputOccurs,
                  residualOutputGet⟩ :=
                ConcreteElaboration.resolvePort?_sound residualOutputResult
              have residualOutputOwnerEq :
                  residualOutputOwner = sourceOutputOwner.castSucc := by
                apply ConcreteElaboration.endpoint_wire_unique
                  targetWellFormed.wire_endpoints_are_disjoint
                  residualOutputOccurs
                exact fissionRaw_selected_output_occurs input selected site
                  producer residual sourceOutputOwner sourceOutputOccurs
              have sourceOutputGet' :
                  sourceContext.get sourceOutput = sourceOutputOwner := by
                simpa only [List.get_eq_getElem] using sourceOutputGet
              have residualOutputGet' :
                  targetContext.get residualOutput =
                    sourceOutputOwner.castSucc := by
                have getOwner : targetContext.get residualOutput =
                    residualOutputOwner := by
                  simpa only [List.get_eq_getElem] using residualOutputGet
                exact getOwner.trans residualOutputOwnerEq
              have outputValueEq :
                  sourceEnvironment sourceOutput =
                    targetEnvironment residualOutput := by
                calc
                  sourceEnvironment sourceOutput = global sourceOutputOwner :=
                    (wireValue_eq_of_get sourceContext sourceNodup fallback
                      sourceEnvironment sourceOutputOwner sourceOutput
                      sourceOutputGet').symm
                  _ = targetEnvironment residualOutput :=
                    (targetOldValue_eq_of_get embedding sourceNodup targetNodup
                      sourceEnvironment targetEnvironment agrees fallback
                      sourceOutputOwner residualOutput residualOutputGet').symm
              have sourceFreeValues : sourceEnvironment ∘ sourceFree =
                  global ∘ portWire := by
                funext port
                have resolvedPort := sequenceFin_sound sourceFreeResult port
                obtain ⟨owner, ownerOccurs, ownerGet⟩ :=
                  ConcreteElaboration.resolvePort?_sound resolvedPort
                have ownerResolution : ConcreteElaboration.endpointOwner?
                    input.val { node := selected, port := .free port } =
                      some (portWire port) := sequenceFin_sound resolved port
                have intendedOccurs :=
                  ConcreteElaboration.endpointOwner?_sound ownerResolution
                have ownerEq : owner = portWire port :=
                  ConcreteElaboration.endpoint_wire_unique
                    input.property.wire_endpoints_are_disjoint ownerOccurs
                    intendedOccurs
                have get' : sourceContext.get (sourceFree port) =
                    portWire port := by
                  have getOwner : sourceContext.get (sourceFree port) = owner := by
                    simpa only [List.get_eq_getElem] using ownerGet
                  exact getOwner.trans ownerEq
                simp only [Function.comp_apply, global]
                exact (wireValue_eq_of_get sourceContext sourceNodup fallback
                  sourceEnvironment (portWire port) (sourceFree port) get').symm
              obtain ⟨producerOutputOwner, producerOutputOccurs,
                  producerOutputGet⟩ :=
                ConcreteElaboration.resolvePort?_sound producerOutputResult
              have producerOutputOwnerEq : producerOutputOwner =
                  Fin.last input.val.wireCount := by
                apply ConcreteElaboration.endpoint_wire_unique
                  targetWellFormed.wire_endpoints_are_disjoint
                  producerOutputOccurs
                exact fissionRaw_producer_output_occurs input selected site
                  producer residual
              have producerOutputGet' : targetContext.get producerOutput =
                  Fin.last input.val.wireCount := by
                have getOwner : targetContext.get producerOutput =
                    producerOutputOwner := by
                  simpa only [List.get_eq_getElem] using producerOutputGet
                exact getOwner.trans producerOutputOwnerEq
              have producerFreeValues : targetEnvironment ∘ producerFree =
                  global ∘ producer.freeSupport.get := by
                funext port
                have resolvedPort := sequenceFin_sound producerFreeResult port
                obtain ⟨owner, ownerOccurs, ownerGet⟩ :=
                  ConcreteElaboration.resolvePort?_sound resolvedPort
                have intendedOccurs := fissionRaw_producer_free_occurs input
                  selected site producer residual port
                have ownerEq : owner = (producer.freeSupport.get port).castSucc :=
                  ConcreteElaboration.endpoint_wire_unique
                    targetWellFormed.wire_endpoints_are_disjoint ownerOccurs
                    intendedOccurs
                have get' : targetContext.get (producerFree port) =
                    (producer.freeSupport.get port).castSucc := by
                  have getOwner : targetContext.get (producerFree port) = owner := by
                    simpa only [List.get_eq_getElem] using ownerGet
                  exact getOwner.trans ownerEq
                simp only [Function.comp_apply, global]
                exact targetOldValue_eq_of_get embedding sourceNodup targetNodup
                  sourceEnvironment targetEnvironment agrees fallback
                  (producer.freeSupport.get port) (producerFree port) get'
              have producerEquation : targetEnvironment producerOutput =
                  model.eval producer global := by
                simp only [denoteItem_equation, model.eval_mapFree] at producerDenotes
                rw [producerFreeValues,
                  LambdaModel.eval_compact model producer global] at producerDenotes
                exact producerDenotes
              let fill : Option (Fin input.val.wireCount) → model.Carrier
                | none => targetEnvironment producerOutput
                | some wire => global wire
              have residualFreeValues : targetEnvironment ∘ residualFree =
                  fill ∘ residual.freeSupport.get := by
                funext port
                have resolvedPort := sequenceFin_sound residualFreeResult port
                obtain ⟨owner, ownerOccurs, ownerGet⟩ :=
                  ConcreteElaboration.resolvePort?_sound resolvedPort
                have intendedOccurs := fissionRaw_residual_free_occurs input
                  selected site producer residual port
                have ownerEq : owner = match residual.freeSupport.get port with
                    | none => Fin.last input.val.wireCount
                    | some wire => wire.castSucc :=
                  ConcreteElaboration.endpoint_wire_unique
                    targetWellFormed.wire_endpoints_are_disjoint ownerOccurs
                    intendedOccurs
                have get' : targetContext.get (residualFree port) =
                    match residual.freeSupport.get port with
                    | none => Fin.last input.val.wireCount
                    | some wire => wire.castSucc := by
                  have getOwner : targetContext.get (residualFree port) = owner := by
                    simpa only [List.get_eq_getElem] using ownerGet
                  exact getOwner.trans ownerEq
                cases support : residual.freeSupport.get port with
                | none =>
                    simp only [support] at get'
                    have indexEq : residualFree port = producerOutput := by
                      apply Fin.ext
                      exact (List.getElem_inj targetNodup).mp (by
                        simpa only [List.get_eq_getElem] using
                          get'.trans producerOutputGet'.symm)
                    simp only [Function.comp_apply, support, fill, indexEq]
                | some wire =>
                    simp only [support] at get'
                    simp only [fill, Function.comp_apply, support]
                    exact targetOldValue_eq_of_get embedding sourceNodup
                      targetNodup sourceEnvironment targetEnvironment agrees
                      fallback wire (residualFree port) get'
              have reconstruction := replaceSelected_reconstruct
                (term.mapFree portWire) path depth selectedTerm residual producer
                selectedResult residualResult producerResult
              have evaluationEq : model.eval residual.compact
                    (fill ∘ residual.freeSupport.get) =
                  model.eval (term.mapFree portWire) global := by
                rw [eval_compact_option]
                have mappedReconstruction :
                    (residual.mapFree optionIndex).bindFree
                        (optionSubstitution producer) =
                      term.mapFree portWire :=
                  (mapOption_bind_optionSubstitution
                    (n := input.val.wireCount) residual producer).trans
                    reconstruction
                calc
                  model.eval (residual.mapFree optionIndex)
                      (optionEnvironment fill) =
                      model.eval (residual.mapFree optionIndex)
                        (fun index => model.eval
                          (optionSubstitution producer index) global) := by
                    apply congrArg (model.eval (residual.mapFree optionIndex))
                    funext index
                    refine Fin.lastCases ?_ (fun wire => ?_) index
                    · simp [optionEnvironment, optionSubstitution,
                        producerEquation, fill]
                    · simp [optionEnvironment, optionSubstitution,
                        model.eval_port, fill]
                  _ = model.eval
                      ((residual.mapFree optionIndex).bindFree
                        (optionSubstitution producer)) global :=
                    (model.eval_bindFree _ _ _).symm
                  _ = model.eval (term.mapFree portWire) global :=
                    congrArg (fun candidate => model.eval candidate global)
                      mappedReconstruction
              simp only [denoteItem_equation, model.eval_mapFree]
              rw [sourceFreeValues, residualFreeValues, evaluationEq,
                model.eval_mapFree, outputValueEq]

end FissionSoundness

end VisualProof.Rule
