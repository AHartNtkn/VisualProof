import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.NestedScopedRewrite
import VisualProof.Diagram.Semantics.OpenIsomorphism
import VisualProof.Diagram.Semantics.ScopedRewrite
import VisualProof.Rule.Lambda.Fission

namespace VisualProof.Rule.Lambda

open Diagram
open Theory

private theorem Values.exists_append
    (values : Values model (left ++ right)) :
    ∃ (leftValues : Values model left) (rightValues : Values model right),
      leftValues.append rightValues = values := by
  induction left with
  | nil => exact ⟨PUnit.unit, values, rfl⟩
  | cons signature rest induction =>
      rcases values with ⟨head, tail⟩
      rcases induction tail with ⟨leftValues, rightValues, equality⟩
      exact ⟨(head, leftValues), rightValues, congrArg (Prod.mk head) equality⟩

private def Values.snocIota (values : Values model context)
    (fresh : model.Carrier) : Values model (context ++ [Sig.iota]) :=
  Values.append values
    ((fresh, PUnit.unit) : Values model [Sig.iota])

@[simp] private theorem Values.lookup_snocIota_left
    (values : Values model context) (fresh : model.Carrier)
    (wire : Var context signature) :
    (Values.snocIota values fresh).lookup (wire.appendLeft [Sig.iota]) =
      values.lookup wire := by
  simp [Values.snocIota]

@[simp] private theorem Values.lookup_snocIota_last
    (values : Values model context) (fresh : model.Carrier) :
    (Values.snocIota values fresh).lookup
      (Var.appendRight context (.here : Var [Sig.iota] .iota)) = fresh := by
  unfold Values.snocIota
  rw [Values.lookup_append_right]
  rfl

namespace Fission

private theorem retainedEnvironment
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (fresh : model.Carrier) :
    Values.rename description.retain
        (Values.append outerEnv (Values.snocIota localEnv fresh)) =
      outerEnv.append localEnv := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases (left := outer) (right := description.locals)
    (motive := fun wire =>
      (Values.rename description.retain
        (outerEnv.append (Values.snocIota localEnv fresh))).lookup wire =
      (outerEnv.append localEnv).lookup wire)
  · intro inheritedSignature inherited
    simp [Description.retain, Region.adjoinHostWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [Description.retain, Region.adjoinHostWire,
      Region.conjoinLeftWire]

private theorem retainedLookup
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (fresh : model.Carrier)
    (wire : Var (outer ++ description.locals) signature) :
    (outerEnv.append (Values.snocIota localEnv fresh)).lookup
        (description.retain wire) =
      (outerEnv.append localEnv).lookup wire := by
  have environments := retainedEnvironment description model outerEnv
    localEnv fresh
  have lookup := congrArg (fun values => values.lookup wire) environments
  simpa only [Values.lookup_rename] using lookup

private theorem freshLookup
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (fresh : model.Carrier) :
    (outerEnv.append (Values.snocIota localEnv fresh)).lookup
      description.bridge = fresh := by
  simp only [Description.bridge, Values.lookup_append_right,
    Values.snocIota]
  rfl

private theorem residualEnvironment
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (localEnv : Values model description.locals) :
    let baseEnv := outerEnv.append localEnv
    let selectedValue := model.eval description.selected
      (fun slot => baseEnv.lookup (description.ports slot))
    (fun slot =>
      (outerEnv.append (Values.snocIota localEnv selectedValue)).lookup
        (description.residualPorts slot)) =
      (fun slot => model.eval
        (Fission.bridgeSubstitution description.selected slot)
        (fun native => baseEnv.lookup (description.ports native))) := by
  dsimp only
  funext slot
  refine Fin.lastCases ?_ (fun native => ?_) slot
  · simp only [Description.residualPorts, Fin.lastCases_last,
      Fission.bridgeSubstitution]
    rw [freshLookup]
  · simp only [Description.residualPorts, Fin.lastCases_castSucc,
      Fission.bridgeSubstitution]
    rw [retainedLookup]
    exact (model.eval_port native
      (fun slot => (outerEnv.append localEnv).lookup
        (description.ports slot))).symm

theorem Local.sound_iff {before after : Region outer}
    (step : Local before after) (model : Model)
    (outerEnv : Values model outer) :
    denoteRegion model outerEnv before ↔
      denoteRegion model outerEnv after := by
  cases step with
  | split description =>
      simp only [Description.source, Description.target, denoteRegion_mk,
        denoteItemSeq_cons, denoteItem_term]
      constructor
      · rintro ⟨localEnv, wholeDenotes, restDenotes⟩
        let baseEnv := outerEnv.append localEnv
        let selectedValue := model.eval description.selected
          (fun slot => baseEnv.lookup (description.ports slot))
        let expandedLocal := Values.snocIota localEnv selectedValue
        let expandedEnv := outerEnv.append expandedLocal
        refine ⟨expandedLocal, ?_, ?_, ?_⟩
        · have bind := model.eval_bindFree description.residual
            (Fission.bridgeSubstitution description.selected)
            (fun slot => baseEnv.lookup (description.ports slot))
          rw [description.reconstruct] at bind
          have residualEnv := residualEnvironment description model outerEnv localEnv
          change expandedEnv.lookup (description.retain description.output) =
            model.eval description.residual
              (fun slot => expandedEnv.lookup
                (description.residualPorts slot))
          have outputEq : expandedEnv.lookup
              (description.retain description.output) =
              baseEnv.lookup description.output := by
            exact retainedLookup description model outerEnv localEnv
              selectedValue description.output
          rw [outputEq, wholeDenotes, residualEnv]
          exact bind
        · change expandedEnv.lookup description.bridge =
            model.eval description.selected
              (fun slot => expandedEnv.lookup
                (description.retain (description.ports slot)))
          rw [freshLookup]
          rw [show (fun slot =>
            (Values.append outerEnv
              (Values.snocIota localEnv selectedValue)).lookup
                  (description.retain (description.ports slot))) =
                (fun slot => baseEnv.lookup (description.ports slot)) by
            funext slot
            exact retainedLookup description model outerEnv localEnv
              selectedValue (description.ports slot)]
        · have retained := retainedEnvironment description model outerEnv
            localEnv selectedValue
          have renamed := denoteItemSeq_renameWires model description.retain
            expandedEnv description.rest
          rw [retained] at renamed
          exact renamed.mpr restDenotes
      · rintro ⟨expandedLocal, residualDenotes, selectedDenotes, restDenotes⟩
        rcases Values.exists_append (left := description.locals)
          (right := [.iota]) expandedLocal with
          ⟨localEnv, freshEnv, expandedEq⟩
        rcases freshEnv with ⟨fresh, unitValue⟩
        cases unitValue
        subst expandedLocal
        let baseEnv := outerEnv.append localEnv
        let expandedEnv := Values.append outerEnv
          (Values.snocIota localEnv fresh)
        change expandedEnv.lookup (description.retain description.output) =
            model.eval description.residual
              (fun slot => expandedEnv.lookup
                (description.residualPorts slot)) at residualDenotes
        change expandedEnv.lookup description.bridge =
            model.eval description.selected
              (fun slot => expandedEnv.lookup
                (description.retain (description.ports slot))) at selectedDenotes
        change denoteItemSeq model expandedEnv
            (description.rest.renameWires description.retain) at restDenotes
        refine ⟨localEnv, ?_, ?_⟩
        · have retained := retainedEnvironment description model outerEnv
            localEnv fresh
          have selectedEq : fresh = model.eval description.selected
              (fun slot => baseEnv.lookup (description.ports slot)) := by
            rw [show (fun slot => expandedEnv.lookup
                (description.retain (description.ports slot))) =
                (fun slot => baseEnv.lookup (description.ports slot)) by
              funext slot
              exact retainedLookup description model outerEnv localEnv fresh
                (description.ports slot)]
              at selectedDenotes
            rw [freshLookup] at selectedDenotes
            exact selectedDenotes
          have bind := model.eval_bindFree description.residual
            (Fission.bridgeSubstitution description.selected)
            (fun slot => baseEnv.lookup (description.ports slot))
          rw [description.reconstruct] at bind
          have residualEnv := residualEnvironment description model outerEnv localEnv
          dsimp only at residualEnv
          rw [← selectedEq] at residualEnv
          have outputEq := retainedLookup description model outerEnv localEnv
            fresh description.output
          rw [← outputEq, residualDenotes, residualEnv]
          exact bind.symm
        · have retained := retainedEnvironment description model outerEnv
            localEnv fresh
          have renamed := denoteItemSeq_renameWires model description.retain
            expandedEnv description.rest
          rw [retained] at renamed
          exact renamed.mp restDenotes

/-- Fission is semantically bidirectional in every lawful Lambda model. -/
theorem sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : VisualProof.Rule.Lambda.Fission source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  intro model args
  cases step with
  | split canonicalSource description sourceIso targetIso =>
      rw [sourceIso.denoteOpen_iff model args,
        description.occurrence.host_iso.denoteOpen_iff model args]
      have bodyIff : ∀ environment,
          denoteRegion model environment
              (description.occurrence.context.fill description.primary.source) ↔
            denoteRegion model environment
              (description.occurrence.context.fill description.primary.target) := by
        intro environment
        exact description.occurrence.context.denote_fill_iff
          description.primary.source description.primary.target
          (fun siteEnv => Local.sound_iff (.split description.primary)
            model siteEnv) environment
      exact (OpenDiagram.denote_body_iff bodyIff).trans
        (targetIso.denoteOpen_iff model args)

end Fission

private theorem denoteRegion_ofItems
    (model : Model) (environment : Values model wires)
    (items : ItemSeq wires) :
    denoteRegion model environment (Region.ofItems items) ↔
      denoteItemSeq model environment items := by
  let appendNil : WireRenaming wires (wires ++ []) :=
    ⟨fun wire => wire.appendLeft []⟩
  change (∃ emptyEnv : Values model [],
      denoteItemSeq model (environment.append emptyEnv)
        (items.renameWires appendNil)) ↔
    denoteItemSeq model environment items
  have retainedEmpty (emptyEnv : Values model []) :
      Values.rename appendNil (environment.append emptyEnv) = environment := by
    apply Values.ext
    intro signature wire
    simp [appendNil]
  constructor
  · rintro ⟨emptyEnv, itemsDenote⟩
    have renamed := denoteItemSeq_renameWires model appendNil
      (environment.append emptyEnv) items
    rw [retainedEmpty emptyEnv] at renamed
    exact renamed.mp itemsDenote
  · intro itemsDenote
    refine ⟨PUnit.unit, ?_⟩
    have renamed := denoteItemSeq_renameWires model appendNil
      (environment.append PUnit.unit) items
    rw [retainedEmpty PUnit.unit] at renamed
    exact renamed.mpr itemsDenote

namespace Fusion

private theorem anchorRetainedEnvironment
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (anchorEnv : Values model description.anchorLocals)
    (fresh : model.Carrier) :
    Values.rename description.anchorRetain
        (outerEnv.append (Values.snocIota anchorEnv fresh)) =
      outerEnv.append anchorEnv := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases (left := outer) (right := description.anchorLocals)
    (motive := fun wire =>
      (Values.rename description.anchorRetain
        (outerEnv.append (Values.snocIota anchorEnv fresh))).lookup wire =
      (outerEnv.append anchorEnv).lookup wire)
  · intro inheritedSignature inherited
    simp [Description.anchorRetain, Region.adjoinHostWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [Description.anchorRetain, Region.adjoinHostWire,
      Region.conjoinLeftWire]

private theorem anchorRetainedLookup
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (anchorEnv : Values model description.anchorLocals)
    (fresh : model.Carrier)
    (wire : Var (outer ++ description.anchorLocals) signature) :
    (outerEnv.append (Values.snocIota anchorEnv fresh)).lookup
        (description.anchorRetain wire) =
      (outerEnv.append anchorEnv).lookup wire := by
  have environments := anchorRetainedEnvironment description model outerEnv
    anchorEnv fresh
  have lookup := congrArg (fun values => values.lookup wire) environments
  simpa only [Values.lookup_rename] using lookup

private theorem bridgeLookup
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (anchorEnv : Values model description.anchorLocals)
    (fresh : model.Carrier) :
    (outerEnv.append (Values.snocIota anchorEnv fresh)).lookup
      description.bridge = fresh := by
  simp only [Description.bridge, Values.lookup_append_right,
    Values.snocIota]
  rfl

private theorem producer_eval
    (description : Description outer)
    (model : Model)
    (baseEnv : Values model
      (description.descendantWires ++ description.consumerLocals)) :
    model.eval (description.producerTerm.mapFree description.producerMap)
        (fun slot => baseEnv.lookup (description.carrier slot)) =
      model.eval description.producerTerm
        (fun slot => baseEnv.lookup
          ((description.descendant.outerWire
            (description.producerNative slot)).appendLeft
              description.consumerLocals)) := by
  rw [model.eval_mapFree]
  apply congrArg (model.eval description.producerTerm)
  funext slot
  simp only [Function.comp_apply]
  rw [description.producer_port]

private theorem merged_eval
    (description : Description outer)
    (model : Model)
    (baseEnv : Values model
      (description.descendantWires ++ description.consumerLocals)) :
    model.eval description.mergedTerm
        (fun slot => baseEnv.lookup (description.carrier slot)) =
      model.eval description.consumerTerm (fun slot =>
        if slot = description.consumed then
          model.eval description.producerTerm
            (fun producerSlot =>
              baseEnv.lookup
                ((description.descendant.outerWire
                  (description.producerNative producerSlot)).appendLeft
                    description.consumerLocals))
        else baseEnv.lookup (description.consumerNative slot)) := by
  let carrierEnv : Fin description.carrierArity → model.Carrier :=
    fun slot => baseEnv.lookup (description.carrier slot)
  let substitution : Fin (description.carrierArity + 1) →
      VisualProof.Lambda.Term 0 (Fin description.carrierArity) :=
    Fin.lastCases (description.producerTerm.mapFree description.producerMap)
      (fun slot => .port slot)
  rw [show description.mergedTerm =
      (description.consumerTerm.mapFree description.consumerMap).bindFree
        substitution by rfl]
  rw [model.eval_bindFree, model.eval_mapFree]
  apply congrArg (model.eval description.consumerTerm)
  funext slot
  simp only [Function.comp_apply]
  by_cases consumed : slot = description.consumed
  · subst slot
    rw [description.consumed_eq]
    simp only [substitution, Fin.lastCases_last]
    exact producer_eval description model baseEnv
  · rw [description.consumer_port slot consumed]
    simp only [substitution, Fin.lastCases_castSucc]
    rw [model.eval_port, description.consumer_carrier slot consumed]
    simp [consumed]

private theorem consumerRetainedEnvironment
    (description : Description outer) (model : Model)
    (targetEnv : Values model description.descendantWires)
    (sourceEnv : Values model description.extension.sourceWires)
    (consumerEnv : Values model description.consumerLocals)
    (producerValue : model.Carrier)
    (environments : DiagramContext.WireExtension.Environments
      description.extension.retain description.extension.wire
      targetEnv sourceEnv producerValue) :
    Values.rename description.consumerRetain
        (sourceEnv.append consumerEnv) = targetEnv.append consumerEnv := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases (left := description.descendantWires)
    (right := description.consumerLocals)
    (motive := fun wire =>
      (Values.rename description.consumerRetain
        (sourceEnv.append consumerEnv)).lookup wire =
      (targetEnv.append consumerEnv).lookup wire)
  · intro inheritedSignature inherited
    have inheritedEq := congrArg
      (fun values => values.lookup inherited) environments.1
    simpa [Description.consumerRetain, WireRenaming.appendRight] using
      inheritedEq
  · intro localSignature localWire
    simp [Description.consumerRetain, WireRenaming.appendRight]

private theorem consumerRetainedLookup
    (description : Description outer) (model : Model)
    (targetEnv : Values model description.descendantWires)
    (sourceEnv : Values model description.extension.sourceWires)
    (consumerEnv : Values model description.consumerLocals)
    (producerValue : model.Carrier)
    (environments : DiagramContext.WireExtension.Environments
      description.extension.retain description.extension.wire
      targetEnv sourceEnv producerValue)
    (wire : Var (description.descendantWires ++
      description.consumerLocals) signature) :
    (sourceEnv.append consumerEnv).lookup
        (description.consumerRetain wire) =
      (targetEnv.append consumerEnv).lookup wire := by
  have environmentEq := consumerRetainedEnvironment description model
    targetEnv sourceEnv consumerEnv producerValue environments
  have lookup := congrArg (fun values => values.lookup wire) environmentEq
  simpa only [Values.lookup_rename] using lookup

private theorem consumerBridgeLookup
    (description : Description outer) (model : Model)
    (targetEnv : Values model description.descendantWires)
    (sourceEnv : Values model description.extension.sourceWires)
    (consumerEnv : Values model description.consumerLocals)
    (producerValue : model.Carrier)
    (environments : DiagramContext.WireExtension.Environments
      description.extension.retain description.extension.wire
      targetEnv sourceEnv producerValue) :
    (sourceEnv.append consumerEnv).lookup
        (description.extension.wire.appendLeft description.consumerLocals) =
      producerValue := by
  simpa using environments.2

private theorem consumer_sound_iff
    (description : Description outer) (model : Model)
    (targetEnv : Values model description.descendantWires)
    (sourceEnv : Values model description.extension.sourceWires)
    (producerValue : model.Carrier)
    (environments : DiagramContext.WireExtension.Environments
      description.extension.retain description.extension.wire
      targetEnv sourceEnv producerValue)
    (producerAtTarget : producerValue =
      model.eval description.producerTerm (fun slot =>
        targetEnv.lookup
          (description.descendant.outerWire
            (description.producerNative slot)))) :
    denoteRegion model sourceEnv description.sourceConsumer ↔
      denoteRegion model targetEnv description.targetConsumer := by
  simp only [Description.sourceConsumer, Description.targetConsumer,
    denoteRegion_mk, denoteItemSeq_cons, denoteItem_term]
  constructor
  · rintro ⟨consumerEnv, consumerDenotes, restDenotes⟩
    let sourceBase := sourceEnv.append consumerEnv
    let targetBase := targetEnv.append consumerEnv
    refine ⟨consumerEnv, ?_, ?_⟩
    · change targetBase.lookup description.consumerOutput =
        model.eval description.mergedTerm
          (fun slot => targetBase.lookup (description.carrier slot))
      rw [merged_eval description model targetBase]
      rw [← consumerRetainedLookup description model targetEnv sourceEnv
        consumerEnv producerValue environments description.consumerOutput]
      rw [consumerDenotes]
      apply congrArg (model.eval description.consumerTerm)
      funext slot
      by_cases consumed : slot = description.consumed
      · subst slot
        simp only [if_pos]
        have sourceBridge : sourceBase.lookup
            (description.consumerPorts description.consumed) =
              producerValue := by
          simpa [sourceBase, Description.consumerPorts] using
            (consumerBridgeLookup description model targetEnv sourceEnv
              consumerEnv producerValue environments)
        rw [sourceBridge]
        rw [producerAtTarget]
        apply congrArg (model.eval description.producerTerm)
        funext producerSlot
        simp [targetBase]
      · simp only [if_neg consumed]
        rw [show description.consumerPorts slot =
            description.consumerRetain
              (description.consumerNative slot) by
          simp [Description.consumerPorts, consumed]]
        exact consumerRetainedLookup description model targetEnv sourceEnv
          consumerEnv producerValue environments
          (description.consumerNative slot)
    · have renamed := denoteItemSeq_renameWires model
        description.consumerRetain sourceBase description.consumerRest
      rw [consumerRetainedEnvironment description model targetEnv sourceEnv
        consumerEnv producerValue environments] at renamed
      exact renamed.mp restDenotes
  · rintro ⟨consumerEnv, mergedDenotes, restDenotes⟩
    let sourceBase := sourceEnv.append consumerEnv
    let targetBase := targetEnv.append consumerEnv
    refine ⟨consumerEnv, ?_, ?_⟩
    · change sourceBase.lookup
          (description.consumerRetain description.consumerOutput) =
        model.eval description.consumerTerm
          (fun slot => sourceBase.lookup (description.consumerPorts slot))
      rw [consumerRetainedLookup description model targetEnv sourceEnv
        consumerEnv producerValue environments description.consumerOutput]
      rw [mergedDenotes, merged_eval description model targetBase]
      apply congrArg (model.eval description.consumerTerm)
      funext slot
      by_cases consumed : slot = description.consumed
      · subst slot
        simp only [if_pos]
        have targetProducer :
            model.eval description.producerTerm (fun producerSlot =>
              targetBase.lookup
                ((description.descendant.outerWire
                  (description.producerNative producerSlot)).appendLeft
                    description.consumerLocals)) = producerValue := by
          rw [show (fun producerSlot => targetBase.lookup
              ((description.descendant.outerWire
                (description.producerNative producerSlot)).appendLeft
                  description.consumerLocals)) =
              (fun producerSlot => targetEnv.lookup
                (description.descendant.outerWire
                  (description.producerNative producerSlot))) by
            funext producerSlot
            simp [targetBase]]
          exact producerAtTarget.symm
        rw [targetProducer]
        simpa [sourceBase, Description.consumerPorts] using
          (consumerBridgeLookup description model targetEnv sourceEnv
            consumerEnv producerValue environments).symm
      · simp only [if_neg consumed]
        rw [show description.consumerPorts slot =
            description.consumerRetain
              (description.consumerNative slot) by
          simp [Description.consumerPorts, consumed]]
        exact (consumerRetainedLookup description model targetEnv sourceEnv
          consumerEnv producerValue environments
          (description.consumerNative slot)).symm
    · have renamed := denoteItemSeq_renameWires model
        description.consumerRetain sourceBase description.consumerRest
      rw [consumerRetainedEnvironment description model targetEnv sourceEnv
        consumerEnv producerValue environments] at renamed
      exact renamed.mpr restDenotes

theorem Local.sound_iff {before after : Region outer}
    (step : Local before after) (model : Model)
    (outerEnv : Values model outer) :
    denoteRegion model outerEnv before ↔
      denoteRegion model outerEnv after := by
  cases step with
  | fuse description =>
      rw [Description.source, Description.target,
        Region.denote_adjoinAt, Region.denote_adjoinAt]
      constructor
      · rintro ⟨expandedAnchorEnv, _, sourceMaterial⟩
        rcases Values.exists_append (left := description.anchorLocals)
          (right := [.iota]) expandedAnchorEnv with
          ⟨anchorEnv, freshEnv, expandedEq⟩
        rcases freshEnv with ⟨bridgeValue, unitValue⟩
        cases unitValue
        subst expandedAnchorEnv
        let anchorBase := outerEnv.append anchorEnv
        let expandedEnv := outerEnv.append
          (Values.snocIota anchorEnv bridgeValue)
        rw [Region.denote_conjoin] at sourceMaterial
        rcases sourceMaterial with
          ⟨selectedDenotes, sourceDescendantDenotes⟩
        have selectedParts :
            expandedEnv.lookup description.bridge =
                model.eval description.producerTerm
                  (fun slot => expandedEnv.lookup
                    (description.producerPorts slot)) ∧
              denoteItemSeq model expandedEnv
                (description.anchorRest.renameWires
                  description.anchorRetain) := by
          simpa [Description.sourceSelected, denoteRegion_ofItems,
            denoteItemSeq_cons, denoteItem_term,
            expandedEnv] using selectedDenotes
        rcases selectedParts with ⟨producerDenotes, sourceRestDenotes⟩
        have producerAtAnchor : bridgeValue =
            model.eval description.producerTerm (fun slot =>
              anchorBase.lookup (description.producerNative slot)) := by
          rw [← bridgeLookup description model outerEnv anchorEnv bridgeValue]
          rw [producerDenotes]
          apply congrArg (model.eval description.producerTerm)
          funext slot
          exact anchorRetainedLookup description model outerEnv anchorEnv
            bridgeValue (description.producerNative slot)
        have targetRestDenotes :
            denoteItemSeq model anchorBase description.anchorRest := by
          have renamed := denoteItemSeq_renameWires model
            description.anchorRetain expandedEnv description.anchorRest
          rw [anchorRetainedEnvironment description model outerEnv anchorEnv
            bridgeValue] at renamed
          exact renamed.mp sourceRestDenotes
        have outerEnvironments :
            DiagramContext.WireExtension.Environments
              description.anchorRetain description.bridge anchorBase
              expandedEnv bridgeValue :=
          ⟨anchorRetainedEnvironment description model outerEnv anchorEnv
              bridgeValue,
            bridgeLookup description model outerEnv anchorEnv bridgeValue⟩
        have descendantIff :=
          DiagramContext.extendWire_denote_fill_iff
            description.descendant
            (outer ++ (description.anchorLocals ++ [Sig.iota]))
            description.anchorRetain description.bridge
            description.sourceConsumer description.targetConsumer model
            anchorBase expandedEnv bridgeValue outerEnvironments
            (fun targetHoleEnv sourceHoleEnv environments reachable => by
              apply consumer_sound_iff description model targetHoleEnv
                sourceHoleEnv bridgeValue environments
              have inheritedEq : (fun slot => targetHoleEnv.lookup
                    (description.descendant.outerWire
                      (description.producerNative slot))) =
                  (fun slot => anchorBase.lookup
                    (description.producerNative slot)) := by
                funext slot
                have lookupEq := congrArg
                  (fun values => values.lookup
                    (description.producerNative slot)) reachable.outerWire
                simpa only [Values.lookup_rename] using lookupEq
              rw [inheritedEq]
              exact producerAtAnchor)
        refine ⟨anchorEnv, trivial, ?_⟩
        rw [Region.denote_conjoin]
        constructor
        · exact (denoteRegion_ofItems model anchorBase
            description.anchorRest).mpr targetRestDenotes
        · exact descendantIff.mp sourceDescendantDenotes
      · rintro ⟨anchorEnv, _, targetMaterial⟩
        let anchorBase := outerEnv.append anchorEnv
        let producerValue := model.eval description.producerTerm (fun slot =>
          anchorBase.lookup (description.producerNative slot))
        let expandedEnv := outerEnv.append
          (Values.snocIota anchorEnv producerValue)
        rw [Region.denote_conjoin] at targetMaterial
        rcases targetMaterial with
          ⟨targetSelectedDenotes, targetDescendantDenotes⟩
        have targetRestDenotes :
            denoteItemSeq model anchorBase description.anchorRest := by
          exact (denoteRegion_ofItems model anchorBase
            description.anchorRest).mp targetSelectedDenotes
        have sourceRestDenotes :
            denoteItemSeq model expandedEnv
              (description.anchorRest.renameWires
                description.anchorRetain) := by
          have renamed := denoteItemSeq_renameWires model
            description.anchorRetain expandedEnv description.anchorRest
          rw [anchorRetainedEnvironment description model outerEnv anchorEnv
            producerValue] at renamed
          exact renamed.mpr targetRestDenotes
        have outerEnvironments :
            DiagramContext.WireExtension.Environments
              description.anchorRetain description.bridge anchorBase
              expandedEnv producerValue :=
          ⟨anchorRetainedEnvironment description model outerEnv anchorEnv
              producerValue,
            bridgeLookup description model outerEnv anchorEnv producerValue⟩
        have descendantIff :=
          DiagramContext.extendWire_denote_fill_iff
            description.descendant
            (outer ++ (description.anchorLocals ++ [Sig.iota]))
            description.anchorRetain description.bridge
            description.sourceConsumer description.targetConsumer model
            anchorBase expandedEnv producerValue outerEnvironments
            (fun targetHoleEnv sourceHoleEnv environments reachable => by
              apply consumer_sound_iff description model targetHoleEnv
                sourceHoleEnv producerValue environments
              have inheritedEq : (fun slot => targetHoleEnv.lookup
                    (description.descendant.outerWire
                      (description.producerNative slot))) =
                  (fun slot => anchorBase.lookup
                    (description.producerNative slot)) := by
                funext slot
                have lookupEq := congrArg
                  (fun values => values.lookup
                    (description.producerNative slot)) reachable.outerWire
                simpa only [Values.lookup_rename] using lookupEq
              rw [inheritedEq]
              )
        have sourceDescendantDenotes :=
          descendantIff.mpr targetDescendantDenotes
        have producerDenotes : expandedEnv.lookup description.bridge =
            model.eval description.producerTerm
              (fun slot => expandedEnv.lookup
                (description.producerPorts slot)) := by
          rw [bridgeLookup]
          apply congrArg (model.eval description.producerTerm)
          funext slot
          exact (anchorRetainedLookup description model outerEnv anchorEnv
            producerValue (description.producerNative slot)).symm
        have selectedDenotes :
            denoteRegion model expandedEnv description.sourceSelected := by
          simpa [Description.sourceSelected, denoteRegion_ofItems,
            denoteItemSeq_cons, denoteItem_term] using
            And.intro producerDenotes sourceRestDenotes
        refine ⟨Values.snocIota anchorEnv producerValue, trivial, ?_⟩
        rw [Region.denote_conjoin]
        exact ⟨selectedDenotes, sourceDescendantDenotes⟩

/-- Fusion is semantically bidirectional in every lawful Lambda model. -/
theorem sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : VisualProof.Rule.Lambda.Fusion source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  intro model args
  cases step with
  | fuse canonicalSource description sourceIso targetIso =>
      rw [sourceIso.denoteOpen_iff model args,
        description.occurrence.host_iso.denoteOpen_iff model args]
      have bodyIff : ∀ environment,
          denoteRegion model environment
              (description.occurrence.context.fill description.primary.source) ↔
            denoteRegion model environment description.targetBody := by
        intro environment
        exact (description.occurrence.context.denote_fill_iff
          description.primary.source description.primary.target
          (fun siteEnv => Local.sound_iff (.fuse description.primary)
            model siteEnv) environment).trans
              (description.completion.sound_iff model environment)
      exact (OpenDiagram.denote_body_iff bodyIff).trans
        (targetIso.denoteOpen_iff model args)

end Fusion

end VisualProof.Rule.Lambda
