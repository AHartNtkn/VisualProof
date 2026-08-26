import VisualProof.Diagram.Semantics.Algebra
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

namespace Fusion

private theorem retainedEnvironment
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (fresh : model.Carrier) :
    Values.rename description.retain
        (outerEnv.append (Values.snocIota localEnv fresh)) =
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

private theorem bridgeLookup
    (description : Description outer)
    (model : Model) (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (fresh : model.Carrier) :
    (outerEnv.append (Values.snocIota localEnv fresh)).lookup
      description.bridge = fresh := by
  simp only [Description.bridge, Values.lookup_append_right,
    Values.snocIota]
  rfl

private theorem producer_eval
    (description : Description outer)
    (model : Model) (baseEnv : Values model (outer ++ description.locals)) :
    model.eval (description.producerTerm.mapFree description.producerMap)
        (fun slot => baseEnv.lookup (description.carrier slot)) =
      model.eval description.producerTerm
        (fun slot => baseEnv.lookup (description.producerNative slot)) := by
  rw [model.eval_mapFree]
  apply congrArg (model.eval description.producerTerm)
  funext slot
  simp only [Function.comp_apply]
  rw [description.producer_port]

private theorem merged_eval
    (description : Description outer)
    (model : Model) (baseEnv : Values model (outer ++ description.locals)) :
    model.eval description.mergedTerm
        (fun slot => baseEnv.lookup (description.carrier slot)) =
      model.eval description.consumerTerm (fun slot =>
        if slot = description.consumed then
          model.eval description.producerTerm
            (fun producerSlot =>
              baseEnv.lookup (description.producerNative producerSlot))
        else baseEnv.lookup (description.consumerNative slot)) := by
  let carrierEnv : Fin description.carrierArity → model.Carrier :=
    fun slot => baseEnv.lookup (description.carrier slot)
  let producerValue := model.eval description.producerTerm
    (fun slot => baseEnv.lookup (description.producerNative slot))
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

theorem Local.sound_iff {before after : Region outer}
    (step : Local before after) (model : Model)
    (outerEnv : Values model outer) :
    denoteRegion model outerEnv before ↔
      denoteRegion model outerEnv after := by
  cases step with
  | fuse description =>
      simp only [Description.source, Description.target, denoteRegion_mk,
        denoteItemSeq_cons, denoteItem_term]
      constructor
      · rintro ⟨expandedLocal, producerDenotes, consumerDenotes,
          restDenotes⟩
        rcases Values.exists_append (left := description.locals)
          (right := [.iota]) expandedLocal with
          ⟨localEnv, freshEnv, expandedEq⟩
        rcases freshEnv with ⟨bridgeValue, unitValue⟩
        cases unitValue
        subst expandedLocal
        let baseEnv := outerEnv.append localEnv
        let expandedEnv := outerEnv.append
          (Values.snocIota localEnv bridgeValue)
        change expandedEnv.lookup description.bridge =
            model.eval description.producerTerm
              (fun slot => expandedEnv.lookup
                (description.producerPorts slot)) at producerDenotes
        change expandedEnv.lookup
              (description.retain description.consumerOutput) =
            model.eval description.consumerTerm
              (fun slot => expandedEnv.lookup
                (description.consumerPorts slot)) at consumerDenotes
        change denoteItemSeq model expandedEnv
            (description.rest.renameWires description.retain) at restDenotes
        refine ⟨localEnv, ?_, ?_⟩
        · rw [merged_eval description model baseEnv]
          rw [← retainedLookup description model outerEnv localEnv bridgeValue
            description.consumerOutput]
          rw [consumerDenotes]
          apply congrArg (model.eval description.consumerTerm)
          funext slot
          by_cases consumed : slot = description.consumed
          · subst slot
            simp only [if_pos]
            rw [show expandedEnv.lookup
                (description.consumerPorts description.consumed) =
                bridgeValue by
              simp [Description.consumerPorts, expandedEnv,
                bridgeLookup]]
            rw [bridgeLookup] at producerDenotes
            rw [show (fun producerSlot => expandedEnv.lookup
                (description.producerPorts producerSlot)) =
                (fun producerSlot =>
                  baseEnv.lookup (description.producerNative producerSlot)) by
              funext producerSlot
              exact retainedLookup description model outerEnv localEnv
                bridgeValue (description.producerNative producerSlot)]
              at producerDenotes
            exact producerDenotes
          · simp only [if_neg consumed]
            rw [show description.consumerPorts slot =
                description.retain (description.consumerNative slot) by
              simp [Description.consumerPorts, consumed]]
            exact retainedLookup description model outerEnv localEnv
              bridgeValue (description.consumerNative slot)
        · have renamed := denoteItemSeq_renameWires model description.retain
            expandedEnv description.rest
          rw [retainedEnvironment description model outerEnv localEnv
            bridgeValue] at renamed
          exact renamed.mp restDenotes
      · rintro ⟨localEnv, mergedDenotes, restDenotes⟩
        let baseEnv := outerEnv.append localEnv
        let producerValue := model.eval description.producerTerm
          (fun slot => baseEnv.lookup (description.producerNative slot))
        let expandedLocal := Values.snocIota localEnv producerValue
        let expandedEnv := outerEnv.append expandedLocal
        refine ⟨expandedLocal, ?_, ?_, ?_⟩
        · change expandedEnv.lookup description.bridge =
            model.eval description.producerTerm
              (fun slot => expandedEnv.lookup
                (description.producerPorts slot))
          rw [bridgeLookup]
          apply congrArg (model.eval description.producerTerm)
          funext slot
          exact (retainedLookup description model outerEnv localEnv
            producerValue (description.producerNative slot)).symm
        · change expandedEnv.lookup
              (description.retain description.consumerOutput) =
            model.eval description.consumerTerm
              (fun slot => expandedEnv.lookup
                (description.consumerPorts slot))
          rw [retainedLookup]
          rw [mergedDenotes, merged_eval description model baseEnv]
          apply congrArg (model.eval description.consumerTerm)
          funext slot
          by_cases consumed : slot = description.consumed
          · subst slot
            simp only [if_pos, Description.consumerPorts]
            exact (bridgeLookup description model outerEnv localEnv
              producerValue).symm
          · simp only [if_neg consumed]
            rw [show description.consumerPorts slot =
                description.retain (description.consumerNative slot) by
              simp [Description.consumerPorts, consumed]]
            exact (retainedLookup description model outerEnv localEnv
              producerValue (description.consumerNative slot)).symm
        · have renamed := denoteItemSeq_renameWires model description.retain
            expandedEnv description.rest
          rw [retainedEnvironment description model outerEnv localEnv
            producerValue] at renamed
          exact renamed.mpr restDenotes

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
