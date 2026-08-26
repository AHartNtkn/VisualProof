import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.OpenIsomorphism
import VisualProof.Diagram.Semantics.ScopedRewrite
import VisualProof.Rule.Lambda.Congruence

namespace VisualProof.Rule.Lambda.Congruence

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

private theorem common_eval
    (description : Description outer) (model : Model)
    (expandedEnv : Values model
      (outer ++ (description.locals ++ [Sig.iota]))) :
    model.eval description.leftTerm (fun slot =>
        expandedEnv.lookup
          (description.carrier (description.correspondence.left slot))) =
      model.eval description.rightTerm (fun slot =>
        expandedEnv.lookup
          (description.carrier (description.correspondence.right slot))) := by
  let commonEnv : Fin description.correspondence.commonArity → model.Carrier :=
    fun slot => expandedEnv.lookup (description.carrier slot)
  calc
    model.eval description.leftTerm (fun slot =>
        expandedEnv.lookup
          (description.carrier (description.correspondence.left slot))) =
        model.eval
          (description.leftTerm.mapFree description.correspondence.left)
          commonEnv := by
      simpa [commonEnv, Function.comp_def] using
        (model.eval_mapFree description.correspondence.left
          description.leftTerm commonEnv).symm
    _ = model.eval
          (description.rightTerm.mapFree description.correspondence.right)
          commonEnv := model.betaEta_sound description.betaEta
    _ = model.eval description.rightTerm (fun slot =>
        expandedEnv.lookup
          (description.carrier (description.correspondence.right slot))) := by
      simpa [commonEnv, Function.comp_def] using
        model.eval_mapFree description.correspondence.right
          description.rightTerm commonEnv

private theorem collapsedEnvironment
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (removedValue : model.Carrier)
    (outputsEqual : removedValue =
      (outerEnv.append localEnv).lookup description.survivor) :
    Values.rename description.collapse
        (outerEnv.append localEnv) =
      outerEnv.append (Values.snocIota localEnv removedValue) := by
  apply Values.ext
  intro signature wire
  apply Var.appendCases (left := outer)
    (right := description.locals ++ [Sig.iota])
    (motive := fun wire =>
      (Values.rename description.collapse
        (outerEnv.append localEnv)).lookup wire =
      (outerEnv.append (Values.snocIota localEnv removedValue)).lookup wire)
  · intro inheritedSignature inherited
    simp [Description.collapse, WireSever.collapseLocal]
  · intro localSignature localWire
    apply Var.appendCases (left := description.locals) (right := [Sig.iota])
      (motive := fun localWire =>
        (Values.rename description.collapse
          (outerEnv.append localEnv)).lookup
            (Var.appendRight outer localWire) =
        (outerEnv.append (Values.snocIota localEnv removedValue)).lookup
          (Var.appendRight outer localWire))
    · intro retainedSignature retained
      simp [Description.collapse, WireSever.collapseLocal,
        Values.snocIota]
    · intro freshSignature fresh
      cases fresh with
      | here =>
          simpa only [Values.lookup_rename, Description.collapse,
            WireSever.collapseLocal, Var.appendMap_right,
            Values.lookup_append_right, Values.snocIota] using
              outputsEqual.symm
      | there tail => exact nomatch tail

private theorem source_outputs_equal
    (description : Description outer) (model : Model)
    (expandedEnv : Values model
      (outer ++ (description.locals ++ [Sig.iota])))
    (sourceDenotes : denoteItemSeq model expandedEnv description.items) :
    expandedEnv.lookup description.removed =
      expandedEnv.lookup (description.retain description.survivor) := by
  rcases sourceDenotes with ⟨leftDenotes, rightDenotes, _⟩
  rw [rightDenotes, leftDenotes]
  exact (common_eval description model expandedEnv).symm

theorem Local.sound_iff {before after : Region outer}
    (step : Local before after) (model : Model)
    (outerEnv : Values model outer) :
    denoteRegion model outerEnv before ↔
      denoteRegion model outerEnv after := by
  cases step with
  | join description =>
      simp only [Description.source, Description.target, denoteRegion_mk]
      constructor
      · rintro ⟨expandedLocal, sourceDenotes⟩
        rcases Values.exists_append (left := description.locals)
          (right := [.iota]) expandedLocal with
          ⟨localEnv, freshEnv, expandedEq⟩
        rcases freshEnv with ⟨removedValue, unitValue⟩
        cases unitValue
        subst expandedLocal
        let expandedEnv := outerEnv.append
          (Values.snocIota localEnv removedValue)
        let baseEnv := outerEnv.append localEnv
        have outputsEqual := source_outputs_equal description model
          expandedEnv sourceDenotes
        have removedLookup : expandedEnv.lookup description.removed =
            removedValue := by
          simp only [expandedEnv, Description.removed,
            Values.lookup_append_right, Values.snocIota]
          rfl
        have survivorLookup : expandedEnv.lookup
              (description.retain description.survivor) =
            baseEnv.lookup description.survivor := by
          apply Var.appendCases (left := outer) (right := description.locals)
            (motive := fun survivor =>
              expandedEnv.lookup (description.retain survivor) =
                baseEnv.lookup survivor)
          · intro inheritedSignature inherited
            simp [expandedEnv, baseEnv, Description.retain,
              Region.adjoinHostWire, Region.conjoinLeftWire]
          · intro localSignature localWire
            simp [expandedEnv, baseEnv, Description.retain,
              Region.adjoinHostWire, Region.conjoinLeftWire,
              Values.snocIota]
        have freshEq : removedValue = baseEnv.lookup description.survivor := by
          rw [← removedLookup, outputsEqual, survivorLookup]
        refine ⟨localEnv, ?_⟩
        have renamed := denoteItemSeq_renameWires model description.collapse
          baseEnv description.items
        have environments := collapsedEnvironment description model outerEnv
          localEnv removedValue freshEq
        rw [environments] at renamed
        exact renamed.mpr sourceDenotes
      · rintro ⟨localEnv, targetDenotes⟩
        let baseEnv := outerEnv.append localEnv
        let survivorValue := baseEnv.lookup description.survivor
        let expandedLocal := Values.snocIota localEnv survivorValue
        let expandedEnv := outerEnv.append expandedLocal
        refine ⟨expandedLocal, ?_⟩
        have renamed := denoteItemSeq_renameWires model description.collapse
          baseEnv description.items
        have environments := collapsedEnvironment description model outerEnv
          localEnv survivorValue rfl
        rw [environments] at renamed
        exact renamed.mp targetDenotes

/-- Congruence output joining preserves denotation in both directions. -/
theorem sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : VisualProof.Rule.Lambda.Congruence source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  intro model args
  cases step with
  | join canonicalSource description sourceIso targetIso =>
      rw [sourceIso.denoteOpen_iff model args,
        description.occurrence.host_iso.denoteOpen_iff model args]
      have bodyIff : ∀ environment,
          denoteRegion model environment
              (description.occurrence.context.fill description.primary.source) ↔
            denoteRegion model environment
              (description.occurrence.context.fill
                description.primary.target) := by
        intro environment
        exact description.occurrence.context.denote_fill_iff
          description.primary.source description.primary.target
          (fun siteEnv => Local.sound_iff (.join description.primary)
            model siteEnv) environment
      exact (OpenDiagram.denote_body_iff bodyIff).trans
        (targetIso.denoteOpen_iff model args)

end VisualProof.Rule.Lambda.Congruence
