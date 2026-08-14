import VisualProof.Diagram.Semantics.ContextReachability
import VisualProof.Diagram.Semantics.OpenIsomorphism
import VisualProof.Diagram.Semantics.UnaryIdentity
import VisualProof.Rule.Iteration

namespace VisualProof.Rule

open VisualProof
open Theory
open Diagram

namespace Iteration

theorem WireFreshening.env_eq
    (freshening : WireFreshening sourceWires targetWires freshWires inherited)
    (model : Model) (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires)
    (inheritedEq : Values.rename inherited targetEnv = sourceEnv) :
    ∃ freshEnv : Values model freshWires,
      Values.rename freshening.wire (targetEnv.append freshEnv) = sourceEnv := by
  classical
  let freshEnv : Values model freshWires := Values.ofLookup fun fresh =>
    sourceEnv.lookup (freshening.sourceOfFresh fresh)
  refine ⟨freshEnv, Values.ext _ _ ?_⟩
  intro signature wire
  simp only [Values.lookup_rename]
  by_cases fresh : ∃ freshWire : Var freshWires signature,
      freshening.sourceOfFresh freshWire = wire
  · obtain ⟨freshWire, equality⟩ := fresh
    subst wire
    rw [freshening.wire_fresh]
    simp [freshEnv]
  · rw [freshening.wire_inherited wire (by
      intro freshWire equality
      exact fresh ⟨freshWire, equality⟩)]
    rw [Values.lookup_append_left]
    have lookupEq := congrArg (fun values => values.lookup wire) inheritedEq
    simpa only [Values.lookup_rename] using lookupEq

theorem copyBlock_denotes
    (descendant : DiagramContext sourceWires targetWires)
    (selected : Region sourceWires)
    (freshening : WireFreshening sourceWires targetWires freshWires
      descendant.outerWire)
    (model : Model) (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires)
    (reachable : descendant.Reachable sourceEnv targetEnv)
    (selectedDenotes : denoteRegion model sourceEnv selected) :
    denoteRegion model targetEnv (copyBlock selected freshening) := by
  obtain ⟨freshEnv, combinedEq⟩ := freshening.env_eq model sourceEnv
    targetEnv reachable.outerWire
  apply (Region.denote_adjoinAt model targetEnv
    (freshPins selected freshening)
    (freshenedSelected selected freshening)).mpr
  refine ⟨freshEnv, ?_, ?_⟩
  · simp only [freshPins, denoteItemSeq_append]
    exact ⟨ItemSeq.pinWires_denotes _ _ _ _ _,
      ItemSeq.pinWires_denotes _ _ _ _ _⟩
  apply (denoteRegion_renameWires model freshening.wire
    (targetEnv.append freshEnv) selected).mpr
  rw [combinedEq]
  exact selectedDenotes

theorem uncopyResidue_denotes_iff
    (selected : Region sourceWires) (remainder : Region targetWires)
    (freshening : WireFreshening sourceWires targetWires freshWires inherited)
    (model : Model) (env : Values model targetWires) :
    denoteRegion model env
        (uncopyResidue selected remainder freshening) ↔
      denoteRegion model env remainder := by
  cases remainder with
  | mk locals items =>
      simp only [uncopyResidue, denoteRegion_mk,
        denoteItemSeq_append]
      constructor
      · rintro ⟨localEnv, _, itemsDenote⟩
        exact ⟨localEnv, itemsDenote⟩
      · rintro ⟨localEnv, itemsDenote⟩
        refine ⟨localEnv, ?_, itemsDenote⟩
        apply (denoteItemSeq_renameWires model
          ⟨fun wire => wire.appendLeft locals⟩
          (env.append localEnv)
          (uncopyPins selected (.mk locals items) freshening)).mpr
        exact ItemSeq.pinWires_denotes _ _ _ _ _

theorem Local.denotes_iff
    (descendant : DiagramContext sourceWires targetWires)
    (selected : Region sourceWires) (before after : Region targetWires)
    (evidence : Local descendant selected before after)
    (model : Model) (sourceEnv : Values model sourceWires)
    (targetEnv : Values model targetWires)
    (reachable : descendant.Reachable sourceEnv targetEnv)
    (selectedDenotes : denoteRegion model sourceEnv selected) :
    denoteRegion model targetEnv before ↔
      denoteRegion model targetEnv after := by
  cases evidence with
  | copy remainder freshWires freshening =>
      have copyDenotes := copyBlock_denotes descendant selected freshening
        model sourceEnv targetEnv reachable selectedDenotes
      simp only [copied]
      rw [Region.denote_conjoin]
      exact ⟨fun remainderDenotes => ⟨copyDenotes, remainderDenotes⟩,
        And.right⟩
  | remove remainder freshWires freshening =>
      have copyDenotes := copyBlock_denotes descendant selected freshening
        model sourceEnv targetEnv reachable selectedDenotes
      simp only [copied]
      rw [Region.denote_conjoin,
        uncopyResidue_denotes_iff selected remainder freshening model
          targetEnv]
      exact ⟨And.right, fun remainderDenotes =>
        ⟨copyDenotes, remainderDenotes⟩⟩

theorem Local.nested_denotes_iff
    (outer : DiagramContext interfaceWires ancestorWires)
    (anchorLocals : List Sig)
    (selected : Region (ancestorWires ++ anchorLocals))
    (descendant : DiagramContext (ancestorWires ++ anchorLocals)
      descendantWires)
    (before after : Region descendantWires)
    (evidence : Local descendant selected before after)
    (model : Model) (env : Values model interfaceWires) :
    denoteRegion model env
        (nestedBody outer anchorLocals selected descendant before) ↔
      denoteRegion model env
        (nestedBody outer anchorLocals selected descendant after) := by
  apply DiagramContext.fill_equiv_of_reachable outer _ _ model env
  intro ancestorEnv outerReachable
  simp only [Region.denote_adjoinAt]
  constructor
  · rintro ⟨anchorEnv, _, combinedDenotes⟩
    rw [Region.denote_conjoin] at combinedDenotes
    refine ⟨anchorEnv, trivial, ?_⟩
    rw [Region.denote_conjoin]
    refine ⟨combinedDenotes.1, ?_⟩
    apply (DiagramContext.fill_equiv_of_reachable descendant _ _ model
      (ancestorEnv.append anchorEnv) ?_).mp combinedDenotes.2
    intro descendantEnv reachable
    exact Local.denotes_iff descendant selected before after evidence model
      (ancestorEnv.append anchorEnv) descendantEnv reachable
      combinedDenotes.1
  · rintro ⟨anchorEnv, _, combinedDenotes⟩
    rw [Region.denote_conjoin] at combinedDenotes
    refine ⟨anchorEnv, trivial, ?_⟩
    rw [Region.denote_conjoin]
    refine ⟨combinedDenotes.1, ?_⟩
    apply (DiagramContext.fill_equiv_of_reachable descendant _ _ model
      (ancestorEnv.append anchorEnv) ?_).mpr combinedDenotes.2
    intro descendantEnv reachable
    exact Local.denotes_iff descendant selected before after evidence model
      (ancestorEnv.append anchorEnv) descendantEnv reachable
      combinedDenotes.1

/-- Higher-order iteration and deiteration preserve denotation in either
direction. -/
theorem Iteration.sound
    {source target : OpenDiagram boundary}
    (step : Rule.Iteration source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  rcases step with ⟨occurrence, after, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  intro model args sourceDenotes
  have localIff : ∀ env : Values model occurrence.interface.external,
      denoteRegion model env
          (occurrence.targetBody occurrence.before) ↔
        denoteRegion model env
          (occurrence.targetBody after) := by
    intro env
    rcases localEvidence with forward | backward
    · exact Local.nested_denotes_iff occurrence.outer
        occurrence.anchorLocals occurrence.selected occurrence.descendant
        occurrence.before after forward model env
    · exact (Local.nested_denotes_iff occurrence.outer
        occurrence.anchorLocals occurrence.selected occurrence.descendant
        after occurrence.before backward model env).symm
  have sourceBody :=
    (occurrence.source_iso.denoteOpen_iff model args).mp sourceDenotes
  have targetBody : denoteOpen model
      (occurrence.interface.withBody
        (occurrence.targetBody after) targetCanonical
        targetExternalTwoEnded) args :=
    (OpenDiagram.denote_body_iff
      (diagram := occurrence.interface)
      (beforeCanonical := occurrence.sourceCanonical)
      (afterCanonical := targetCanonical) localIff).mp sourceBody
  exact (targetIso.denoteOpen_iff model args).mpr targetBody

end Iteration

end VisualProof.Rule
