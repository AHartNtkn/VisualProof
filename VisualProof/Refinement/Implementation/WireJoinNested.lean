import VisualProof.Refinement.Implementation.WireJoinOpenContext
import VisualProof.Diagram.ContextPathIsomorphism

namespace VisualProof.Refinement.Implementation.WireJoinNested

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Refinement.Implementation.WireJoin
open VisualProof.Refinement.Implementation.WireJoinOpenContext

private def castOpenIso
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem castArity_cancel
    (diagram : OpenDiagram sourceArity)
    (equality : sourceArity = targetArity) :
    (diagram.castArity equality).castArity equality.symm = diagram := by
  subst targetArity
  rfl

theorem nested
    (source : Concrete.CheckedOpen)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceView : Concrete.Splice.OpenSiteView source
      (source.val.diagram.wires inner).scope)
    (targetView : Concrete.Splice.OpenSiteView
      (targetOpen source outer inner distinct ordered targetWellFormed)
      (source.val.diagram.wires inner).scope) :
    let target := targetOpen source outer inner distinct ordered
      targetWellFormed
    let boundaryLength := boundaryLengthEq source.val outer inner distinct
    Rule.atPolarity sourceView.focus.context.polarity Rule.WireSever
      target.elaborate (source.elaborate.castArity boundaryLength.symm) := by
  dsimp only
  let target := targetOpen source outer inner distinct ordered
    targetWellFormed
  let boundaryLength := boundaryLengthEq source.val outer inner distinct
  obtain ⟨result⟩ := openSiteContextIso source outer inner distinct ordered
    targetWellFormed nested sourceView targetView
  let targetInterface := target.elaborate
  have targetBodyIso : Core.Isomorphic target.elaborate.body
      (targetView.focus.context.fill result.before) := by
    have rebuildIso : Core.Isomorphic target.elaborate.body
        (targetView.focus.context.fill targetView.focus.body) := by
      exact cast (congrArg
        (fun body => Core.Isomorphic body
          (targetView.focus.context.fill targetView.focus.body))
        targetView.rebuild)
        (RegionIso.refl
          (targetView.focus.context.fill targetView.focus.body))
    exact rebuildIso.trans
      (targetView.focus.context.fill_iso result.target_iso)
  let targetHostIso : OpenDiagramIso target.elaborate
      (targetInterface.withBody
        (targetView.focus.context.fill result.before)) := {
    external := FiniteEquiv.refl (Fin target.elaborate.externalClasses)
    boundary := fun _ => rfl
    body := targetBodyIso
  }
  have sourceBodyIso : RegionIso
      (nestedOuterEquiv source outer inner distinct nested) []
      source.elaborate.body
      (targetView.focus.context.fill result.after) := by
    exact result.alignment.contexts.root result.source_iso sourceView.rebuild
      (DiagramContext.fill_castHoleRels
        result.alignment.holeRelsEq.symm targetView.focus.context result.after)
  let sourceUncastIso : OpenDiagramIso source.elaborate
      ((targetInterface.withBody
        (targetView.focus.context.fill result.after)).castArity
          boundaryLength) :=
    OpenDiagramIso.ofArityEq boundaryLength.symm
      (nestedOuterEquiv source outer inner distinct nested)
      (by
        intro position
        let targetPosition := Fin.cast boundaryLength.symm position
        have boundaryEq := boundaryClass_map source.val outer inner distinct
          targetPosition
        simpa [target, targetInterface, targetPosition, boundaryLength,
          nestedOuterEquiv, Concrete.CheckedOpen.elaborate_boundary] using
            boundaryEq.symm)
      sourceBodyIso
  let sourceHostIso : OpenDiagramIso
      (source.elaborate.castArity boundaryLength.symm)
      (targetInterface.withBody
        (targetView.focus.context.fill result.after)) := by
    have casted := castOpenIso boundaryLength.symm sourceUncastIso
    let desired := targetInterface.withBody
      (targetView.focus.context.fill result.after)
    have sourceCastEq :
        (desired.castArity boundaryLength).castArity boundaryLength.symm =
          desired := by
      exact castArity_cancel desired boundaryLength
    exact cast (congrArg
      (fun diagram => OpenDiagramIso
        (source.elaborate.castArity boundaryLength.symm) diagram)
        sourceCastEq) casted
  have contextsDepth : sourceView.focus.context.cutDepth =
      targetView.focus.context.cutDepth :=
    result.alignment.contexts.cutDepth_eq.trans
      (DiagramContext.cutDepth_castRels result.alignment.holeRelsEq.symm
        targetView.focus.context)
  have contextsPolarity : sourceView.focus.context.polarity =
      targetView.focus.context.polarity := by
    unfold DiagramContext.polarity
    rw [contextsDepth]
  cases polarityEq : sourceView.focus.context.polarity with
  | positive =>
      simp only [Rule.atPolarity]
      let occurrence : Occurrence result.before target.elaborate := {
        interface := targetInterface
        context := targetView.focus.context
        host_iso := targetHostIso
      }
      exact Or.inl ⟨_, _, result.before, result.after, occurrence,
        sourceHostIso, by
          change Rule.atPolarity targetView.focus.context.polarity
            Rule.WireSever.Local result.before result.after
          rw [← contextsPolarity, polarityEq]
          exact result.rewrite⟩
  | negative =>
      simp only [Rule.atPolarity, Rule.converse]
      let occurrence : Occurrence result.after
          (source.elaborate.castArity boundaryLength.symm) := {
        interface := targetInterface
        context := targetView.focus.context
        host_iso := sourceHostIso
      }
      exact Or.inl ⟨_, _, result.after, result.before, occurrence,
        targetHostIso, by
          change Rule.atPolarity targetView.focus.context.polarity
            Rule.WireSever.Local result.after result.before
          rw [← contextsPolarity, polarityEq]
          exact result.rewrite⟩

end VisualProof.Refinement.Implementation.WireJoinNested
