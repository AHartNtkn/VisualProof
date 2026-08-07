import VisualProof.Refinement.Implementation.WireSeverPairedContext
import VisualProof.Diagram.ContextPathIsomorphism

namespace VisualProof.Refinement.Implementation.WireSeverNested

open VisualProof
open VisualProof.Diagram
open VisualProof.Data.Finite
open VisualProof.Refinement.Implementation.WireSeverPairedContext

private def castOpenIso
    {sourceArity targetArity : Nat}
    (equality : sourceArity = targetArity)
    {source target : OpenDiagram sourceArity}
    (iso : OpenDiagramIso source target) :
    OpenDiagramIso (source.castArity equality) (target.castArity equality) := by
  subst targetArity
  simpa using iso

private theorem castArity_castArity
    (diagram : OpenDiagram firstArity)
    (first : firstArity = secondArity)
    (second : secondArity = thirdArity) :
    (diagram.castArity first).castArity second =
      diagram.castArity (first.trans second) := by
  subst secondArity
  subst thirdArity
  rfl

theorem nested
    (source : Concrete.CheckedOpen)
    (wire : Fin source.val.diagram.wireCount)
    (keep : List (Concrete.CEndpoint source.val.diagram.nodeCount))
    (targetWellFormed :
      (Concrete.severWireRaw source.val.diagram wire keep).WellFormed)
    (nested : source.val.diagram.root ≠
      (source.val.diagram.wires wire).scope)
    (targetView : Concrete.Splice.OpenSiteView
      (VisualProof.Refinement.Implementation.WireSever.canonicalOpen
        source wire keep targetWellFormed)
      (source.val.diagram.wires wire).scope)
    (sourceView : Concrete.Splice.OpenSiteView source
      (source.val.diagram.wires wire).scope) :
    let target := VisualProof.Refinement.Implementation.WireSever.canonicalOpen
      source wire keep targetWellFormed
    let boundaryLength := VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq source.val wire keep
    Rule.atPolarity sourceView.focus.context.polarity Rule.WireSever
      source.elaborate (target.elaborate.castArity boundaryLength) := by
  dsimp only
  let target := VisualProof.Refinement.Implementation.WireSever.canonicalOpen
    source wire keep targetWellFormed
  let boundaryLength := VisualProof.Refinement.Implementation.WireSever.severBoundaryLengthEq source.val wire keep
  obtain ⟨result⟩ := severOpenSiteContextIso source wire keep
    targetWellFormed nested targetView sourceView
  let sourceInterface := source.elaborate
  have sourceBodyIso : Core.Isomorphic source.elaborate.body
      (sourceView.focus.context.fill result.before) := by
    have rebuildIso : Core.Isomorphic source.elaborate.body
        (sourceView.focus.context.fill sourceView.focus.body) := by
      exact cast (congrArg
        (fun body => Core.Isomorphic body
          (sourceView.focus.context.fill sourceView.focus.body))
        sourceView.rebuild)
        (RegionIso.refl
          (sourceView.focus.context.fill sourceView.focus.body))
    exact rebuildIso.trans
      (sourceView.focus.context.fill_iso result.source_iso)
  let sourceHostIso : OpenDiagramIso source.elaborate
      (sourceInterface.withBody
        (sourceView.focus.context.fill result.before)) := {
    external := FiniteEquiv.refl (Fin source.elaborate.externalClasses)
    boundary := fun _ => rfl
    body := sourceBodyIso
  }
  have targetBodyIso : RegionIso
      (nestedRootOuterEquiv source wire keep) [] target.elaborate.body
      (sourceView.focus.context.fill result.after) := by
    exact result.alignment.contexts.root result.target_iso targetView.rebuild
      (DiagramContext.fill_castHoleRels
        result.alignment.holeRelsEq.symm sourceView.focus.context result.after)
  let targetUncastIso : OpenDiagramIso target.elaborate
      ((sourceInterface.withBody
        (sourceView.focus.context.fill result.after)).castArity
          boundaryLength.symm) :=
    OpenDiagramIso.ofArityEq boundaryLength
      (by
        simpa [target, sourceInterface] using
          nestedRootOuterEquiv source wire keep)
      (by
        intro position
        let sourcePosition := Fin.cast boundaryLength position
        have boundaryEq :=
          VisualProof.Refinement.Implementation.WireSever.severBoundaryClass source.val wire keep sourcePosition
        simpa [target, sourceInterface, sourcePosition, nestedRootOuterEquiv,
          Concrete.CheckedOpen.elaborate_boundary] using boundaryEq)
      targetBodyIso
  let targetHostIso : OpenDiagramIso
      (target.elaborate.castArity boundaryLength)
      (sourceInterface.withBody
        (sourceView.focus.context.fill result.after)) := by
    have casted := castOpenIso boundaryLength targetUncastIso
    let desired := sourceInterface.withBody
      (sourceView.focus.context.fill result.after)
    have targetCastEq :
        (desired.castArity boundaryLength.symm).castArity boundaryLength =
          desired := by
      rw [castArity_castArity]
      have proofEq : boundaryLength.symm.trans boundaryLength = rfl :=
        Subsingleton.elim _ _
      rw [proofEq]
      rfl
    exact cast (congrArg
      (fun diagram => OpenDiagramIso
        (target.elaborate.castArity boundaryLength) diagram) targetCastEq)
      casted
  cases polarityEq : sourceView.focus.context.polarity with
  | positive =>
      simp only [Rule.atPolarity]
      let occurrence : Occurrence result.before source.elaborate := {
        interface := sourceInterface
        context := sourceView.focus.context
        host_iso := sourceHostIso
      }
      exact Or.inl ⟨_, _, result.before, result.after, occurrence,
        targetHostIso, by
          change Rule.atPolarity sourceView.focus.context.polarity
            Rule.WireSever.Local result.before result.after
          rw [polarityEq]
          exact result.rewrite⟩
  | negative =>
      simp only [Rule.atPolarity, Rule.converse]
      let occurrence : Occurrence result.after
          (target.elaborate.castArity boundaryLength) := {
        interface := sourceInterface
        context := sourceView.focus.context
        host_iso := targetHostIso
      }
      exact Or.inl ⟨_, _, result.after, result.before, occurrence,
        sourceHostIso, by
          change Rule.atPolarity sourceView.focus.context.polarity
            Rule.WireSever.Local result.after result.before
          rw [polarityEq]
          exact result.rewrite⟩

end VisualProof.Refinement.Implementation.WireSeverNested
