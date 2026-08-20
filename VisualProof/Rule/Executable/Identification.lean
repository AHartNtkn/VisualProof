import VisualProof.Rule.Identification
import VisualProof.Rule.Executable.WirePrimitive.Uniform

namespace VisualProof.Rule.Identification

open Theory
open Diagram

/-- Direct source-indexed identification execution.  Every constructor stores
the exact selected node, wire, away partition, and (for root exposure) ordered
boundary partition.  No constructor stores a target diagram or rule witness. -/
inductive ForwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) : Type
  | localExpose
      (data : Local.Data wires)
      (occurrence : Occurrence data.collapsedRegion source) :
      ForwardIndex source
  | localCollapse
      (data : Local.Data wires)
      (occurrence : Occurrence data.exposedRegion source) :
      ForwardIndex source
  | openExpose
      (external : List Sig)
      (data : Open.Data boundary external)
      (sourceExternal : WireEquiv source.external external)
      (sourceBody : RegionIso sourceExternal source.body data.collapsedRegion)
      (sourceBoundary : ∀ position : Fin boundary.length,
        sourceExternal (source.boundaryWire.get position) =
          data.collapsedBoundary.get position)
      (sourceCanonical : data.collapsedRegion.Canonical)
      (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        data.collapsedBoundary data.collapsedRegion) :
      ForwardIndex source
  | openCollapse
      (external : List Sig)
      (data : Open.Data boundary external)
      (sourceExternal : WireEquiv source.external
        (external ++ List.replicate data.count data.signature))
      (sourceBody : RegionIso sourceExternal source.body data.exposedRegion)
      (sourceBoundary : ∀ position : Fin boundary.length,
        sourceExternal (source.boundaryWire.get position) =
          data.exposedBoundary.get position)
      (sourceCanonical : data.exposedRegion.Canonical)
      (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        data.exposedBoundary data.exposedRegion) :
      ForwardIndex source

def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

private def exposedCandidate (external : List Sig)
    (data : Open.Data boundary external) : OpenDiagram.Candidate boundary :=
  .mk (external ++ List.replicate data.count data.signature)
    data.exposedBoundary data.exposedRegion

private def collapsedCandidate (external : List Sig)
    (data : Open.Data boundary external) : OpenDiagram.Candidate boundary :=
  .mk external data.collapsedBoundary data.collapsedRegion

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → Option (OpenDiagram boundary)
  | .localExpose data occurrence =>
      WirePrimitive.Executable.validateBodyWhen
        (Local.Applicability data) occurrence.interface
        (occurrence.context.fill data.exposedRegion)
  | .localCollapse data occurrence =>
      WirePrimitive.Executable.validateBodyWhen
        (Local.Applicability data) occurrence.interface
        (occurrence.context.fill data.collapsedRegion)
  | .openExpose external data _ _ _ _ _ =>
      (exposedCandidate external data).validateWhen (Open.Applicability data)
  | .openCollapse external data _ _ _ _ _ =>
      (collapsedCandidate external data).validateWhen (Open.Applicability data)

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → Option (OpenDiagram boundary) :=
  runForward source


theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ (index : ForwardIndex source) (output : OpenDiagram boundary),
      runForward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Identification source target := by
  constructor
  · rintro ⟨index, output, computed, ⟨outputIso⟩⟩
    cases index with
    | localExpose data occurrence =>
        obtain ⟨applicability, canonical, twoEnded, outputEq⟩ :=
          (WirePrimitive.Executable.validateBodyWhen_eq_some_iff
            (Local.Applicability data) occurrence.interface
            (occurrence.context.fill data.exposedRegion) output).mp computed
        subst output
        exact Or.inl ⟨_, _, _, occurrence, canonical, twoEnded,
          outputIso.symm,
          atPolarity_symmetric_of occurrence.context.polarity
            (.expose data applicability)⟩
    | localCollapse data occurrence =>
        obtain ⟨applicability, canonical, twoEnded, outputEq⟩ :=
          (WirePrimitive.Executable.validateBodyWhen_eq_some_iff
            (Local.Applicability data) occurrence.interface
            (occurrence.context.fill data.collapsedRegion) output).mp computed
        subst output
        refine Or.inl ⟨_, _, _, occurrence, canonical, twoEnded,
          outputIso.symm, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr (.expose data applicability)
        · exact Or.inl (.expose data applicability)
    | openExpose external data sourceExternal sourceBody sourceBoundary
        sourceCanonical sourceTwoEnded =>
        obtain ⟨applicability, valid, outputEq⟩ :=
          (OpenDiagram.Candidate.validateWhen_eq_some_iff
            (exposedCandidate external data) (Open.Applicability data)
            output).mp computed
        subst output
        exact Or.inr (Or.inl ⟨{
          external := external
          data := data
          applicability := applicability
          sourceExternal := sourceExternal
          sourceBody := sourceBody
          sourceBoundary := sourceBoundary
          sourceCanonical := sourceCanonical
          sourceExternalTwoEnded := sourceTwoEnded
          targetExternal := outputIso.external.symm
          targetBody := outputIso.body.symm
          targetBoundary := fun position => by
            rw [← outputIso.boundary_eq position,
              WireEquiv.symm_apply_apply]
            rfl
          targetCanonical := valid.2.1
          targetExternalTwoEnded := valid.2.2
        }⟩)
    | openCollapse external data sourceExternal sourceBody sourceBoundary
        sourceCanonical sourceTwoEnded =>
        obtain ⟨applicability, valid, outputEq⟩ :=
          (OpenDiagram.Candidate.validateWhen_eq_some_iff
            (collapsedCandidate external data) (Open.Applicability data)
            output).mp computed
        subst output
        exact Or.inr (Or.inr ⟨{
          external := external
          data := data
          applicability := applicability
          sourceExternal := outputIso.external.symm
          sourceBody := outputIso.body.symm
          sourceBoundary := fun position => by
            rw [← outputIso.boundary_eq position,
              WireEquiv.symm_apply_apply]
            rfl
          sourceCanonical := valid.2.1
          sourceExternalTwoEnded := valid.2.2
          targetExternal := sourceExternal
          targetBody := sourceBody
          targetBoundary := sourceBoundary
          targetCanonical := sourceCanonical
          targetExternalTwoEnded := sourceTwoEnded
        }⟩)
  · rintro (localStep | openForward | openBackward)
    · rcases localStep with ⟨wires, before, after, occurrence,
        canonical, twoEnded, targetIso, localEvidence⟩
      cases polarity : occurrence.context.polarity with
      | positive =>
          simp only [polarity, atPolarity, symmetric] at localEvidence
          rcases localEvidence with direct | reverse
          · cases direct with
            | expose data applicability =>
                refine ⟨.localExpose data occurrence,
                  occurrence.interface.withBody
                    (occurrence.context.fill data.exposedRegion)
                    canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
                exact WirePrimitive.Executable.validateBodyWhen_of_valid
                  (Local.Applicability data) applicability _ _ canonical twoEnded
          · cases reverse with
            | expose data applicability =>
                refine ⟨.localCollapse data occurrence,
                  occurrence.interface.withBody
                    (occurrence.context.fill data.collapsedRegion)
                    canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
                exact WirePrimitive.Executable.validateBodyWhen_of_valid
                  (Local.Applicability data) applicability _ _ canonical twoEnded
      | negative =>
          simp only [polarity, atPolarity, symmetric, converse]
            at localEvidence
          rcases localEvidence with reverse | direct
          · cases reverse with
            | expose data applicability =>
                refine ⟨.localCollapse data occurrence,
                  occurrence.interface.withBody
                    (occurrence.context.fill data.collapsedRegion)
                    canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
                exact WirePrimitive.Executable.validateBodyWhen_of_valid
                  (Local.Applicability data) applicability _ _ canonical twoEnded
          · cases direct with
            | expose data applicability =>
                refine ⟨.localExpose data occurrence,
                  occurrence.interface.withBody
                    (occurrence.context.fill data.exposedRegion)
                    canonical twoEnded, ?_, ⟨targetIso.symm⟩⟩
                exact WirePrimitive.Executable.validateBodyWhen_of_valid
                  (Local.Applicability data) applicability _ _ canonical twoEnded
    · rcases openForward with ⟨step⟩
      let index := ForwardIndex.openExpose step.external step.data
        step.sourceExternal step.sourceBody step.sourceBoundary
        step.sourceCanonical step.sourceExternalTwoEnded
      let valid : (exposedCandidate step.external step.data).Valid :=
        ⟨step.applicability.boundarySurjective, step.targetCanonical,
          step.targetExternalTwoEnded⟩
      refine ⟨index, (exposedCandidate step.external step.data).toOpen valid,
        ?_, ?_⟩
      · exact OpenDiagram.Candidate.validateWhen_of_valid _
          (Open.Applicability step.data) step.applicability valid
      · exact ⟨{
          external := step.targetExternal.symm
          boundary_eq := fun position => by
            change step.targetExternal.symm
              (step.data.exposedBoundary.get position) =
                target.boundaryWire.get position
            rw [← step.targetBoundary position,
              WireEquiv.symm_apply_apply]
          body := step.targetBody.symm
        }⟩
    · rcases openBackward with ⟨step⟩
      let index := ForwardIndex.openCollapse step.external step.data
        step.targetExternal step.targetBody step.targetBoundary
        step.targetCanonical step.targetExternalTwoEnded
      let valid : (collapsedCandidate step.external step.data).Valid :=
        ⟨step.data.collapsedBoundarySurjective, step.sourceCanonical,
          step.sourceExternalTwoEnded⟩
      refine ⟨index, (collapsedCandidate step.external step.data).toOpen valid,
        ?_, ?_⟩
      · exact OpenDiagram.Candidate.validateWhen_of_valid _
          (Open.Applicability step.data) step.applicability valid
      · exact ⟨{
          external := step.sourceExternal.symm
          boundary_eq := fun position => by
            change step.sourceExternal.symm
              (step.data.collapsedBoundary.get position) =
                target.boundaryWire.get position
            rw [← step.sourceBoundary position,
              WireEquiv.symm_apply_apply]
          body := step.sourceBody.symm
        }⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ (index : BackwardIndex source) (output : OpenDiagram boundary),
      runBackward source index = some output ∧
        OpenDiagram.Isomorphic output target) ↔
      VisualProof.Rule.Identification target source := by
  constructor
  · intro witness
    exact Rule.Identification.symm ((forward_exact source target).mp witness)
  · intro step
    exact (forward_exact source target).mpr (Rule.Identification.symm step)

end VisualProof.Rule.Identification
