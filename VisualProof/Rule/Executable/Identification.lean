import VisualProof.Rule.Identification

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
      (applicability : Local.Applicability data)
      (occurrence : Occurrence data.collapsedRegion source)
      (targetCanonical : data.exposedRegion.Canonical) :
      ForwardIndex source
  | localCollapse
      (data : Local.Data wires)
      (applicability : Local.Applicability data)
      (occurrence : Occurrence data.exposedRegion source)
      (targetCanonical : data.collapsedRegion.Canonical) :
      ForwardIndex source
  | openExpose
      (external : List Sig)
      (data : Open.Data boundary external)
      (applicability : Open.Applicability data)
      (sourceExternal : WireEquiv source.external external)
      (sourceBody : RegionIso sourceExternal source.body data.collapsedRegion)
      (sourceBoundary : ∀ position : Fin boundary.length,
        sourceExternal (source.boundaryWire.get position) =
          data.collapsedBoundary.get position)
      (sourceCanonical : data.collapsedRegion.Canonical)
      (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        data.collapsedBoundary data.collapsedRegion)
      (targetCanonical : data.exposedRegion.Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        data.exposedBoundary data.exposedRegion) :
      ForwardIndex source
  | openCollapse
      (external : List Sig)
      (data : Open.Data boundary external)
      (applicability : Open.Applicability data)
      (sourceExternal : WireEquiv source.external
        (external ++ List.replicate data.count data.signature))
      (sourceBody : RegionIso sourceExternal source.body data.exposedRegion)
      (sourceBoundary : ∀ position : Fin boundary.length,
        sourceExternal (source.boundaryWire.get position) =
          data.exposedBoundary.get position)
      (sourceCanonical : data.exposedRegion.Canonical)
      (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        data.exposedBoundary data.exposedRegion)
      (targetCanonical : data.collapsedRegion.Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        data.collapsedBoundary data.collapsedRegion) :
      ForwardIndex source

def BackwardIndex {boundary : List Sig}
    (source : OpenDiagram boundary) := ForwardIndex source

def runForward (source : OpenDiagram boundary) :
    ForwardIndex source → OpenDiagram boundary
  | .localExpose data applicability occurrence targetCanonical =>
      let validity := Local.exposedValidity data applicability occurrence
        targetCanonical
      occurrence.interface.withBody
        (occurrence.context.fill data.exposedRegion) validity.1 validity.2
  | .localCollapse data applicability occurrence targetCanonical =>
      let validity := Local.collapsedValidity data applicability occurrence
        targetCanonical
      occurrence.interface.withBody
        (occurrence.context.fill data.collapsedRegion) validity.1 validity.2
  | .openExpose _ data applicability _ _ _ _ _
      targetCanonical targetExternalTwoEnded => {
        external := _
        boundaryWire := data.exposedBoundary
        boundarySurjective := applicability.boundarySurjective
        body := data.exposedRegion
        canonical := targetCanonical
        externalTwoEnded := targetExternalTwoEnded
      }
  | .openCollapse _ data _ _ _ _ _ _
      targetCanonical targetExternalTwoEnded => {
        external := _
        boundaryWire := data.collapsedBoundary
        boundarySurjective := data.collapsedBoundarySurjective
        body := data.collapsedRegion
        canonical := targetCanonical
        externalTwoEnded := targetExternalTwoEnded
      }

def runBackward (source : OpenDiagram boundary) :
    BackwardIndex source → OpenDiagram boundary :=
  runForward source

theorem forward_exact (source target : OpenDiagram boundary) :
    (∃ index : ForwardIndex source,
      OpenDiagram.Isomorphic (runForward source index) target) ↔
      VisualProof.Rule.Identification source target := by
  constructor
  · rintro ⟨index, isomorphic⟩
    apply Rule.Identification.respectsTargetIso (target' := target) ?_
      isomorphic
    cases index with
    | localExpose data applicability occurrence targetCanonical =>
        let validity := Local.exposedValidity data applicability occurrence
          targetCanonical
        exact Or.inl ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _,
          atPolarity_symmetric_of occurrence.context.polarity
            (.expose data applicability)⟩
    | localCollapse data applicability occurrence targetCanonical =>
        let validity := Local.collapsedValidity data applicability occurrence
          targetCanonical
        refine Or.inl ⟨_, _, _, occurrence, validity.1, validity.2,
          OpenDiagramIso.refl _, ?_⟩
        cases occurrence.context.polarity <;>
          simp only [atPolarity, symmetric, converse]
        · exact Or.inr (.expose data applicability)
        · exact Or.inl (.expose data applicability)
    | openExpose external data applicability sourceExternal sourceBody
        sourceBoundary sourceCanonical sourceExternalTwoEnded
        targetCanonical targetExternalTwoEnded =>
        exact Or.inr (Or.inl ⟨{
          external := external
          data := data
          applicability := applicability
          sourceExternal := sourceExternal
          sourceBody := sourceBody
          sourceBoundary := sourceBoundary
          sourceCanonical := sourceCanonical
          sourceExternalTwoEnded := sourceExternalTwoEnded
          targetExternal := WireEquiv.refl _
          targetBody := RegionIso.refl _
          targetBoundary := fun _ => rfl
          targetCanonical := targetCanonical
          targetExternalTwoEnded := targetExternalTwoEnded
        }⟩)
    | openCollapse external data applicability sourceExternal sourceBody
        sourceBoundary sourceCanonical sourceExternalTwoEnded
        targetCanonical targetExternalTwoEnded =>
        exact Or.inr (Or.inr ⟨{
          external := external
          data := data
          applicability := applicability
          sourceExternal := WireEquiv.refl _
          sourceBody := RegionIso.refl _
          sourceBoundary := fun _ => rfl
          sourceCanonical := targetCanonical
          sourceExternalTwoEnded := targetExternalTwoEnded
          targetExternal := sourceExternal
          targetBody := sourceBody
          targetBoundary := sourceBoundary
          targetCanonical := sourceCanonical
          targetExternalTwoEnded := sourceExternalTwoEnded
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
                exact ⟨.localExpose data applicability occurrence
                  (occurrence.context.holeCanonical _ canonical),
                  ⟨targetIso.symm⟩⟩
          · cases reverse with
            | expose data applicability =>
                exact ⟨.localCollapse data applicability occurrence
                  (occurrence.context.holeCanonical _ canonical),
                  ⟨targetIso.symm⟩⟩
      | negative =>
          simp only [polarity, atPolarity, symmetric, converse]
            at localEvidence
          rcases localEvidence with reverse | direct
          · cases reverse with
            | expose data applicability =>
                exact ⟨.localCollapse data applicability occurrence
                  (occurrence.context.holeCanonical _ canonical),
                  ⟨targetIso.symm⟩⟩
          · cases direct with
            | expose data applicability =>
                exact ⟨.localExpose data applicability occurrence
                  (occurrence.context.holeCanonical _ canonical),
                  ⟨targetIso.symm⟩⟩
    · rcases openForward with ⟨step⟩
      let index := ForwardIndex.openExpose step.external step.data
        step.applicability step.sourceExternal step.sourceBody
        step.sourceBoundary step.sourceCanonical step.sourceExternalTwoEnded
        step.targetCanonical step.targetExternalTwoEnded
      let targetPresentation := runForward source index
      let targetIso : OpenDiagramIso target targetPresentation := {
        external := step.targetExternal
        boundary_eq := step.targetBoundary
        body := step.targetBody
      }
      exact ⟨index, ⟨targetIso.symm⟩⟩
    · rcases openBackward with ⟨step⟩
      let index := ForwardIndex.openCollapse step.external step.data
        step.applicability step.targetExternal step.targetBody
        step.targetBoundary step.targetCanonical step.targetExternalTwoEnded
        step.sourceCanonical step.sourceExternalTwoEnded
      let targetPresentation := runForward source index
      let targetIso : OpenDiagramIso target targetPresentation := {
        external := step.sourceExternal
        boundary_eq := step.sourceBoundary
        body := step.sourceBody
      }
      exact ⟨index, ⟨targetIso.symm⟩⟩

theorem backward_exact (source target : OpenDiagram boundary) :
    (∃ index : BackwardIndex source,
      OpenDiagram.Isomorphic (runBackward source index) target) ↔
      VisualProof.Rule.Identification target source := by
  constructor
  · intro witness
    have forwardWitness : ∃ index : ForwardIndex source,
        OpenDiagram.Isomorphic (runForward source index) target := by
      simpa only [BackwardIndex, runBackward] using witness
    exact Rule.Identification.symm
      ((forward_exact source target).mp forwardWitness)
  · intro step
    have forwardWitness :=
      (forward_exact source target).mpr (Rule.Identification.symm step)
    simpa only [BackwardIndex, runBackward] using forwardWitness

end VisualProof.Rule.Identification
