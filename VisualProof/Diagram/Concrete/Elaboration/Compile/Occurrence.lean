import VisualProof.Diagram.Concrete.Elaboration.Compile.Certified

namespace VisualProof.Diagram

open ConcreteElaboration
open VisualProof.Data.Finite
open VisualProof.Theory

namespace OpenOccurrenceEquiv

/-- Certified ordered occurrence equivalence commutes with elaboration. -/
def elaborate_equivalent {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (hsource : source.WellFormed signature)
    (htarget : target.WellFormed signature) :
    OpenDiagramIso (source.elaborate hsource)
      ((target.elaborate htarget).castArity
        equiv.boundary_length_eq.symm) := by
  have hambient : CertifiedWireContextsAgree equiv.diagram
      source.exposedWires target.exposedWires equiv.exposedWiresEquiv :=
    equiv.exposedWiresEquiv_spec
  have hlocal : CertifiedWireContextsAgree equiv.diagram
      source.hiddenWires target.hiddenWires equiv.hiddenWiresEquiv :=
    equiv.hiddenWiresEquiv_spec
  have hwires := certifiedAppendContextsAgree hambient hlocal
  have htargetExact : ConcreteElaboration.WireContext.Exact
      (target.exposedWires ++ target.hiddenWires) target.diagram.root := by
    simpa only [OpenConcreteDiagram.rootWires] using
      ConcreteElaboration.openRootWires_exact htarget
  have hbody : RegionIso signature equiv.exposedWiresEquiv []
      (source.elaborate hsource).body (target.elaborate htarget).body := by
    obtain ⟨sourceBody, hsourceKernel, hsourceElaborate⟩ :=
      CheckedOpenDiagram.elaborate_body_computation
        (show CheckedOpenDiagram signature from ⟨source, hsource⟩)
    obtain ⟨targetBody, htargetKernel, htargetElaborate⟩ :=
      CheckedOpenDiagram.elaborate_body_computation
        (show CheckedOpenDiagram signature from ⟨target, htarget⟩)
    change (source.elaborate hsource).body = sourceBody at hsourceElaborate
    change (target.elaborate htarget).body = targetBody at htargetElaborate
    rw [hsourceElaborate, htargetElaborate]
    exact compileRoot?_certifiedEquivariant equiv.diagram
      htarget.diagram_well_formed hwires htargetExact
      hsourceKernel htargetKernel
  apply OpenDiagramIso.ofArityEq equiv.boundary_length_eq
    equiv.exposedWiresEquiv
  · intro position
    simpa only [OpenConcreteDiagram.elaborate_boundary] using
      equiv.boundaryClass_commute position
  · exact hbody

/-- Public ordered-open semantic contract for a certified occurrence. -/
theorem denote_iff {source target : OpenConcreteDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (hsource : source.WellFormed signature)
    (htarget : target.WellFormed signature)
    (model : Model)
    (named : NamedEnv model.Carrier signature)
    (args : Fin source.boundary.length → model.Carrier) :
    denoteOpen model named (source.elaborate hsource) args ↔
      denoteOpen model named
        ((target.elaborate htarget).castArity
          equiv.boundary_length_eq.symm) args :=
  (equiv.elaborate_equivalent hsource htarget).denoteOpen_iff model named args

end OpenOccurrenceEquiv

namespace ConcreteExamples

def bareWireChecked : CheckedDiagram [] :=
  ⟨bareWire, checkWellFormed_iff.mp bareWire_check⟩

def repeatedBoundaryChecked : CheckedOpenDiagram [] :=
  ⟨repeatedBoundary, repeatedBoundary_wellFormed⟩

def exposedAndHiddenOpenChecked : CheckedOpenDiagram [] :=
  ⟨exposedAndHiddenOpen, exposedAndHiddenOpen_wellFormed⟩

theorem bareWire_elaborate :
    bareWireChecked.elaborate = bareLocalWireExample := by
  obtain ⟨body, hkernel, helaborate⟩ :=
    CheckedDiagram.elaborate_computation bareWireChecked
  have hbody : body = bareLocalWireExample := by
    have hkernel' := hkernel
    simp only [bareWireChecked] at hkernel'
    change some bareLocalWireExample = some body at hkernel'
    exact Option.some.inj hkernel'.symm
  exact helaborate.trans hbody

theorem repeatedBoundary_open_elaborate_shape :
    repeatedBoundaryChecked.elaborate.externalClasses = 1 ∧
      repeatedBoundaryChecked.elaborate.boundary ⟨0, by decide⟩ =
        ⟨0, by
          rw [CheckedOpenDiagram.elaborate_externalClasses]
          decide⟩ ∧
      repeatedBoundaryChecked.elaborate.boundary ⟨1, by decide⟩ =
        ⟨0, by
          rw [CheckedOpenDiagram.elaborate_externalClasses]
          decide⟩ ∧
      repeatedBoundaryChecked.elaborate.body = Region.mk 0 .nil := by
  obtain ⟨body, hkernel, helaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation repeatedBoundaryChecked
  have hbody : body = Region.mk 0 .nil := by
    have hkernel' := hkernel
    simp only [repeatedBoundaryChecked] at hkernel'
    change some (Region.mk 0 .nil) = some body at hkernel'
    exact Option.some.inj hkernel'.symm
  exact ⟨rfl, rfl, rfl, helaborate.trans hbody⟩

theorem exposedAndHidden_open_elaborate_shape :
    exposedAndHiddenOpenChecked.elaborate.externalClasses = 1 ∧
      exposedAndHiddenOpenChecked.elaborate.boundary ⟨0, by decide⟩ =
        ⟨0, by
          rw [CheckedOpenDiagram.elaborate_externalClasses]
          decide⟩ ∧
      exposedAndHiddenOpenChecked.elaborate.body = Region.mk 1 .nil := by
  obtain ⟨body, hkernel, helaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation exposedAndHiddenOpenChecked
  have hbody : body = Region.mk 1 .nil := by
    have hkernel' := hkernel
    simp only [exposedAndHiddenOpenChecked] at hkernel'
    change some (Region.mk 1 .nil) = some body at hkernel'
    exact Option.some.inj hkernel'.symm
  exact ⟨rfl, rfl, helaborate.trans hbody⟩

end ConcreteExamples

namespace OpenConcreteIsomorphismExamples

def relabeledOpenElaborationIso :
    OpenDiagramIso
      (relabeledSource.elaborate relabeledSource_wellFormed)
      ((relabeledTarget.elaborate relabeledTarget_wellFormed).castArity
        relabeledOpenIso.boundary_length_eq.symm) :=
  relabeledOpenIso.elaborate_isomorphic relabeledSource_wellFormed
    relabeledTarget_wellFormed

theorem relabeledOpenElaboration_preserves_positions
    (position : Fin relabeledSource.boundary.length) :
    relabeledOpenElaborationIso.external
        ((relabeledSource.elaborate
          relabeledSource_wellFormed).boundary position) =
      ((relabeledTarget.elaborate relabeledTarget_wellFormed).castArity
        relabeledOpenIso.boundary_length_eq.symm).boundary position :=
  relabeledOpenElaborationIso.boundary position

end OpenConcreteIsomorphismExamples

end VisualProof.Diagram
