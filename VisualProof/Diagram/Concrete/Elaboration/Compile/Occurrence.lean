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



end VisualProof.Diagram
