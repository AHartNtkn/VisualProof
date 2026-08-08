import VisualProof.Concrete.Elaboration.Compile.Certified

namespace VisualProof.Concrete

open VisualProof.Diagram

open Elaboration
open VisualProof.Data.Finite
open VisualProof.Theory

namespace OpenOccurrenceEquiv

/-- Certified ordered occurrence equivalence commutes with elaboration. -/
noncomputable def elaborate_equivalent {source target : OpenDiagram}
    (equiv : OpenOccurrenceEquiv source target)
    (hsource : source.WellFormed )
    (htarget : target.WellFormed ) :
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
  have htargetExact : Elaboration.WireContext.Exact
      (target.exposedWires ++ target.hiddenWires) target.diagram.root := by
    simpa only [OpenDiagram.rootWires] using
      Elaboration.openRootWires_exact htarget
  have hbody : RegionIso  equiv.exposedWiresEquiv []
      (source.elaborate hsource).body (target.elaborate htarget).body := by
    have hsourceKernel : compileRoot? source.diagram source.exposedWires
        source.hiddenWires = some (source.elaborate hsource).body := by
      obtain ⟨sourceBody, hkernel, helaborate⟩ :=
        CheckedOpen.elaborate_body_computation
          (show CheckedOpen from ⟨source, hsource⟩)
      change (source.elaborate hsource).body = sourceBody at helaborate
      rw [helaborate]
      exact hkernel
    have htargetKernel : compileRoot? target.diagram target.exposedWires
        target.hiddenWires = some (target.elaborate htarget).body := by
      obtain ⟨targetBody, hkernel, helaborate⟩ :=
        CheckedOpen.elaborate_body_computation
          (show CheckedOpen from ⟨target, htarget⟩)
      change (target.elaborate htarget).body = targetBody at helaborate
      rw [helaborate]
      exact hkernel
    exact compileRoot?_certifiedEquivariant equiv.diagram
      htarget.diagram_well_formed hwires htargetExact
      hsourceKernel htargetKernel
  apply OpenDiagramIso.ofArityEq equiv.boundary_length_eq
    equiv.exposedWiresEquiv
  · intro position
    simpa only [OpenDiagram.elaborate_boundary] using
      equiv.boundaryClass_commute position
  · exact hbody

end OpenOccurrenceEquiv



end VisualProof.Concrete
