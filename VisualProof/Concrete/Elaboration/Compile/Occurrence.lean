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
    have hsourceKernel : compileRoot? source.diagram
        hsource.diagram_well_formed source.exposedWires source.hiddenWires =
          some (CheckedOpen.compilation ⟨source, hsource⟩) :=
      CheckedOpen.compilation_computation ⟨source, hsource⟩
    have htargetKernel : compileRoot? target.diagram
        htarget.diagram_well_formed target.exposedWires target.hiddenWires =
          some (CheckedOpen.compilation ⟨target, htarget⟩) :=
      CheckedOpen.compilation_computation ⟨target, htarget⟩
    simpa [OpenDiagram.elaborate, CheckedOpen.elaborate] using
      compileRoot?_certifiedEquivariant equiv.diagram
        hsource.diagram_well_formed htarget.diagram_well_formed
        hwires htargetExact
        hsourceKernel htargetKernel
  apply OpenDiagramIso.ofArityEq equiv.boundary_length_eq
    equiv.exposedWiresEquiv
  · intro position
    simpa only [OpenDiagram.elaborate_boundary] using
      equiv.boundaryClass_commute position
  · exact hbody

end OpenOccurrenceEquiv



end VisualProof.Concrete
