import VisualProof.Concrete.Elaboration.Compile.Region
import VisualProof.Concrete.OpenIsomorphism
import VisualProof.Concrete.Occurrence

namespace VisualProof.Concrete

open VisualProof.Diagram
open Elaboration
open VisualProof.Data.Finite

namespace Checked

/-- The one symbolic compilation of a checked concrete diagram. -/
noncomputable def compilation (checked : Checked) : CompiledRegion checked.val :=
  compileRegion checked.val checked.property checked.val.root

@[simp] theorem compilation_origin (checked : Checked) :
    checked.compilation.origin = checked.val.root :=
  compileRegion_origin checked.val checked.property checked.val.root

theorem compilation_valid (checked : Checked) : checked.compilation.Valid :=
  compileRegion_valid checked.val checked.property checked.val.root

/-- Closed elaboration introduces lexical positions only at this erasure. -/
noncomputable def elaborate (checked : Checked) : Region 0 [] :=
  checked.compilation.erase checked.compilation_valid checked.property []
    (exactScopeWires checked.val checked.val.root) [] BinderContext.empty
    (by simpa only [compilation_origin] using
      closedRootWires_exact checked.property)
    (by simpa only [compilation_origin] using
      BinderContext.empty_covers_root checked.property)

end Checked

namespace CheckedOpen

/-- The one symbolic compilation of a checked open concrete diagram. -/
noncomputable def compilation (checked : CheckedOpen) :
    CompiledRegion checked.val.diagram :=
  compileRegion checked.val.diagram checked.property.diagram_well_formed
    checked.val.diagram.root

@[simp] theorem compilation_origin (checked : CheckedOpen) :
    checked.compilation.origin = checked.val.diagram.root :=
  compileRegion_origin checked.val.diagram
    checked.property.diagram_well_formed checked.val.diagram.root

theorem compilation_valid (checked : CheckedOpen) :
    checked.compilation.Valid :=
  compileRegion_valid checked.val.diagram
    checked.property.diagram_well_formed checked.val.diagram.root

/-- Total elaboration of a checked open concrete diagram. -/
noncomputable def elaborate (checked : CheckedOpen) :
    VisualProof.Diagram.OpenDiagram checked.val.boundary.length where
  externalClasses := checked.val.exposedWires.length
  boundary := checked.val.boundaryClass
  boundary_surjective := checked.val.boundaryClass_surjective
  body := checked.compilation.erase checked.compilation_valid
    checked.property.diagram_well_formed checked.val.exposedWires
    checked.val.hiddenWires [] BinderContext.empty (by
      simpa only [compilation_origin, OpenDiagram.rootWires] using
        openRootWires_exact checked.property)
    (by
      have covers := BinderContext.empty_covers_root
        checked.property.diagram_well_formed
      simpa only [compilation_origin] using covers)

@[simp] theorem elaborate_externalClasses (checked : CheckedOpen) :
    checked.elaborate.externalClasses = checked.val.exposedWires.length := rfl

@[simp] theorem elaborate_boundary (checked : CheckedOpen) :
    checked.elaborate.boundary = checked.val.boundaryClass := rfl

end CheckedOpen

namespace Checked

@[simp] theorem asOpen_elaborate_externalClasses (checked : Checked) :
    checked.asOpen.elaborate.externalClasses = 0 := rfl

/-- Empty-boundary open elaboration agrees with closed elaboration. -/
@[simp] theorem asOpen_elaborate_body (checked : Checked) :
    checked.asOpen.elaborate.body = checked.elaborate := by
  unfold CheckedOpen.elaborate Checked.elaborate CheckedOpen.compilation
    Checked.compilation
  simp only [Checked.asOpen_val, Diagram.asOpen_diagram,
    Diagram.asOpen_exposedWires, Diagram.asOpen_hiddenWires]

end Checked

namespace OpenDiagram

noncomputable def elaborate (d : OpenDiagram) (hwf : d.WellFormed) :
    VisualProof.Diagram.OpenDiagram d.boundary.length :=
  CheckedOpen.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : OpenDiagram)
    (first second : d.WellFormed) :
    d.elaborate first = d.elaborate second := by
  rfl

@[simp] theorem elaborate_externalClasses (d : OpenDiagram)
    (hwf : d.WellFormed) :
    (d.elaborate hwf).externalClasses = d.exposedWires.length := rfl

@[simp] theorem elaborate_boundary (d : OpenDiagram)
    (hwf : d.WellFormed) :
    (d.elaborate hwf).boundary = d.boundaryClass := rfl

end OpenDiagram

namespace Diagram

noncomputable def elaborate (d : Diagram) (hwf : d.WellFormed) : Region 0 [] :=
  Checked.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : Diagram)
    (first second : d.WellFormed) :
    d.elaborate first = d.elaborate second := by
  rfl

@[simp] theorem asOpen_elaborate_externalClasses (d : Diagram)
    (hwf : d.WellFormed) :
    (d.asOpen.elaborate (d.asOpen_wellFormed hwf)).externalClasses = 0 :=
  Checked.asOpen_elaborate_externalClasses ⟨d, hwf⟩

@[simp] theorem asOpen_elaborate_body (d : Diagram)
    (hwf : d.WellFormed) :
    (d.asOpen.elaborate (d.asOpen_wellFormed hwf)).body = d.elaborate hwf :=
  Checked.asOpen_elaborate_body ⟨d, hwf⟩

end Diagram

def certifiedRenameOccurrence {source target : Diagram}
    (equiv : OccurrenceEquiv source target) :
    LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount
  | .node node => .node (equiv.nodes node)
  | .child region => .child (equiv.regions region)

def certifiedOccurrenceEquiv {source target : Diagram}
    (equiv : OccurrenceEquiv source target) :
    FiniteEquiv
      (LocalOccurrence source.regionCount source.nodeCount)
      (LocalOccurrence target.regionCount target.nodeCount) where
  toFun := certifiedRenameOccurrence equiv
  invFun
    | .node node => .node (equiv.nodes.invFun node)
    | .child region => .child (equiv.regions.invFun region)
  left_inv := by
    intro occurrence
    cases occurrence with
    | node node => exact congrArg LocalOccurrence.node (equiv.nodes.left_inv node)
    | child region =>
        exact congrArg LocalOccurrence.child (equiv.regions.left_inv region)
  right_inv := by
    intro occurrence
    cases occurrence with
    | node node => exact congrArg LocalOccurrence.node (equiv.nodes.right_inv node)
    | child region =>
        exact congrArg LocalOccurrence.child (equiv.regions.right_inv region)

end VisualProof.Concrete
