import VisualProof.Concrete.Elaboration.Compile.Region

namespace VisualProof.Concrete

open VisualProof.Diagram

open Elaboration
open VisualProof.Data.Finite
open VisualProof.Theory

namespace Checked

def compilation (checked : Checked ) :
    CompiledRegion checked.val
      (.root [] (exactScopeWires checked.val checked.val.root)) :=
  (compileRoot?  checked.val []
    (exactScopeWires checked.val checked.val.root)).get
      (Option.isSome_iff_exists.mpr
        (compileRoot?_complete checked.property [] _
          (closedRootWires_exact checked.property)))

def elaborate (checked : Checked ) : Region  0 [] := checked.compilation.erase

theorem elaborate_computation (checked : Checked ) :
    exists body,
      compileRoot?  checked.val []
          (exactScopeWires checked.val checked.val.root) = some body /\
        checked.compilation = body ∧
        checked.elaborate = body.erase := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete checked.property [] _
    (closedRootWires_exact checked.property)
  refine ⟨body, hbody, ?_, ?_⟩
  · simp [compilation, hbody]
  · simp [elaborate, compilation, hbody]

end Checked

namespace CheckedOpen

def compilation (checked : CheckedOpen ) :
    CompiledRegion checked.val.diagram
      (.root checked.val.exposedWires checked.val.hiddenWires) :=
  (compileRoot? checked.val.diagram checked.val.exposedWires
    checked.val.hiddenWires).get
      (Option.isSome_iff_exists.mpr
        (compileRoot?_complete checked.property.diagram_well_formed _ _ (by
          simpa [OpenDiagram.rootWires] using
            openRootWires_exact checked.property)))

/-- Total elaboration of a checked open concrete diagram. -/
def elaborate (checked : CheckedOpen ) :
    VisualProof.Diagram.OpenDiagram checked.val.boundary.length where
  externalClasses := checked.val.exposedWires.length
  boundary := checked.val.boundaryClass
  boundary_surjective := checked.val.boundaryClass_surjective
  body := checked.compilation.erase

@[simp] theorem elaborate_externalClasses
    (checked : CheckedOpen ) :
    checked.elaborate.externalClasses = checked.val.exposedWires.length :=
  rfl

@[simp] theorem elaborate_boundary
    (checked : CheckedOpen ) :
    checked.elaborate.boundary = checked.val.boundaryClass :=
  rfl

theorem elaborate_body_computation
    (checked : CheckedOpen ) :
    exists body,
      compileRoot?  checked.val.diagram checked.val.exposedWires
          checked.val.hiddenWires = some body ∧
        checked.compilation = body ∧
        checked.elaborate.body = body.erase := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete
    checked.property.diagram_well_formed _ _ (by
      simpa [OpenDiagram.rootWires] using
        openRootWires_exact checked.property)
  refine ⟨body, hbody, ?_, ?_⟩
  · simp [compilation, hbody]
  · simp [elaborate, compilation, hbody]

/-- The canonical annotated open compilation is returned by the sole root
compiler call that defines it. -/
theorem compilation_computation (checked : CheckedOpen) :
    compileRoot? checked.val.diagram checked.val.exposedWires
      checked.val.hiddenWires = some checked.compilation := by
  obtain ⟨body, compiled, compilationEq, _⟩ :=
    checked.elaborate_body_computation
  rw [compilationEq]
  exact compiled

end CheckedOpen

private theorem compiledRootErase_eq_of_locals_eq
    (d : Diagram) (ambient first second : WireContext d)
    (localsEq : first = second)
    {firstBody : CompiledRegion d (.root ambient first)}
    {secondBody : CompiledRegion d (.root ambient second)}
    (firstCompiled : compileRoot? d ambient first = some firstBody)
    (secondCompiled : compileRoot? d ambient second = some secondBody) :
    firstBody.erase = secondBody.erase := by
  subst second
  rw [firstCompiled] at secondCompiled
  cases Option.some.inj secondCompiled
  rfl

namespace Checked

@[simp] theorem asOpen_elaborate_externalClasses
    (checked : Checked ) :
    checked.asOpen.elaborate.externalClasses = 0 := rfl

/-- Empty-boundary open elaboration is exactly the existing closed elaboration. -/
@[simp] theorem asOpen_elaborate_body
    (checked : Checked ) :
    checked.asOpen.elaborate.body = checked.elaborate := by
  obtain ⟨openBody, openCompiled, _, openErased⟩ :=
    CheckedOpen.elaborate_body_computation checked.asOpen
  obtain ⟨closedBody, closedCompiled, _, closedErased⟩ :=
    Checked.elaborate_computation checked
  have erasedEq : openBody.erase = closedBody.erase :=
    compiledRootErase_eq_of_locals_eq checked.val []
      checked.val.asOpen.hiddenWires
      (exactScopeWires checked.val checked.val.root)
      (Diagram.asOpen_hiddenWires checked.val) openCompiled closedCompiled
  exact openErased.trans (erasedEq.trans closedErased.symm)

end Checked

namespace OpenDiagram

def elaborate (d : OpenDiagram) (hwf : d.WellFormed ) :
    VisualProof.Diagram.OpenDiagram d.boundary.length :=
  CheckedOpen.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : OpenDiagram)
    (first second : d.WellFormed ) :
    d.elaborate first = d.elaborate second := by
  rfl

@[simp] theorem elaborate_externalClasses (d : OpenDiagram)
    (hwf : d.WellFormed ) :
    (d.elaborate hwf).externalClasses = d.exposedWires.length :=
  rfl

@[simp] theorem elaborate_boundary (d : OpenDiagram)
    (hwf : d.WellFormed ) :
    (d.elaborate hwf).boundary = d.boundaryClass :=
  rfl

end OpenDiagram

namespace Diagram

def elaborate (d : Diagram) (hwf : d.WellFormed ) :
    Region  0 [] :=
  Checked.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : Diagram)
    (first second : d.WellFormed ) :
    d.elaborate first = d.elaborate second := by
  rfl

@[simp] theorem asOpen_elaborate_externalClasses (d : Diagram)
    (hwf : d.WellFormed ) :
    (d.asOpen.elaborate (d.asOpen_wellFormed hwf)).externalClasses = 0 :=
  Checked.asOpen_elaborate_externalClasses ⟨d, hwf⟩

@[simp] theorem asOpen_elaborate_body (d : Diagram)
    (hwf : d.WellFormed ) :
    (d.asOpen.elaborate (d.asOpen_wellFormed hwf)).body = d.elaborate hwf :=
  Checked.asOpen_elaborate_body ⟨d, hwf⟩

theorem elaborate_computation (d : Diagram)
    (hwf : d.WellFormed ) :
    exists body,
      compileRoot?  d [] (exactScopeWires d d.root) = some body /\
        d.elaborate hwf = body.erase := by
  obtain ⟨body, compiled, _, erased⟩ :=
    Checked.elaborate_computation ⟨d, hwf⟩
  exact ⟨body, compiled, erased⟩

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
