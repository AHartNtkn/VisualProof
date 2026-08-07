import VisualProof.Concrete.Elaboration.Compile.Region

namespace VisualProof.Concrete

open VisualProof.Diagram

open Elaboration
open VisualProof.Data.Finite
open VisualProof.Theory

private theorem checkedOpen_rootWires_exact
    (checked : CheckedOpen ) :
    WireContext.Exact checked.val.rootWires checked.val.diagram.root := by
  constructor
  · exact checked.val.rootWires_nodup
  · intro wire
    rw [OpenDiagram.mem_rootWires_iff checked.val checked.property]
    constructor
    · intro hscope
      rw [hscope]
      exact Diagram.Encloses.refl _ _
    · exact Elaboration.encloses_sheet_eq
        checked.property.diagram_well_formed.root_is_sheet

/-- Canonically reorder any exact root context of an open diagram into that
diagram's exposed-then-hidden root context. -/
noncomputable def exactContextToOpenRootWireEquiv
    (checked : CheckedOpen )
    (context : WireContext checked.val.diagram)
    (exact : context.Exact checked.val.diagram.root) :
    FiniteEquiv (Fin context.length) (Fin checked.val.rootWires.length) :=
  FiniteEquiv.restrictLists
    (FiniteEquiv.refl (Fin checked.val.diagram.wireCount))
    context checked.val.rootWires exact.nodup checked.val.rootWires_nodup
    (fun wire => by
      simp only [FiniteEquiv.refl_apply]
      rw [exact.mem_iff]
      constructor
      · intro hmember
        have hscope := (OpenDiagram.mem_rootWires_iff checked.val
          checked.property wire).1 hmember
        rw [hscope]
        exact Diagram.Encloses.refl _ _
      · intro hencloses
        apply (OpenDiagram.mem_rootWires_iff checked.val
          checked.property wire).2
        exact Elaboration.encloses_sheet_eq
          checked.property.diagram_well_formed.root_is_sheet hencloses)

theorem exactContextToOpenRootWireEquiv_spec
    (checked : CheckedOpen )
    (context : WireContext checked.val.diagram)
    (exact : context.Exact checked.val.diagram.root)
    (index : Fin context.length) :
    checked.val.rootWires.get
        (exactContextToOpenRootWireEquiv checked context exact index) =
      context.get index := by
  exact FiniteEquiv.restrictLists_spec _ _ _ _ _ _ index

theorem compiledOpenRootItemsIsoFromExactContext
    (checked : CheckedOpen )
    (context : WireContext checked.val.diagram)
    (exact : context.Exact checked.val.diagram.root)
    {closedItems : ItemSeq  context.length []}
    {openItems : ItemSeq  checked.val.rootWires.length []}
    (hclosed : compileOccurrencesWith?  checked.val.diagram
      (compileRegion?  checked.val.diagram
        checked.val.diagram.regionCount)
      context BinderContext.empty
      (localOccurrences checked.val.diagram checked.val.diagram.root) =
        some closedItems)
    (hopen : compileOccurrencesWith?  checked.val.diagram
      (compileRegion?  checked.val.diagram
        checked.val.diagram.regionCount)
      checked.val.rootWires BinderContext.empty
      (localOccurrences checked.val.diagram checked.val.diagram.root) =
        some openItems) :
    ItemSeqIso
      (exactContextToOpenRootWireEquiv checked context exact) []
      closedItems openItems := by
  apply compileRootItems?_equivariant
    (Iso.refl checked.val.diagram)
    checked.property.diagram_well_formed context checked.val.rootWires
    (exactContextToOpenRootWireEquiv checked context exact)
  · exact exactContextToOpenRootWireEquiv_spec checked context exact
  · exact checkedOpen_rootWires_exact checked
  · exact hclosed
  · exact hopen

namespace Checked

def elaborate (checked : Checked ) : Region  0 [] :=
  (compileRoot?  checked.val []
    (exactScopeWires checked.val checked.val.root)).get
      (Option.isSome_iff_exists.mpr
        (compileRoot?_complete checked.property [] _
          (closedRootWires_exact checked.property)))

theorem elaborate_computation (checked : Checked ) :
    exists body,
      compileRoot?  checked.val []
          (exactScopeWires checked.val checked.val.root) = some body /\
        checked.elaborate = body := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete checked.property [] _
    (closedRootWires_exact checked.property)
  refine ⟨body, hbody, ?_⟩
  simp [elaborate, hbody]

end Checked

namespace CheckedOpen

/-- Total elaboration of a checked open concrete diagram. -/
def elaborate (checked : CheckedOpen ) :
    VisualProof.Diagram.OpenDiagram checked.val.boundary.length where
  externalClasses := checked.val.exposedWires.length
  boundary := checked.val.boundaryClass
  boundary_surjective := checked.val.boundaryClass_surjective
  body := (compileRoot?  checked.val.diagram
    checked.val.exposedWires checked.val.hiddenWires).get
      (Option.isSome_iff_exists.mpr
        (compileRoot?_complete checked.property.diagram_well_formed _ _ (by
          simpa [OpenDiagram.rootWires] using
            openRootWires_exact checked.property)))

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
        checked.elaborate.body = body := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete
    checked.property.diagram_well_formed _ _ (by
      simpa [OpenDiagram.rootWires] using
        openRootWires_exact checked.property)
  refine ⟨body, hbody, ?_⟩
  simp [elaborate, hbody]

end CheckedOpen

private theorem checked_asOpen_compileRoot_eq
    (checked : Checked ) :
    compileRoot?  checked.asOpen.val.diagram
        checked.asOpen.val.exposedWires checked.asOpen.val.hiddenWires =
      compileRoot?  checked.val []
        (exactScopeWires checked.val checked.val.root) := by
  change compileRoot?  checked.val [] checked.val.asOpen.hiddenWires =
    compileRoot?  checked.val []
      (exactScopeWires checked.val checked.val.root)
  rw [Diagram.asOpen_hiddenWires]

namespace Checked

@[simp] theorem asOpen_elaborate_externalClasses
    (checked : Checked ) :
    checked.asOpen.elaborate.externalClasses = 0 := rfl

/-- Empty-boundary open elaboration is exactly the existing closed elaboration. -/
@[simp] theorem asOpen_elaborate_body
    (checked : Checked ) :
    checked.asOpen.elaborate.body = checked.elaborate := by
  obtain ⟨openBody, hopenKernel, hopenElaborate⟩ :=
    CheckedOpen.elaborate_body_computation checked.asOpen
  obtain ⟨closedBody, hclosedKernel, hclosedElaborate⟩ :=
    Checked.elaborate_computation checked
  have hbodies : openBody = closedBody := by
    have hopenKernel' := hopenKernel
    rw [checked_asOpen_compileRoot_eq checked] at hopenKernel'
    exact Option.some.inj (hopenKernel'.symm.trans hclosedKernel)
  exact hopenElaborate.trans (hbodies.trans hclosedElaborate.symm)

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
        d.elaborate hwf = body :=
  Checked.elaborate_computation ⟨d, hwf⟩

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
