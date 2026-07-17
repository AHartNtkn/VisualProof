import VisualProof.Diagram.Concrete.Elaboration.Compile.Region

namespace VisualProof.Diagram

open ConcreteElaboration
open VisualProof.Data.Finite
open VisualProof.Theory

private theorem checkedOpen_rootWires_exact
    (checked : CheckedOpenDiagram signature) :
    WireContext.Exact checked.val.rootWires checked.val.diagram.root := by
  constructor
  · exact checked.val.rootWires_nodup
  · intro wire
    rw [OpenConcreteDiagram.mem_rootWires_iff checked.val checked.property]
    constructor
    · intro hscope
      rw [hscope]
      exact ConcreteDiagram.Encloses.refl _ _
    · exact ConcreteElaboration.encloses_sheet_eq
        checked.property.diagram_well_formed.root_is_sheet

/-- Canonically reorder any exact root context of an open diagram into that
diagram's exposed-then-hidden root context. -/
noncomputable def exactContextToOpenRootWireEquiv
    (checked : CheckedOpenDiagram signature)
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
        have hscope := (OpenConcreteDiagram.mem_rootWires_iff checked.val
          checked.property wire).1 hmember
        rw [hscope]
        exact ConcreteDiagram.Encloses.refl _ _
      · intro hencloses
        apply (OpenConcreteDiagram.mem_rootWires_iff checked.val
          checked.property wire).2
        exact ConcreteElaboration.encloses_sheet_eq
          checked.property.diagram_well_formed.root_is_sheet hencloses)

theorem exactContextToOpenRootWireEquiv_spec
    (checked : CheckedOpenDiagram signature)
    (context : WireContext checked.val.diagram)
    (exact : context.Exact checked.val.diagram.root)
    (index : Fin context.length) :
    checked.val.rootWires.get
        (exactContextToOpenRootWireEquiv checked context exact index) =
      context.get index := by
  exact FiniteEquiv.restrictLists_spec _ _ _ _ _ _ index

theorem compiledOpenRootItemsIsoFromExactContext
    (checked : CheckedOpenDiagram signature)
    (context : WireContext checked.val.diagram)
    (exact : context.Exact checked.val.diagram.root)
    {closedItems : ItemSeq signature context.length []}
    {openItems : ItemSeq signature checked.val.rootWires.length []}
    (hclosed : compileOccurrencesWith? signature checked.val.diagram
      (compileRegion? signature checked.val.diagram
        checked.val.diagram.regionCount)
      context BinderContext.empty
      (localOccurrences checked.val.diagram checked.val.diagram.root) =
        some closedItems)
    (hopen : compileOccurrencesWith? signature checked.val.diagram
      (compileRegion? signature checked.val.diagram
        checked.val.diagram.regionCount)
      checked.val.rootWires BinderContext.empty
      (localOccurrences checked.val.diagram checked.val.diagram.root) =
        some openItems) :
    ItemSeqIso signature
      (exactContextToOpenRootWireEquiv checked context exact) []
      closedItems openItems := by
  apply compileRootItems?_equivariant
    (ConcreteIso.refl checked.val.diagram)
    checked.property.diagram_well_formed context checked.val.rootWires
    (exactContextToOpenRootWireEquiv checked context exact)
  · exact exactContextToOpenRootWireEquiv_spec checked context exact
  · exact checkedOpen_rootWires_exact checked
  · exact hclosed
  · exact hopen

namespace CheckedDiagram

def elaborate (checked : CheckedDiagram signature) : Region signature 0 [] :=
  (compileRoot? signature checked.val []
    (exactScopeWires checked.val checked.val.root)).get
      (Option.isSome_iff_exists.mpr
        (compileRoot?_complete checked.property [] _
          (closedRootWires_exact checked.property)))

theorem elaborate_computation (checked : CheckedDiagram signature) :
    exists body,
      compileRoot? signature checked.val []
          (exactScopeWires checked.val checked.val.root) = some body /\
        checked.elaborate = body := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete checked.property [] _
    (closedRootWires_exact checked.property)
  refine ⟨body, hbody, ?_⟩
  simp [elaborate, hbody]

end CheckedDiagram

namespace CheckedOpenDiagram

/-- Total elaboration of a checked open concrete diagram. -/
def elaborate (checked : CheckedOpenDiagram signature) :
    OpenDiagram signature checked.val.boundary.length where
  externalClasses := checked.val.exposedWires.length
  boundary := checked.val.boundaryClass
  boundary_surjective := checked.val.boundaryClass_surjective
  body := (compileRoot? signature checked.val.diagram
    checked.val.exposedWires checked.val.hiddenWires).get
      (Option.isSome_iff_exists.mpr
        (compileRoot?_complete checked.property.diagram_well_formed _ _ (by
          simpa [OpenConcreteDiagram.rootWires] using
            openRootWires_exact checked.property)))

@[simp] theorem elaborate_externalClasses
    (checked : CheckedOpenDiagram signature) :
    checked.elaborate.externalClasses = checked.val.exposedWires.length :=
  rfl

@[simp] theorem elaborate_boundary
    (checked : CheckedOpenDiagram signature) :
    checked.elaborate.boundary = checked.val.boundaryClass :=
  rfl

theorem elaborate_body_computation
    (checked : CheckedOpenDiagram signature) :
    exists body,
      compileRoot? signature checked.val.diagram checked.val.exposedWires
          checked.val.hiddenWires = some body ∧
        checked.elaborate.body = body := by
  obtain ⟨body, hbody⟩ := compileRoot?_complete
    checked.property.diagram_well_formed _ _ (by
      simpa [OpenConcreteDiagram.rootWires] using
        openRootWires_exact checked.property)
  refine ⟨body, hbody, ?_⟩
  simp [elaborate, hbody]

end CheckedOpenDiagram

private theorem checked_asOpen_compileRoot_eq
    (checked : CheckedDiagram signature) :
    compileRoot? signature checked.asOpen.val.diagram
        checked.asOpen.val.exposedWires checked.asOpen.val.hiddenWires =
      compileRoot? signature checked.val []
        (exactScopeWires checked.val checked.val.root) := by
  change compileRoot? signature checked.val [] checked.val.asOpen.hiddenWires =
    compileRoot? signature checked.val []
      (exactScopeWires checked.val checked.val.root)
  rw [ConcreteDiagram.asOpen_hiddenWires]

namespace CheckedDiagram

@[simp] theorem asOpen_elaborate_externalClasses
    (checked : CheckedDiagram signature) :
    checked.asOpen.elaborate.externalClasses = 0 := rfl

/-- Empty-boundary open elaboration is exactly the existing closed elaboration. -/
@[simp] theorem asOpen_elaborate_body
    (checked : CheckedDiagram signature) :
    checked.asOpen.elaborate.body = checked.elaborate := by
  obtain ⟨openBody, hopenKernel, hopenElaborate⟩ :=
    CheckedOpenDiagram.elaborate_body_computation checked.asOpen
  obtain ⟨closedBody, hclosedKernel, hclosedElaborate⟩ :=
    CheckedDiagram.elaborate_computation checked
  have hbodies : openBody = closedBody := by
    have hopenKernel' := hopenKernel
    rw [checked_asOpen_compileRoot_eq checked] at hopenKernel'
    exact Option.some.inj (hopenKernel'.symm.trans hclosedKernel)
  exact hopenElaborate.trans (hbodies.trans hclosedElaborate.symm)

end CheckedDiagram

namespace OpenConcreteDiagram

def elaborate (d : OpenConcreteDiagram) (hwf : d.WellFormed signature) :
    OpenDiagram signature d.boundary.length :=
  CheckedOpenDiagram.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : OpenConcreteDiagram)
    (first second : d.WellFormed signature) :
    d.elaborate first = d.elaborate second := by
  rfl

@[simp] theorem elaborate_externalClasses (d : OpenConcreteDiagram)
    (hwf : d.WellFormed signature) :
    (d.elaborate hwf).externalClasses = d.exposedWires.length :=
  rfl

@[simp] theorem elaborate_boundary (d : OpenConcreteDiagram)
    (hwf : d.WellFormed signature) :
    (d.elaborate hwf).boundary = d.boundaryClass :=
  rfl

end OpenConcreteDiagram

namespace ConcreteDiagram

def elaborate (d : ConcreteDiagram) (hwf : d.WellFormed signature) :
    Region signature 0 [] :=
  CheckedDiagram.elaborate ⟨d, hwf⟩

theorem elaborate_proof_irrelevant (d : ConcreteDiagram)
    (first second : d.WellFormed signature) :
    d.elaborate first = d.elaborate second := by
  rfl

@[simp] theorem asOpen_elaborate_externalClasses (d : ConcreteDiagram)
    (hwf : d.WellFormed signature) :
    (d.asOpen.elaborate (d.asOpen_wellFormed hwf)).externalClasses = 0 :=
  CheckedDiagram.asOpen_elaborate_externalClasses ⟨d, hwf⟩

@[simp] theorem asOpen_elaborate_body (d : ConcreteDiagram)
    (hwf : d.WellFormed signature) :
    (d.asOpen.elaborate (d.asOpen_wellFormed hwf)).body = d.elaborate hwf :=
  CheckedDiagram.asOpen_elaborate_body ⟨d, hwf⟩

theorem elaborate_computation (d : ConcreteDiagram)
    (hwf : d.WellFormed signature) :
    exists body,
      compileRoot? signature d [] (exactScopeWires d d.root) = some body /\
        d.elaborate hwf = body :=
  CheckedDiagram.elaborate_computation ⟨d, hwf⟩

end ConcreteDiagram

def certifiedRenameOccurrence {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target) :
    LocalOccurrence source.regionCount source.nodeCount →
      LocalOccurrence target.regionCount target.nodeCount
  | .node node => .node (equiv.nodes node)
  | .child region => .child (equiv.regions region)

def certifiedOccurrenceEquiv {source target : ConcreteDiagram}
    (equiv : ConcreteOccurrenceEquiv source target) :
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

end VisualProof.Diagram
