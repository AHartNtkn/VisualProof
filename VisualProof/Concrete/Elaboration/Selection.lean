import VisualProof.Concrete.Elaboration.Compile.SiteKernel
import VisualProof.Concrete.Operation.Structural.Flat

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram

/-- The checked open fragment canonically extracted from one source
selection.  Its layout and every identity are derived from the source. -/
def extractedSelectionOpen (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) : CheckedOpen :=
  let layout : FragmentLayout source.checked.val.diagram selection := {}
  ⟨source.checked.val.diagram.extractOpenRaw selection layout,
    Diagram.extractOpenRaw_wellFormed source.diagram selection layout⟩

/-- The extracted source fragment as an arity-indexed compiler input. -/
def extractedSelectionState (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    State selection.touchingWires.length :=
  let layout : FragmentLayout source.checked.val.diagram selection := {}
  { checked := extractedSelectionOpen source selection
    boundary_length :=
      source.checked.val.diagram.extractBoundaryRaw_length selection layout }

/-- The source-derived binder spine of the canonical extracted fragment. -/
def extractedSelectionSpine (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    BinderSpine (extractedSelectionState source selection).checked.val.diagram :=
  let layout : FragmentLayout source.checked.val.diagram selection := {}
  source.checked.val.diagram.extractedBinderSpine selection layout

/-- Source-only compiler evidence for a checked selection.  One certificate
focuses the selection's anchor in the host; the other focuses the terminal
material body in its canonical extraction.  No generated target data occurs
in either derivation. -/
structure CompiledSelection (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) where
  anchor : CompiledSite source selection.val.anchor
  material : LocalCompiledSite (extractedSelectionState source selection)
    (extractedSelectionSpine source selection).bodyContainer

/-- Compile all source-derived evidence for one selection as one proof-only
operation. -/
noncomputable def CompiledSelection.ofSource (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram) :
    CompiledSelection source selection where
  anchor := CompiledSite.ofSource source selection.val.anchor
  material := (CompiledSite.ofSource
    (extractedSelectionState source selection)
    (extractedSelectionSpine source selection).bodyContainer).local

end VisualProof.Concrete
