import VisualProof.Diagram.Concrete.OpenCompilation
import VisualProof.Theory.Semantics

namespace VisualProof

namespace ConcreteDefinitionWeakening

/-- Shift every stored definition reference through one chronological snoc. -/
def node : CNode regionCount definitions.length →
    CNode regionCount (newArgs :: definitions).length
  | .atom region args => .atom region args
  | .ref region definition args => .ref region definition.succ args
  | .identity region sig arity => .identity region sig arity

/-- The same concrete carrier in a definition context extended at its head. -/
def diagram (source : ConcreteDiagram definitions.length) :
    ConcreteDiagram (newArgs :: definitions).length where
  regionCount := source.regionCount
  nodeCount := source.nodeCount
  wireCount := source.wireCount
  root := source.root
  regions := source.regions
  nodes := fun sourceNode => node (source.nodes sourceNode)
  wires := source.wires

/-- Preserve the ordered boundary while weakening every reference in the body. -/
def openDiagram (source : OpenConcreteDiagram definitions.length) :
    OpenConcreteDiagram (newArgs :: definitions).length where
  diagram := diagram source.diagram
  boundary := source.boundary

end ConcreteDefinitionWeakening

/-- Stable failures while transporting a checked definition body through a
later chronological definition. -/
inductive DefinitionBodyError
  | weakeningRejected (error : WFError)
  | compilationRejected
  deriving Repr, DecidableEq

/-- A rechecked concrete body after one chronological definition snoc. -/
structure WeakenedDefinitionBody
    (newArgs : List Sig) (source : CheckedOpenDiagram definitions) where
  body : CheckedOpenDiagram (newArgs :: definitions)
  generated : body.val =
    ConcreteDefinitionWeakening.openDiagram (newArgs := newArgs) source.val

/-- Recheck the weakened body with the ordinary concrete well-formedness
authority. Only definition indices change; boundary order and aliases do not. -/
def weakenDefinitionBody
    (newArgs : List Sig) (source : CheckedOpenDiagram definitions) :
    Except DefinitionBodyError (WeakenedDefinitionBody newArgs source) := by
  let raw :=
    ConcreteDefinitionWeakening.openDiagram (newArgs := newArgs) source.val
  match accepted : ConcreteDiagram.checkWellFormed
      (newArgs :: definitions) raw.diagram with
  | .error error => exact .error (.weakeningRejected error)
  | .ok checked =>
      have generatedDiagram : checked.val = raw.diagram :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      let body : CheckedOpenDiagram (newArgs :: definitions) :=
        ⟨raw,
          { diagram := generatedDiagram ▸ checked.property
            boundary_root_scoped := by
              simpa [raw, ConcreteDefinitionWeakening.openDiagram,
                ConcreteDefinitionWeakening.diagram] using
                source.property.boundary_root_scoped }⟩
      exact .ok ⟨body, rfl⟩

@[simp] theorem weakened_checkedBoundarySigs
    {newArgs : List Sig} {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source) :
    checkedBoundarySigs weakened.body = checkedBoundarySigs source := by
  simp only [checkedBoundarySigs]
  rw [weakened.generated]
  rfl

namespace WeakenedDefinitionBody

/-- Compile the weakened body through the sole concrete-to-intrinsic authority. -/
def compile?
    {newArgs : List Sig} {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source) :
    Except DefinitionBodyError (OpenCompilation weakened.body) :=
  match compileOpen weakened.body with
  | none => .error .compilationRejected
  | some compiled => .ok compiled

end WeakenedDefinitionBody

/-- Chronological concrete definition data indexed by the intrinsic store it
generates. The intrinsic body is never supplied independently: it is exactly
the output of the checked concrete compiler. -/
inductive CheckedDefinitionData : (definitions : Definitions) → Type
  | nil : CheckedDefinitionData Definitions.nil
  | snoc {prior : Definitions}
      (priorData : CheckedDefinitionData prior)
      {body : CheckedOpenDiagram prior.signatures}
      (compiled : OpenCompilation body) :
      CheckedDefinitionData
        (Definitions.snoc prior (checkedBoundarySigs body)
          compiled.openDiagram)

/-- The sole paired concrete/intrinsic chronological definition authority. -/
structure CheckedDefinitions where
  intrinsic : Definitions
  data : CheckedDefinitionData intrinsic

namespace CheckedDefinitions

/-- Empty concrete and intrinsic definition stores. -/
def nil : CheckedDefinitions :=
  ⟨Definitions.nil, .nil⟩

/-- Append one checked concrete body, deriving the intrinsic entry exclusively
from its successful open compilation. -/
def snoc (prior : CheckedDefinitions)
    (body : CheckedOpenDiagram prior.intrinsic.signatures) :
    Except DefinitionBodyError CheckedDefinitions :=
  match compileOpen body with
  | none => .error .compilationRejected
  | some compiled =>
      .ok
        ⟨Definitions.snoc prior.intrinsic (checkedBoundarySigs body)
            compiled.openDiagram,
          .snoc prior.data compiled⟩

end CheckedDefinitions

/-- A concrete stored body resolved in the complete current definition
context, with its exact ordered signature retained in the type. -/
structure ResolvedDefinitionBody
    (definitions : Definitions) (args : List Sig) where
  body : CheckedOpenDiagram definitions.signatures
  boundarySignatures : checkedBoundarySigs body = args

namespace CheckedDefinitionData

/-- Resolve a typed definition reference and weaken its concrete body through
every later chronological entry. This is index traversal, never graph search. -/
def resolveBody :
    {definitions : Definitions} →
      CheckedDefinitionData definitions →
      DefVar definitions.signatures args →
      Except DefinitionBodyError (ResolvedDefinitionBody definitions args)
  | _, .nil, reference => nomatch reference
  | _, @CheckedDefinitionData.snoc prior _ body compiled, .here => do
      let weakened ← weakenDefinitionBody (checkedBoundarySigs body) body
      pure
        { body := weakened.body
          boundarySignatures := weakened_checkedBoundarySigs weakened }
  | _, @CheckedDefinitionData.snoc prior priorData body compiled,
      .there earlier => do
      let resolved ← resolveBody priorData earlier
      let weakened ←
        weakenDefinitionBody (checkedBoundarySigs body) resolved.body
      pure
        { body := weakened.body
          boundarySignatures :=
            (weakened_checkedBoundarySigs weakened).trans
              resolved.boundarySignatures }

end CheckedDefinitionData

namespace CheckedDefinitions

/-- Resolve one typed stored body in the current full definition context. -/
def resolveBody (definitions : CheckedDefinitions)
    (reference : DefVar definitions.intrinsic.signatures args) :
    Except DefinitionBodyError
      (ResolvedDefinitionBody definitions.intrinsic args) :=
  definitions.data.resolveBody reference

end CheckedDefinitions

end VisualProof
