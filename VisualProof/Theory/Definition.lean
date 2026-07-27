import VisualProof.Diagram.Open

namespace VisualProof

/-- One relation definition whose body may reference exactly a prior prefix. -/
structure Definition (prior : List (List Sig)) (args : List Sig) where
  body : OpenDiagram prior args

/--
Chronological definition data indexed by its de Bruijn signature context.
Construction is snoc-order; the index is newest-first so weakening is `there`.
-/
inductive DefinitionData : List (List Sig) → Type
  | nil : DefinitionData []
  | snoc {prior : List (List Sig)}
      (priorData : DefinitionData prior) (args : List Sig)
      (definition : Definition prior args) :
      DefinitionData (args :: prior)

/-- A hidden-index ordered definition store. -/
structure Definitions where
  signatures : List (List Sig)
  data : DefinitionData signatures

namespace DefVar

/-- An earlier definition remains available after one chronological snoc. -/
def weaken (reference : DefVar prior args) :
    DefVar (newest :: prior) args :=
  .there reference

end DefVar

namespace Definitions

/-- The empty ordered definition store. -/
def nil : Definitions :=
  ⟨[], .nil⟩

/--
Append one definition chronologically. Its body is indexed by only the prior
prefix, so forward references and cycles are unrepresentable.
-/
def snoc (priorDefs : Definitions) (args : List Sig)
    (body : OpenDiagram priorDefs.signatures args) : Definitions :=
  ⟨args :: priorDefs.signatures, .snoc priorDefs.data args ⟨body⟩⟩

@[simp] theorem signatures_nil :
    nil.signatures = [] :=
  rfl

@[simp] theorem signatures_snoc
    (priorDefs : Definitions) (args : List Sig)
    (body : OpenDiagram priorDefs.signatures args) :
    (snoc priorDefs args body).signatures = args :: priorDefs.signatures :=
  rfl

/-- The chronologically newest definition has de Bruijn index zero. -/
def newest (priorDefs : Definitions) (args : List Sig)
    (body : OpenDiagram priorDefs.signatures args) :
    DefVar (snoc priorDefs args body).signatures args :=
  .here

/-- Weaken an earlier definition reference through one chronological snoc. -/
def weaken (priorDefs : Definitions) (newArgs : List Sig)
    (body : OpenDiagram priorDefs.signatures newArgs)
    (reference : DefVar priorDefs.signatures args) :
    DefVar (snoc priorDefs newArgs body).signatures args :=
  .there reference

end Definitions

end VisualProof
