import VisualProof.Diagram.Scope

namespace VisualProof.Diagram

open VisualProof.Theory

/-- A recursively scoped open diagram with an ordered typed boundary. -/
structure OpenDiagram (boundary : List Sig) where
  external : List Sig
  boundaryWire : Vars external boundary
  boundarySurjective : ∀ wire : Fin external.length,
    ∃ position : Fin boundary.length,
      (boundaryWire.get position).index = wire
  body : Region external
  canonical : body.Canonical

namespace OpenDiagram

/-- Replace the body while preserving the typed interface. The replacement
must independently establish canonical DCA placement. -/
def withBody (diagram : OpenDiagram boundary)
    (body : Region diagram.external) (canonical : body.Canonical) :
    OpenDiagram boundary where
  external := diagram.external
  boundaryWire := diagram.boundaryWire
  boundarySurjective := diagram.boundarySurjective
  body := body
  canonical := canonical

/-- A wire identity is recursive: either an external boundary wire or a wire
introduced at one exact region in the body. It stores identity, not scope. -/
inductive Wire (diagram : OpenDiagram boundary) : Sig → Type
  | external (wire : Var diagram.external signature) : Wire diagram signature
  | internal (wire : Region.InternalWire diagram.body signature) :
      Wire diagram signature

def incidencePaths (diagram : OpenDiagram boundary) :
    Wire diagram signature → List RegionPath
  | .external wire =>
      List.replicate
          (diagram.boundaryWire.countIndex wire.index.val) [] ++
        diagram.body.incidencePaths wire.index.val
  | .internal wire => wire.occurrencePaths

/-- Wire scope is calculated from all actual boundary and body incidences. -/
def scopePath (diagram : OpenDiagram boundary)
    (wire : Wire diagram signature) : RegionPath :=
  RegionPath.deepestCommonAncestor (diagram.incidencePaths wire)

theorem scopePath_external
    (diagram : OpenDiagram boundary)
    (wire : Var diagram.external signature) :
    diagram.scopePath (.external wire) = [] := by
  obtain ⟨position, maps⟩ := diagram.boundarySurjective wire.index
  have positive := diagram.boundaryWire.countIndex_get_positive position
  have countPositive :
      0 < diagram.boundaryWire.countIndex wire.index.val := by
    rw [maps] at positive
    exact positive
  cases countEq : diagram.boundaryWire.countIndex wire.index.val with
  | zero => simp only [countEq, Nat.lt_irrefl] at countPositive
  | succ count =>
      simp only [scopePath, incidencePaths, countEq, List.replicate_succ,
        List.cons_append, RegionPath.deepestCommonAncestor_cons_nil]

theorem scopePath_internal
    (diagram : OpenDiagram boundary)
    (wire : Region.InternalWire diagram.body signature) :
    diagram.scopePath (.internal wire) = wire.ownerPath := by
  exact (wire.scope_spec diagram.canonical).2

end OpenDiagram

end VisualProof.Diagram
