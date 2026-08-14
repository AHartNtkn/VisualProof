import VisualProof.Diagram.Scope

namespace VisualProof.Diagram

open VisualProof.Theory

namespace OpenDiagram

/-- Every external wire has at least two combined boundary and body
incidences. -/
def ExternalTwoEnded (boundaryWire : Vars external boundary)
    (body : Region external) : Prop :=
  ∀ {signature} (wire : Var external signature),
    2 ≤ boundaryWire.countIndex wire.index.val +
      (body.incidencePaths wire.index.val).length

end OpenDiagram

/-- A recursively scoped open diagram with an ordered typed boundary. -/
structure OpenDiagram (boundary : List Sig) where
  external : List Sig
  boundaryWire : Vars external boundary
  boundarySurjective : ∀ wire : Fin external.length,
    ∃ position : Fin boundary.length,
      (boundaryWire.get position).index = wire
  body : Region external
  canonical : body.Canonical
  externalTwoEnded : OpenDiagram.ExternalTwoEnded boundaryWire body

namespace OpenDiagram

/-- Replace the body while preserving the typed interface. The replacement
must independently establish canonical DCA placement. -/
def withBody (diagram : OpenDiagram boundary)
    (body : Region diagram.external) (canonical : body.Canonical)
    (externalTwoEnded : ExternalTwoEnded diagram.boundaryWire body) :
    OpenDiagram boundary where
  external := diagram.external
  boundaryWire := diagram.boundaryWire
  boundarySurjective := diagram.boundarySurjective
  body := body
  canonical := canonical
  externalTwoEnded := externalTwoEnded

theorem boundaryWire_countIndex_pos (diagram : OpenDiagram boundary)
    (wire : Var diagram.external signature) :
    0 < diagram.boundaryWire.countIndex wire.index.val := by
  obtain ⟨position, maps⟩ := diagram.boundarySurjective wire.index
  have positive := diagram.boundaryWire.countIndex_get_positive position
  rw [maps] at positive
  exact positive

/-- Replacing the body by one with the same nonempty external-wire incidence
sets preserves the external two-end invariant. -/
theorem externalTwoEnded_of_nonempty_iff
    (diagram : OpenDiagram boundary)
    (body : Region diagram.external)
    (sameNonempty : ∀ {signature} (wire : Var diagram.external signature),
      diagram.body.incidencePaths wire.index.val ≠ [] ↔
        body.incidencePaths wire.index.val ≠ []) :
    ExternalTwoEnded diagram.boundaryWire body := by
  intro signature wire
  have boundaryPositive := diagram.boundaryWire_countIndex_pos wire
  by_cases sourceEmpty : diagram.body.incidencePaths wire.index.val = []
  · have targetEmpty : body.incidencePaths wire.index.val = [] := by
      by_cases targetEmpty : body.incidencePaths wire.index.val = []
      · exact targetEmpty
      · exact False.elim ((sameNonempty wire).mpr targetEmpty sourceEmpty)
    simpa [ExternalTwoEnded, sourceEmpty, targetEmpty] using
      diagram.externalTwoEnded wire
  · have targetNonempty := (sameNonempty wire).mp sourceEmpty
    have targetPositive : 0 < (body.incidencePaths wire.index.val).length :=
      List.length_pos_iff.mpr targetNonempty
    omega

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
