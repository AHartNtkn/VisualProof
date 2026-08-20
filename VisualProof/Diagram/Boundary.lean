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

theorem externalTwoEnded_iff_fin
    (boundaryWire : Vars external boundary) (body : Region external) :
    ExternalTwoEnded boundaryWire body ↔
      ∀ index : Fin external.length,
        2 ≤ boundaryWire.countIndex index.val +
          (body.incidencePaths index.val).length := by
  constructor
  · intro validity index
    simpa using validity (Var.ofIndex index)
  · intro validity signature wire
    exact validity wire.index

instance (boundaryWire : Vars external boundary) (body : Region external) :
    Decidable (ExternalTwoEnded boundaryWire body) := by
  letI : Decidable (∀ index : Fin external.length,
      2 ≤ boundaryWire.countIndex index.val +
        (body.incidencePaths index.val).length) :=
    VisualProof.Data.Finite.decidableForallFin _ fun _ => inferInstance
  exact decidable_of_iff _
    (externalTwoEnded_iff_fin boundaryWire body).symm

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

/-- Raw executable output before the finite diagram-validity checks run. -/
structure Candidate (boundary : List Sig) where
  external : List Sig
  boundaryWire : Vars external boundary
  body : Region external

def Candidate.Valid (candidate : Candidate boundary) : Prop :=
  (∀ wire : Fin candidate.external.length,
      ∃ position : Fin boundary.length,
        (candidate.boundaryWire.get position).index = wire) ∧
    candidate.body.Canonical ∧
    ExternalTwoEnded candidate.boundaryWire candidate.body

instance (candidate : Candidate boundary) : Decidable candidate.Valid := by
  unfold Candidate.Valid
  infer_instance

def Candidate.toOpen (candidate : Candidate boundary)
    (valid : candidate.Valid) : OpenDiagram boundary where
  external := candidate.external
  boundaryWire := candidate.boundaryWire
  boundarySurjective := valid.1
  body := candidate.body
  canonical := valid.2.1
  externalTwoEnded := valid.2.2

def Candidate.validate (candidate : Candidate boundary) :
    Option (OpenDiagram boundary) :=
  if valid : candidate.Valid then some (candidate.toOpen valid) else none

def Candidate.validateWhen (candidate : Candidate boundary)
    (condition : Prop) [Decidable condition] : Option (OpenDiagram boundary) :=
  if condition then candidate.validate else none

@[simp] theorem Candidate.validateWhen_of_valid
    (candidate : Candidate boundary) (condition : Prop) [Decidable condition]
    (conditionEvidence : condition) (valid : candidate.Valid) :
    candidate.validateWhen condition = some (candidate.toOpen valid) := by
  simp [Candidate.validateWhen, conditionEvidence,
    Candidate.validate, valid]

theorem Candidate.validateWhen_eq_some_iff
    (candidate : Candidate boundary) (condition : Prop)
    [Decidable condition] (output : OpenDiagram boundary) :
    candidate.validateWhen condition = some output ↔
      ∃ (_conditionEvidence : condition) (valid : candidate.Valid),
        output = candidate.toOpen valid := by
  constructor
  · intro computed
    simp only [Candidate.validateWhen] at computed
    split at computed
    next conditionEvidence =>
      simp only [Candidate.validate] at computed
      split at computed
      next valid =>
        simp only [Option.some.injEq] at computed
        exact ⟨conditionEvidence, valid, computed.symm⟩
      next => simp at computed
    next => simp at computed
  · rintro ⟨conditionEvidence, valid, rfl⟩
    exact Candidate.validateWhen_of_valid candidate condition
      conditionEvidence valid

@[simp] theorem Candidate.validate_of_valid
    (candidate : Candidate boundary) (valid : candidate.Valid) :
    candidate.validate = some (candidate.toOpen valid) := by
  simp [Candidate.validate, valid]

theorem Candidate.valid_of_validate_eq_some
    (candidate : Candidate boundary) (target : OpenDiagram boundary)
    (computed : candidate.validate = some target) : candidate.Valid := by
  simp only [Candidate.validate] at computed
  split at computed
  · assumption
  · simp at computed

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
