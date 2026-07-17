import VisualProof.Data.Finite
import VisualProof.Diagram.Concrete.Core

namespace VisualProof.Diagram

open VisualProof.Data.Finite

/--
A proof-free receipt describing which identifiers of a finite carrier survive
compaction. Dense enumeration and lookup are delegated to `FilteredFiber`.
-/
structure SurvivorDomain (size : Nat) where
  survives : Fin size → Bool

namespace SurvivorDomain

/-- Surviving original identifiers, in the stable `filterFin` order. -/
def enumeration (domain : SurvivorDomain size) : List (Fin size) :=
  filterFin domain.survives

/-- The size of the compact survivor carrier. -/
def count (domain : SurvivorDomain size) : Nat :=
  domain.enumeration.length

/-- Dense identifiers for the compact survivor carrier. -/
abbrev Carrier (domain : SurvivorDomain size) := Fin domain.count

/-- The original identifier represented by a dense survivor identifier. -/
def origin (domain : SurvivorDomain size) (index : domain.Carrier) : Fin size :=
  FilteredFiber.origin domain.survives index

/-- The dense identifier of an original identifier, when it survives. -/
def index? (domain : SurvivorDomain size)
    (original : Fin size) : Option domain.Carrier :=
  FilteredFiber.index? domain.survives original

/-- A total compact identifier when survival is already proved. -/
def index (domain : SurvivorDomain size) (original : Fin size)
    (hsurvives : domain.survives original = true) : domain.Carrier :=
  (domain.index? original).get
    ((FilteredFiber.index?_isSome_iff domain.survives original).2 hsurvives)

@[simp] theorem count_eq_filterFin_length (domain : SurvivorDomain size) :
    domain.count = (filterFin domain.survives).length := rfl

@[simp] theorem mem_enumeration (domain : SurvivorDomain size)
    (original : Fin size) :
    original ∈ domain.enumeration ↔ domain.survives original = true := by
  exact mem_filterFin original

theorem enumeration_nodup (domain : SurvivorDomain size) :
    domain.enumeration.Nodup :=
  filterFin_nodup domain.survives

@[simp] theorem origin_eq_enumeration_get (domain : SurvivorDomain size)
    (index : domain.Carrier) :
    domain.origin index = domain.enumeration.get index := rfl

@[simp] theorem origin_survives (domain : SurvivorDomain size)
    (index : domain.Carrier) :
    domain.survives (domain.origin index) = true :=
  FilteredFiber.origin_survives domain.survives index

theorem index?_eq_some_iff (domain : SurvivorDomain size)
    (original : Fin size) (index : domain.Carrier) :
    domain.index? original = some index ↔ domain.origin index = original :=
  FilteredFiber.index?_eq_some_iff domain.survives original index

@[simp] theorem index?_eq_none_iff (domain : SurvivorDomain size)
    (original : Fin size) :
    domain.index? original = none ↔ domain.survives original = false :=
  FilteredFiber.index?_eq_none_iff domain.survives original

@[simp] theorem index?_origin (domain : SurvivorDomain size)
    (index : domain.Carrier) :
    domain.index? (domain.origin index) = some index :=
  FilteredFiber.index?_origin domain.survives index

@[simp] theorem index?_isSome_iff (domain : SurvivorDomain size)
    (original : Fin size) :
    (domain.index? original).isSome = true ↔
      domain.survives original = true :=
  FilteredFiber.index?_isSome_iff domain.survives original

@[simp] theorem index?_index (domain : SurvivorDomain size)
    (original : Fin size) (hsurvives : domain.survives original = true) :
    domain.index? original = some (domain.index original hsurvives) := by
  let hsome : (domain.index? original).isSome = true :=
    (domain.index?_isSome_iff original).2 hsurvives
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  calc
    domain.index? original = some found := hfound
    _ = some ((domain.index? original).get hsome) :=
      congrArg some (Option.get_of_eq_some hsome hfound).symm
    _ = some (domain.index original hsurvives) := by rfl

@[simp] theorem origin_index (domain : SurvivorDomain size)
    (original : Fin size) (hsurvives : domain.survives original = true) :
    domain.origin (domain.index original hsurvives) = original :=
  (domain.index?_eq_some_iff original _).1
    (domain.index?_index original hsurvives)

@[simp] theorem index_origin (domain : SurvivorDomain size)
    (index : domain.Carrier) :
    domain.index (domain.origin index) (domain.origin_survives index) = index := by
  apply Option.some.inj
  exact (domain.index?_index (domain.origin index)
    (domain.origin_survives index)).symm.trans (domain.index?_origin index)

theorem coverage (domain : SurvivorDomain size) (original : Fin size) :
    domain.survives original = true ↔
      ∃ index : domain.Carrier, domain.origin index = original :=
  FilteredFiber.survives_iff_exists_origin domain.survives original

theorem origin_injective (domain : SurvivorDomain size) :
    Function.Injective domain.origin :=
  FilteredFiber.origin_injective domain.survives

/-- Canonical equivalence between dense survivor carriers selected by
extensionally equal predicates. -/
def equivOfSurvivesIff (source target : SurvivorDomain size)
    (same : ∀ original,
      target.survives original = true ↔ source.survives original = true) :
    FiniteEquiv source.Carrier target.Carrier :=
  FiniteEquiv.restrictLists (FiniteEquiv.refl (Fin size))
    source.enumeration target.enumeration
    source.enumeration_nodup target.enumeration_nodup (by
      intro original
      simp only [FiniteEquiv.refl_apply, mem_enumeration]
      exact same original)

/-- The survivor equivalence preserves the represented original identifier. -/
@[simp] theorem origin_equivOfSurvivesIff
    (source target : SurvivorDomain size)
    (same : ∀ original,
      target.survives original = true ↔ source.survives original = true)
    (index : source.Carrier) :
    target.origin (equivOfSurvivesIff source target same index) =
      source.origin index := by
  exact FiniteEquiv.restrictLists_spec (FiniteEquiv.refl (Fin size))
    source.enumeration target.enumeration
    source.enumeration_nodup target.enumeration_nodup (by
      intro original
      simp only [FiniteEquiv.refl_apply, mem_enumeration]
      exact same original) index

/-- Restrict a dependent family to surviving origins. -/
def pullback {family : Fin size → Sort u} (domain : SurvivorDomain size)
    (values : (original : Fin size) → family original) :
    (index : domain.Carrier) → family (domain.origin index) :=
  FilteredFiber.pullback domain.survives values

@[simp] theorem pullback_apply {family : Fin size → Sort u}
    (domain : SurvivorDomain size)
    (values : (original : Fin size) → family original)
    (index : domain.Carrier) :
    domain.pullback values index = values (domain.origin index) := rfl

/-- Embed a survivor carrier as the first block of a larger finite carrier. -/
def inLeftBlock (domain : SurvivorDomain size) (suffix : Nat)
    (index : domain.Carrier) : Fin (domain.count + suffix) :=
  Fin.castAdd suffix index

/-- Embed a survivor carrier as the second block of a larger finite carrier. -/
def inRightBlock (domain : SurvivorDomain size) (initial : Nat)
    (index : domain.Carrier) : Fin (initial + domain.count) :=
  Fin.natAdd initial index

@[simp] theorem inLeftBlock_val (domain : SurvivorDomain size) (suffix : Nat)
    (index : domain.Carrier) :
    (domain.inLeftBlock suffix index).val = index.val := rfl

@[simp] theorem inRightBlock_val (domain : SurvivorDomain size) (initial : Nat)
    (index : domain.Carrier) :
    (domain.inRightBlock initial index).val = initial + index.val := rfl

theorem inLeftBlock_injective (domain : SurvivorDomain size) (suffix : Nat) :
    Function.Injective (domain.inLeftBlock suffix) := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg (fun value => value.val) heq
  simpa only [inLeftBlock_val] using hvals

theorem inRightBlock_injective (domain : SurvivorDomain size) (initial : Nat) :
    Function.Injective (domain.inRightBlock initial) := by
  intro left right heq
  apply Fin.ext
  have hvals := congrArg (fun value => value.val) heq
  simp only [inRightBlock_val] at hvals
  omega

/-! Structure-preserving partial reindexing through survivor receipts. -/

/-- Reindex a concrete region when its parent survives. -/
def reindexRegion? (domain : SurvivorDomain size) :
    CRegion size → Option (CRegion domain.count)
  | .sheet => some .sheet
  | .cut parent => (domain.index? parent).map CRegion.cut
  | .bubble parent arity =>
      (domain.index? parent).map fun mapped => CRegion.bubble mapped arity

/-- Reindex a concrete node when its owner and, for atoms, binder survive. -/
def reindexNode? (domain : SurvivorDomain size) :
    CNode size → Option (CNode domain.count)
  | .term region freePorts term =>
      (domain.index? region).map fun mapped =>
        CNode.term mapped freePorts term
  | .atom region binder => do
      let mappedRegion ← domain.index? region
      let mappedBinder ← domain.index? binder
      pure (.atom mappedRegion mappedBinder)
  | .named region definition arity =>
      (domain.index? region).map fun mapped =>
        CNode.named mapped definition arity

/-- Reindex an endpoint when its node survives. -/
def reindexEndpoint? (domain : SurvivorDomain size)
    (endpoint : CEndpoint size) : Option (CEndpoint domain.count) :=
  (domain.index? endpoint.node).map fun node =>
    { node, port := endpoint.port }

@[simp] theorem reindexRegion?_sheet (domain : SurvivorDomain size) :
    domain.reindexRegion? .sheet = some .sheet := rfl

theorem reindexRegion?_cut_eq_some_iff (domain : SurvivorDomain size)
    (parent : Fin size) (region : CRegion domain.count) :
    domain.reindexRegion? (.cut parent) = some region ↔
      ∃ mapped, domain.index? parent = some mapped ∧ region = .cut mapped := by
  change (domain.index? parent).map CRegion.cut = some region ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨mapped, hindex, hregion⟩
    exact ⟨mapped, hindex, hregion.symm⟩
  · rintro ⟨mapped, hindex, hregion⟩
    exact ⟨mapped, hindex, hregion.symm⟩

theorem reindexRegion?_bubble_eq_some_iff (domain : SurvivorDomain size)
    (parent : Fin size) (arity : Nat) (region : CRegion domain.count) :
    domain.reindexRegion? (.bubble parent arity) = some region ↔
      ∃ mapped, domain.index? parent = some mapped ∧
        region = .bubble mapped arity := by
  change (domain.index? parent).map
      (fun mapped => CRegion.bubble mapped arity) = some region ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨mapped, hindex, hregion⟩
    exact ⟨mapped, hindex, hregion.symm⟩
  · rintro ⟨mapped, hindex, hregion⟩
    exact ⟨mapped, hindex, hregion.symm⟩

theorem reindexEndpoint?_eq_some_iff (domain : SurvivorDomain size)
    (endpoint : CEndpoint size) (mapped : CEndpoint domain.count) :
    domain.reindexEndpoint? endpoint = some mapped ↔
      ∃ node, domain.index? endpoint.node = some node ∧
        mapped = { node, port := endpoint.port } := by
  change (domain.index? endpoint.node).map
      (fun node => ({ node, port := endpoint.port } :
        CEndpoint domain.count)) = some mapped ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨node, hindex, hendpoint⟩
    exact ⟨node, hindex, hendpoint.symm⟩
  · rintro ⟨node, hindex, hendpoint⟩
    exact ⟨node, hindex, hendpoint.symm⟩

end SurvivorDomain

end VisualProof.Diagram
