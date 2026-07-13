namespace VisualProof.Data.Finite

/-! Deterministic enumeration and reindexing for finite carriers. -/

def allFin : (n : Nat) -> List (Fin n)
  | 0 => []
  | n + 1 => 0 :: (allFin n).map Fin.succ

theorem allFin_eq_finRange (n : Nat) : allFin n = List.finRange n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allFin, List.finRange_succ, ih]

@[simp] theorem mem_allFin {n : Nat} (i : Fin n) : i ∈ allFin n := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [allFin]
      · simp [allFin, ih]

theorem allFin_nodup (n : Nat) : (allFin n).Nodup := by
  induction n with
  | zero => simp [allFin]
  | succ n ih =>
      simp only [allFin, List.nodup_cons, List.mem_map]
      constructor
      · rintro ⟨i, _, h⟩
        exact Fin.succ_ne_zero i h
      · exact ih.map Fin.succ (by
          intro a b hab hs
          apply hab
          apply Fin.ext
          exact Nat.succ.inj (congrArg Fin.val hs))

def filterFin (p : Fin n -> Bool) : List (Fin n) :=
  (allFin n).filter p

@[simp] theorem mem_filterFin {p : Fin n -> Bool} (i : Fin n) :
    i ∈ filterFin p ↔ p i = true := by
  simp [filterFin]

theorem filterFin_nodup (p : Fin n -> Bool) : (filterFin p).Nodup := by
  exact (allFin_nodup n).filter p

/-! A dense carrier for the elements accepted by a Boolean predicate. -/

abbrev FilteredFiber (p : Fin n -> Bool) := Fin (filterFin p).length

namespace FilteredFiber

/-- The original element represented by a dense filtered index. -/
def origin (p : Fin n -> Bool) (index : FilteredFiber p) : Fin n :=
  (filterFin p).get (show Fin (filterFin p).length from index)

end FilteredFiber

def indexOf? [DecidableEq α] : (xs : List α) -> α -> Option (Fin xs.length)
  | [], _ => none
  | y :: ys, x =>
      if x = y then
        some 0
      else
        (indexOf? ys x).map Fin.succ

theorem indexOf?_sound [DecidableEq α] {xs : List α} {x : α}
    {i : Fin xs.length} (h : indexOf? xs x = some i) : xs[i] = x := by
  induction xs with
  | nil => simp [indexOf?] at h
  | cons y ys ih =>
      simp only [indexOf?] at h
      split at h
      · rename_i hxy
        cases h
        simpa using hxy.symm
      · rename_i hxy
        cases hi : indexOf? ys x with
        | none => simp [hi] at h
        | some j =>
            simp [hi] at h
            cases h
            simpa using ih hi

theorem indexOf?_complete [DecidableEq α] {xs : List α} {x : α}
    (hmem : x ∈ xs) : exists i, indexOf? xs x = some i := by
  induction xs with
  | nil => simp at hmem
  | cons y ys ih =>
      simp only [indexOf?]
      by_cases hxy : x = y
      · simp [hxy]
      · have : x ∈ ys := by simpa [hxy] using hmem
        obtain ⟨i, hi⟩ := ih this
        exact ⟨Fin.succ i, by simp [hxy, hi]⟩

theorem indexOf?_isSome_iff [DecidableEq α] {xs : List α} {x : α} :
    (indexOf? xs x).isSome = true ↔ x ∈ xs := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
    rw [← indexOf?_sound hi]
    exact List.getElem_mem ..
  · intro h
    obtain ⟨i, hi⟩ := indexOf?_complete h
    exact Option.isSome_iff_exists.mpr ⟨i, hi⟩

theorem indexOf?_unique_of_nodup [DecidableEq α] {xs : List α}
    (hnodup : xs.Nodup) {x : α} {i : Fin xs.length}
    (hi : indexOf? xs x = some i) {j : Fin xs.length}
    (hj : xs[j] = x) : j = i := by
  apply Fin.ext
  have hvalues : xs[j.val]? = xs[i.val]? := by
    rw [List.getElem?_eq_getElem j.isLt, List.getElem?_eq_getElem i.isLt]
    exact congrArg some (hj.trans (indexOf?_sound hi).symm)
  exact (List.getElem?_inj j.isLt hnodup).mp hvalues

namespace FilteredFiber

/-- The dense filtered index of an original element, when it survives. -/
def index? (p : Fin n -> Bool) (original : Fin n) : Option (FilteredFiber p) :=
  indexOf? (filterFin p) original

@[simp] theorem origin_survives (p : Fin n -> Bool) (index : FilteredFiber p) :
    p (origin p index) = true := by
  rw [← mem_filterFin]
  exact List.get_mem ..

@[simp] theorem index?_isSome_iff (p : Fin n -> Bool) (original : Fin n) :
    (index? p original).isSome = true ↔ p original = true := by
  change (indexOf? (filterFin p) original).isSome = true ↔ _
  rw [indexOf?_isSome_iff, mem_filterFin]

theorem index?_eq_some_iff (p : Fin n -> Bool) (original : Fin n)
    (index : FilteredFiber p) :
    index? p original = some index ↔ origin p index = original := by
  constructor
  · intro h
    exact indexOf?_sound h
  · intro horigin
    obtain ⟨found, hfound⟩ := indexOf?_complete
      (show original ∈ filterFin p by
        rw [← horigin]
        exact List.get_mem ..)
    have : found = index := (indexOf?_unique_of_nodup
      (filterFin_nodup p) hfound horigin).symm
    simpa [index?, this] using hfound

@[simp] theorem index?_eq_none_iff (p : Fin n -> Bool) (original : Fin n) :
    index? p original = none ↔ p original = false := by
  constructor
  · intro hnone
    cases hsurvives : p original with
    | false => rfl
    | true =>
        have hsome := (index?_isSome_iff p original).2 hsurvives
        simp [hnone] at hsome
  · intro hdeleted
    cases hindex : index? p original with
    | none => rfl
    | some index =>
        have hsurvives := origin_survives p index
        have horigin := (index?_eq_some_iff p original index).1 hindex
        rw [horigin, hdeleted] at hsurvives
        contradiction

@[simp] theorem index?_origin (p : Fin n -> Bool) (index : FilteredFiber p) :
    index? p (origin p index) = some index := by
  exact (index?_eq_some_iff p _ _).2 rfl

theorem survives_iff_exists_origin (p : Fin n -> Bool) (original : Fin n) :
    p original = true ↔ ∃ index : FilteredFiber p, origin p index = original := by
  constructor
  · intro hsurvives
    have hsome : (index? p original).isSome = true :=
      (index?_isSome_iff p original).2 hsurvives
    obtain ⟨index, hindex⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨index, (index?_eq_some_iff p original index).1 hindex⟩
  · rintro ⟨index, rfl⟩
    exact origin_survives p index

theorem origin_injective (p : Fin n -> Bool) : Function.Injective (origin p) := by
  intro left right heq
  have hleft := index?_origin p left
  have hright := index?_origin p right
  rw [heq] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

theorem exists_index_of_survives (p : Fin n -> Bool) (original : Fin n)
    (hsurvives : p original = true) :
    ∃ index : FilteredFiber p,
      index? p original = some index ∧ origin p index = original := by
  obtain ⟨index, horigin⟩ := (survives_iff_exists_origin p original).1 hsurvives
  exact ⟨index, (index?_eq_some_iff p original index).2 horigin, horigin⟩

/-- Restrict a dependent family to the dense filtered carrier. -/
def pullback {α : Fin n -> Sort u} (p : Fin n -> Bool)
    (values : (original : Fin n) -> α original) :
    (index : FilteredFiber p) -> α (origin p index) :=
  fun index => values (origin p index)

@[simp] theorem pullback_apply {α : Fin n -> Sort u} (p : Fin n -> Bool)
    (values : (original : Fin n) -> α original) (index : FilteredFiber p) :
    pullback p values index = values (origin p index) := rfl

end FilteredFiber

namespace FilteredFiber.Examples

def keepEvenFour (index : Fin 4) : Bool := index.val % 2 == 0

theorem keepEvenFour_count : (filterFin keepEvenFour).length = 2 := by
  decide

def keepEvenFourFirst : FilteredFiber keepEvenFour := ⟨0, by decide⟩

def keepEvenFourSecond : FilteredFiber keepEvenFour := ⟨1, by decide⟩

theorem keepEvenFour_origins :
    origin keepEvenFour keepEvenFourFirst = 0 ∧
    origin keepEvenFour keepEvenFourSecond = 2 := by
  decide

theorem keepEvenFour_indices :
    index? keepEvenFour 0 = some keepEvenFourFirst ∧
    index? keepEvenFour 1 = none ∧
    index? keepEvenFour 2 = some keepEvenFourSecond ∧
    index? keepEvenFour 3 = none := by
  decide

end FilteredFiber.Examples

def sequenceFin : {n : Nat} -> (Fin n -> Option α) -> Option (Fin n -> α)
  | 0, _ => some Fin.elim0
  | _n + 1, values => do
      let head <- values 0
      let tail <- sequenceFin (fun i => values i.succ)
      pure (Fin.cases head tail)

theorem sequenceFin_complete {values : Fin n -> Option α}
    (f : Fin n -> α) (h : forall i, values i = some (f i)) :
    exists result, sequenceFin values = some result := by
  induction n with
  | zero => exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
      obtain ⟨tail, htail⟩ := ih (fun i => f i.succ) (fun i => h i.succ)
      exact ⟨Fin.cases (f 0) tail, by simp [sequenceFin, h 0, htail]⟩

theorem sequenceFin_sound {values : Fin n -> Option α}
    {result : Fin n -> α} (h : sequenceFin values = some result) :
    forall i, values i = some (result i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      simp only [sequenceFin] at h
      cases hhead : values 0 with
      | none => simp [hhead] at h
      | some head =>
          cases htail : sequenceFin (fun i => values i.succ) with
          | none => simp [hhead, htail] at h
          | some tail =>
              simp [hhead, htail] at h
              cases h
              refine Fin.cases ?_ (fun j => ?_) i
              · exact hhead
              · exact ih htail j

theorem sequenceFin_isSome_iff {values : Fin n -> Option α} :
    (sequenceFin values).isSome = true ↔
      forall i, exists value, values i = some value := by
  constructor
  · intro hsome i
    obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨result i, sequenceFin_sound hresult i⟩
  · intro h
    induction n with
    | zero => rfl
    | succ n ih =>
        obtain ⟨head, hhead⟩ := h 0
        have htail : forall i : Fin n,
            exists value, values i.succ = some value :=
          fun i => h i.succ
        have hsome := ih htail
        obtain ⟨tail, htailResult⟩ := Option.isSome_iff_exists.mp hsome
        exact Option.isSome_iff_exists.mpr
          ⟨Fin.cases head tail, by simp [sequenceFin, hhead, htailResult]⟩

/-! Exhaustive finite function enumeration. -/

def enumerateFinFunctions : (n m : Nat) -> List (Fin n -> Fin m)
  | 0, _ => [Fin.elim0]
  | n + 1, m =>
      (allFin m).flatMap fun head =>
        (enumerateFinFunctions n m).map fun tail => Fin.cases head tail

theorem enumerateFinFunctions_complete (n m : Nat) (f : Fin n -> Fin m) :
    f ∈ enumerateFinFunctions n m := by
  induction n generalizing m with
  | zero =>
      simp [enumerateFinFunctions]
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [enumerateFinFunctions, List.mem_flatMap, List.mem_map]
      refine ⟨f 0, mem_allFin _, ?_⟩
      refine ⟨fun i : Fin n => f i.succ, ih m _, ?_⟩
      funext i
      exact Fin.cases rfl (fun j => rfl) i

@[simp] theorem mem_enumerateFinFunctions_iff (f : Fin n -> Fin m) :
    f ∈ enumerateFinFunctions n m ↔ True := by
  exact iff_true_intro (enumerateFinFunctions_complete n m f)

private theorem nodup_flatMap_of
    {xs : List α} {f : α -> List β}
    (hxs : xs.Nodup)
    (hparts : ∀ x ∈ xs, (f x).Nodup)
    (hdisjoint : ∀ x ∈ xs, ∀ y ∈ xs, x ≠ y ->
      ∀ a ∈ f x, ∀ b ∈ f y, a ≠ b) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.nodup_append]
      have ⟨hx, hxs⟩ := List.nodup_cons.mp hxs
      refine ⟨hparts x (by simp), ?_, ?_⟩
      · exact ih hxs
          (fun y hy => hparts y (by simp [hy]))
          (fun y hy z hz hyz =>
            hdisjoint y (by simp [hy]) z (by simp [hz]) hyz)
      · intro a ha b hb
        obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hb
        apply hdisjoint x (by simp) y (by simp [hy])
        · intro hxy
          subst y
          exact hx hy
        · exact ha
        · exact hb

theorem enumerateFinFunctions_nodup (n m : Nat) :
    (enumerateFinFunctions n m).Nodup := by
  induction n generalizing m with
  | zero => simp [enumerateFinFunctions]
  | succ n ih =>
      rw [enumerateFinFunctions]
      apply nodup_flatMap_of (allFin_nodup m)
      · intro head _
        exact List.Pairwise.map (R := fun a b => a ≠ b) (S := fun a b => a ≠ b)
          (fun tail : Fin n -> Fin m =>
            (Fin.cases head tail : Fin (n + 1) -> Fin m)) (by
          intro tail₁ tail₂ hne htail
          apply hne
          funext i
          exact congrFun htail i.succ) (ih m)
      · intro head₁ _ head₂ _ hne g hg₁ g' hg₂ heq
        rcases List.mem_map.1 hg₁ with ⟨tail₁, _, hg₁eq⟩
        rcases List.mem_map.1 hg₂ with ⟨tail₂, _, hg₂eq⟩
        have hfun :
            (Fin.cases head₁ tail₁ : Fin (n + 1) -> Fin m) =
              Fin.cases head₂ tail₂ :=
          hg₁eq.trans (heq.trans hg₂eq.symm)
        exact hne (congrFun hfun 0)

end VisualProof.Data.Finite
