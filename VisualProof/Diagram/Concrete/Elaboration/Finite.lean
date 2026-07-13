import VisualProof.Diagram.Concrete.WellFormed

namespace VisualProof.Diagram.ConcreteElaboration

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

end VisualProof.Diagram.ConcreteElaboration
