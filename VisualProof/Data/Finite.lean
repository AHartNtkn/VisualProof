namespace VisualProof.Data.Finite

/-- A constructive equivalence used for finite diagram carriers. -/
structure FiniteEquiv (alpha beta : Type) where
  toFun : alpha -> beta
  invFun : beta -> alpha
  left_inv : forall x, invFun (toFun x) = x
  right_inv : forall y, toFun (invFun y) = y

instance : CoeFun (FiniteEquiv alpha beta) (fun _ => alpha -> beta) where
  coe equivalence := equivalence.toFun

namespace FiniteEquiv

def refl (alpha : Type) : FiniteEquiv alpha alpha where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem refl_apply (x : alpha) : refl alpha x = x := rfl

def symm (equivalence : FiniteEquiv alpha beta) : FiniteEquiv beta alpha where
  toFun := equivalence.invFun
  invFun := equivalence.toFun
  left_inv := equivalence.right_inv
  right_inv := equivalence.left_inv

@[simp] theorem symm_toFun (equivalence : FiniteEquiv alpha beta) :
    equivalence.symm.toFun = equivalence.invFun := rfl

def trans (first : FiniteEquiv alpha beta) (second : FiniteEquiv beta gamma) :
    FiniteEquiv alpha gamma where
  toFun := second.toFun ∘ first.toFun
  invFun := first.invFun ∘ second.invFun
  left_inv := by
    intro x
    simp only [Function.comp_apply, second.left_inv, first.left_inv]
  right_inv := by
    intro z
    simp only [Function.comp_apply, first.right_inv, second.right_inv]

@[simp] theorem trans_apply (first : FiniteEquiv alpha beta)
    (second : FiniteEquiv beta gamma) (x : alpha) :
    first.trans second x = second (first x) := rfl

@[simp] theorem symm_apply_apply (equivalence : FiniteEquiv alpha beta)
    (x : alpha) : equivalence.symm (equivalence x) = x :=
  equivalence.left_inv x

@[simp] theorem apply_symm_apply (equivalence : FiniteEquiv alpha beta)
    (y : beta) : equivalence (equivalence.symm y) = y :=
  equivalence.right_inv y

theorem injective (equivalence : FiniteEquiv alpha beta) :
    Function.Injective equivalence := by
  intro left right heq
  have := congrArg equivalence.invFun heq
  simpa only [equivalence.left_inv] using this

@[ext] theorem ext {left right : FiniteEquiv alpha beta}
    (forward_eq : forall x, left x = right x) : left = right := by
  have forward_fun_eq : left.toFun = right.toFun := funext forward_eq
  cases left with
  | mk leftForward leftInverse leftLeft leftRight =>
      cases right with
      | mk rightForward rightInverse rightLeft rightRight =>
          simp only at forward_fun_eq
          subst rightForward
          have inverse_eq : leftInverse = rightInverse := by
            funext y
            calc
              leftInverse y = leftInverse (leftForward (rightInverse y)) :=
                congrArg leftInverse (rightRight y).symm
              _ = rightInverse y := leftLeft (rightInverse y)
          subst rightInverse
          rfl

end FiniteEquiv

end VisualProof.Data.Finite

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

private theorem map_allFin_add
    (m n : Nat) (f : Fin (m + n) → α) :
    (allFin (m + n)).map f =
      (allFin m).map (fun index => f (Fin.castAdd n index)) ++
        (allFin n).map (fun index => f (Fin.natAdd m index)) := by
  rw [allFin_eq_finRange, allFin_eq_finRange, allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn, List.map_ofFn, List.map_ofFn, List.ofFn_add]
  congr 1

/-- Split a dense finite enumeration into its retained prefix and fresh suffix. -/
theorem allFin_add (m n : Nat) :
    allFin (m + n) =
      (allFin m).map (Fin.castAdd n) ++
        (allFin n).map (Fin.natAdd m) := by
  have split := map_allFin_add m n (fun value => value)
  change
    (allFin (m + n)).map id =
      (allFin m).map (Fin.castAdd n) ++
        (allFin n).map (Fin.natAdd m) at split
  simpa only [List.map_id] using split

/-- Filtering a dense carrier by an exact suffix predicate preserves site order. -/
theorem filter_allFin_suffix
    (m n : Nat)
    (selected : Fin (m + n) → Bool)
    (selectedExact : ∀ value, selected value = decide (m ≤ value.val)) :
    (allFin (m + n)).filter selected =
      (allFin n).map (Fin.natAdd m) := by
  rw [allFin_add, List.filter_append]
  have prefixEmpty :
      ((allFin m).map (Fin.castAdd n)).filter selected = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro value member accepted
    rw [selectedExact] at accepted
    have large : m ≤ value.val := of_decide_eq_true accepted
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    change m ≤ index.val at large
    exact (Nat.not_le_of_gt index.isLt) large
  have suffixExact :
      ((allFin n).map (Fin.natAdd m)).filter selected =
        (allFin n).map (Fin.natAdd m) := by
    apply List.filter_eq_self.mpr
    intro value member
    rw [selectedExact]
    apply decide_eq_true
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    simp
  rw [prefixEmpty, suffixExact]
  rfl

/-- Suffix filtering transported across an explicit carrier-count equation. -/
theorem filter_allFin_suffix_of_eq
    (total m n : Nat)
    (countExact : total = m + n)
    (selected : Fin total → Bool)
    (selectedExact : ∀ value, selected value = decide (m ≤ value.val)) :
    (allFin total).filter selected =
      (allFin n).map (fun value =>
        Fin.cast countExact.symm (Fin.natAdd m value)) := by
  subst total
  exact filter_allFin_suffix m n selected selectedExact

/-- Lift an equivalence of finite tails across a common list head. -/
def FiniteEquiv.finSucc
    (equivalence : FiniteEquiv (Fin left) (Fin right)) :
    FiniteEquiv (Fin (left + 1)) (Fin (right + 1)) where
  toFun := Fin.cases 0 (fun index => Fin.succ (equivalence index))
  invFun := Fin.cases 0 (fun index => Fin.succ (equivalence.symm index))
  left_inv := by
    intro index
    refine Fin.cases rfl (fun tail => ?_) index
    change Fin.succ (equivalence.symm (equivalence tail)) = Fin.succ tail
    exact congrArg Fin.succ (equivalence.left_inv tail)
  right_inv := by
    intro index
    refine Fin.cases rfl (fun tail => ?_) index
    change Fin.succ (equivalence (equivalence.symm tail)) = Fin.succ tail
    exact congrArg Fin.succ (equivalence.right_inv tail)

/-- Swap the first two positions of a finite list carrier. -/
def FiniteEquiv.finSwapHead (tail : Nat) :
    FiniteEquiv (Fin (tail + 2)) (Fin (tail + 2)) where
  toFun :=
    Fin.cases 1 (Fin.cases 0 (fun index => Fin.succ (Fin.succ index)))
  invFun :=
    Fin.cases 1 (Fin.cases 0 (fun index => Fin.succ (Fin.succ index)))
  left_inv := by
    intro index
    refine Fin.cases rfl (fun rest => ?_) index
    refine Fin.cases rfl (fun tailIndex => ?_) rest
    rfl
  right_inv := by
    intro index
    refine Fin.cases rfl (fun rest => ?_) index
    refine Fin.cases rfl (fun tailIndex => ?_) rest
    rfl

/-- Exact equivalence between propositionally equal finite initial segments. -/
def FiniteEquiv.finCast {left right : Nat} (same : left = right) :
    FiniteEquiv (Fin left) (Fin right) where
  toFun := Fin.cast same
  invFun := Fin.cast same.symm
  left_inv := by intro value; apply Fin.ext; rfl
  right_inv := by intro value; apply Fin.ext; rfl

/--
A list permutation owns an exact equivalence of dense positions.  The
equivalence maps each source position to a target position containing the
same value, retaining multiplicity rather than merely membership.
-/
theorem FiniteEquiv.exists_ofListPerm
    {left right : List α} (permuted : left.Perm right) :
    ∃ equivalence : FiniteEquiv (Fin left.length) (Fin right.length),
      ∀ position, right.get (equivalence position) = left.get position := by
  induction permuted with
  | nil =>
      exact ⟨FiniteEquiv.refl (Fin 0), fun position => Fin.elim0 position⟩
  | @cons value left right permuted induction =>
      obtain ⟨tailEquivalence, tailExact⟩ := induction
      let equivalence := tailEquivalence.finSucc
      refine ⟨equivalence, ?_⟩
      intro position
      refine Fin.cases rfl (fun tail => ?_) position
      exact tailExact tail
  | @swap leftValue rightValue tail =>
      let equivalence := FiniteEquiv.finSwapHead tail.length
      refine ⟨equivalence, ?_⟩
      intro position
      refine Fin.cases rfl (fun rest => ?_) position
      refine Fin.cases rfl (fun tailPosition => ?_) rest
      rfl
  | @trans left middle right first second firstInduction secondInduction =>
      obtain ⟨firstEquivalence, firstExact⟩ := firstInduction
      obtain ⟨secondEquivalence, secondExact⟩ := secondInduction
      let equivalence := firstEquivalence.trans secondEquivalence
      refine ⟨equivalence, ?_⟩
      intro position
      exact (secondExact (firstEquivalence position)).trans
        (firstExact position)

/-- Noncomputable position equivalence selected from a permutation proof. -/
noncomputable def FiniteEquiv.ofListPerm
    {left right : List α} (permuted : left.Perm right) :
    { equivalence : FiniteEquiv (Fin left.length) (Fin right.length) //
      ∀ position, right.get (equivalence position) = left.get position } :=
  ⟨Classical.choose (FiniteEquiv.exists_ofListPerm permuted),
    Classical.choose_spec (FiniteEquiv.exists_ofListPerm permuted)⟩

/-- Executably invert an explicitly supplied bijection of finite initial
segments. The inverse is the first source whose forward image is the target;
the bijection proof establishes totality and the inverse laws. -/
def FiniteEquiv.ofBijectiveFin
    (forward : Fin sourceCount → Fin targetCount)
    (bijective : Function.Injective forward ∧
      ∀ target, ∃ source, forward source = target) :
    FiniteEquiv (Fin sourceCount) (Fin targetCount) := by
  let inverse (target : Fin targetCount) : Fin sourceCount :=
    ((allFin sourceCount).find? fun source => decide (forward source = target)).get
      (by
        apply List.find?_isSome.mpr
        obtain ⟨source, equality⟩ := bijective.2 target
        exact ⟨source, mem_allFin source, by simpa [equality]⟩)
  exact
    { toFun := forward
      invFun := inverse
      left_inv := by
        intro source
        apply bijective.1
        unfold inverse
        let found := (allFin sourceCount).find? fun candidate =>
          decide (forward candidate = forward source)
        have foundSome : found.isSome = true := by
          apply List.find?_isSome.mpr
          exact ⟨source, mem_allFin source, by simp⟩
        obtain ⟨candidate, candidateFound⟩ :=
          Option.isSome_iff_exists.mp foundSome
        rw [Option.get_of_eq_some foundSome candidateFound]
        have selected := List.find?_some candidateFound
        exact of_decide_eq_true (by simpa [found] using selected)
      right_inv := by
        intro target
        unfold inverse
        let found := (allFin sourceCount).find? fun candidate =>
          decide (forward candidate = target)
        have foundSome : found.isSome = true := by
          apply List.find?_isSome.mpr
          obtain ⟨source, equality⟩ := bijective.2 target
          exact ⟨source, mem_allFin source, by simpa [equality]⟩
        obtain ⟨candidate, candidateFound⟩ :=
          Option.isSome_iff_exists.mp foundSome
        rw [Option.get_of_eq_some foundSome candidateFound]
        have selected := List.find?_some candidateFound
        exact of_decide_eq_true (by simpa [found] using selected) }

/-- An injection between finite initial segments witnesses the cardinal bound. -/
theorem fin_card_le_of_injective {m n : Nat} (f : Fin m → Fin n)
    (hinjective : Function.Injective f) : m ≤ n := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => simp
      | succ m => exact Fin.elim0 (f 0)
  | succ n ih =>
      cases m with
      | zero => simp
      | succ m =>
          let skipped : Fin (n + 1) := f 0
          let lower (value : Fin (n + 1)) (hne : value ≠ skipped) : Fin n :=
            if hlt : value.val < skipped.val then
              ⟨value.val, by omega⟩
            else
              ⟨value.val - 1, by
                have hbound := value.isLt
                omega⟩
          have lower_injective :
              ∀ {first second} (hfirst : first ≠ skipped)
                (hsecond : second ≠ skipped),
                lower first hfirst = lower second hsecond → first = second := by
            intro first second hfirst hsecond heq
            have hfirstVal : first.val ≠ skipped.val := by
              intro h
              exact hfirst (Fin.ext h)
            have hsecondVal : second.val ≠ skipped.val := by
              intro h
              exact hsecond (Fin.ext h)
            unfold lower at heq
            split at heq <;> split at heq
            all_goals
              apply Fin.ext
              have hvals := congrArg Fin.val heq
              simp only at hvals
              omega
          let tail (index : Fin m) : Fin (n + 1) := f index.succ
          have tail_ne (index : Fin m) : tail index ≠ skipped := by
            intro heq
            have hindices := hinjective heq
            exact Fin.succ_ne_zero index hindices
          let reduced (index : Fin m) : Fin n :=
            lower (tail index) (tail_ne index)
          have reduced_injective : Function.Injective reduced := by
            intro first second heq
            have htail : tail first = tail second :=
              lower_injective (tail_ne first) (tail_ne second) heq
            have hsucc : first.succ = second.succ := hinjective htail
            apply Fin.ext
            exact Nat.succ.inj (congrArg Fin.val hsucc)
          have hle := ih reduced reduced_injective
          omega

/-- An injective endomap of a finite initial segment is surjective. -/
theorem fin_surjective_of_injective
    {n : Nat} (forward : Fin n → Fin n)
    (injective : Function.Injective forward) :
    ∀ target, ∃ source, forward source = target := by
  cases n with
  | zero => exact fun target => Fin.elim0 target
  | succ n =>
      intro target
      by_cases found : ∃ source, forward source = target
      · exact found
      have avoids (source : Fin (n + 1)) : forward source ≠ target := by
        intro exact
        exact found ⟨source, exact⟩
      let lower (value : Fin (n + 1)) (different : value ≠ target) : Fin n :=
        if before : value.val < target.val then
          ⟨value.val, by omega⟩
        else
          ⟨value.val - 1, by
            have bound := value.isLt
            have unequal : value.val ≠ target.val := by
              intro same
              exact different (Fin.ext same)
            omega⟩
      have lower_injective :
          ∀ {left right} (leftDifferent : left ≠ target)
            (rightDifferent : right ≠ target),
            lower left leftDifferent = lower right rightDifferent →
              left = right := by
        intro left right leftDifferent rightDifferent same
        have leftUnequal : left.val ≠ target.val := by
          intro equal
          exact leftDifferent (Fin.ext equal)
        have rightUnequal : right.val ≠ target.val := by
          intro equal
          exact rightDifferent (Fin.ext equal)
        unfold lower at same
        split at same <;> split at same
        all_goals
          apply Fin.ext
          have values := congrArg Fin.val same
          simp only at values
          omega
      let reduced (source : Fin (n + 1)) : Fin n :=
        lower (forward source) (avoids source)
      have reduced_injective : Function.Injective reduced := by
        intro left right same
        apply injective
        exact lower_injective (avoids left) (avoids right) same
      have impossible := fin_card_le_of_injective reduced reduced_injective
      omega

theorem fin_surjective_of_injective_of_card_eq
    {m n : Nat} (forward : Fin m → Fin n)
    (injective : Function.Injective forward)
    (sameCardinality : m = n) :
    ∀ target, ∃ source, forward source = target := by
  subst n
  exact fin_surjective_of_injective forward injective

/-- A duplicate-free list of finite identifiers and its complement partition
the complete dense carrier exactly. -/
theorem filter_not_mem_length_add_removed_length
    (removed : List (Fin n)) (nodup : removed.Nodup) :
    ((allFin n).filter fun value => decide (value ∉ removed)).length +
      removed.length = n := by
  let selected :=
    (allFin n).filter fun value => decide (value ∈ removed)
  have selectedNodup : selected.Nodup :=
    (allFin_nodup n).filter _
  have selectedPerm : selected.Perm removed := by
    rw [List.perm_iff_count]
    intro value
    rw [selectedNodup.count, nodup.count]
    simp [selected, mem_allFin]
  have partition :
      ((allFin n).filter fun value => decide (value ∉ removed)).length +
        selected.length = (allFin n).length := by
    have partitionValues : ∀ values : List (Fin n),
        (values.filter fun value => decide (value ∉ removed)).length +
          (values.filter fun value => decide (value ∈ removed)).length =
            values.length := by
      intro values
      induction values with
      | nil => simp
      | cons head tail induction =>
          by_cases member : head ∈ removed
          · simpa [member, Nat.add_assoc] using
              congrArg Nat.succ induction
          · simpa [member, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using congrArg Nat.succ induction
    simpa [selected] using partitionValues (allFin n)
  rw [selectedPerm.length_eq] at partition
  simpa [allFin_eq_finRange] using partition

theorem list_perm_of_nodup_mem_iff
    [BEq α] [LawfulBEq α]
    {left right : List α}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro value
  rw [leftNodup.count, rightNodup.count]
  by_cases leftMember : value ∈ left
  · have rightMember := (sameMembers value).mp leftMember
    simp [leftMember, rightMember]
  · have rightMember : value ∉ right := by
      exact fun member => leftMember ((sameMembers value).mpr member)
    simp [leftMember, rightMember]

theorem list_map_nodup_of_injective_on
    {values : List α} (nodup : values.Nodup)
    (mapping : α → β)
    (injective : ∀ {left right}, left ∈ values → right ∈ values →
      mapping left = mapping right → left = right) :
    (values.map mapping).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        rcases List.mem_map.mp member with ⟨right, rightMember, same⟩
        have exact := injective
          (by simp only [List.mem_cons]; exact Or.inr rightMember)
          (by simp) same
        exact nodup.1 (exact ▸ rightMember)
      · exact induction nodup.2 (by
          intro left right leftMember rightMember same
          exact injective (by simp [leftMember]) (by simp [rightMember]) same)

def filterFin (p : Fin n -> Bool) : List (Fin n) :=
  (allFin n).filter p

@[simp] theorem mem_filterFin {p : Fin n -> Bool} (i : Fin n) :
    i ∈ filterFin p ↔ p i = true := by
  simp [filterFin]

theorem filterFin_nodup (p : Fin n -> Bool) : (filterFin p).Nodup := by
  exact (allFin_nodup n).filter p

/-- Duplicate erasure always produces a duplicate-free list. -/
theorem eraseDups_nodup [BEq α] [LawfulBEq α]
    (values : List α) : values.eraseDups.Nodup := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (tail.filter fun value => !value == head)
termination_by values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

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

@[simp] theorem indexOf?_get_eq_some_of_nodup [DecidableEq α]
    {xs : List α} (hnodup : xs.Nodup) (index : Fin xs.length) :
    indexOf? xs (xs.get index) = some index := by
  obtain ⟨found, hfound⟩ := indexOf?_complete (List.get_mem xs index)
  have hindex : index = found :=
    indexOf?_unique_of_nodup hnodup hfound rfl
  subst found
  exact hfound

namespace FiniteEquiv

/-!
Stable, executable transport between two permutations of the same list.  The
rank of each occurrence among equal values selects its target position, so
duplicate values remain distinct without a choice principle.
-/

private def matchingPositions [DecidableEq α] :
    (values : List α) → α → List (Fin values.length)
  | [], _ => []
  | head :: tail, value =>
      if head = value then
        0 :: (matchingPositions tail value).map Fin.succ
      else
        (matchingPositions tail value).map Fin.succ

private theorem matchingPositions_mem [DecidableEq α]
    (values : List α) (value : α) (position : Fin values.length) :
    position ∈ matchingPositions values value ↔ values.get position = value := by
  induction values with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      refine Fin.cases ?_ (fun position => ?_) position
      · by_cases same : head = value
        · simp [matchingPositions, same]
        · rw [matchingPositions, if_neg same]
          rw [List.mem_map]
          constructor
          · rintro ⟨candidate, _member, exact⟩
            have values := congrArg Fin.val exact
            simp at values
          · exact False.elim ∘ same
      · by_cases same : head = value
        · rw [matchingPositions, if_pos same]
          simp only [List.mem_cons, Fin.succ_ne_zero, false_or, List.mem_map]
          constructor
          · rintro ⟨candidate, member, exact⟩
            have candidateExact : candidate = position := Fin.succ_inj.mp exact
            subst candidate
            simpa using (induction position).mp member
          · intro exact
            have tailExact : tail.get position = value := by simpa using exact
            exact ⟨position, (induction position).mpr tailExact, rfl⟩
        · rw [matchingPositions, if_neg same]
          simp only [List.mem_map]
          constructor
          · rintro ⟨candidate, member, exact⟩
            have candidateExact : candidate = position := Fin.succ_inj.mp exact
            subst candidate
            simpa using (induction position).mp member
          · intro exact
            have tailExact : tail.get position = value := by simpa using exact
            exact ⟨position, (induction position).mpr tailExact, rfl⟩

private theorem matchingPositions_nodup [DecidableEq α]
    (values : List α) (value : α) :
    (matchingPositions values value).Nodup := by
  induction values with
  | nil => simp [matchingPositions]
  | cons head tail induction =>
      have mappedNodup :
          ((matchingPositions tail value).map Fin.succ).Nodup :=
        induction.map Fin.succ (by
          intro left right different same
          exact different (Fin.succ_inj.mp same))
      by_cases same : head = value
      · rw [matchingPositions, if_pos same, List.nodup_cons]
        exact ⟨by
          intro member
          rcases List.mem_map.mp member with ⟨position, _, exact⟩
          exact Fin.succ_ne_zero position exact, mappedNodup⟩
      · simpa [matchingPositions, same] using mappedNodup

private theorem matchingPositions_length [DecidableEq α]
    (values : List α) (value : α) :
    (matchingPositions values value).length = values.count value := by
  induction values with
  | nil => simp [matchingPositions]
  | cons head tail induction =>
      by_cases same : head = value
      · simp [matchingPositions, same, induction]
      · simp [matchingPositions, same, induction]

private def matchingRank [DecidableEq α]
    (values : List α) (value : α) (position : Fin values.length)
    (exact : values.get position = value) :
    Fin (matchingPositions values value).length :=
  (indexOf? (matchingPositions values value) position).get (by
    rw [indexOf?_isSome_iff]
    exact (matchingPositions_mem values value position).mpr exact)

private theorem matchingRank_spec [DecidableEq α]
    (values : List α) (value : α) (position : Fin values.length)
    (exact : values.get position = value) :
    (matchingPositions values value).get
        (matchingRank values value position exact) = position := by
  unfold matchingRank
  let found := indexOf? (matchingPositions values value) position
  have foundSome : found.isSome = true := by
    rw [indexOf?_isSome_iff]
    exact (matchingPositions_mem values value position).mpr exact
  obtain ⟨candidate, candidateFound⟩ :=
    Option.isSome_iff_exists.mp foundSome
  rw [Option.get_of_eq_some foundSome candidateFound]
  exact indexOf?_sound candidateFound

private theorem matchingRank_congr [DecidableEq α]
    (values : List α) (value : α)
    (first second : Fin values.length)
    (firstExact : values.get first = value)
    (secondExact : values.get second = value)
    (same : first = second) :
    matchingRank values value first firstExact =
      matchingRank values value second secondExact := by
  subst second
  rfl

private theorem matchingRank_get [DecidableEq α]
    (values : List α) (value : α)
    (rank : Fin (matchingPositions values value).length) :
    matchingRank values value
        ((matchingPositions values value).get rank)
        ((matchingPositions_mem values value _).mp
          (List.get_mem _ rank)) = rank := by
  let computed := matchingRank values value
    ((matchingPositions values value).get rank)
    ((matchingPositions_mem values value _).mp
      (List.get_mem _ rank))
  have dataExact :
      (matchingPositions values value).get computed =
        (matchingPositions values value).get rank := by
    exact matchingRank_spec values value
      ((matchingPositions values value).get rank)
      ((matchingPositions_mem values value _).mp
        (List.get_mem _ rank))
  apply Fin.ext
  exact (List.getElem_inj
    (i := computed.val) (j := rank.val)
    (matchingPositions_nodup values value)).mp (by
      simpa only [List.get_eq_getElem] using dataExact)

private def stablePermForward [DecidableEq α]
    {left right : List α} (permuted : left.Perm right) :
    Fin left.length → Fin right.length := fun position =>
  let value := left.get position
  let sourcePositions := matchingPositions left value
  let targetPositions := matchingPositions right value
  let rank := matchingRank left value position rfl
  let lengthExact : sourcePositions.length = targetPositions.length := by
    simp only [sourcePositions, targetPositions, matchingPositions_length]
    exact permuted.count_eq value
  targetPositions.get (Fin.cast lengthExact rank)

private theorem stablePermForward_exact [DecidableEq α]
    {left right : List α} (permuted : left.Perm right)
    (position : Fin left.length) :
    right.get (stablePermForward permuted position) = left.get position := by
  unfold stablePermForward
  apply (matchingPositions_mem right (left.get position) _).mp
  exact List.get_mem _ _

private theorem stablePermForward_rank [DecidableEq α]
    {left right : List α} (permuted : left.Perm right)
    (position : Fin left.length) (value : α)
    (sourceExact : left.get position = value) :
    let lengthExact :
        (matchingPositions left value).length =
          (matchingPositions right value).length := by
      simp only [matchingPositions_length]
      exact permuted.count_eq value
    matchingRank right value (stablePermForward permuted position)
        ((stablePermForward_exact permuted position).trans sourceExact) =
      Fin.cast lengthExact
        (matchingRank left value position sourceExact) := by
  subst value
  dsimp only
  unfold stablePermForward
  dsimp only
  exact matchingRank_get right (left.get position) _

private theorem stablePermForward_injective [DecidableEq α]
    {left right : List α} (permuted : left.Perm right) :
    Function.Injective (stablePermForward permuted) := by
  intro first second mappedSame
  let value := left.get first
  have secondExact : left.get second = value := by
    calc
      left.get second = right.get (stablePermForward permuted second) :=
        (stablePermForward_exact permuted second).symm
      _ = right.get (stablePermForward permuted first) :=
        congrArg right.get mappedSame.symm
      _ = left.get first := stablePermForward_exact permuted first
      _ = value := rfl
  let lengthExact :
      (matchingPositions left value).length =
        (matchingPositions right value).length := by
    simp only [matchingPositions_length]
    exact permuted.count_eq value
  have targetRanksSame :
      matchingRank right value (stablePermForward permuted first)
          ((stablePermForward_exact permuted first).trans rfl) =
        matchingRank right value (stablePermForward permuted second)
          ((stablePermForward_exact permuted second).trans secondExact) :=
    matchingRank_congr right value _ _ _ _ mappedSame
  rw [stablePermForward_rank permuted first value rfl,
    stablePermForward_rank permuted second value secondExact] at targetRanksSame
  have sourceRanksSame :
      matchingRank left value first rfl =
        matchingRank left value second secondExact := by
    apply Fin.ext
    simpa using congrArg Fin.val targetRanksSame
  have sourcePositionsSame :
      (matchingPositions left value).get
          (matchingRank left value first rfl) =
        (matchingPositions left value).get
          (matchingRank left value second secondExact) :=
    congrArg (matchingPositions left value).get sourceRanksSame
  rw [matchingRank_spec left value first rfl,
    matchingRank_spec left value second secondExact] at sourcePositionsSame
  exact sourcePositionsSame

private def stablePermEquiv [DecidableEq α]
    {left right : List α} (permuted : left.Perm right) :
    FiniteEquiv (Fin left.length) (Fin right.length) :=
  ofBijectiveFin (stablePermForward permuted)
    ⟨stablePermForward_injective permuted,
      fin_surjective_of_injective_of_card_eq
        (stablePermForward permuted)
        (stablePermForward_injective permuted) permuted.length_eq⟩

/--
Executable positional equivalence between permuted lists.  Equal values are
matched by their left-to-right occurrence rank.
-/
def ofListPermStable [DecidableEq α]
    {left right : List α} (permuted : left.Perm right) :
    {equivalence : FiniteEquiv (Fin left.length) (Fin right.length) //
      ∀ position, right.get (equivalence position) = left.get position} :=
  ⟨stablePermEquiv permuted, stablePermForward_exact permuted⟩

end FiniteEquiv

end VisualProof.Data.Finite

namespace VisualProof.Data.Finite.FiniteEquiv

open VisualProof.Data.Finite

private def restrictIndex [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (index : Fin source.length) : Fin target.length :=
  (indexOf? target (equivalence source[index])).get (by
    rw [indexOf?_isSome_iff]
    exact (mem_iff source[index]).mpr (List.getElem_mem ..))

private theorem restrictIndex_spec [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (index : Fin source.length) :
    target.get (restrictIndex equivalence source target mem_iff index) =
      equivalence (source.get index) := by
  unfold restrictIndex
  let hsome : (indexOf? target (equivalence source[index])).isSome = true := by
    rw [indexOf?_isSome_iff]
    exact (mem_iff source[index]).mpr (List.getElem_mem ..)
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  calc
    target.get ((indexOf? target (equivalence source[index])).get _) =
        target.get found := congrArg target.get
          (Option.get_of_eq_some hsome hfound)
    _ = equivalence (source.get index) := by
      simpa only [List.get_eq_getElem] using indexOf?_sound hfound

private theorem restrict_inverse_mem_iff
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (y : beta) : equivalence.symm y ∈ source ↔ y ∈ target := by
  constructor
  · intro hsource
    have := (mem_iff (equivalence.symm y)).mpr hsource
    rwa [apply_symm_apply] at this
  · intro htarget
    apply (mem_iff (equivalence.symm y)).mp
    rwa [apply_symm_apply]

/-- Restrict an equivalence to two nodup lists that enumerate matching fibers. -/
def restrictLists [DecidableEq alpha] [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source) :
    FiniteEquiv (Fin source.length) (Fin target.length) where
  toFun := restrictIndex equivalence source target mem_iff
  invFun := restrictIndex equivalence.symm target source
    (restrict_inverse_mem_iff equivalence source target mem_iff)
  left_inv := by
    intro index
    have houter := restrictIndex_spec equivalence.symm target source
      (restrict_inverse_mem_iff equivalence source target mem_iff)
      (restrictIndex equivalence source target mem_iff index)
    have hinner := restrictIndex_spec equivalence source target mem_iff index
    rw [hinner, symm_apply_apply] at houter
    apply Fin.ext
    exact (List.getElem_inj sourceNodup).mp (by
      simpa only [List.get_eq_getElem] using houter)
  right_inv := by
    intro index
    have houter := restrictIndex_spec equivalence source target mem_iff
      (restrictIndex equivalence.symm target source
        (restrict_inverse_mem_iff equivalence source target mem_iff) index)
    have hinner := restrictIndex_spec equivalence.symm target source
      (restrict_inverse_mem_iff equivalence source target mem_iff) index
    rw [hinner, apply_symm_apply] at houter
    apply Fin.ext
    exact (List.getElem_inj targetNodup).mp (by
      simpa only [List.get_eq_getElem] using houter)

theorem restrictLists_spec [DecidableEq alpha] [DecidableEq beta]
    (equivalence : FiniteEquiv alpha beta)
    (source : List alpha) (target : List beta)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (mem_iff : forall x, equivalence x ∈ target ↔ x ∈ source)
    (index : Fin source.length) :
    target.get (restrictLists equivalence source target sourceNodup targetNodup
      mem_iff index) = equivalence (source.get index) :=
  restrictIndex_spec equivalence source target mem_iff index

end VisualProof.Data.Finite.FiniteEquiv

namespace VisualProof.Data.Finite

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

/-! Deterministic equivalence closure on a finite carrier. -/

/-- A proof-independent representative map for a finite partition. -/
structure FinitePartition (n : Nat) where
  representative : Fin n -> Fin n

namespace FinitePartition

/-- The discrete partition. -/
def identity (n : Nat) : FinitePartition n :=
  ⟨fun index => index⟩

/--
Merge the current classes containing `left` and `right`.

The representative of the right class is deterministically replaced by the
representative of the left class. All other representatives are unchanged.
-/
def merge (partition : FinitePartition n) (left right : Fin n) :
    FinitePartition n :=
  ⟨fun index =>
    if partition.representative index = partition.representative right then
      partition.representative left
    else
      partition.representative index⟩

/--
The deterministic partition generated by the ordered list of equations.

This is a right fold: the tail is processed first, then the head equation. The
choice is computational only; the universal-property theorems below characterize
the resulting relation independently of representative choices.
-/
def ofEdges : List (Fin n × Fin n) -> FinitePartition n
  | [] => identity n
  | edge :: edges => merge (ofEdges edges) edge.1 edge.2

/-- Equality of final representatives, exposed as an executable relation. -/
def related (partition : FinitePartition n) (left right : Fin n) : Bool :=
  partition.representative left == partition.representative right

@[simp] theorem related_eq_true_iff (partition : FinitePartition n)
    (left right : Fin n) :
    partition.related left right = true ↔
      partition.representative left = partition.representative right := by
  simp [related]

def Normalized (partition : FinitePartition n) : Prop :=
  ∀ index, partition.representative (partition.representative index) =
    partition.representative index

@[simp] theorem identity_representative (index : Fin n) :
    (identity n).representative index = index := rfl

theorem identity_normalized (n : Nat) : (identity n).Normalized := by
  intro index
  rfl

@[simp] theorem merge_representative (partition : FinitePartition n)
    (left right index : Fin n) :
    (partition.merge left right).representative index =
      if partition.representative index = partition.representative right then
        partition.representative left
      else
        partition.representative index := rfl

theorem merge_normalized (partition : FinitePartition n)
    (normalized : partition.Normalized) (left right : Fin n) :
    (partition.merge left right).Normalized := by
  intro index
  simp only [merge_representative]
  by_cases hindex :
      partition.representative index = partition.representative right
  · rw [if_pos hindex, normalized left]
    by_cases hclasses :
        partition.representative left = partition.representative right
    · rw [if_pos hclasses]
    · rw [if_neg hclasses]
  · rw [if_neg hindex, normalized index, if_neg hindex]

theorem ofEdges_normalized (edges : List (Fin n × Fin n)) :
    (ofEdges edges).Normalized := by
  induction edges with
  | nil => exact identity_normalized n
  | cons edge edges ih =>
      exact merge_normalized (ofEdges edges) ih edge.1 edge.2

theorem merge_preserves_related (partition : FinitePartition n)
    {first second left right : Fin n}
    (related : partition.representative first =
      partition.representative second) :
    (partition.merge left right).representative first =
      (partition.merge left right).representative second := by
  simp only [merge_representative]
  rw [related]

theorem merge_relates_inputs (partition : FinitePartition n)
    (left right : Fin n) :
    (partition.merge left right).representative left =
      (partition.merge left right).representative right := by
  simp only [merge_representative]
  by_cases hclasses :
      partition.representative left = partition.representative right
  · simp [hclasses]
  · simp [hclasses]

theorem generator_related {edges : List (Fin n × Fin n)}
    {edge : Fin n × Fin n} (member : edge ∈ edges) :
    (ofEdges edges).related edge.1 edge.2 = true := by
  induction edges with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (related_eq_true_iff _ _ _).2
          (merge_relates_inputs (ofEdges tail) edge.1 edge.2)
      · exact (related_eq_true_iff _ _ _).2
          (merge_preserves_related (partition := ofEdges tail)
            ((related_eq_true_iff _ _ _).1 (ih member)))

@[simp] theorem related_refl (partition : FinitePartition n) (index : Fin n) :
    partition.related index index = true := by
  exact (related_eq_true_iff _ _ _).2 rfl

theorem related_symm (partition : FinitePartition n) {left right : Fin n}
    (related : partition.related left right = true) :
    partition.related right left = true := by
  exact (related_eq_true_iff _ _ _).2
    ((related_eq_true_iff _ _ _).1 related).symm

theorem related_trans (partition : FinitePartition n) {first second third : Fin n}
    (firstSecond : partition.related first second = true)
    (secondThird : partition.related second third = true) :
    partition.related first third = true := by
  exact (related_eq_true_iff _ _ _).2
    (((related_eq_true_iff _ _ _).1 firstSecond).trans
      ((related_eq_true_iff _ _ _).1 secondThird))

private theorem representative_respects
    {relation : Fin n -> Fin n -> Prop}
    (refl : ∀ index, relation index index)
    (symm : ∀ {left right}, relation left right -> relation right left)
    (trans : ∀ {first second third},
      relation first second -> relation second third -> relation first third)
    {edges : List (Fin n × Fin n)}
    (contains : ∀ edge ∈ edges, relation edge.1 edge.2) :
    ∀ index, relation index ((ofEdges edges).representative index) := by
  induction edges with
  | nil =>
      intro index
      exact refl index
  | cons edge edges ih =>
      intro index
      have tailContains : ∀ tailEdge ∈ edges,
          relation tailEdge.1 tailEdge.2 := by
        intro tailEdge member
        exact contains tailEdge (by simp [member])
      have indexToOld := ih tailContains index
      by_cases hclass :
          (ofEdges edges).representative index =
            (ofEdges edges).representative edge.2
      · rw [ofEdges, merge_representative, if_pos hclass]
        have leftToRepresentative := ih tailContains edge.1
        have rightToRepresentative := ih tailContains edge.2
        have edgeRelated : relation edge.1 edge.2 :=
          contains edge (by simp)
        have oldToNew :
            relation ((ofEdges edges).representative edge.2)
              ((ofEdges edges).representative edge.1) :=
          trans (symm rightToRepresentative)
            (trans (symm edgeRelated) leftToRepresentative)
        exact trans indexToOld
          (by simpa [hclass] using oldToNew)
      · rw [ofEdges, merge_representative, if_neg hclass]
        exact indexToOld

/--
The computed relation is the least equivalence relation containing every
generator edge.
-/
theorem least
    {relation : Fin n -> Fin n -> Prop}
    (refl : ∀ index, relation index index)
    (symm : ∀ {left right}, relation left right -> relation right left)
    (trans : ∀ {first second third},
      relation first second -> relation second third -> relation first third)
    {edges : List (Fin n × Fin n)}
    (contains : ∀ edge ∈ edges, relation edge.1 edge.2)
    {left right : Fin n}
    (closed : (ofEdges edges).related left right = true) :
    relation left right := by
  have leftRepresentative :=
    representative_respects refl symm trans contains left
  have rightRepresentative :=
    representative_respects refl symm trans contains right
  have representativesEqual := (related_eq_true_iff _ _ _).1 closed
  exact trans leftRepresentative (by
    rw [representativesEqual]
    exact symm rightRepresentative)

end FinitePartition

namespace FinitePartition.Examples

def fourEdges : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 2)]

theorem four_transitive :
    (FinitePartition.ofEdges fourEdges).related 0 2 = true := by
  decide

theorem four_three_separate :
    (FinitePartition.ofEdges fourEdges).related 0 3 = false ∧
    (FinitePartition.ofEdges fourEdges).related 1 3 = false ∧
    (FinitePartition.ofEdges fourEdges).related 2 3 = false := by
  decide

theorem four_representatives :
    (FinitePartition.ofEdges fourEdges).representative 0 = 0 ∧
    (FinitePartition.ofEdges fourEdges).representative 1 = 0 ∧
    (FinitePartition.ofEdges fourEdges).representative 2 = 0 ∧
    (FinitePartition.ofEdges fourEdges).representative 3 = 3 := by
  decide

end FinitePartition.Examples

end VisualProof.Data.Finite
