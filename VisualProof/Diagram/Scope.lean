import VisualProof.Diagram.Core

namespace VisualProof.Diagram

open VisualProof.Theory

/-- A region path lists the cut-item index taken at each nesting level. -/
abbrev RegionPath := List Nat

mutual
  /-- Port incidences of one inherited wire, expressed relative to a region. -/
  def Region.incidencePaths (wireIndex : Nat) :
      Region outer → List RegionPath
    | .mk _ items => items.incidencePaths wireIndex 0

  def Item.incidencePaths (wireIndex itemIndex : Nat) :
      Item wires → List RegionPath
    | .atom head ports =>
        List.replicate
          ((if head.index.val = wireIndex then 1 else 0) +
            ports.countIndex wireIndex) []
    | .identity _ arity ports =>
        List.replicate
          ((List.ofFn fun index : Fin arity => (ports index).index.val).count
            wireIndex) []
    | .cut body =>
        (body.incidencePaths wireIndex).map (fun path => itemIndex :: path)

  def ItemSeq.incidencePaths (wireIndex itemIndex : Nat) :
      ItemSeq wires → List RegionPath
    | .nil => []
    | .cons head tail =>
        head.incidencePaths wireIndex itemIndex ++
          tail.incidencePaths wireIndex (itemIndex + 1)
end

namespace RegionPath

/-- Longest common prefix of two region paths. -/
def commonPrefix : RegionPath → RegionPath → RegionPath
  | left :: leftTail, right :: rightTail =>
      if left = right then
        left :: commonPrefix leftTail rightTail
      else []
  | _, _ => []

private def dcaFrom : RegionPath → List RegionPath → RegionPath
  | first, [] => first
  | first, next :: rest => dcaFrom (first.commonPrefix next) rest

/-- Deepest common ancestor of a finite collection of occurrence paths. -/
def deepestCommonAncestor : List RegionPath → RegionPath
  | [] => []
  | first :: rest => dcaFrom first rest

private theorem dcaFrom_nil (rest : List RegionPath) :
    dcaFrom [] rest = [] := by
  induction rest with
  | nil => rfl
  | cons next rest induction =>
      simp only [dcaFrom, commonPrefix]
      exact induction

@[simp] theorem deepestCommonAncestor_cons_nil (rest : List RegionPath) :
    deepestCommonAncestor ([] :: rest) = [] := by
  simp only [deepestCommonAncestor]
  exact dcaFrom_nil rest

private theorem dcaFrom_eq_nil_of_mem_nil
    (first : RegionPath) (rest : List RegionPath) (contains : [] ∈ rest) :
    dcaFrom first rest = [] := by
  induction rest generalizing first with
  | nil => simp at contains
  | cons next rest induction =>
      simp only [List.mem_cons] at contains
      rcases contains with rfl | contains
      · simp only [dcaFrom, commonPrefix]
        exact dcaFrom_nil rest
      · simp only [dcaFrom]
        exact induction (first := first.commonPrefix next) contains

theorem deepestCommonAncestor_eq_nil_of_mem_nil
    (paths : List RegionPath) (contains : [] ∈ paths) :
    deepestCommonAncestor paths = [] := by
  cases paths with
  | nil => simp at contains
  | cons first rest =>
      simp only [List.mem_cons] at contains
      rcases contains with rfl | contains
      · exact deepestCommonAncestor_cons_nil rest
      · exact dcaFrom_eq_nil_of_mem_nil first rest contains

@[simp] theorem commonPrefix_cons_same
    (index : Nat) (left right : RegionPath) :
    commonPrefix (index :: left) (index :: right) =
      index :: commonPrefix left right := by
  simp [commonPrefix]

private theorem dcaFrom_map_cons
    (index : Nat) (first : RegionPath) (rest : List RegionPath) :
    dcaFrom (index :: first) (rest.map (List.cons index)) =
      index :: dcaFrom first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest induction =>
      simp only [List.map_cons, dcaFrom, commonPrefix_cons_same]
      exact induction (first := first.commonPrefix next)

private theorem dcaFrom_append
    (first : RegionPath) (left right : List RegionPath) :
    dcaFrom first (left ++ right) = dcaFrom (dcaFrom first left) right := by
  induction left generalizing first with
  | nil => rfl
  | cons next rest induction =>
      simp only [List.cons_append, dcaFrom]
      exact induction (first := first.commonPrefix next)

theorem deepestCommonAncestor_append_eq_nil
    (left right : List RegionPath) (nonempty : left ≠ [])
    (leftDca : deepestCommonAncestor left = []) :
    deepestCommonAncestor (left ++ right) = [] := by
  cases left with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      simp only [deepestCommonAncestor] at leftDca ⊢
      change dcaFrom first (rest ++ right) = []
      rw [dcaFrom_append, leftDca]
      exact dcaFrom_nil right

theorem deepestCommonAncestor_map_cons
    (index : Nat) (paths : List RegionPath) (nonempty : paths ≠ []) :
    deepestCommonAncestor (paths.map (List.cons index)) =
      index :: deepestCommonAncestor paths := by
  cases paths with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      simp only [List.map_cons, deepestCommonAncestor]
      exact dcaFrom_map_cons index first rest

end RegionPath

theorem ItemSeq.incidencePaths_append
    (first second : ItemSeq wires) (wireIndex itemIndex : Nat) :
    (first.append second).incidencePaths wireIndex itemIndex =
      first.incidencePaths wireIndex itemIndex ++
        second.incidencePaths wireIndex (itemIndex + first.length) := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive : ∀ context, Item context → Prop := fun _ _ => True
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    ∀ (second : ItemSeq context) (wireIndex itemIndex : Nat),
      (items.append second).incidencePaths wireIndex itemIndex =
        items.incidencePaths wireIndex itemIndex ++
          second.incidencePaths wireIndex (itemIndex + items.length)
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by intro second wireIndex itemIndex; simp [ItemSeq.append,
      ItemSeq.incidencePaths, ItemSeq.length])
    (by
      intro _ head tail _ tailIH second wireIndex itemIndex
      simp only [ItemSeq.append, ItemSeq.incidencePaths, ItemSeq.length,
        List.append_assoc]
      rw [tailIH second wireIndex (itemIndex + 1)]
      congr 2
      simp [Nat.add_assoc, Nat.add_comm])
    first second wireIndex itemIndex

mutual
  /-- Every local wire is used at this region's DCA, recursively. -/
  def Region.Canonical : Region outer → Prop
    | .mk locals items =>
        (∀ localIndex : Fin locals.length,
          let paths := items.incidencePaths (outer.length + localIndex.val) 0
          paths ≠ [] ∧
            RegionPath.deepestCommonAncestor paths = []) ∧
        items.ChildrenCanonical

  def Item.ChildrenCanonical : Item wires → Prop
    | .atom _ _ => True
    | .identity _ _ _ => True
    | .cut body => body.Canonical

  def ItemSeq.ChildrenCanonical : ItemSeq wires → Prop
    | .nil => True
    | .cons head tail => head.ChildrenCanonical ∧ tail.ChildrenCanonical
end

theorem ItemSeq.childrenCanonical_append
    (first second : ItemSeq wires) :
    (first.append second).ChildrenCanonical ↔
      first.ChildrenCanonical ∧ second.ChildrenCanonical := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive : ∀ context, Item context → Prop := fun _ _ => True
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    ∀ second : ItemSeq context,
      (items.append second).ChildrenCanonical ↔
        items.ChildrenCanonical ∧ second.ChildrenCanonical
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by
      intro _ second
      constructor
      · intro secondCanonical
        exact ⟨True.intro, secondCanonical⟩
      · intro bothCanonical
        exact bothCanonical.2)
    (by
      intro _ head tail _ tailIH second
      simp only [ItemSeq.append, ItemSeq.ChildrenCanonical]
      rw [tailIH second]
      constructor
      · rintro ⟨headCanonical, tailCanonical, secondCanonical⟩
        exact ⟨⟨headCanonical, tailCanonical⟩, secondCanonical⟩
      · rintro ⟨⟨headCanonical, tailCanonical⟩, secondCanonical⟩
        exact ⟨headCanonical, tailCanonical, secondCanonical⟩)
    first second

mutual
  /-- A typed wire introduced somewhere inside a recursive region. -/
  inductive Region.InternalWire :
      (region : Region outer) → Sig → Type
    | here {locals : List Sig} {items : ItemSeq (outer ++ locals)}
        (wire : Var locals signature) :
        Region.InternalWire (.mk locals items) signature
    | nested {locals : List Sig} {items : ItemSeq (outer ++ locals)}
        (wire : ItemSeq.InternalWire items signature) :
        Region.InternalWire (.mk locals items) signature

  inductive ItemSeq.InternalWire :
      (items : ItemSeq wires) → Sig → Type
    | headCut {body : Region wires} {tail : ItemSeq wires}
        (wire : Region.InternalWire body signature) :
        ItemSeq.InternalWire (.cons (.cut body) tail) signature
    | tail {head : Item wires} {tail : ItemSeq wires}
        (wire : ItemSeq.InternalWire tail signature) :
        ItemSeq.InternalWire (.cons head tail) signature
end

mutual
  def Region.InternalWire.ownerPath :
      {region : Region outer} → Region.InternalWire region signature →
        RegionPath
    | _, .here _ => []
    | _, .nested wire => wire.ownerPathFrom 0

  def ItemSeq.InternalWire.ownerPathFrom :
      {items : ItemSeq wires} → ItemSeq.InternalWire items signature →
        Nat → RegionPath
    | _, .headCut wire, itemIndex => itemIndex :: wire.ownerPath
    | _, .tail wire, itemIndex => wire.ownerPathFrom (itemIndex + 1)
end

mutual
  def Region.InternalWire.occurrencePaths :
      {region : Region outer} → Region.InternalWire region signature →
        List RegionPath
    | @Region.mk _ _ items, .here wire =>
        items.incidencePaths (outer.length + wire.index.val) 0
    | _, .nested wire => wire.occurrencePathsFrom 0

  def ItemSeq.InternalWire.occurrencePathsFrom :
      {items : ItemSeq wires} → ItemSeq.InternalWire items signature →
        Nat → List RegionPath
    | _, .headCut wire, itemIndex =>
        wire.occurrencePaths.map (List.cons itemIndex)
    | _, .tail wire, itemIndex => wire.occurrencePathsFrom (itemIndex + 1)
end

mutual
  theorem Region.InternalWire.scope_spec
      {region : Region outer} (canonical : region.Canonical)
      (wire : Region.InternalWire region signature) :
      wire.occurrencePaths ≠ [] ∧
        RegionPath.deepestCommonAncestor wire.occurrencePaths =
          wire.ownerPath := by
    cases region with
    | mk locals items =>
        cases wire with
        | here wire =>
            exact canonical.1 wire.index
        | nested wire =>
            exact wire.scope_spec_from canonical.2 0

  theorem ItemSeq.InternalWire.scope_spec_from
      {items : ItemSeq wires} (canonical : items.ChildrenCanonical)
      (wire : ItemSeq.InternalWire items signature) (itemIndex : Nat) :
      wire.occurrencePathsFrom itemIndex ≠ [] ∧
        RegionPath.deepestCommonAncestor
            (wire.occurrencePathsFrom itemIndex) =
          wire.ownerPathFrom itemIndex := by
    cases wire with
    | headCut wire =>
        have child := wire.scope_spec canonical.1
        constructor
        · intro empty
          exact child.1 (List.map_eq_nil_iff.mp empty)
        · simp only [ItemSeq.InternalWire.occurrencePathsFrom,
            ItemSeq.InternalWire.ownerPathFrom]
          rw [RegionPath.deepestCommonAncestor_map_cons _ _ child.1,
            child.2]
    | tail wire =>
        exact wire.scope_spec_from canonical.2 (itemIndex + 1)
end

end VisualProof.Diagram
