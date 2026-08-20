import VisualProof.Data.Finite
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

def StartsWith (index : Nat) (path : RegionPath) : Prop :=
  ∃ tail, path = index :: tail

def CommonHead (paths : List RegionPath) : Prop :=
  ∃ index, ∀ path ∈ paths, StartsWith index path

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

/-- A local wire has at least two actual incidences and is rooted at the
current region. -/
def RootedTwo (paths : List RegionPath) : Prop :=
  2 ≤ paths.length ∧ deepestCommonAncestor paths = []

instance (paths : List RegionPath) : Decidable (RootedTwo paths) := by
  unfold RootedTwo
  infer_instance

theorem RootedTwo.nonempty {paths : List RegionPath}
    (rooted : RootedTwo paths) : paths ≠ [] := by
  intro empty
  rw [empty] at rooted
  simp [RootedTwo] at rooted

private theorem dcaFrom_nil (rest : List RegionPath) :
    dcaFrom [] rest = [] := by
  induction rest with
  | nil => rfl
  | cons next rest induction =>
      simp only [dcaFrom, commonPrefix]
      exact induction

private theorem commonPrefix_starts
    (left right : RegionPath) (index : Nat)
    (starts : StartsWith index (left.commonPrefix right)) :
    StartsWith index left ∧ StartsWith index right := by
  cases left with
  | nil => simp [StartsWith, commonPrefix] at starts
  | cons leftHead leftTail =>
      cases right with
      | nil => simp [StartsWith, commonPrefix] at starts
      | cons rightHead rightTail =>
          simp only [commonPrefix] at starts
          split at starts
          · rcases starts with ⟨tail, equality⟩
            injection equality with headEq
            subst index
            subst rightHead
            exact ⟨⟨leftTail, rfl⟩, ⟨rightTail, rfl⟩⟩
          · simp [StartsWith] at starts

private theorem dcaFrom_starts
    (first : RegionPath) (rest : List RegionPath) (index : Nat)
    (firstStarts : StartsWith index first)
    (restStarts : ∀ path ∈ rest, StartsWith index path) :
    StartsWith index (dcaFrom first rest) := by
  induction rest generalizing first with
  | nil => exact firstStarts
  | cons next tail induction =>
      simp only [dcaFrom]
      apply induction
      · rcases firstStarts with ⟨firstTail, rfl⟩
        rcases restStarts next (by simp) with ⟨nextTail, nextEq⟩
        subst next
        exact ⟨RegionPath.commonPrefix firstTail nextTail, by
          simp [RegionPath.commonPrefix]⟩
      · intro path member
        exact restStarts path (by simp [member])

private theorem dcaFrom_ne_nil_commonHead
    (first : RegionPath) (rest : List RegionPath)
    (nonempty : dcaFrom first rest ≠ []) :
    ∃ index, StartsWith index first ∧
      ∀ path ∈ rest, StartsWith index path := by
  induction rest generalizing first with
  | nil =>
      cases first with
      | nil => exact False.elim (nonempty rfl)
      | cons index tail => exact ⟨index, ⟨tail, rfl⟩, by simp⟩
  | cons next tail induction =>
      simp only [dcaFrom] at nonempty
      obtain ⟨index, commonStarts, tailStarts⟩ := induction
        (first := first.commonPrefix next) nonempty
      have bothStarts := commonPrefix_starts first next index commonStarts
      exact ⟨index, bothStarts.1, by
        intro path member
        rcases List.mem_cons.mp member with rfl | member
        · exact bothStarts.2
        · exact tailStarts path member⟩

theorem deepestCommonAncestor_ne_nil_iff_commonHead
    (paths : List RegionPath) (nonempty : paths ≠ []) :
    deepestCommonAncestor paths ≠ [] ↔ CommonHead paths := by
  cases paths with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      simp only [deepestCommonAncestor, CommonHead]
      constructor
      · intro dcaNonempty
        obtain ⟨index, firstStarts, restStarts⟩ :=
          dcaFrom_ne_nil_commonHead first rest dcaNonempty
        exact ⟨index, by
          intro path member
          rcases List.mem_cons.mp member with rfl | member
          · exact firstStarts
          · exact restStarts path member⟩
      · rintro ⟨index, allStart⟩
        have resultStarts := dcaFrom_starts first rest index
          (allStart first (by simp))
          (by intro path member; exact allStart path (by simp [member]))
        rcases resultStarts with ⟨tail, equality⟩
        rw [equality]
        simp

theorem rooted_iff_not_commonHead (paths : List RegionPath) :
    (paths ≠ [] ∧ deepestCommonAncestor paths = []) ↔
      (paths ≠ [] ∧ ¬CommonHead paths) := by
  constructor
  · rintro ⟨nonempty, dcaEq⟩
    refine ⟨nonempty, ?_⟩
    intro common
    exact (deepestCommonAncestor_ne_nil_iff_commonHead paths nonempty).mpr
      common dcaEq
  · rintro ⟨nonempty, noCommon⟩
    refine ⟨nonempty, ?_⟩
    by_cases dcaEq : deepestCommonAncestor paths = []
    · exact dcaEq
    · exact False.elim (noCommon
        ((deepestCommonAncestor_ne_nil_iff_commonHead paths nonempty).mp
          dcaEq))

private theorem commonHead_replaceForward
    (before source target after : List RegionPath) (index : Nat)
    (sameEmpty : source = [] ↔ target = []) :
    CommonHead (before ++ source.map (List.cons index) ++ after) →
      CommonHead (before ++ target.map (List.cons index) ++ after) := by
  intro sourceCommon
  by_cases targetEmpty : target = []
  · have sourceEmpty := sameEmpty.mpr targetEmpty
    simpa [sourceEmpty, targetEmpty] using sourceCommon
  · have sourceNonempty : source ≠ [] := by
      intro sourceEmpty
      exact targetEmpty (sameEmpty.mp sourceEmpty)
    obtain ⟨commonIndex, allStart⟩ := sourceCommon
    obtain ⟨sourcePath, sourceMember⟩ :=
      List.exists_mem_of_ne_nil source sourceNonempty
    have mappedMember : index :: sourcePath ∈
        before ++ source.map (List.cons index) ++ after := by
      simp [sourceMember]
    obtain ⟨tail, equality⟩ := allStart _ mappedMember
    have commonEq : commonIndex = index := by
      injection equality with headEq
      exact headEq.symm
    subst commonIndex
    refine ⟨index, ?_⟩
    intro path member
    rcases List.mem_append.mp member with beforeOrTarget | afterMember
    · rcases List.mem_append.mp beforeOrTarget with beforeMember | targetMember
      · exact allStart path (List.mem_append_left _
          (List.mem_append_left _ beforeMember))
      · rcases List.mem_map.mp targetMember with ⟨targetPath, _, rfl⟩
        exact ⟨targetPath, rfl⟩
    · exact allStart path (List.mem_append_right _ afterMember)

theorem commonHead_replace
    (before source target after : List RegionPath) (index : Nat)
    (sameEmpty : source = [] ↔ target = []) :
    CommonHead (before ++ source.map (List.cons index) ++ after) ↔
      CommonHead (before ++ target.map (List.cons index) ++ after) := by
  constructor
  · exact commonHead_replaceForward before source target after index sameEmpty
  · exact commonHead_replaceForward before target source after index
      sameEmpty.symm

theorem nonempty_replace
    (before source target after : List RegionPath) (index : Nat)
    (sameEmpty : source = [] ↔ target = []) :
    before ++ source.map (List.cons index) ++ after ≠ [] ↔
      before ++ target.map (List.cons index) ++ after ≠ [] := by
  by_cases beforeEmpty : before = []
  · by_cases afterEmpty : after = []
    · simp [beforeEmpty, afterEmpty, List.map_eq_nil_iff, sameEmpty]
    · simp [afterEmpty]
  · constructor <;> intro _ <;>
      exact List.append_ne_nil_of_left_ne_nil
        (List.append_ne_nil_of_left_ne_nil beforeEmpty _) _

theorem rooted_replace
    (before source target after : List RegionPath) (index : Nat)
    (sameEmpty : source = [] ↔ target = []) :
    let sourcePaths := before ++ source.map (List.cons index) ++ after
    let targetPaths := before ++ target.map (List.cons index) ++ after
    (sourcePaths ≠ [] ∧ deepestCommonAncestor sourcePaths = []) ↔
      (targetPaths ≠ [] ∧ deepestCommonAncestor targetPaths = []) := by
  dsimp only
  rw [rooted_iff_not_commonHead, rooted_iff_not_commonHead,
    nonempty_replace before source target after index sameEmpty,
    commonHead_replace before source target after index sameEmpty]

private theorem rootedTwo_replaceForward
    (before source target after : List RegionPath) (index : Nat)
    (sameEmpty : source = [] ↔ target = [])
    (sourceRooted :
      RootedTwo (before ++ source.map (List.cons index) ++ after)) :
    RootedTwo (before ++ target.map (List.cons index) ++ after) := by
  have targetRooted := (rooted_replace before source target after index
    sameEmpty).mp ⟨sourceRooted.nonempty, sourceRooted.2⟩
  refine ⟨?_, targetRooted.2⟩
  by_cases sourceEmpty : source = []
  · have targetEmpty := sameEmpty.mp sourceEmpty
    simpa [sourceEmpty, targetEmpty] using sourceRooted.1
  · have targetNonempty : target ≠ [] := by
      intro targetEmpty
      exact sourceEmpty (sameEmpty.mpr targetEmpty)
    by_cases beforeEmpty : before = []
    · by_cases afterEmpty : after = []
      · have mappedNonempty : source.map (List.cons index) ≠ [] := by
          simpa [List.map_eq_nil_iff] using sourceEmpty
        have mappedCommon : CommonHead (source.map (List.cons index)) := by
          refine ⟨index, ?_⟩
          intro path member
          obtain ⟨sourcePath, _, rfl⟩ := List.mem_map.mp member
          exact ⟨sourcePath, rfl⟩
        have mappedDcaNonempty :=
          (deepestCommonAncestor_ne_nil_iff_commonHead _ mappedNonempty).mpr
            mappedCommon
        rw [beforeEmpty, afterEmpty] at sourceRooted
        simp only [List.nil_append, List.append_nil] at sourceRooted
        exact False.elim (mappedDcaNonempty sourceRooted.2)
      · have afterPositive : 0 < after.length :=
          List.length_pos_iff.mpr afterEmpty
        have targetPositive : 0 < target.length :=
          List.length_pos_iff.mpr targetNonempty
        simp only [List.length_append, List.length_map]
        omega
    · have beforePositive : 0 < before.length :=
        List.length_pos_iff.mpr beforeEmpty
      have targetPositive : 0 < target.length :=
        List.length_pos_iff.mpr targetNonempty
      simp only [List.length_append, List.length_map]
      omega

theorem rootedTwo_replace
    (before source target after : List RegionPath) (index : Nat)
    (sameEmpty : source = [] ↔ target = []) :
    let sourcePaths := before ++ source.map (List.cons index) ++ after
    let targetPaths := before ++ target.map (List.cons index) ++ after
    RootedTwo sourcePaths ↔ RootedTwo targetPaths := by
  dsimp only
  constructor
  · exact rootedTwo_replaceForward before source target after index sameEmpty
  · exact rootedTwo_replaceForward before target source after index
      sameEmpty.symm

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

theorem ItemSeq.incidencePaths_frame
    (before after : ItemSeq wires) (body : Region wires)
    (wireIndex itemIndex : Nat) :
    (before.append (.cons (.cut body) after)).incidencePaths
        wireIndex itemIndex =
      before.incidencePaths wireIndex itemIndex ++
        (body.incidencePaths wireIndex).map
          (List.cons (itemIndex + before.length)) ++
        after.incidencePaths wireIndex
          (itemIndex + before.length + 1) := by
  rw [ItemSeq.incidencePaths_append]
  simp [ItemSeq.incidencePaths, Item.incidencePaths, Nat.add_assoc]

theorem ItemSeq.incidencePaths_eq_nil_iff_itemIndex
    (items : ItemSeq wires) (wireIndex firstIndex secondIndex : Nat) :
    items.incidencePaths wireIndex firstIndex = [] ↔
      items.incidencePaths wireIndex secondIndex = [] := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive := fun (context : List Sig) (item : Item context) =>
    ∀ (wireIndex firstIndex secondIndex : Nat),
      item.incidencePaths wireIndex firstIndex = [] ↔
        item.incidencePaths wireIndex secondIndex = []
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    ∀ (wireIndex firstIndex secondIndex : Nat),
      items.incidencePaths wireIndex firstIndex = [] ↔
        items.incidencePaths wireIndex secondIndex = []
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (by intro _ _ _ _ _ _ _; rfl)
    (by intro _ _ _ _ _ _ _; rfl)
    (by
      intro _ body _ wireIndex firstIndex secondIndex
      simp [Item.incidencePaths, List.map_eq_nil_iff])
    (by intro _ _ _ _; rfl)
    (by
      intro _ head tail headIH tailIH wireIndex firstIndex secondIndex
      simp only [ItemSeq.incidencePaths, List.append_eq_nil_iff]
      rw [headIH wireIndex firstIndex secondIndex,
        tailIH wireIndex (firstIndex + 1) (secondIndex + 1)])
    items wireIndex firstIndex secondIndex

mutual
  /-- Every local wire has at least two actual incidences at this region's
  DCA, recursively. -/
  def Region.Canonical : Region outer → Prop
    | .mk locals items =>
        (∀ localIndex : Fin locals.length,
          let paths := items.incidencePaths (outer.length + localIndex.val) 0
          RegionPath.RootedTwo paths) ∧
        items.ChildrenCanonical

  def Item.ChildrenCanonical : Item wires → Prop
    | .atom _ _ => True
    | .identity _ _ _ => True
    | .cut body => body.Canonical

  def ItemSeq.ChildrenCanonical : ItemSeq wires → Prop
    | .nil => True
    | .cons head tail => head.ChildrenCanonical ∧ tail.ChildrenCanonical
end

mutual
  def Region.decidableCanonical : (region : Region outer) →
      Decidable region.Canonical
    | .mk locals items => by
        letI : Decidable (∀ localIndex : Fin locals.length,
            RegionPath.RootedTwo
              (items.incidencePaths (outer.length + localIndex.val) 0)) :=
          VisualProof.Data.Finite.decidableForallFin _ fun _ => inferInstance
        letI : Decidable items.ChildrenCanonical :=
          ItemSeq.decidableChildrenCanonical items
        simp only [Region.Canonical]
        infer_instance

  def Item.decidableChildrenCanonical : (item : Item wires) →
      Decidable item.ChildrenCanonical
    | .atom _ _ => isTrue trivial
    | .identity _ _ _ => isTrue trivial
    | .cut body => Region.decidableCanonical body

  def ItemSeq.decidableChildrenCanonical : (items : ItemSeq wires) →
      Decidable items.ChildrenCanonical
    | .nil => isTrue trivial
    | .cons head tail => by
        letI : Decidable head.ChildrenCanonical :=
          Item.decidableChildrenCanonical head
        letI : Decidable tail.ChildrenCanonical :=
          ItemSeq.decidableChildrenCanonical tail
        simp only [ItemSeq.ChildrenCanonical]
        infer_instance
end

instance (region : Region outer) : Decidable region.Canonical :=
  Region.decidableCanonical region

instance (item : Item wires) : Decidable item.ChildrenCanonical :=
  Item.decidableChildrenCanonical item

instance (items : ItemSeq wires) : Decidable items.ChildrenCanonical :=
  ItemSeq.decidableChildrenCanonical items

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
            have rooted := canonical.1 wire.index
            exact ⟨rooted.nonempty, rooted.2⟩
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
