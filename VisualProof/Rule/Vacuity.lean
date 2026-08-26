import VisualProof.Diagram.Scope.Rename
import VisualProof.Diagram.Scope.Context
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Vacuity

private theorem DiagramContext.outerWire_index
    (context : DiagramContext outer holeWires)
    (wire : Var outer signature) :
    (context.outerWire wire).index.val = wire.index.val := by
  induction context with
  | hole => simp [DiagramContext.outerWire, WireRenaming.id]
  | @cut currentOuter currentHole locals leading trailing child induction =>
      change (child.outerWire (wire.appendLeft locals)).index.val = wire.index.val
      rw [induction]
      simp

namespace Point

def plain (locals : List Sig)
    (items : ItemSeq (outer ++ locals)) : Region outer :=
  .mk locals items

def present (locals : List Sig)
    (items : ItemSeq (outer ++ locals)) (signature : Sig) : Region outer :=
  .mk locals (items.append (.cons (.identity signature 0 Fin.elim0) .nil))

private theorem incidencePaths_eq (locals : List Sig)
    (items : ItemSeq (outer ++ locals)) (signature : Sig) (wireIndex : Nat) :
    (present locals items signature).incidencePaths wireIndex =
      (plain locals items).incidencePaths wireIndex := by
  simp [present, plain, Region.incidencePaths,
    ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
    Item.incidencePaths]

private theorem canonical_iff (locals : List Sig)
    (items : ItemSeq (outer ++ locals)) (signature : Sig) :
    (present locals items signature).Canonical ↔
      (plain locals items).Canonical := by
  simp only [present, plain, Region.Canonical]
  rw [ItemSeq.childrenCanonical_append]
  simp only [ItemSeq.ChildrenCanonical, Item.ChildrenCanonical, and_true]
  constructor
  · rintro ⟨roots, children⟩
    refine ⟨fun localIndex => ?_, children⟩
    have rooted := roots localIndex
    simpa [ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
      Item.incidencePaths] using rooted
  · rintro ⟨roots, children⟩
    refine ⟨fun localIndex => ?_, children⟩
    simpa [ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
      Item.incidencePaths] using roots localIndex

end Point

namespace Pin

def plain (locals : List Sig)
    (items : ItemSeq (outer ++ locals)) : Region outer :=
  .mk locals items

def present (locals : List Sig)
    (items : ItemSeq (outer ++ locals))
    (signature : Sig) (wire : Var (outer ++ locals) signature) : Region outer :=
  .mk locals (items.append
    (.cons (.identity signature 1 (fun _ => wire)) .nil))

/-- The same unary pin presentation with the pin placed first. -/
def front (locals : List Sig)
    (items : ItemSeq (outer ++ locals))
    (signature : Sig) (wire : Var (outer ++ locals) signature) : Region outer :=
  .mk locals (.cons (.identity signature 1 (fun _ => wire)) items)

private theorem canonical (locals : List Sig)
    (items : ItemSeq (outer ++ locals))
    (signature : Sig) (wire : Var (outer ++ locals) signature)
    (sourceCanonical : (plain locals items).Canonical) :
    (present locals items signature wire).Canonical := by
  change (Region.mk locals items).Canonical at sourceCanonical
  change (Region.mk locals (items.append
    (.cons (.identity signature 1 (fun _ => wire)) .nil))).Canonical
  simp only [Region.Canonical] at sourceCanonical ⊢
  rcases sourceCanonical with ⟨roots, children⟩
  constructor
  · intro localIndex
    have rooted := roots localIndex
    rw [ItemSeq.incidencePaths_append]
    simp only [ItemSeq.incidencePaths, Item.incidencePaths]
    exact ⟨Nat.le_trans rooted.1 (by simp),
      RegionPath.deepestCommonAncestor_append_eq_nil _ _
        rooted.nonempty rooted.2⟩
  · rw [ItemSeq.childrenCanonical_append]
    exact ⟨children, by simp [ItemSeq.ChildrenCanonical,
      Item.ChildrenCanonical]⟩

theorem frontCanonical (locals : List Sig)
    (items : ItemSeq (outer ++ locals))
    (signature : Sig) (wire : Var (outer ++ locals) signature)
    (sourceCanonical : (present locals items signature wire).Canonical) :
    (front locals items signature wire).Canonical := by
  simp only [present, front, Region.Canonical] at sourceCanonical ⊢
  constructor
  · intro localIndex
    have sourceRoot := sourceCanonical.1 localIndex
    by_cases selected : wire.index.val = outer.length + localIndex.val
    · have sourcePaths :
          (items.append
            (.cons (.identity signature 1 (fun _ => wire)) .nil)).incidencePaths
              (outer.length + localIndex.val) 0 =
            items.incidencePaths (outer.length + localIndex.val) 0 ++ [[]] := by
        simp [ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
          Item.incidencePaths, selected]
      rw [sourcePaths] at sourceRoot
      have targetPaths :
          (.cons (.identity signature 1 (fun _ => wire)) items :
            ItemSeq (outer ++ locals)).incidencePaths
              (outer.length + localIndex.val) 0 =
            [] :: items.incidencePaths (outer.length + localIndex.val) 1 := by
        simp [ItemSeq.incidencePaths, Item.incidencePaths, selected]
      rw [targetPaths]
      have oldLength :
          (items.incidencePaths (outer.length + localIndex.val) 1).length =
            (items.incidencePaths
              (outer.length + localIndex.val) 0).length := by
        have shifted := ItemSeq.incidencePaths_add_itemIndex items
          (outer.length + localIndex.val) 0 1
        simpa only [Nat.zero_add, List.length_map] using congrArg List.length shifted
      constructor
      · simp only [List.length_cons]
        have sourceLength := sourceRoot.1
        simp only [List.length_append, List.length_singleton] at sourceLength
        omega
      · exact RegionPath.deepestCommonAncestor_cons_nil _
    · have oldRoot : RegionPath.RootedTwo
          (items.incidencePaths (outer.length + localIndex.val) 0) := by
        simpa [ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
          Item.incidencePaths, selected] using sourceRoot
      have shiftedRoot :=
        (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff
          items (outer.length + localIndex.val) 0 1).mpr oldRoot
      simpa [ItemSeq.incidencePaths, Item.incidencePaths, selected] using
        shiftedRoot
  · have children := sourceCanonical.2
    have itemChildren :
        (Item.identity signature 1 (fun _ => wire)).ChildrenCanonical :=
      True.intro
    have oldChildren :=
      (ItemSeq.childrenCanonical_append _ _).mp children |>.1
    exact ⟨itemChildren, oldChildren⟩

theorem present_front_incidence_nonempty_iff
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (signature : Sig) (selected : Var (outer ++ locals) signature)
    (wireIndex : Nat) :
    (present locals items signature selected).incidencePaths wireIndex ≠ [] ↔
      (front locals items signature selected).incidencePaths wireIndex ≠ [] := by
  simp only [present, front, Region.incidencePaths,
    ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
    List.append_nil, Nat.zero_add]
  have shiftedEmpty := ItemSeq.incidencePaths_eq_nil_iff_itemIndex
    items wireIndex 0 1
  constructor <;> intro nonempty empty
  · apply nonempty
    apply List.append_eq_nil_iff.mpr
    exact ⟨shiftedEmpty.mpr (List.append_eq_nil_iff.mp empty).2,
      (List.append_eq_nil_iff.mp empty).1⟩
  · apply nonempty
    apply List.append_eq_nil_iff.mpr
    exact ⟨(List.append_eq_nil_iff.mp empty).2,
      shiftedEmpty.mp (List.append_eq_nil_iff.mp empty).1⟩

private theorem incidencePaths_sublist (locals : List Sig)
    (items : ItemSeq (outer ++ locals))
    (signature : Sig) (selected : Var (outer ++ locals) signature)
    (wireIndex : Nat) :
    (plain locals items).incidencePaths wireIndex |>.Sublist
      ((present locals items signature selected).incidencePaths wireIndex) := by
  simp only [plain, present, Region.incidencePaths,
    ItemSeq.incidencePaths_append]
  exact List.sublist_append_left _ _

private theorem fill_incidencePaths_sublist
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (selected : Var (holeWires ++ locals) signature)
    (wireIndex : Nat) :
    (context.fill (plain locals items)).incidencePaths wireIndex |>.Sublist
      ((context.fill (present locals items signature selected)).incidencePaths
        wireIndex) := by
  induction context with
  | hole => exact incidencePaths_sublist _ _ _ _ _
  | @cut currentOuter currentHole contextLocals leading trailing child induction =>
      simp only [DiagramContext.fill, Region.incidencePaths,
        ItemSeq.incidencePaths_frame]
      simpa only [Nat.zero_add] using ((List.Sublist.refl
        (leading.incidencePaths wireIndex 0)).append
        ((induction items selected).map
          (List.cons leading.length))).append
            (List.Sublist.refl
              (trailing.incidencePaths wireIndex (leading.length + 1)))

private theorem fillCanonical
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (selected : Var (holeWires ++ locals) signature)
    (sourceCanonical : (context.fill (plain locals items)).Canonical) :
    (context.fill (present locals items signature selected)).Canonical := by
  induction context with
  | hole => exact canonical _ _ _ _ sourceCanonical
  | @cut currentOuter currentHole contextLocals leading trailing child induction =>
      have sourceChildren := sourceCanonical.2
      have leadingAndRest := (ItemSeq.childrenCanonical_append leading
        (.cons (.cut (child.fill (plain locals items))) trailing)).mp
          sourceChildren
      have childCanonical := induction items selected leadingAndRest.2.1
      constructor
      · intro localIndex
        exact RegionPath.RootedTwo.of_sublist
          (fill_incidencePaths_sublist
            (.cut contextLocals leading trailing child)
            locals items signature selected
            (currentOuter.length + localIndex.val))
          (sourceCanonical.1 localIndex)
      · apply (ItemSeq.childrenCanonical_append leading
          (.cons (.cut (child.fill
            (present locals items signature selected))) trailing)).mpr
        exact ⟨leadingAndRest.1, ⟨childCanonical, leadingAndRest.2.2⟩⟩

private theorem fillExternalTwoEnded
    (boundaryWire : Vars outer boundary)
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (selected : Var (holeWires ++ locals) signature)
    (sourceTwoEnded : OpenDiagram.ExternalTwoEnded boundaryWire
      (context.fill (plain locals items))) :
    OpenDiagram.ExternalTwoEnded boundaryWire
      (context.fill (present locals items signature selected)) := by
  intro wireSignature wire
  have pathSublist := fill_incidencePaths_sublist context locals items
    signature selected wire.index.val
  have sourceFloor := sourceTwoEnded wire
  exact Nat.le_trans sourceFloor (Nat.add_le_add_left pathSublist.length_le _)

private theorem incidencePaths_eq_of_ne (locals : List Sig)
    (items : ItemSeq (outer ++ locals))
    (signature : Sig) (selected : Var (outer ++ locals) signature)
    (wireIndex : Nat) (different : selected.index.val ≠ wireIndex) :
    (present locals items signature selected).incidencePaths wireIndex =
      (plain locals items).incidencePaths wireIndex := by
  simp [present, plain, Region.incidencePaths,
    ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
    Item.incidencePaths, different]

private theorem fill_incidencePaths_eq_of_ne
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (selected : Var (holeWires ++ locals) signature)
    (wire : Var outer wireSignature)
    (different : selected.index.val ≠
      ((context.outerWire wire).appendLeft locals).index.val) :
    (context.fill (present locals items signature selected)).incidencePaths
        wire.index.val =
      (context.fill (plain locals items)).incidencePaths wire.index.val := by
  induction context with
  | hole =>
      have different' : selected.index.val ≠ wire.index.val := by
        simpa [DiagramContext.outerWire, WireRenaming.id] using different
      simpa [DiagramContext.outerWire, WireRenaming.id] using
        incidencePaths_eq_of_ne locals items signature selected
          wire.index.val different'
  | @cut currentOuter currentHole contextLocals leading trailing child induction =>
      have childDifferent : selected.index.val ≠
          ((child.outerWire (wire.appendLeft contextLocals)).appendLeft locals).index.val := by
        simpa [DiagramContext.outerWire, WireRenaming.comp_apply] using different
      have childEq := induction items selected (wire.appendLeft contextLocals)
        childDifferent
      have childEq' :
          (child.fill (present locals items signature selected)).incidencePaths
              wire.index.val =
            (child.fill (plain locals items)).incidencePaths wire.index.val := by
        simpa using childEq
      simp only [DiagramContext.fill, Region.incidencePaths,
        ItemSeq.incidencePaths_frame]
      rw [childEq']

def ContextDCAGuard
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (selected : Var (holeWires ++ locals) signature) : Prop :=
  match context with
  | .hole => True
  | @DiagramContext.cut currentOuter currentHole contextLocals leading trailing child =>
      (∀ localIndex : Fin contextLocals.length,
        selected.index.val =
            ((child.outerWire (Var.appendRight currentOuter
              (Var.ofIndex localIndex))).appendLeft locals).index.val →
          RegionPath.RootedTwo
            ((DiagramContext.cut contextLocals leading trailing child |>.fill
              (plain locals items)).incidencePaths
                (currentOuter.length + localIndex.val))) ∧
        ContextDCAGuard child locals items signature selected

structure DeletionGuard
    {holeWires : List Sig} {items : ItemSeq (holeWires ++ locals)}
    {signature : Sig} {selected : Var (holeWires ++ locals) signature}
    (occurrence : Occurrence
      (present locals items signature selected) source) : Prop where
  localDCA : ∀ localIndex : Fin locals.length,
    selected.index.val = holeWires.length + localIndex.val →
      RegionPath.RootedTwo
        ((plain locals items).incidencePaths
          (holeWires.length + localIndex.val))
  ancestorDCA : ContextDCAGuard occurrence.context locals items signature selected
  externalTwoEnded : ∀ {wireSignature}
      (wire : Var occurrence.interface.external wireSignature),
    selected.index.val =
        ((occurrence.context.outerWire wire).appendLeft locals).index.val →
      2 ≤ occurrence.interface.boundaryWire.countIndex wire.index.val +
        ((occurrence.context.fill (plain locals items)).incidencePaths
          wire.index.val).length

private theorem plainCanonical_of_guard
    (locals : List Sig) (items : ItemSeq (outer ++ locals))
    (signature : Sig) (selected : Var (outer ++ locals) signature)
    (sourceCanonical : (present locals items signature selected).Canonical)
    (localDCA : ∀ localIndex : Fin locals.length,
      selected.index.val = outer.length + localIndex.val →
        RegionPath.RootedTwo ((plain locals items).incidencePaths
          (outer.length + localIndex.val))) :
    (plain locals items).Canonical := by
  constructor
  · intro localIndex
    by_cases equal : selected.index.val = outer.length + localIndex.val
    · exact localDCA localIndex equal
    · have sourceRoot := sourceCanonical.1 localIndex
      simpa [present, plain, Region.incidencePaths,
        ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
        Item.incidencePaths, equal] using sourceRoot
  · have sourceChildren := sourceCanonical.2
    change (items.append
      (.cons (.identity signature 1 (fun _ => selected)) .nil)).ChildrenCanonical
      at sourceChildren
    exact (ItemSeq.childrenCanonical_append _ _).mp sourceChildren |>.1

private theorem fillCanonical_of_guard
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (selected : Var (holeWires ++ locals) signature)
    (sourceCanonical :
      (context.fill (present locals items signature selected)).Canonical)
    (localCanonical : (plain locals items).Canonical)
    (guard : ContextDCAGuard context locals items signature selected) :
    (context.fill (plain locals items)).Canonical := by
  induction context with
  | hole => exact localCanonical
  | @cut currentOuter currentHole contextLocals leading trailing child induction =>
      have sourceChildren := sourceCanonical.2
      have leadingAndRest := (ItemSeq.childrenCanonical_append leading
        (.cons (.cut (child.fill
          (present locals items signature selected))) trailing)).mp sourceChildren
      have childCanonical := induction items selected leadingAndRest.2.1
        localCanonical guard.2
      constructor
      · intro localIndex
        let localWire := Var.appendRight currentOuter (Var.ofIndex localIndex)
        by_cases equal : selected.index.val =
            ((child.outerWire localWire).appendLeft locals).index.val
        · exact guard.1 localIndex equal
        · have childEq := fill_incidencePaths_eq_of_ne child locals items
              signature selected localWire equal
          have sourceRoot := sourceCanonical.1 localIndex
          simp only [ItemSeq.incidencePaths_frame] at sourceRoot ⊢
          have childEq' :
              (child.fill (present locals items signature selected)).incidencePaths
                  (currentOuter.length + localIndex.val) =
                (child.fill (plain locals items)).incidencePaths
                  (currentOuter.length + localIndex.val) := by
            simpa [localWire] using childEq
          rwa [childEq'] at sourceRoot
      · apply (ItemSeq.childrenCanonical_append leading
          (.cons (.cut (child.fill
            (plain locals items))) trailing)).mpr
        exact ⟨leadingAndRest.1, ⟨childCanonical, leadingAndRest.2.2⟩⟩

private theorem contextDCAGuard_inherited
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (wire : Var outer signature) :
    ContextDCAGuard context locals items signature
      ((context.outerWire wire).appendLeft locals) := by
  induction context with
  | hole => trivial
  | @cut currentOuter currentHole contextLocals leading trailing child induction =>
      constructor
      · intro localIndex equal
        have inheritedBound := wire.index.isLt
        have leftEq :
            (((DiagramContext.cut contextLocals leading trailing child).outerWire
              wire).appendLeft locals).index.val = wire.index.val := by
          rw [Var.index_appendLeft, DiagramContext.outerWire_index]
        have rightEq :
            ((child.outerWire (Var.appendRight currentOuter
              (Var.ofIndex localIndex))).appendLeft locals).index.val =
                currentOuter.length + localIndex.val := by
          rw [Var.index_appendLeft, DiagramContext.outerWire_index]
          simp
        have impossible : currentOuter.length ≤ wire.index.val := by omega
        exact False.elim (Nat.not_le_of_lt inheritedBound impossible)
      · simpa [DiagramContext.outerWire, WireRenaming.comp_apply] using
          induction items (wire.appendLeft contextLocals)

private theorem fillCanonical_iff_inherited
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (wire : Var outer signature) :
    (context.fill (present locals items signature
      ((context.outerWire wire).appendLeft locals))).Canonical ↔
        (context.fill (plain locals items)).Canonical := by
  constructor
  · intro sourceCanonical
    have localSource := context.holeCanonical _ sourceCanonical
    have localTarget := plainCanonical_of_guard locals items signature
      ((context.outerWire wire).appendLeft locals) localSource (by
        intro localIndex equal
        have inheritedBound := (context.outerWire wire).index.isLt
        have equality : (context.outerWire wire).index.val =
            holeWires.length + localIndex.val := by simpa using equal
        have impossible : holeWires.length ≤
            (context.outerWire wire).index.val := by
          omega
        exact False.elim (Nat.not_le_of_lt inheritedBound impossible))
    exact fillCanonical_of_guard context locals items signature
      ((context.outerWire wire).appendLeft locals) sourceCanonical localTarget
      (contextDCAGuard_inherited context locals items signature wire)
  · exact fillCanonical context locals items signature
      ((context.outerWire wire).appendLeft locals)

private theorem fill_incidencePaths_length_inherited
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (wire : Var outer signature) :
    ((context.fill (present locals items signature
      ((context.outerWire wire).appendLeft locals))).incidencePaths
        wire.index.val).length =
      ((context.fill (plain locals items)).incidencePaths
        wire.index.val).length + 1 := by
  induction context with
  | hole =>
      simp [DiagramContext.fill, present, plain, Region.incidencePaths,
        ItemSeq.incidencePaths_append, ItemSeq.incidencePaths,
        Item.incidencePaths, DiagramContext.outerWire, WireRenaming.id]
  | @cut currentOuter currentHole contextLocals leading trailing child induction =>
      simp only [DiagramContext.fill, Region.incidencePaths,
        ItemSeq.incidencePaths_frame, List.length_append, List.length_map]
      have childLength := induction items (wire.appendLeft contextLocals)
      have childLength' :
          ((child.fill (present locals items signature
            ((((DiagramContext.cut contextLocals leading trailing child).outerWire
              wire)).appendLeft locals))).incidencePaths wire.index.val).length =
            ((child.fill (plain locals items)).incidencePaths
              wire.index.val).length + 1 := by
        simpa [DiagramContext.outerWire, WireRenaming.comp_apply] using childLength
      omega

end Pin

namespace Stub

def plain (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature) : Region outer :=
  .mk hostLocals
    (before.append (.cons (.identity signature arity ports) after))

def hostRename (outer hostLocals : List Sig) (signature : Sig) :
    WireRenaming (outer ++ hostLocals)
      (outer ++ (hostLocals ++ [signature])) :=
  Region.adjoinHostWire outer hostLocals [signature]

def freshWire (outer hostLocals : List Sig) (signature : Sig) :
    Var (outer ++ (hostLocals ++ [signature])) signature :=
  Var.appendRight outer (Var.appendRight hostLocals Var.here)

private theorem hostRename_index
    (wire : Var (outer ++ hostLocals) wireSignature) :
    (hostRename outer hostLocals signature wire).index.val = wire.index.val := by
  apply Var.appendCases (left := outer) (right := hostLocals)
    (motive := fun wire =>
      (hostRename outer hostLocals signature wire).index.val = wire.index.val)
  · intros
    simp [hostRename, Region.adjoinHostWire, Region.conjoinLeftWire]
  · intros
    simp [hostRename, Region.adjoinHostWire, Region.conjoinLeftWire]

private theorem length_renameWires (items : ItemSeq source)
    (rename : WireRenaming source target) :
    (items.renameWires rename).length = items.length := by
  let regionMotive : ∀ context, Region context → Prop := fun _ _ => True
  let itemMotive : ∀ context, Item context → Prop := fun _ _ => True
  let itemsMotive := fun (context : List Sig) (items : ItemSeq context) =>
    ∀ {target} (rename : WireRenaming context target),
      (items.renameWires rename).length = items.length
  exact ItemSeq.rec (motive_1 := regionMotive) (motive_2 := itemMotive)
    (motive_3 := itemsMotive)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (by intro source target rename; rfl)
    (by
      intro source head tail headIH tailIH target rename
      simp only [ItemSeq.renameWires, ItemSeq.length]
      rw [tailIH rename])
    items rename

def insertPort (position : Fin (arity + 1)) (fresh : α)
    (ports : Fin arity → α) : Fin (arity + 1) → α := fun index =>
  ((List.ofFn ports).insertIdx position.val fresh)[index.val]'(by
    rw [List.length_insertIdx]
    have positionLe : position.val ≤ arity := by omega
    simp [positionLe])

theorem ofFn_insertPort (position : Fin (arity + 1))
    (fresh : α) (ports : Fin arity → α) :
    List.ofFn (insertPort position fresh ports) =
      (List.ofFn ports).insertIdx position.val fresh := by
  have positionLe : position.val ≤ arity := by omega
  have lengthEq : ((List.ofFn ports).insertIdx position.val fresh).length =
      arity + 1 := by simp [List.length_insertIdx, positionLe]
  have lengths : (List.ofFn (insertPort position fresh ports)).length =
      ((List.ofFn ports).insertIdx position.val fresh).length := by
    simp [lengthEq]
  apply List.ext_getElem lengths
  intro index left right
  rw [List.getElem_ofFn]
  rfl

private theorem map_insertIdx (list : List α) (position : Nat) (fresh : α)
    (map : α → β) (bound : position ≤ list.length) :
    List.map map (list.insertIdx position fresh) =
      (List.map map list).insertIdx position (map fresh) := by
  induction list generalizing position with
  | nil =>
      simp only [List.length_nil] at bound
      have : position = 0 := by omega
      subst position
      simp [List.insertIdx_zero]
  | cons head tail induction =>
      cases position with
      | zero => simp [List.insertIdx_zero]
      | succ position =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at bound
          rw [List.insertIdx_succ_cons, List.map_cons,
            List.map_cons, List.insertIdx_succ_cons, induction position bound]

private theorem ofFn_map_insertPort (position : Fin (arity + 1))
    (fresh : α) (ports : Fin arity → α) (map : α → β) :
    List.ofFn (fun index => map (insertPort position fresh ports index)) =
      (List.ofFn (fun index => map (ports index))).insertIdx
        position.val (map fresh) := by
  have equality := congrArg (List.map map)
    (ofFn_insertPort position fresh ports)
  have positionLe : position.val ≤ (List.ofFn ports).length := by simp; omega
  rw [map_insertIdx _ _ _ _ positionLe] at equality
  simpa only [List.map_ofFn, Function.comp_apply] using equality

private theorem count_insertIdx [BEq α]
    (list : List α) (position : Nat) (fresh selected : α)
    (bound : position ≤ list.length) :
    (list.insertIdx position fresh).count selected =
      list.count selected + (if fresh == selected then 1 else 0) := by
  induction list generalizing position with
  | nil =>
      simp only [List.length_nil] at bound
      have : position = 0 := by omega
      subst position
      simp [List.insertIdx_zero, List.count_cons]
  | cons head tail induction =>
      cases position with
      | zero =>
          simp [List.insertIdx_zero, List.count_cons,
            Nat.add_left_comm, Nat.add_comm]
      | succ position =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at bound
          rw [List.insertIdx_succ_cons, List.count_cons,
            induction position bound, List.count_cons]
          omega

def extendedItems (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1)) :
    ItemSeq (outer ++ (hostLocals ++ [signature])) :=
  let rename := hostRename outer hostLocals signature
  let fresh := freshWire outer hostLocals signature
  (before.renameWires rename).append
    (.cons
      (.identity signature (arity + 1)
        (insertPort position fresh (fun index => rename (ports index))))
      (after.renameWires rename))

private theorem extendedItems_incidencePaths_old
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (wire : Var (outer ++ hostLocals) wireSignature) (itemIndex : Nat) :
    (extendedItems hostLocals before after signature arity ports position).incidencePaths
        wire.index.val itemIndex =
      (before.append (.cons (.identity signature arity ports) after)).incidencePaths
        wire.index.val itemIndex := by
  simp only [extendedItems, ItemSeq.incidencePaths_append,
    ItemSeq.incidencePaths, Item.incidencePaths]
  simp only [hostRename]
  rw [ItemSeq.incidencePaths_renameWires_adjoinHost,
    ItemSeq.incidencePaths_renameWires_adjoinHost]
  have insertedIndices :
      (List.ofFn fun index =>
        (insertPort position (freshWire outer hostLocals signature)
          (fun index => (Region.adjoinHostWire outer hostLocals [signature])
            (ports index)) index).index.val) =
        (List.ofFn fun index =>
          ((Region.adjoinHostWire outer hostLocals [signature])
            (ports index)).index.val).insertIdx position.val
          (freshWire outer hostLocals signature).index.val :=
    ofFn_map_insertPort position (freshWire outer hostLocals signature)
      (fun index => (Region.adjoinHostWire outer hostLocals [signature])
        (ports index)) (fun wire => wire.index.val)
  have positionLe : position.val ≤
      (List.ofFn fun index =>
        ((Region.adjoinHostWire outer hostLocals [signature])
          (ports index)).index.val).length := by simp; omega
  rw [insertedIndices, count_insertIdx _ _ _ _ positionLe]
  have portIndices :
      (List.ofFn fun index : Fin arity =>
        ((Region.adjoinHostWire outer hostLocals [signature])
          (ports index)).index.val) =
        List.ofFn fun index : Fin arity => (ports index).index.val := by
    apply congrArg List.ofFn
    funext index
    exact hostRename_index (signature := signature) (ports index)
  rw [portIndices]
  have freshNe : wire.index.val ≠ outer.length + hostLocals.length := by
    have wireBound := wire.index.isLt
    simp only [List.length_append] at wireBound
    omega
  have freshNe' : outer.length + hostLocals.length ≠ wire.index.val :=
    Ne.symm freshNe
  simp [freshWire, Region.adjoinHostWire, Region.conjoinLeftWire,
    length_renameWires, freshNe']

private theorem extendedItems_childrenCanonical_iff
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1)) :
    (extendedItems hostLocals before after signature arity ports position).ChildrenCanonical ↔
      (before.append (.cons (.identity signature arity ports) after)).ChildrenCanonical := by
  simp only [extendedItems, ItemSeq.childrenCanonical_append,
    ItemSeq.ChildrenCanonical, Item.ChildrenCanonical]
  simp only [hostRename]
  rw [ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff,
    ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff]

private theorem extendedItems_fresh_mem_nil
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (itemIndex : Nat) :
    [] ∈ (extendedItems hostLocals before after signature arity ports position).incidencePaths
      (freshWire outer hostLocals signature).index.val itemIndex := by
  simp only [extendedItems, ItemSeq.incidencePaths_append,
    ItemSeq.incidencePaths, Item.incidencePaths, List.mem_append]
  right
  left
  have insertedIndices :
      (List.ofFn fun index =>
        (insertPort position (freshWire outer hostLocals signature)
          (fun index => hostRename outer hostLocals signature
            (ports index)) index).index.val) =
        (List.ofFn fun index =>
          (hostRename outer hostLocals signature (ports index)).index.val).insertIdx
            position.val (freshWire outer hostLocals signature).index.val :=
    ofFn_map_insertPort position (freshWire outer hostLocals signature)
      (fun index => hostRename outer hostLocals signature (ports index))
      (fun wire => wire.index.val)
  have positionLe : position.val ≤
      (List.ofFn fun index =>
        (hostRename outer hostLocals signature (ports index)).index.val).length := by
    simp
    omega
  rw [insertedIndices, count_insertIdx _ _ _ _ positionLe]
  simp [freshWire]

inductive Far
    (wire : Var baseWires signature)
    (items : ItemSeq baseWires) : Type
  | atBase
      : Far wire items
  | below
      (before after : ItemSeq baseWires)
      {body : Region baseWires}
      (focus : before.append (.cons (.cut body) after) = items)
      (descendant : DiagramContext baseWires farWires)
      (farLocals : List Sig)
      (farItems : ItemSeq (farWires ++ farLocals))
      (bodyEq : descendant.fill
        (.mk farLocals farItems) = body) :
      Far wire items

def Far.result
    {baseWires : List Sig} {signature : Sig}
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Far wire items) : ItemSeq baseWires :=
  match far with
  | .atBase =>
      items.append (.cons (.identity signature 1 (fun _ => wire)) .nil)
  | .below before after _ descendant farLocals farItems _ =>
      let farWire := descendant.outerWire wire
      let farBody := .mk farLocals (farItems.append
        (.cons (.identity signature 1
          (fun _ => farWire.appendLeft farLocals)) .nil))
      before.append (.cons (.cut (descendant.fill farBody)) after)

private theorem Far.incidencePaths_eq_of_ne
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Far wire items) (other : Var baseWires otherSignature)
    (different : wire.index.val ≠ other.index.val) (itemIndex : Nat) :
    far.result.incidencePaths other.index.val itemIndex =
      items.incidencePaths other.index.val itemIndex := by
  cases far with
  | atBase =>
      simp [Far.result, ItemSeq.incidencePaths_append,
        ItemSeq.incidencePaths, Item.incidencePaths, different]
  | below before after focus descendant farLocals farItems bodyEq =>
      subst items
      simp only [Far.result, ItemSeq.incidencePaths_frame]
      have selectedDifferent :
          ((descendant.outerWire wire).appendLeft farLocals).index.val ≠
            ((descendant.outerWire other).appendLeft farLocals).index.val := by
        simpa [DiagramContext.outerWire_index] using different
      have childEq := Pin.fill_incidencePaths_eq_of_ne descendant
        farLocals farItems signature
        ((descendant.outerWire wire).appendLeft farLocals) other
        selectedDifferent
      simp only [Pin.present, Pin.plain] at childEq
      rw [childEq]
      rw [bodyEq]

private theorem Far.childrenCanonical_iff
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Far wire items) :
    far.result.ChildrenCanonical ↔ items.ChildrenCanonical := by
  cases far with
  | atBase =>
      simp [Far.result, ItemSeq.childrenCanonical_append,
        ItemSeq.ChildrenCanonical, Item.ChildrenCanonical]
  | below before after focus descendant farLocals farItems bodyEq =>
      subst items
      simp only [Far.result, ItemSeq.childrenCanonical_append,
        ItemSeq.ChildrenCanonical, Item.ChildrenCanonical]
      have childIff := Pin.fillCanonical_iff_inherited descendant
        farLocals farItems signature wire
      simp only [Pin.present, Pin.plain] at childIff
      rw [childIff, bodyEq]

private theorem Far.incidencePaths_sublist
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Far wire items) (itemIndex : Nat) :
    (items.incidencePaths wire.index.val itemIndex).Sublist
      (far.result.incidencePaths wire.index.val itemIndex) := by
  cases far with
  | atBase =>
      simp only [Far.result, ItemSeq.incidencePaths_append]
      exact List.sublist_append_left _ _
  | below before after focus descendant farLocals farItems bodyEq =>
      subst items
      simp only [Far.result, ItemSeq.incidencePaths_frame]
      have childSublist := Pin.fill_incidencePaths_sublist descendant
        farLocals farItems signature
        ((descendant.outerWire wire).appendLeft farLocals) wire.index.val
      simp only [Pin.present, Pin.plain] at childSublist
      rw [bodyEq] at childSublist
      exact ((List.Sublist.refl
        (before.incidencePaths wire.index.val itemIndex)).append
          (childSublist.map (List.cons (itemIndex + before.length)))).append
            (List.Sublist.refl (after.incidencePaths wire.index.val
              (itemIndex + before.length + 1)))

private theorem Far.incidencePaths_length
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Far wire items) (itemIndex : Nat) :
    (far.result.incidencePaths wire.index.val itemIndex).length =
      (items.incidencePaths wire.index.val itemIndex).length + 1 := by
  cases far with
  | atBase =>
      simp [Far.result, ItemSeq.incidencePaths_append,
        ItemSeq.incidencePaths, Item.incidencePaths]
  | below before after focus descendant farLocals farItems bodyEq =>
      subst items
      simp only [Far.result, ItemSeq.incidencePaths_frame,
        List.length_append, List.length_map]
      have childLength := Pin.fill_incidencePaths_length_inherited descendant
        farLocals farItems signature wire
      simp only [Pin.present, Pin.plain] at childLength
      rw [bodyEq] at childLength
      omega

private theorem Far.freshRootedTwo
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Far wire items) (sourceRoot : [] ∈
      items.incidencePaths wire.index.val 0) :
    RegionPath.RootedTwo
      (far.result.incidencePaths wire.index.val 0) := by
  have sourceNonempty : items.incidencePaths wire.index.val 0 ≠ [] :=
    List.ne_nil_of_mem sourceRoot
  have targetRoot := far.incidencePaths_sublist 0 |>.mem sourceRoot
  constructor
  · rw [far.incidencePaths_length 0]
    exact Nat.succ_le_succ (List.length_pos_iff.mpr sourceNonempty)
  · exact RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _ targetRoot

def present (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (far : Far (freshWire outer hostLocals signature)
      (extendedItems hostLocals before after signature arity ports position)) :
    Region outer :=
  .mk (hostLocals ++ [signature]) far.result

private theorem present_incidencePaths_old
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (far : Far (freshWire outer hostLocals signature)
      (extendedItems hostLocals before after signature arity ports position))
    (wire : Var (outer ++ hostLocals) wireSignature) :
    (present hostLocals before after signature arity ports position far).incidencePaths
        wire.index.val =
      (plain hostLocals before after signature arity ports).incidencePaths
        wire.index.val := by
  have different : (freshWire outer hostLocals signature).index.val ≠
      (hostRename outer hostLocals signature wire).index.val := by
    have wireBound := wire.index.isLt
    rw [hostRename_index]
    simp only [freshWire, Var.index_appendRight]
    simp only [List.length_append] at wireBound
    omega
  have farEq := far.incidencePaths_eq_of_ne
    (hostRename outer hostLocals signature wire) different 0
  have extendedEq := extendedItems_incidencePaths_old hostLocals before after
    signature arity ports position wire 0
  simp only [present, plain, Region.incidencePaths, hostRename_index] at farEq ⊢
  exact farEq.trans extendedEq

private theorem present_childrenCanonical_iff
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (far : Far (freshWire outer hostLocals signature)
      (extendedItems hostLocals before after signature arity ports position)) :
    (present hostLocals before after signature arity ports position far).items.ChildrenCanonical ↔
      (plain hostLocals before after signature arity ports).items.ChildrenCanonical := by
  exact (far.childrenCanonical_iff).trans
    (extendedItems_childrenCanonical_iff hostLocals before after
      signature arity ports position)

private theorem canonical_iff
    (hostLocals : List Sig)
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1))
    (far : Far (freshWire outer hostLocals signature)
      (extendedItems hostLocals before after signature arity ports position)) :
    (present hostLocals before after signature arity ports position far).Canonical ↔
      (plain hostLocals before after signature arity ports).Canonical := by
  constructor
  · rintro ⟨presentRoots, presentChildren⟩
    constructor
    · intro localIndex
      let targetIndex : Fin (hostLocals ++ [signature]).length :=
        ⟨localIndex.val, by simp; omega⟩
      let wire := Var.appendRight outer (Var.ofIndex localIndex)
      have pathsEq := present_incidencePaths_old hostLocals before after
        signature arity ports position far wire
      have rooted := presentRoots targetIndex
      have rooted' : RegionPath.RootedTwo
          ((present hostLocals before after signature arity ports position far).incidencePaths
            wire.index.val) := by
        simpa [wire, targetIndex] using rooted
      rw [pathsEq] at rooted'
      simpa [wire] using rooted'
    · exact (present_childrenCanonical_iff hostLocals before after
        signature arity ports position far).mp presentChildren
  · rintro ⟨plainRoots, plainChildren⟩
    constructor
    · intro localIndex
      by_cases old : localIndex.val < hostLocals.length
      · let hostIndex : Fin hostLocals.length := ⟨localIndex.val, old⟩
        let wire := Var.appendRight outer (Var.ofIndex hostIndex)
        have pathsEq := present_incidencePaths_old hostLocals before after
          signature arity ports position far wire
        have rooted := plainRoots hostIndex
        have rooted' : RegionPath.RootedTwo
            ((plain hostLocals before after signature arity ports).incidencePaths
              wire.index.val) := by
          simpa [wire, hostIndex] using rooted
        rw [← pathsEq] at rooted'
        simpa [wire, hostIndex] using rooted'
      · have freshIndex : localIndex.val = hostLocals.length := by
          have bound := localIndex.isLt
          simp only [List.length_append, List.length_singleton] at bound
          omega
        simpa [freshWire, freshIndex] using far.freshRootedTwo
          (extendedItems_fresh_mem_nil hostLocals before after signature
            arity ports position 0)
    · exact (present_childrenCanonical_iff hostLocals before after
        signature arity ports position far).mpr plainChildren

end Stub

private theorem replacementValidity
    {holeWires : List Sig} {before : Region holeWires}
    (occurrence : Occurrence before source)
    (after : Region holeWires) (afterCanonical : after.Canonical)
    (holeNonempty : ∀ {signature} (wire : Var holeWires signature),
      before.incidencePaths wire.index.val ≠ [] ↔
        after.incidencePaths wire.index.val ≠ []) :
    (occurrence.context.fill after).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill after) := by
  have replaced := occurrence.context.replaceCanonical before after
    occurrence.sourceCanonical afterCanonical holeNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill before) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  exact ⟨replaced.1,
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill after) replaced.2⟩

theorem Point.introduceValidity
    (occurrence : Occurrence (Point.plain locals items) source)
    (signature : Sig) :
    (occurrence.context.fill (Point.present locals items signature)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill (Point.present locals items signature)) := by
  apply replacementValidity occurrence
  · exact (Point.canonical_iff locals items signature).mpr
      (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
  · intro wireSignature wire
    rw [Point.incidencePaths_eq]

theorem Point.eliminateValidity
    (occurrence : Occurrence (Point.present locals items signature) source) :
    (occurrence.context.fill (Point.plain locals items)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill (Point.plain locals items)) := by
  apply replacementValidity occurrence
  · exact (Point.canonical_iff locals items signature).mp
      (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
  · intro wireSignature wire
    rw [Point.incidencePaths_eq]

theorem Pin.introduceValidity
    {holeWires : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    (occurrence : Occurrence (Pin.plain locals items) source)
    (signature : Sig) (wire : Var (holeWires ++ locals) signature) :
    (occurrence.context.fill
        (Pin.present locals items signature wire)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Pin.present locals items signature wire)) :=
  ⟨Pin.fillCanonical occurrence.context locals items signature wire
      occurrence.sourceCanonical,
    Pin.fillExternalTwoEnded occurrence.interface.boundaryWire
      occurrence.context locals items signature wire
      occurrence.sourceExternalTwoEnded⟩

theorem Pin.frontValidity
    {holeWires : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {signature : Sig} {wire : Var (holeWires ++ locals) signature}
    (occurrence : Occurrence (Pin.present locals items signature wire) source) :
    (occurrence.context.fill
        (Pin.front locals items signature wire)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Pin.front locals items signature wire)) := by
  apply replacementValidity occurrence
  · exact Pin.frontCanonical locals items signature wire
      (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
  · intro wireSignature selected
    exact Pin.present_front_incidence_nonempty_iff locals items signature wire
      selected.index.val

theorem Pin.eliminateValidity
    {holeWires : List Sig} {items : ItemSeq (holeWires ++ locals)}
    {signature : Sig} {selected : Var (holeWires ++ locals) signature}
    (occurrence : Occurrence
      (Pin.present locals items signature selected) source)
    (guard : Pin.DeletionGuard occurrence) :
    (occurrence.context.fill (Pin.plain locals items)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill (Pin.plain locals items)) := by
  have localSource := occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have localTarget := Pin.plainCanonical_of_guard locals items signature selected
    localSource guard.localDCA
  refine ⟨Pin.fillCanonical_of_guard occurrence.context locals items signature
    selected occurrence.sourceCanonical localTarget guard.ancestorDCA, ?_⟩
  intro wireSignature wire
  by_cases equal : selected.index.val =
      ((occurrence.context.outerWire wire).appendLeft locals).index.val
  · exact guard.externalTwoEnded wire equal
  · have pathsEq := Pin.fill_incidencePaths_eq_of_ne occurrence.context
        locals items signature selected wire equal
    have sourceFloor := occurrence.sourceExternalTwoEnded wire
    rwa [pathsEq] at sourceFloor

private theorem Pin.contextDCAGuard_of_canonical
    (context : DiagramContext outer holeWires)
    (locals : List Sig) (items : ItemSeq (holeWires ++ locals))
    (signature : Sig) (selected : Var (holeWires ++ locals) signature)
    (canonical : (context.fill (Pin.plain locals items)).Canonical) :
    Pin.ContextDCAGuard context locals items signature selected := by
  induction context with
  | hole => trivial
  | @cut currentOuter currentHole contextLocals leading trailing child induction =>
      constructor
      · intro localIndex equal
        exact canonical.1 localIndex
      · have children := (ItemSeq.childrenCanonical_append leading
          (.cons (.cut (child.fill (Pin.plain locals items))) trailing)).mp
            canonical.2
        exact induction items selected children.2.1

theorem Pin.DeletionGuard.ofValidity
    {holeWires : List Sig} {items : ItemSeq (holeWires ++ locals)}
    {signature : Sig} {selected : Var (holeWires ++ locals) signature}
    (occurrence : Occurrence
      (Pin.present locals items signature selected) source)
    (targetCanonical :
      (occurrence.context.fill (Pin.plain locals items)).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
        (occurrence.context.fill (Pin.plain locals items))) :
    Pin.DeletionGuard occurrence := by
  refine ⟨?_, Pin.contextDCAGuard_of_canonical occurrence.context locals items
    signature selected targetCanonical, ?_⟩
  · intro localIndex equal
    exact (occurrence.context.holeCanonical _ targetCanonical).1 localIndex
  · intro wireSignature wire equal
    exact targetExternalTwoEnded wire

theorem Stub.introduceValidity
    {holeWires : List Sig}
    {before after : ItemSeq (holeWires ++ hostLocals)}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var (holeWires ++ hostLocals) signature}
    (position : Fin (arity + 1))
    (occurrence : Occurrence
      (Stub.plain hostLocals before after signature arity ports) source)
    (far : Stub.Far (Stub.freshWire holeWires hostLocals signature)
      (Stub.extendedItems hostLocals before after signature arity ports position)) :
    (occurrence.context.fill
      (Stub.present hostLocals before after signature arity ports position far)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Stub.present hostLocals before after signature arity ports position far)) := by
  apply replacementValidity occurrence
  · exact (Stub.canonical_iff hostLocals before after signature arity ports
      position far).mpr
      (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
  · intro wireSignature wire
    have pathsEq := Stub.present_incidencePaths_old hostLocals before after
      signature arity ports position far (wire.appendLeft hostLocals)
    simpa using (congrArg (fun paths => paths ≠ []) pathsEq).symm

theorem Stub.eliminateValidity
    {holeWires : List Sig}
    {before after : ItemSeq (holeWires ++ hostLocals)}
    {signature : Sig} {arity : Nat}
    {ports : Fin arity → Var (holeWires ++ hostLocals) signature}
    {position : Fin (arity + 1)}
    {far : Stub.Far (Stub.freshWire holeWires hostLocals signature)
      (Stub.extendedItems hostLocals before after signature arity ports position)}
    (occurrence : Occurrence
      (Stub.present hostLocals before after signature arity ports position far) source) :
    (occurrence.context.fill
      (Stub.plain hostLocals before after signature arity ports)).Canonical ∧
      OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Stub.plain hostLocals before after signature arity ports)) := by
  apply replacementValidity occurrence
  · exact (Stub.canonical_iff hostLocals before after signature arity ports
      position far).mp
      (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
  · intro wireSignature wire
    have pathsEq := Stub.present_incidencePaths_old hostLocals before after
      signature arity ports position far (wire.appendLeft hostLocals)
    simpa using congrArg (fun paths => paths ≠ []) pathsEq

private def appendInternalWireSuffix
    (suffix : ItemSeq wires) :
    {items : ItemSeq wires} → ItemSeq.InternalWire items signature →
      ItemSeq.InternalWire (items.append suffix) signature
  | .cons (.cut _) _, .headCut wire => .headCut wire
  | .cons _ _, .tail wire => .tail (appendInternalWireSuffix suffix wire)

private theorem ownerPathFrom_appendInternalWireSuffix
    (suffix : ItemSeq wires) {items : ItemSeq wires}
    (wire : ItemSeq.InternalWire items signature) (itemIndex : Nat) :
    (appendInternalWireSuffix suffix wire).ownerPathFrom itemIndex =
      wire.ownerPathFrom itemIndex :=
  match wire with
  | .headCut _ => rfl
  | .tail nested => by
      simp only [appendInternalWireSuffix,
        ItemSeq.InternalWire.ownerPathFrom]
      exact ownerPathFrom_appendInternalWireSuffix suffix nested (itemIndex + 1)

mutual
  private def renameRegionInternal
      (rename : WireRenaming source target) :
      {region : Region source} → Region.InternalWire region signature →
        Region.InternalWire (region.renameWires rename) signature
    | .mk _ _, .here wire => .here wire
    | .mk locals _, .nested wire =>
        .nested (renameItemsInternal (rename.appendRight locals) wire)

  private def renameItemsInternal
      (rename : WireRenaming source target) :
      {items : ItemSeq source} → ItemSeq.InternalWire items signature →
        ItemSeq.InternalWire (items.renameWires rename) signature
    | .cons (.cut _) _, .headCut wire =>
        .headCut (renameRegionInternal rename wire)
    | .cons _ _, .tail wire => .tail (renameItemsInternal rename wire)
end

mutual
  private theorem ownerPath_renameRegionInternal
      (rename : WireRenaming source target)
      {region : Region source} (wire : Region.InternalWire region signature) :
      (renameRegionInternal rename wire).ownerPath = wire.ownerPath :=
    match region, wire with
    | .mk _ _, .here _ => rfl
    | .mk locals _, .nested nested =>
        ownerPathFrom_renameItemsInternal
          (rename.appendRight locals) nested 0

  private theorem ownerPathFrom_renameItemsInternal
      (rename : WireRenaming source target)
      {items : ItemSeq source} (wire : ItemSeq.InternalWire items signature)
      (itemIndex : Nat) :
      (renameItemsInternal rename wire).ownerPathFrom itemIndex =
        wire.ownerPathFrom itemIndex :=
    match items, wire with
    | .cons (.cut _) _, .headCut nested =>
        congrArg (List.cons itemIndex)
          (ownerPath_renameRegionInternal rename nested)
    | .cons _ _, .tail nested => by
        simp only [renameItemsInternal,
          ItemSeq.InternalWire.ownerPathFrom]
        exact ownerPathFrom_renameItemsInternal rename nested (itemIndex + 1)
end

private def appendRegionItems
    (suffix : ItemSeq (outer ++ locals)) :
    {items : ItemSeq (outer ++ locals)} →
      Region.InternalWire (.mk locals items) signature →
      Region.InternalWire (.mk locals (items.append suffix)) signature
  | _, .here wire => .here wire
  | _, .nested wire => .nested (appendInternalWireSuffix suffix wire)

private theorem ownerPath_appendRegionItems
    (suffix : ItemSeq (outer ++ locals)) {items : ItemSeq (outer ++ locals)}
    (wire : Region.InternalWire (.mk locals items) signature) :
    (appendRegionItems suffix wire).ownerPath = wire.ownerPath := by
  cases wire with
  | here wire => rfl
  | nested wire => exact ownerPathFrom_appendInternalWireSuffix suffix wire 0

private def Stub.embedExtendedItems
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1)) :
    ∀ {wireSignature}, ItemSeq.InternalWire
        (before.append (.cons (.identity signature arity ports) after))
          wireSignature →
      ItemSeq.InternalWire
        (Stub.extendedItems hostLocals before after signature arity ports position)
          wireSignature :=
  match before with
  | .nil => fun wire =>
      match wire with
      | .tail nested => .tail (renameItemsInternal
          (Stub.hostRename outer hostLocals signature) nested)
  | .cons (.atom _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail (Stub.embedExtendedItems tail after
          signature arity ports position nested)
  | .cons (.identity _ _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail (Stub.embedExtendedItems tail after
          signature arity ports position nested)
  | .cons (.term _ _ _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail (Stub.embedExtendedItems tail after
          signature arity ports position nested)
  | .cons (.cut _) tail => fun wire =>
      match wire with
      | .headCut nested => .headCut (renameRegionInternal
          (Stub.hostRename outer hostLocals signature) nested)
      | .tail nested => .tail (Stub.embedExtendedItems tail after
          signature arity ports position nested)

private theorem Stub.ownerPathFrom_embedExtendedItems
    (before after : ItemSeq (outer ++ hostLocals))
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var (outer ++ hostLocals) signature)
    (position : Fin (arity + 1)) {wireSignature}
    (wire : ItemSeq.InternalWire
      (before.append (.cons (.identity signature arity ports) after))
        wireSignature) (itemIndex : Nat) :
    (Stub.embedExtendedItems before after signature arity ports position wire).ownerPathFrom
        itemIndex = wire.ownerPathFrom itemIndex :=
  match before with
  | .nil =>
      match wire with
      | .tail nested => by
          simp only [Stub.embedExtendedItems,
            ItemSeq.InternalWire.ownerPathFrom]
          exact ownerPathFrom_renameItemsInternal
            (Stub.hostRename outer hostLocals signature) nested (itemIndex + 1)
  | .cons (.atom _ _) tail =>
      match wire with
      | .tail nested => by
          simp only [Stub.embedExtendedItems,
            ItemSeq.InternalWire.ownerPathFrom]
          exact Stub.ownerPathFrom_embedExtendedItems tail after
            signature arity ports position nested (itemIndex + 1)
  | .cons (.identity _ _ _) tail =>
      match wire with
      | .tail nested => by
          simp only [Stub.embedExtendedItems,
            ItemSeq.InternalWire.ownerPathFrom]
          exact Stub.ownerPathFrom_embedExtendedItems tail after
            signature arity ports position nested (itemIndex + 1)
  | .cons (.term _ _ _ _) tail =>
      match wire with
      | .tail nested => by
          simp only [Stub.embedExtendedItems,
            ItemSeq.InternalWire.ownerPathFrom]
          exact Stub.ownerPathFrom_embedExtendedItems tail after
            signature arity ports position nested (itemIndex + 1)
  | .cons (.cut _) tail =>
      match wire with
      | .headCut nested => by
          simp only [Stub.embedExtendedItems,
            ItemSeq.InternalWire.ownerPathFrom]
          exact congrArg (List.cons itemIndex)
            (ownerPath_renameRegionInternal
              (Stub.hostRename outer hostLocals signature) nested)
      | .tail nested => by
          simp only [Stub.embedExtendedItems,
            ItemSeq.InternalWire.ownerPathFrom]
          exact Stub.ownerPathFrom_embedExtendedItems tail after
            signature arity ports position nested (itemIndex + 1)

private def mapExactFrameInternal
    (leading trailing : ItemSeq wires)
    {before after : Region wires}
    (bodyMap : ∀ {signature}, Region.InternalWire before signature →
      Region.InternalWire after signature) :
    ∀ {signature}, ItemSeq.InternalWire
        (leading.append (.cons (.cut before) trailing)) signature →
      ItemSeq.InternalWire
        (leading.append (.cons (.cut after) trailing)) signature :=
  match leading with
  | .nil => fun wire =>
      match wire with
      | .headCut nested => .headCut (bodyMap nested)
      | .tail nested => .tail nested
  | .cons (.atom _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail
          (mapExactFrameInternal tail trailing bodyMap nested)
  | .cons (.identity _ _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail
          (mapExactFrameInternal tail trailing bodyMap nested)
  | .cons (.term _ _ _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail
          (mapExactFrameInternal tail trailing bodyMap nested)
  | .cons (.cut _) tail => fun wire =>
      match wire with
      | .headCut nested => .headCut nested
      | .tail nested => .tail
          (mapExactFrameInternal tail trailing bodyMap nested)

private theorem ownerPathFrom_mapExactFrameInternal
    (leading trailing : ItemSeq wires)
    {before after : Region wires}
    (bodyMap : ∀ {signature}, Region.InternalWire before signature →
      Region.InternalWire after signature)
    (bodyOwner : ∀ {signature} (wire : Region.InternalWire before signature),
      (bodyMap wire).ownerPath = wire.ownerPath)
    {signature} (wire : ItemSeq.InternalWire
      (leading.append (.cons (.cut before) trailing)) signature)
    (itemIndex : Nat) :
    (mapExactFrameInternal leading trailing bodyMap wire).ownerPathFrom itemIndex =
      wire.ownerPathFrom itemIndex := by
  cases leading with
  | nil =>
      cases wire with
      | headCut nested => exact congrArg (List.cons itemIndex) (bodyOwner nested)
      | tail nested => rfl
  | cons head tail =>
      cases head with
      | atom _ _ =>
          cases wire with
          | tail nested =>
              exact ownerPathFrom_mapExactFrameInternal tail trailing bodyMap
                bodyOwner nested (itemIndex + 1)
      | identity _ _ _ =>
          cases wire with
          | tail nested =>
              exact ownerPathFrom_mapExactFrameInternal tail trailing bodyMap
                bodyOwner nested (itemIndex + 1)
      | term _ _ _ _ =>
          cases wire with
          | tail nested =>
              exact ownerPathFrom_mapExactFrameInternal tail trailing bodyMap
                bodyOwner nested (itemIndex + 1)
      | cut _ =>
          cases wire with
          | headCut nested => rfl
          | tail nested =>
              exact ownerPathFrom_mapExactFrameInternal tail trailing bodyMap
                bodyOwner nested (itemIndex + 1)

private def Stub.Far.embedInternal
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Stub.Far wire items) :
    ∀ {wireSignature}, ItemSeq.InternalWire items wireSignature →
      ItemSeq.InternalWire far.result wireSignature := by
  intro wireSignature internal
  cases far with
  | atBase =>
      exact appendInternalWireSuffix
        (.cons (.identity signature 1 (fun _ => wire)) .nil) internal
  | below before after focus descendant farLocals farItems bodyEq =>
      subst items
      cases bodyEq
      let suffix := ItemSeq.cons (.identity signature 1 (fun _ =>
          (descendant.outerWire wire).appendLeft farLocals)) .nil
      let holeMap := fun {wireSignature}
          (nested : Region.InternalWire (.mk farLocals farItems) wireSignature) =>
        appendRegionItems suffix nested
      exact mapExactFrameInternal before after
        (descendant.mapInternalWire holeMap) internal

private theorem Stub.Far.ownerPathFrom_embedInternal_zero
    {wire : Var baseWires signature} {items : ItemSeq baseWires}
    (far : Stub.Far wire items) {wireSignature}
    (internal : ItemSeq.InternalWire items wireSignature) :
    (far.embedInternal internal).ownerPathFrom 0 =
      internal.ownerPathFrom 0 := by
  cases far with
  | atBase =>
      exact ownerPathFrom_appendInternalWireSuffix
        (.cons (.identity signature 1 (fun _ => wire)) .nil) internal 0
  | below before after focus descendant farLocals farItems bodyEq =>
      subst items
      cases bodyEq
      let suffix := ItemSeq.cons (.identity signature 1 (fun _ =>
          (descendant.outerWire wire).appendLeft farLocals)) .nil
      let holeMap := fun {wireSignature}
          (nested : Region.InternalWire (.mk farLocals farItems) wireSignature) =>
        appendRegionItems suffix nested
      have holeOwner : ∀ {wireSignature}
          (nested : Region.InternalWire (.mk farLocals farItems) wireSignature),
          (holeMap nested).ownerPath = nested.ownerPath := by
        intro wireSignature nested
        exact ownerPath_appendRegionItems suffix nested
      have descendantOwner : ∀ {wireSignature}
          (nested : Region.InternalWire
            (descendant.fill (.mk farLocals farItems)) wireSignature),
          (descendant.mapInternalWire holeMap nested).ownerPath =
            nested.ownerPath := by
        intro wireSignature nested
        exact descendant.ownerPath_mapInternalWire holeMap holeOwner nested
      simpa only [Stub.Far.embedInternal, suffix, holeMap] using
        ownerPathFrom_mapExactFrameInternal before after
          (descendant.mapInternalWire holeMap)
          (fun nested => descendantOwner nested) internal 0
inductive Description (outer : List Sig) : Type
  | point (locals : List Sig)
      (items : ItemSeq (outer ++ locals)) (signature : Sig)
  | stub (hostLocals : List Sig)
      (before after : ItemSeq (outer ++ hostLocals))
      (signature : Sig) (arity : Nat)
      (ports : Fin arity → Var (outer ++ hostLocals) signature)
      (position : Fin (arity + 1))
      (far : Stub.Far (Stub.freshWire outer hostLocals signature)
        (Stub.extendedItems hostLocals before after signature arity ports position))
  | pin (locals : List Sig)
      (items : ItemSeq (outer ++ locals))
      (signature : Sig) (wire : Var (outer ++ locals) signature)

def Description.source : Description outer → Region outer
  | .point locals items _ => Point.plain locals items
  | .stub hostLocals before after signature arity ports _ _ =>
      Stub.plain hostLocals before after signature arity ports
  | .pin locals items _ _ => Pin.plain locals items

def Description.target : (description : Description outer) → Region outer
  | .point locals items signature => Point.present locals items signature
  | .stub hostLocals before after signature arity ports position far =>
      Stub.present hostLocals before after signature arity ports position far
  | .pin locals items signature wire =>
      Pin.present locals items signature wire

inductive Local : LocalRule
  | mk (description : Description outer) :
      Local description.source description.target

private theorem Local.internalEmbedding
    {before after : Region outer} (step : Local before after) :
    ∃ map : ∀ {signature}, Region.InternalWire before signature →
        Region.InternalWire after signature,
      ∀ {signature} (wire : Region.InternalWire before signature),
        (map wire).ownerPath = wire.ownerPath := by
  cases step with
  | mk description => cases description with
  | point locals items signature =>
      let suffix : ItemSeq (outer ++ locals) :=
        .cons (.identity signature 0 Fin.elim0) .nil
      exact ⟨appendRegionItems suffix,
        fun wire => ownerPath_appendRegionItems suffix wire⟩
  | pin locals items signature selected =>
      let suffix : ItemSeq (outer ++ locals) :=
        .cons (.identity signature 1 (fun _ => selected)) .nil
      exact ⟨appendRegionItems suffix,
        fun wire => ownerPath_appendRegionItems suffix wire⟩
  | stub hostLocals before after signature arity ports position far =>
      let map : ∀ {wireSignature}, Region.InternalWire
          (Stub.plain hostLocals before after signature arity ports)
            wireSignature →
        Region.InternalWire
          (Stub.present hostLocals before after signature arity ports position far)
            wireSignature := fun internal =>
        match internal with
        | .here localWire => .here (localWire.appendLeft [signature])
        | .nested nestedWire => .nested (far.embedInternal
            (Stub.embedExtendedItems before after signature arity ports
              position nestedWire))
      refine ⟨map, ?_⟩
      intro wireSignature wire
      cases wire with
      | here localWire => rfl
      | nested nestedWire =>
          exact (far.ownerPathFrom_embedInternal_zero
              (Stub.embedExtendedItems before after signature arity ports position
                nestedWire)).trans
            (Stub.ownerPathFrom_embedExtendedItems before after signature arity
              ports position nestedWire 0)

theorem Local.existsInternalWire_ownerPath
    {before after : Region outer} (step : Local before after)
    {signature} (wire : Region.InternalWire before signature) :
    ∃ targetWire : Region.InternalWire after signature,
      targetWire.ownerPath = wire.ownerPath := by
  rcases step.internalEmbedding with ⟨map, owner⟩
  exact ⟨map wire, owner wire⟩

theorem Local.existsPresentedWire_scopePath
    {before after : Region wires} (step : Local before after)
    (occurrence : Occurrence before source)
    (targetCanonical : (occurrence.context.fill after).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire (occurrence.context.fill after))
    {signature}
    (wire : OpenDiagram.Wire
      (occurrence.interface.withBody
        (occurrence.context.fill before) occurrence.sourceCanonical
          occurrence.sourceExternalTwoEnded) signature) :
    ∃ targetWire : OpenDiagram.Wire
        (occurrence.interface.withBody
          (occurrence.context.fill after) targetCanonical
            targetExternalTwoEnded) signature,
      (occurrence.interface.withBody
          (occurrence.context.fill after) targetCanonical
            targetExternalTwoEnded).scopePath targetWire =
        (occurrence.interface.withBody
          (occurrence.context.fill before) occurrence.sourceCanonical
            occurrence.sourceExternalTwoEnded).scopePath wire := by
  cases wire with
  | external externalWire =>
      refine ⟨.external externalWire, ?_⟩
      rw [OpenDiagram.scopePath_external, OpenDiagram.scopePath_external]
  | internal internalWire =>
      rcases step.internalEmbedding with ⟨holeMap, holeOwner⟩
      let targetWire := occurrence.context.mapInternalWire holeMap internalWire
      refine ⟨.internal targetWire, ?_⟩
      rw [OpenDiagram.scopePath_internal, OpenDiagram.scopePath_internal]
      exact occurrence.context.ownerPath_mapInternalWire
        holeMap holeOwner internalWire

end Vacuity

def Vacuity : Rule :=
  Contextual (symmetric Vacuity.Local)

theorem Vacuity.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Vacuity source target)
    (targetIso : OpenDiagramIso target target') :
    Vacuity source' target' :=
  Contextual.iso sourceIso step targetIso

theorem Vacuity.respectsTargetIso
    (step : Vacuity source target)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Vacuity source target' := by
  rcases isomorphic with ⟨targetIso⟩
  exact Vacuity.iso (OpenDiagramIso.refl source) step targetIso

theorem Vacuity.backward_respectsTargetIso
    (step : Vacuity target source)
    (isomorphic : OpenDiagram.Isomorphic target target') :
    Vacuity target' source := by
  rcases isomorphic with ⟨targetIso⟩
  exact Vacuity.iso targetIso step (OpenDiagramIso.refl source)

theorem Vacuity.symm
    (step : Vacuity source target) : Vacuity target source := by
  rcases step with ⟨wires, before, after, occurrence, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  let reverseOccurrence : Occurrence after target := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := targetCanonical
    sourceExternalTwoEnded := targetExternalTwoEnded
    host_iso := targetIso
  }
  refine ⟨wires, after, before, reverseOccurrence,
    occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
    occurrence.host_iso, ?_⟩
  cases polarity : occurrence.context.polarity <;>
    simp only [polarity, atPolarity, converse, symmetric] at localEvidence ⊢
  · exact localEvidence.elim Or.inr Or.inl
  · exact localEvidence.elim Or.inr Or.inl

end VisualProof.Rule
