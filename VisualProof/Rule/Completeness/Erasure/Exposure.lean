import VisualProof.Rule.Completeness.Reachability
import VisualProof.Rule.Erasure
import VisualProof.Rule.Comprehension.Relation

namespace VisualProof.Rule.Completeness.Erasure.Exposure

open Diagram
open Theory

/-- Every wire of a typed context, in context order. -/
def identityBoundary : (wires : List Sig) -> Vars wires wires
  | [] => .nil
  | _ :: tail =>
      .cons .here ((identityBoundary tail).map fun wire => .there wire)

private theorem Vars.get_map
    (variables : Vars source signatures)
    (rename : forall {signature}, Var source signature -> Var target signature)
    (position : Fin signatures.length) :
    (variables.map rename).get position = rename (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun rest => induction rest) position

theorem identityBoundary_get_index
    (position : Fin wires.length) :
    ((identityBoundary wires).get position).index = position := by
  induction wires with
  | nil => exact Fin.elim0 position
  | cons signature tail induction =>
      refine Fin.cases rfl (fun rest => ?_) position
      simp only [identityBoundary]
      change (((identityBoundary tail).map fun wire => .there wire).get rest).index =
        rest.succ
      rw [Vars.get_map]
      change ((identityBoundary tail).get rest).index.succ = rest.succ
      exact congrArg Fin.succ (induction rest)

private def VariablesIndexInjective
    (variables : Vars wires signatures) : Prop :=
  ∀ first second : Fin signatures.length,
    (variables.get first).index.val = (variables.get second).index.val →
      first = second

private theorem identityBoundary_indexInjective :
    VariablesIndexInjective (identityBoundary wires) := by
  intro first second equality
  apply Fin.ext
  have firstIndex := identityBoundary_get_index (wires := wires) first
  have secondIndex := identityBoundary_get_index (wires := wires) second
  have firstValue := congrArg Fin.val firstIndex
  have secondValue := congrArg Fin.val secondIndex
  omega

/-- Unary pins added exactly at the material externals unused by its body. -/
def supportPins (material : Region materialWires) :
    (signatures : List Sig) -> Vars materialWires signatures ->
      ItemSeq (materialWires ++ material.locals)
  | [], .nil => .nil
  | signature :: signatures, .cons wire tail =>
      let rest := supportPins material signatures tail
      if material.incidencePaths wire.index.val = [] then
        .cons (.identity signature 1
          (fun _ => wire.appendLeft material.locals)) rest
      else
        rest

def supportBody (material : Region materialWires) : Region materialWires :=
  .mk material.locals
    (material.items.append
      (supportPins material materialWires (identityBoundary materialWires)))

private theorem supportPins_childrenCanonical
    (material : Region materialWires)
    (variables : Vars materialWires signatures) :
    (supportPins material signatures variables).ChildrenCanonical := by
  induction variables with
  | nil => trivial
  | @cons signature signatures wire tail induction =>
      simp only [supportPins]
      split
      · exact ⟨True.intro, induction⟩
      · exact induction

private theorem supportPins_get_nonempty
    (material : Region materialWires)
    (variables : Vars materialWires signatures)
    (position : Fin signatures.length) (itemIndex : Nat)
    (unused : material.incidencePaths
      (variables.get position).index.val = []) :
    (supportPins material signatures variables).incidencePaths
      (variables.get position).index.val itemIndex ≠ [] := by
  induction variables generalizing itemIndex with
  | nil => exact Fin.elim0 position
  | @cons signature signatures head tail induction =>
      revert unused itemIndex
      refine Fin.cases (fun itemIndex unused => ?_)
        (fun rest itemIndex unused => ?_) position
      · change material.incidencePaths head.index.val = [] at unused
        change (supportPins material (signature :: signatures)
          (.cons head tail)).incidencePaths head.index.val itemIndex ≠ []
        simp [supportPins, unused, ItemSeq.incidencePaths,
          Item.incidencePaths]
      · change material.incidencePaths (tail.get rest).index.val = [] at unused
        change (supportPins material (signature :: signatures)
          (.cons head tail)).incidencePaths
            (tail.get rest).index.val itemIndex ≠ []
        simp only [supportPins]
        split
        · simp only [ItemSeq.incidencePaths]
          intro empty
          have tailEmpty := (List.append_eq_nil_iff.mp empty).2
          exact induction rest (itemIndex + 1) unused tailEmpty
        · exact induction rest itemIndex unused

private theorem supportBody_canonical
    (material : Region materialWires)
    (canonical : material.Canonical) :
    (supportBody material).Canonical := by
  cases material with
  | mk locals items =>
      simp only [supportBody, Region.locals, Region.items, Region.Canonical]
      constructor
      · intro localIndex
        have rooted := canonical.1 localIndex
        rw [ItemSeq.incidencePaths_append]
        exact ⟨by
          simp only [List.length_append]
          exact Nat.le_trans rooted.1 (Nat.le_add_right _ _),
          RegionPath.deepestCommonAncestor_append_eq_nil _ _
            rooted.nonempty rooted.2⟩
      · exact (ItemSeq.childrenCanonical_append _ _).mpr
          ⟨canonical.2, supportPins_childrenCanonical _ _⟩

private theorem identityBoundary_surjective
    (wire : Fin materialWires.length) :
    ∃ position : Fin materialWires.length,
      ((identityBoundary materialWires).get position).index = wire := by
  exact ⟨wire, identityBoundary_get_index wire⟩

private theorem supportBody_incidence_nonempty
    (material : Region materialWires)
    (wire : Var materialWires signature) :
    (supportBody material).incidencePaths wire.index.val ≠ [] := by
  cases material with
  | mk locals items =>
      simp only [supportBody, Region.locals, Region.items,
        Region.incidencePaths, ItemSeq.incidencePaths_append]
      by_cases unused :
          items.incidencePaths wire.index.val 0 = []
      · have selectedIndex := identityBoundary_get_index
          (wires := materialWires) wire.index
        have selectedIndexVal := congrArg Fin.val selectedIndex
        have unused' :
            (Region.mk locals items).incidencePaths
              ((identityBoundary materialWires).get wire.index).index.val = [] := by
          rw [selectedIndexVal]
          exact unused
        have supportNonempty := supportPins_get_nonempty
          (Region.mk locals items) (identityBoundary materialWires)
          wire.index items.length unused'
        rw [selectedIndexVal] at supportNonempty
        intro empty
        exact supportNonempty (by
          simpa using (List.append_eq_nil_iff.mp empty).2)
      · intro empty
        exact unused (List.append_eq_nil_iff.mp empty).1

/-- The support-completed material pattern used by erasure factorization. -/
def supportPattern
    (material : Region materialWires) (canonical : material.Canonical) :
    OpenDiagram materialWires where
  external := materialWires
  boundaryWire := identityBoundary materialWires
  boundarySurjective := identityBoundary_surjective
  body := supportBody material
  canonical := supportBody_canonical material canonical
  externalTwoEnded := by
    intro signature wire
    have boundaryPositive :
        0 < (identityBoundary materialWires).countIndex wire.index.val := by
      obtain ⟨position, maps⟩ := identityBoundary_surjective wire.index
      have positive :=
        (identityBoundary materialWires).countIndex_get_positive position
      rw [maps] at positive
      exact positive
    have bodyPositive :
        0 < ((supportBody material).incidencePaths wire.index.val).length :=
      List.length_pos_iff.mpr (supportBody_incidence_nonempty material wire)
    omega

private theorem supportInstantiation_canonical
    (material : Region materialWires) (canonical : material.Canonical)
    (ports : Vars targetWires materialWires) :
    (Comprehension.Instantiation.instantiate
      (supportPattern material canonical) ports).Canonical := by
  let embed : WireRenaming materialWires (targetWires ++ materialWires) :=
    ⟨fun wire => Var.appendRight targetWires wire⟩
  let body := (supportBody material).renameWires embed
  let left := ports.map (fun wire => wire.appendLeft materialWires)
  let right := (identityBoundary materialWires).map
    (fun wire => Var.appendRight targetWires wire)
  let equalityItems :=
    Comprehension.Instantiation.equalityItems left right
  have bodyCanonical : body.Canonical :=
    (Region.Canonical.renameWires_iff (supportBody material) embed).mpr
      (supportBody_canonical material canonical)
  have equalityChildren : equalityItems.ChildrenCanonical :=
    Comprehension.Instantiation.equalityItems_childrenCanonical left right
  have joinedCanonical :
      (body.conjoin (Region.ofItems equalityItems)).Canonical :=
    Region.Canonical.conjoinRightItems body equalityItems bodyCanonical
      equalityChildren
  unfold Comprehension.Instantiation.instantiate
  rw [Comprehension.Instantiation.Equalities_eq_ofItems]
  change (Region.adjoinAt materialWires .nil
    (body.conjoin (Region.ofItems equalityItems))).Canonical
  apply Region.Canonical.adjoinAt_of_material_roots materialWires .nil
    (body.conjoin (Region.ofItems equalityItems)) True.intro joinedCanonical
  intro externalIndex
  let external := (identityBoundary materialWires).get externalIndex
  let embedded := Var.appendRight targetWires external
  have externalIndexEq : external.index = externalIndex :=
    identityBoundary_get_index externalIndex
  have embeddedIndex : embedded.index.val =
      targetWires.length + externalIndex.val := by
    simp [embedded, external, externalIndexEq]
  cases material with
  | mk materialLocals materialItems =>
      let firstItems := body.items.renameWires
        (Region.conjoinLeftWire (targetWires ++ materialWires)
          body.locals [])
      let appendNil : WireRenaming (targetWires ++ materialWires)
          ((targetWires ++ materialWires) ++ []) :=
        ⟨fun wire => wire.appendLeft []⟩
      let rightItems := (equalityItems.renameWires appendNil).renameWires
        (Region.conjoinRightWire (targetWires ++ materialWires)
          body.locals [])
      rw [← embeddedIndex]
      change RegionPath.RootedTwo
        ((firstItems.append rightItems).incidencePaths
          embedded.index.val 0)
      rw [ItemSeq.incidencePaths_append]
      simp only [Nat.zero_add]
      have bodyPathsEq : body.incidencePaths embedded.index.val =
          (supportBody (Region.mk materialLocals materialItems)).incidencePaths
            external.index.val := by
        simp only [body]
        apply ItemSeq.incidencePaths_renameWires_of_index_iff
        · have bound := external.index.isLt
          simp only [List.length_append, Region.locals]
          omega
        · have bound := embedded.index.isLt
          simp only [List.length_append, Region.locals]
          omega
        · intro signature wire
          apply Var.appendCases (left := materialWires)
            (right := materialLocals)
            (motive := fun wire =>
              ((embed.appendRight materialLocals) wire).index.val =
                    embedded.index.val ↔
                wire.index.val = external.index.val)
          · intro inheritedSignature inherited
            simp only [WireRenaming.appendRight, Var.appendMap_left,
              Var.index_appendLeft, embed, Var.index_appendRight]
            omega
          · intro localSignature localWire
            have externalBound := external.index.isLt
            have localBound := localWire.index.isLt
            simp only [WireRenaming.appendRight, Var.appendMap_right,
              Var.index_appendRight]
            omega
      have firstPathsEq :
          firstItems.incidencePaths embedded.index.val 0 =
            body.incidencePaths embedded.index.val := by
        have renamed := ItemSeq.incidencePaths_renameWires_adjoinHost
          (addedLocals := []) body.items
          (embedded.appendLeft body.locals) 0
        simpa [firstItems, Region.adjoinHostWire,
          Region.incidencePaths] using renamed
      have firstNonempty :
          firstItems.incidencePaths embedded.index.val 0 ≠ [] := by
        rw [firstPathsEq, bodyPathsEq]
        exact supportBody_incidence_nonempty
          (Region.mk materialLocals materialItems) external
      have rightGetIndex : (right.get externalIndex).index.val =
          embedded.index.val := by
        simp [right, Vars.get_map, embedded, external, externalIndexEq]
      have baseRightMem :=
        Comprehension.Instantiation.equalityItems_right_mem_nil
          left right externalIndex firstItems.length
      rw [rightGetIndex] at baseRightMem
      have rightPathsEq :
          rightItems.incidencePaths embedded.index.val firstItems.length =
            equalityItems.incidencePaths embedded.index.val
              firstItems.length := by
        simp only [rightItems, ItemSeq.renameWires_comp]
        apply ItemSeq.incidencePaths_renameWires_of_index_iff
        · exact embedded.index.isLt
        · simpa [body, Region.locals] using
            (embedded.appendLeft body.locals).index.isLt
        · intro signature wire
          simp [WireRenaming.comp, appendNil, Region.conjoinRightWire, body,
            Region.locals]
      have rightMem : [] ∈
          rightItems.incidencePaths embedded.index.val firstItems.length := by
        rw [rightPathsEq]
        exact baseRightMem
      constructor
      · simp only [List.length_append]
        have firstPositive := List.length_pos_iff.mpr firstNonempty
        have rightPositive := List.length_pos_iff.mpr
          (List.ne_nil_of_mem rightMem)
        omega
      · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
        exact List.mem_append_right _ rightMem

private theorem retainWire_index
    (wire : Var (outer ++ locals) wireSignature) :
    (Identification.retainWire outer locals signature count wire).index.val =
      wire.index.val := by
  apply Var.appendCases (left := outer) (right := locals)
    (motive := fun wire =>
      (Identification.retainWire outer locals signature count wire).index.val =
        wire.index.val)
  · intro inheritedSignature inherited
    simp [Identification.retainWire, Region.adjoinHostWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [Identification.retainWire, Region.adjoinHostWire,
      Region.conjoinLeftWire]

private def redirectExternal
    (retain : WireRenaming current expanded)
    (fresh : Var expanded selectedSignature) :
    {materialWires : List Sig} ->
      (selected : Var materialWires selectedSignature) ->
      WireRenaming materialWires current ->
      WireRenaming materialWires expanded
  | _ :: _, .here, currentMap => ⟨fun wire =>
      match wire with
      | .here => fresh
      | .there tail => retain (currentMap (.there tail))⟩
  | _ :: _, .there selected, currentMap =>
      let redirectedTail := redirectExternal retain fresh selected
        ⟨fun wire => currentMap (.there wire)⟩
      ⟨fun wire =>
        match wire with
        | .here => retain (currentMap .here)
        | .there tail => redirectedTail tail⟩

private theorem redirectExternal_collapse
    (retain : WireRenaming current expanded)
    (collapse : WireRenaming expanded current)
    (retained : forall {signature} (wire : Var current signature),
      collapse (retain wire) = wire)
    (currentMap : WireRenaming materialWires current)
    (selected : Var materialWires selectedSignature)
    (fresh : Var expanded selectedSignature)
    (freshCollapse : collapse fresh = currentMap selected)
    (wire : Var materialWires signature) :
    collapse (redirectExternal retain fresh selected currentMap wire) =
      currentMap wire := by
  induction selected with
  | here =>
      cases wire with
      | here => exact freshCollapse
      | there tail => exact retained _
  | there selected induction =>
      cases wire with
      | here => exact retained _
      | there wire =>
          exact induction
            ⟨fun tailWire => currentMap (.there tailWire)⟩ fresh
              freshCollapse wire

private theorem redirectExternal_other
    (retain : WireRenaming current expanded)
    (fresh : Var expanded selectedSignature)
    (currentMap : WireRenaming materialWires current)
    (selected : Var materialWires selectedSignature)
    (wire : Var materialWires wireSignature)
    (different : wire.index.val ≠ selected.index.val) :
    redirectExternal retain fresh selected currentMap wire =
      retain (currentMap wire) := by
  induction selected with
  | here =>
      cases wire with
      | here => exact False.elim (different rfl)
      | there tail => rfl
  | there selected induction =>
      cases wire with
      | here => rfl
      | there wire =>
          apply induction
          intro equality
          apply different
          change wire.index.val + 1 = selected.index.val + 1
          omega

private theorem redirectExternal_fresh_index_iff
    (retain : WireRenaming current expanded)
    (fresh : Var expanded selectedSignature)
    (freshNotRetained : ∀ {signature} (wire : Var current signature),
      (retain wire).index.val ≠ fresh.index.val)
    (currentMap : WireRenaming materialWires current)
    (selected : Var materialWires selectedSignature)
    (wire : Var materialWires wireSignature) :
    (redirectExternal retain fresh selected currentMap wire).index.val =
        fresh.index.val ↔
      wire.index.val = selected.index.val := by
  induction selected with
  | here =>
      cases wire with
      | here => simp [redirectExternal]
      | there tail =>
          simp only [redirectExternal]
          constructor
          · exact fun equality => False.elim
              (freshNotRetained (currentMap (.there tail)) equality)
          · intro equality
            change tail.index.val + 1 = 0 at equality
            omega
  | there selected induction =>
      cases wire with
      | here =>
          simp only [redirectExternal]
          constructor
          · exact fun equality => False.elim
              (freshNotRetained (currentMap .here) equality)
          · intro equality
            change 0 = selected.index.val + 1 at equality
            omega
      | there wire =>
          have recurse := induction fresh freshNotRetained
            ⟨fun tailWire => currentMap (.there tailWire)⟩ wire
          simp only [redirectExternal]
          constructor
          · intro equality
            have sourceEq := recurse.mp equality
            change wire.index.val = selected.index.val at sourceEq
            change wire.index.val + 1 = selected.index.val + 1
            omega
          · intro equality
            apply recurse.mpr
            change wire.index.val + 1 = selected.index.val + 1 at equality
            change wire.index.val = selected.index.val
            omega

private def redirectMaterial
    (currentMap : WireRenaming
      (materialWires ++ materialLocals) (outer ++ locals))
    (selected : Var materialWires signature) :
    WireRenaming (materialWires ++ materialLocals)
      (outer ++ (locals ++ [signature])) :=
  let retain := Identification.retainWire outer locals signature 1
  let fresh := Identification.freshLocalWire outer locals signature (0 : Fin 1)
  let externalMap : WireRenaming materialWires (outer ++ locals) :=
    ⟨fun wire => currentMap (wire.appendLeft materialLocals)⟩
  let redirected := redirectExternal retain fresh selected externalMap
  ⟨Var.appendMap
    (fun wire => redirected wire)
    (fun wire => retain (currentMap (Var.appendRight materialWires wire)))⟩

private theorem redirectMaterial_collapse
    (currentMap : WireRenaming
      (materialWires ++ materialLocals) (outer ++ locals))
    (selected : Var materialWires signature)
    (wire : Var (materialWires ++ materialLocals) wireSignature) :
    Identification.collapseLocal outer locals
      (currentMap (selected.appendLeft materialLocals)) 1
      (redirectMaterial currentMap selected wire) = currentMap wire := by
  apply Var.appendCases (left := materialWires) (right := materialLocals)
    (motive := fun wire =>
      Identification.collapseLocal outer locals
        (currentMap (selected.appendLeft materialLocals)) 1
        (redirectMaterial currentMap selected wire) = currentMap wire)
  · intro inheritedSignature inherited
    simp only [redirectMaterial, Var.appendMap_left]
    apply redirectExternal_collapse
      (Identification.retainWire outer locals signature 1)
      (Identification.collapseLocal outer locals
        (currentMap (selected.appendLeft materialLocals)) 1)
      (fun wire => Identification.collapseLocal_retained _ _ wire)
      ⟨fun wire => currentMap (wire.appendLeft materialLocals)⟩ selected
      (Identification.freshLocalWire outer locals signature (0 : Fin 1))
      (Identification.collapseLocal_fresh _ (0 : Fin 1)) inherited
  · intro localSignature localWire
    simp only [redirectMaterial, Var.appendMap_right]
    exact Identification.collapseLocal_retained _ _ _

private theorem redirectMaterial_other_external
    (currentMap : WireRenaming
      (materialWires ++ materialLocals) (outer ++ locals))
    (selected : Var materialWires signature)
    (wire : Var materialWires wireSignature)
    (different : wire.index.val ≠ selected.index.val) :
    redirectMaterial currentMap selected
        (wire.appendLeft materialLocals) =
      Identification.retainWire outer locals signature 1
        (currentMap (wire.appendLeft materialLocals)) := by
  simp only [redirectMaterial, Var.appendMap_left]
  exact redirectExternal_other
    (Identification.retainWire outer locals signature 1)
    (Identification.freshLocalWire outer locals signature (0 : Fin 1))
    ⟨fun inherited => currentMap (inherited.appendLeft materialLocals)⟩
    selected wire different

private theorem redirectMaterial_other
    (currentMap : WireRenaming
      (materialWires ++ materialLocals) (outer ++ locals))
    (selected : Var materialWires signature)
    (wire : Var (materialWires ++ materialLocals) wireSignature)
    (different : wire.index.val ≠
      (selected.appendLeft materialLocals).index.val) :
    redirectMaterial currentMap selected wire =
      Identification.retainWire outer locals signature 1
        (currentMap wire) := by
  refine Var.appendCases (left := materialWires) (right := materialLocals)
    (motive := fun wire => wire.index.val ≠
      (selected.appendLeft materialLocals).index.val →
      redirectMaterial currentMap selected wire =
        Identification.retainWire outer locals signature 1
          (currentMap wire)) ?_ ?_ wire different
  · intro inheritedSignature inherited inheritedDifferent
    apply redirectMaterial_other_external currentMap selected inherited
    simpa only [Var.index_appendLeft] using inheritedDifferent
  · intro localSignature localWire _
    simp only [redirectMaterial, Var.appendMap_right]

private theorem redirectMaterial_fresh_index_iff
    (currentMap : WireRenaming
      (materialWires ++ materialLocals) (outer ++ locals))
    (selected : Var materialWires signature)
    (wire : Var (materialWires ++ materialLocals) wireSignature) :
    (redirectMaterial currentMap selected wire).index.val =
        (Identification.freshLocalWire outer locals signature
          (0 : Fin 1)).index.val ↔
      wire.index.val = (selected.appendLeft materialLocals).index.val := by
  apply Var.appendCases (left := materialWires) (right := materialLocals)
    (motive := fun wire =>
      (redirectMaterial currentMap selected wire).index.val =
          (Identification.freshLocalWire outer locals signature
            (0 : Fin 1)).index.val ↔
        wire.index.val = (selected.appendLeft materialLocals).index.val)
  · intro inheritedSignature inherited
    simp only [redirectMaterial, Var.appendMap_left]
    simpa only [Var.index_appendLeft] using
      (redirectExternal_fresh_index_iff
        (Identification.retainWire outer locals signature 1)
        (Identification.freshLocalWire outer locals signature (0 : Fin 1))
        (by
          intro retainedSignature retained
          have retainedIndex := retainWire_index
            (signature := signature) (count := 1) retained
          intro equality
          have retainedBound := retained.index.isLt
          have impossible : retained.index.val =
              (Identification.freshLocalWire outer locals signature
                (0 : Fin 1)).index.val := retainedIndex.symm.trans equality
          have freshIndex :
              (Identification.freshLocalWire outer locals signature
                (0 : Fin 1)).index.val = (outer ++ locals).length := by
            simp [Identification.freshLocalWire, List.length_append]
          rw [freshIndex] at impossible
          omega)
        ⟨fun wire => currentMap (wire.appendLeft materialLocals)⟩
        selected inherited)
  · intro localSignature localWire
    simp only [redirectMaterial, Var.appendMap_right]
    have retainedIndex := retainWire_index
      (signature := signature) (count := 1)
      (currentMap (Var.appendRight materialWires localWire))
    have retainedBound :=
      (currentMap (Var.appendRight materialWires localWire)).index.isLt
    have selectedBound := selected.index.isLt
    constructor
    · intro equality
      have impossible :
          (currentMap (Var.appendRight materialWires localWire)).index.val =
            (Identification.freshLocalWire outer locals signature
              (0 : Fin 1)).index.val := retainedIndex.symm.trans equality
      have freshIndex :
          (Identification.freshLocalWire outer locals signature
            (0 : Fin 1)).index.val = (outer ++ locals).length := by
        simp [Identification.freshLocalWire, List.length_append]
      rw [freshIndex] at impossible
      omega
    · intro equality
      have localIndex :
          (Var.appendRight materialWires localWire).index.val =
            materialWires.length + localWire.index.val := by simp
      have selectedIndex :
          (selected.appendLeft materialLocals).index.val = selected.index.val := by
        simp
      rw [localIndex, selectedIndex] at equality
      omega

private theorem redirectMaterial_selected
    (currentMap : WireRenaming
      (materialWires ++ materialLocals) (outer ++ locals))
    (selected : Var materialWires signature) :
    redirectMaterial currentMap selected
        (selected.appendLeft materialLocals) =
      Identification.freshLocalWire outer locals signature (0 : Fin 1) := by
  apply Var.eq_of_index_eq
  apply Fin.ext
  exact (redirectMaterial_fresh_index_iff currentMap selected
    (selected.appendLeft materialLocals)).mpr rfl

private structure State
    (outer materialWires : List Sig) (material : Region materialWires) where
  locals : List Sig
  before : ItemSeq (outer ++ locals)
  after : ItemSeq (outer ++ locals)
  materialMap : WireRenaming (materialWires ++ material.locals)
    (outer ++ locals)

private def State.items
    (state : State outer materialWires material) :
    ItemSeq (outer ++ state.locals) :=
  state.before.append
    ((material.items.renameWires state.materialMap).append state.after)

private def State.region
    (state : State outer materialWires material) : Region outer :=
  .mk state.locals state.items

private def equalityNode
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    Item (outer ++ (state.locals ++ [signature])) :=
  let retain := Identification.retainWire outer state.locals signature 1
  let survivor := state.materialMap
    (selected.appendLeft material.locals)
  let fresh := Identification.freshLocalWire outer state.locals signature
    (0 : Fin 1)
  .identity signature 2 (Fin.cases (retain survivor) (fun _ => fresh))

private def supportSuffix
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    ItemSeq (outer ++ (state.locals ++ [signature])) :=
  if material.incidencePaths selected.index.val = [] then
    .cons (.identity signature 1 (fun _ =>
      Identification.freshLocalWire outer state.locals signature
        (0 : Fin 1))) .nil
  else
    .nil

private def State.advance
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    State outer materialWires material where
  locals := state.locals ++ [signature]
  before := .cons (equalityNode state selected)
    (state.before.renameWires
      (Identification.retainWire outer state.locals signature 1))
  after :=
    (state.after.renameWires
      (Identification.retainWire outer state.locals signature 1)).append
      (supportSuffix state selected)
  materialMap := redirectMaterial state.materialMap selected

private def State.advanceAll
    (state : State outer materialWires material) :
    {signatures : List Sig} -> Vars materialWires signatures ->
      State outer materialWires material
  | [], .nil => state
  | _ :: _, .cons selected tail =>
      (state.advance selected).advanceAll tail

private theorem State.advanceAll_locals
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures) :
    (state.advanceAll variables).locals = state.locals ++ signatures := by
  induction variables generalizing state with
  | nil => simp [State.advanceAll]
  | @cons signature signatures selected tail induction =>
      simp [State.advanceAll, induction, State.advance, List.append_assoc]

/-- The exact composite retaining every wire that predates a batch of
exposures.  Its codomain follows the fold's actual local-context shape. -/
private def State.retainAll
    (state : State outer materialWires material) :
    {signatures : List Sig} -> (variables : Vars materialWires signatures) ->
      WireRenaming (outer ++ state.locals)
        (outer ++ (state.advanceAll variables).locals)
  | [], .nil => WireRenaming.id
  | _ :: _, .cons selected tail =>
      WireRenaming.comp ((state.advance selected).retainAll tail)
        (Identification.retainWire outer state.locals _ 1)

private theorem State.advanceAll_materialMap_other
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (wire : Var (materialWires ++ material.locals) wireSignature)
    (different : ∀ position : Fin signatures.length,
      wire.index.val ≠
        ((variables.get position).appendLeft material.locals).index.val) :
    (state.advanceAll variables).materialMap wire =
      state.retainAll variables (state.materialMap wire) := by
  induction variables generalizing state with
  | nil => rfl
  | @cons signature signatures selected tail induction =>
      change
        ((state.advance selected).advanceAll tail).materialMap wire =
          (state.advance selected).retainAll tail
            (Identification.retainWire outer state.locals signature 1
              (state.materialMap wire))
      rw [induction (state := state.advance selected)
        (different := fun position => different position.succ)]
      change (state.advance selected).retainAll tail
        (redirectMaterial state.materialMap selected wire) = _
      rw [redirectMaterial_other state.materialMap selected wire
        (by simpa using different 0)]

private theorem State.retainAll_index
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (wire : Var (outer ++ state.locals) signature) :
    (state.retainAll variables wire).index.val = wire.index.val := by
  induction variables generalizing state with
  | nil => rfl
  | @cons selectedSignature signatures selected tail induction =>
      change
        ((state.advance selected).retainAll tail
          (Identification.retainWire outer state.locals
            selectedSignature 1 wire)).index.val = wire.index.val
      calc
        _ = (Identification.retainWire outer state.locals
              selectedSignature 1 wire).index.val :=
          induction (state := state.advance selected)
            (wire := Identification.retainWire outer state.locals
              selectedSignature 1 wire)
        _ = _ := retainWire_index wire

private theorem State.advanceAll_materialMap_get_index
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (injective : VariablesIndexInjective variables)
    (wire : Var materialWires signature)
    (position : Fin signatures.length)
    (selectedIndex : wire.index.val =
      (variables.get position).index.val) :
    ((state.advanceAll variables).materialMap
      (wire.appendLeft material.locals)).index.val =
        (outer ++ state.locals).length + position.val := by
  induction variables generalizing state wire with
  | nil => exact Fin.elim0 position
  | @cons selectedSignature signatures selected tail induction =>
      revert selectedIndex
      refine Fin.cases (fun selectedIndex => ?_)
        (fun rest selectedIndex => ?_) position
      · let next := state.advance selected
        have different : ∀ tailPosition : Fin signatures.length,
            (wire.appendLeft material.locals).index.val ≠
              ((tail.get tailPosition).appendLeft material.locals).index.val := by
          intro tailPosition equality
          have positions := injective 0 tailPosition.succ (by
            simpa only [Var.index_appendLeft, selectedIndex] using equality)
          have values := congrArg Fin.val positions
          simp at values
        have retained := State.advanceAll_materialMap_other next tail
          (wire.appendLeft material.locals) different
        calc
          ((next.advanceAll tail).materialMap
              (wire.appendLeft material.locals)).index.val =
              (next.retainAll tail
                (next.materialMap
                  (wire.appendLeft material.locals))).index.val :=
            congrArg (fun mapped => mapped.index.val) retained
          _ = (next.materialMap
                (wire.appendLeft material.locals)).index.val :=
            State.retainAll_index next tail _
          _ = (Identification.freshLocalWire outer state.locals
                selectedSignature (0 : Fin 1)).index.val :=
            (redirectMaterial_fresh_index_iff state.materialMap selected
              (wire.appendLeft material.locals)).mpr (by
                simpa only [Var.index_appendLeft] using selectedIndex)
          _ = (outer ++ state.locals).length + (0 : Fin _).val := by
            simp [Identification.freshLocalWire]
      · have tailInjective : VariablesIndexInjective tail := by
          intro first second equality
          have positions := injective first.succ second.succ (by
            simpa using equality)
          apply Fin.ext
          have values := congrArg Fin.val positions
          simpa using values
        have recurse := induction (state := state.advance selected)
          tailInjective wire rest (by simpa using selectedIndex)
        change
          (((state.advance selected).advanceAll tail).materialMap
            (wire.appendLeft material.locals)).index.val =
              (outer ++ state.locals).length + rest.succ.val
        calc
          _ = (outer ++ (state.advance selected).locals).length + rest.val :=
            recurse
          _ = _ := by
            simp only [State.advance, List.length_append,
              List.length_singleton, Fin.val_succ]
            omega

/-- Equality nodes generated by a batch, in boundary order rather than the
front-insertion order used by the operational fold. -/
private def State.batchEqualities
    (state : State outer materialWires material) :
    {signatures : List Sig} -> (variables : Vars materialWires signatures) ->
      ItemSeq (outer ++ (state.advanceAll variables).locals)
  | [], .nil => .nil
  | _ :: _, .cons selected tail =>
      .cons
        ((equalityNode state selected).renameWires
          ((state.advance selected).retainAll tail))
        ((state.advance selected).batchEqualities tail)

/-- Optional unary support nodes generated by a batch, in boundary order. -/
private def State.batchSupports
    (state : State outer materialWires material) :
    {signatures : List Sig} -> (variables : Vars materialWires signatures) ->
      ItemSeq (outer ++ (state.advanceAll variables).locals)
  | [], .nil => .nil
  | _ :: _, .cons selected tail =>
      ((supportSuffix state selected).renameWires
        ((state.advance selected).retainAll tail)).append
        ((state.advance selected).batchSupports tail)

private def State.batchLeft
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures) :
    Vars (outer ++ (state.advanceAll variables).locals) signatures :=
  variables.map fun selected =>
    state.retainAll variables
      (state.materialMap (selected.appendLeft material.locals))

private def State.batchRight
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures) :
    Vars (outer ++ (state.advanceAll variables).locals) signatures :=
  variables.map fun selected =>
    (state.advanceAll variables).materialMap
      (selected.appendLeft material.locals)

private theorem Vars.map_congr
    (variables : Vars source signatures)
    (first second : ∀ {signature},
      Var source signature → Var target signature)
    (equal : ∀ {signature} (wire : Var source signature),
      first wire = second wire) :
    variables.map first = variables.map second := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map]
      rw [equal head, induction]

private theorem Vars.map_map
    (variables : Vars source signatures)
    (first : ∀ {signature}, Var source signature → Var middle signature)
    (second : ∀ {signature}, Var middle signature → Var target signature) :
    (variables.map first).map second =
      variables.map (fun wire => second (first wire)) := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons (second (first head))) induction

private theorem Vars.map_eq_of_position
    (variables : Vars source signatures)
    (first second : ∀ {signature},
      Var source signature → Var target signature)
    (equal : ∀ position : Fin signatures.length,
      first (variables.get position) = second (variables.get position)) :
    variables.map first = variables.map second := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map]
      have headEq : first head = second head := by
        simpa using equal 0
      rw [headEq]
      apply congrArg (Vars.cons (second head))
      apply induction
      intro position
      simpa using equal position.succ

private theorem State.advanceAll_after
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures) :
    (state.advanceAll variables).after =
      (state.after.renameWires (state.retainAll variables)).append
        (state.batchSupports variables) := by
  induction variables generalizing state with
  | nil =>
      simp [State.advanceAll, State.retainAll, State.batchSupports,
        ItemSeq.renameWires_id]
  | @cons signature signatures selected tail induction =>
      change ((state.advance selected).advanceAll tail).after =
        (state.after.renameWires
          (WireRenaming.comp ((state.advance selected).retainAll tail)
            (Identification.retainWire outer state.locals signature 1))).append
          (((supportSuffix state selected).renameWires
            ((state.advance selected).retainAll tail)).append
            ((state.advance selected).batchSupports tail))
      rw [induction (state := state.advance selected)]
      let retain := Identification.retainWire outer state.locals signature 1
      let tailRetain := (state.advance selected).retainAll tail
      let rest := (state.advance selected).batchSupports tail
      have nextAfter : (state.advance selected).after =
          (state.after.renameWires retain).append
            (supportSuffix state selected) := rfl
      rw [nextAfter]
      calc
        (((state.after.renameWires retain).append
              (supportSuffix state selected)).renameWires tailRetain).append rest =
            (((state.after.renameWires retain).renameWires tailRetain).append
              ((supportSuffix state selected).renameWires tailRetain)).append
                rest := congrArg (fun items => items.append rest)
                  (ItemSeq.renameWires_append _ _ _)
        _ = ((state.after.renameWires
              (WireRenaming.comp tailRetain retain)).append
              ((supportSuffix state selected).renameWires tailRetain)).append
                rest := congrArg
                  (fun items => (items.append
                    ((supportSuffix state selected).renameWires
                      tailRetain)).append rest)
                  (ItemSeq.renameWires_comp state.after retain tailRetain)
        _ = (state.after.renameWires
              (WireRenaming.comp tailRetain retain)).append
              (((supportSuffix state selected).renameWires tailRetain).append
                rest) := ItemSeq.append_assoc _ _ _

private theorem State.batchSupports_eq
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (injective : VariablesIndexInjective variables) :
    state.batchSupports variables =
      (supportPins material signatures variables).renameWires
        (state.advanceAll variables).materialMap := by
  induction variables generalizing state with
  | nil => rfl
  | @cons signature signatures selected tail induction =>
      let next := state.advance selected
      let tailRetain := next.retainAll tail
      have tailInjective : VariablesIndexInjective tail := by
        intro first second equality
        have positions := injective first.succ second.succ (by
          simpa using equality)
        apply Fin.ext
        have values := congrArg Fin.val positions
        simpa using values
      have selectedDifferent : ∀ position : Fin signatures.length,
          (selected.appendLeft material.locals).index.val ≠
            ((tail.get position).appendLeft material.locals).index.val := by
        intro position equality
        have positions := injective 0 position.succ (by
          simpa only [Var.index_appendLeft] using equality)
        have values := congrArg Fin.val positions
        simp at values
      have selectedFinal :
          (next.advanceAll tail).materialMap
              (selected.appendLeft material.locals) =
            tailRetain
              (Identification.freshLocalWire outer state.locals
                signature (0 : Fin 1)) := by
        calc
          _ = tailRetain
              (next.materialMap
                (selected.appendLeft material.locals)) :=
            State.advanceAll_materialMap_other next tail
              (selected.appendLeft material.locals) selectedDifferent
          _ = _ := congrArg (fun wire => tailRetain wire)
            (redirectMaterial_selected state.materialMap selected)
      have tailEq := induction (state := next) tailInjective
      change
        ((supportSuffix state selected).renameWires tailRetain).append
            (next.batchSupports tail) =
          (supportPins material (signature :: signatures)
            (.cons selected tail)).renameWires
              (next.advanceAll tail).materialMap
      by_cases unused : material.incidencePaths selected.index.val = []
      · have pinEq :
            (Item.identity signature 1 (fun _ =>
              Identification.freshLocalWire outer state.locals
                signature (0 : Fin 1))).renameWires tailRetain =
            (Item.identity signature 1 (fun _ =>
              selected.appendLeft material.locals)).renameWires
                (next.advanceAll tail).materialMap := by
          simp only [Item.renameWires]
          apply congrArg (Item.identity signature 1)
          funext position
          exact selectedFinal.symm
        rw [tailEq]
        simp only [supportSuffix, supportPins, unused, if_pos,
          ItemSeq.renameWires]
        exact congrArg (fun item => ItemSeq.cons item
          ((supportPins material signatures tail).renameWires
            (next.advanceAll tail).materialMap)) pinEq
      · simpa [State.batchSupports, supportSuffix, supportPins, unused,
          next, tailRetain] using tailEq

private theorem State.batchEqualities_eq
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (injective : VariablesIndexInjective variables) :
    state.batchEqualities variables =
      Comprehension.Instantiation.equalityItems
        (state.batchLeft variables) (state.batchRight variables) := by
  induction variables generalizing state with
  | nil => rfl
  | @cons signature signatures selected tail induction =>
      let next := state.advance selected
      let tailRetain := next.retainAll tail
      have tailInjective : VariablesIndexInjective tail := by
        intro first second equality
        have positions := injective first.succ second.succ (by
          simpa using equality)
        apply Fin.ext
        have values := congrArg Fin.val positions
        simpa using values
      have selectedDifferent : ∀ position : Fin signatures.length,
          (selected.appendLeft material.locals).index.val ≠
            ((tail.get position).appendLeft material.locals).index.val := by
        intro position equality
        have positions := injective 0 position.succ (by
          simpa only [Var.index_appendLeft] using equality)
        have values := congrArg Fin.val positions
        simp at values
      have selectedFinal :
          (next.advanceAll tail).materialMap
              (selected.appendLeft material.locals) =
            tailRetain
              (Identification.freshLocalWire outer state.locals
                signature (0 : Fin 1)) := by
        calc
          _ = tailRetain
              (next.materialMap
                (selected.appendLeft material.locals)) :=
            State.advanceAll_materialMap_other next tail
              (selected.appendLeft material.locals) selectedDifferent
          _ = _ := congrArg (fun wire => tailRetain wire)
            (redirectMaterial_selected state.materialMap selected)
      have tailLeft : next.batchLeft tail =
          tail.map (fun wire =>
            state.retainAll (.cons selected tail)
              (state.materialMap
                (wire.appendLeft material.locals))) := by
        unfold State.batchLeft
        apply Vars.map_eq_of_position
        intro position
        change tailRetain
            (next.materialMap
              ((tail.get position).appendLeft material.locals)) =
          tailRetain
            (Identification.retainWire outer state.locals signature 1
              (state.materialMap
                ((tail.get position).appendLeft material.locals)))
        apply congrArg (fun mapped => tailRetain mapped)
        apply redirectMaterial_other_external state.materialMap selected
          (tail.get position)
        intro equality
        have positions := injective position.succ 0 equality
        have values := congrArg Fin.val positions
        simp at values
      have tailEq := induction (state := next) tailInjective
      have headEq :
          (equalityNode state selected).renameWires tailRetain =
            .identity signature 2
              (Comprehension.Instantiation.equalityPorts
                (state.retainAll (.cons selected tail)
                  (state.materialMap
                    (selected.appendLeft material.locals)))
                ((next.advanceAll tail).materialMap
                  (selected.appendLeft material.locals))) := by
        unfold equalityNode
        simp only [Item.renameWires]
        apply congrArg (Item.identity signature 2)
        funext position
        refine Fin.cases rfl (fun _ => ?_) position
        exact selectedFinal.symm
      change
        .cons ((equalityNode state selected).renameWires tailRetain)
            (next.batchEqualities tail) =
          Comprehension.Instantiation.equalityItems
            (state.batchLeft (.cons selected tail))
            (state.batchRight (.cons selected tail))
      rw [tailEq, tailLeft]
      simp only [State.batchLeft, State.batchRight, Vars.map,
        Comprehension.Instantiation.equalityItems]
      exact congrArg (fun item => ItemSeq.cons item
        (Comprehension.Instantiation.equalityItems
          (tail.map fun wire =>
            state.retainAll (.cons selected tail)
              (state.materialMap (wire.appendLeft material.locals)))
          (tail.map fun wire =>
            (next.advanceAll tail).materialMap
              (wire.appendLeft material.locals)))) headEq

private noncomputable def State.advanceAll_beforeIso
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures) :
    ItemSeqIso
      (WireEquiv.refl (outer ++ (state.advanceAll variables).locals))
      (state.advanceAll variables).before
      ((state.before.renameWires (state.retainAll variables)).append
        (state.batchEqualities variables)) := by
  induction variables generalizing state with
  | nil =>
      simpa [State.advanceAll, State.retainAll, State.batchEqualities,
        ItemSeq.renameWires_id] using ItemSeqIso.refl state.before
  | @cons signature signatures selected tail induction =>
      let next := state.advance selected
      let tailRetain := next.retainAll tail
      let node := (equalityNode state selected).renameWires tailRetain
      let base := state.before.renameWires
        (WireRenaming.comp tailRetain
          (Identification.retainWire outer state.locals signature 1))
      let equalities := next.batchEqualities tail
      have beforeMap :
          (state.before.renameWires
              (Identification.retainWire outer state.locals signature 1)).renameWires
                tailRetain = base := by
        exact ItemSeq.renameWires_comp state.before
          (Identification.retainWire outer state.locals signature 1)
          tailRetain
      have nextBefore : next.before.renameWires tailRetain =
          ItemSeq.cons node base := by
        change
          (ItemSeq.cons (equalityNode state selected)
            (state.before.renameWires
              (Identification.retainWire outer state.locals signature 1))).renameWires
                tailRetain = ItemSeq.cons node base
        simp only [ItemSeq.renameWires]
        exact congrArg (ItemSeq.cons node) beforeMap
      have first := induction (state := next)
      rw [nextBefore] at first
      have swap : ItemSeqIso
          (WireEquiv.refl (outer ++ (next.advanceAll tail).locals))
          ((ItemSeq.cons node base).append equalities)
          (base.append (ItemSeq.cons node equalities)) := by
        let swapped := ItemSeqIso.append
          (ItemSeqIso.swapAppend (ItemSeq.cons node .nil) base)
          (ItemSeqIso.refl equalities)
        simpa only [ItemSeq.nil_append, ItemSeq.append_nil,
          ItemSeq.append_assoc] using swapped
      have composed := first.trans swap
      have composed' := composed.castAmbient
        (WireEquiv.trans_refl
          (WireEquiv.refl (outer ++ (next.advanceAll tail).locals)))
      simpa [next, tailRetain, node, base, equalities,
        State.advanceAll, State.retainAll, State.batchEqualities] using composed'

private noncomputable def State.advanceAll_itemsIso
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (afterEmpty : state.after = .nil) :
    ItemSeqIso
      (WireEquiv.refl (outer ++ (state.advanceAll variables).locals))
      (state.advanceAll variables).items
      ((state.before.renameWires (state.retainAll variables)).append
        ((material.items.renameWires
            (state.advanceAll variables).materialMap).append
          ((state.batchSupports variables).append
            (state.batchEqualities variables)))) := by
  let final := state.advanceAll variables
  let base := state.before.renameWires (state.retainAll variables)
  let equalities := state.batchEqualities variables
  let materialItems := material.items.renameWires final.materialMap
  let supports := state.batchSupports variables
  have finalAfter : final.after = supports := by
    have presentation := State.advanceAll_after state variables
    rw [afterEmpty] at presentation
    simpa [final, supports] using presentation
  have beforeIso : ItemSeqIso
      (WireEquiv.refl (outer ++ final.locals)) final.before
      (base.append equalities) := by
    simpa [final, base, equalities] using
      State.advanceAll_beforeIso state variables
  have trailing : ItemSeqIso
      (WireEquiv.refl (outer ++ final.locals))
      (materialItems.append final.after)
      (materialItems.append supports) := by
    rw [finalAfter]
    exact ItemSeqIso.refl _
  let first := ItemSeqIso.append beforeIso trailing
  have reordered : ItemSeqIso
      (WireEquiv.refl (outer ++ final.locals))
      ((base.append equalities).append
        (materialItems.append supports))
      (base.append
        ((materialItems.append supports).append equalities)) := by
    let swapped := ItemSeqIso.append (ItemSeqIso.refl base)
      (ItemSeqIso.swapAppend equalities
        (materialItems.append supports))
    simpa only [ItemSeq.append_assoc] using swapped
  have composed := first.trans reordered
  have composed' := composed.castAmbient
    (WireEquiv.trans_refl (WireEquiv.refl (outer ++ final.locals)))
  simpa [final, base, equalities, materialItems, supports, State.items,
    ItemSeq.append_assoc] using composed'

private def sourceSupportSuffix
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    ItemSeq (outer ++ state.locals) :=
  if material.incidencePaths selected.index.val = [] then
    .cons (.identity signature 1 (fun _ => state.materialMap
      (selected.appendLeft material.locals))) .nil
  else
    .nil

private theorem pinStep
    {boundary holeWires locals : List Sig}
    {items : ItemSeq (holeWires ++ locals)}
    {source : OpenDiagram boundary}
    (occurrence : Occurrence (Vacuity.Pin.plain locals items) source)
    (signature : Sig) (wire : Var (holeWires ++ locals) signature) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Vacuity.Pin.present locals items signature wire)).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Vacuity.Pin.present locals items signature wire)),
        Step source
          (occurrence.interface.withBody
            (occurrence.context.fill
              (Vacuity.Pin.present locals items signature wire))
            targetCanonical targetExternalTwoEnded) := by
  have validity := Vacuity.Pin.introduceValidity occurrence signature wire
  refine ⟨validity.1, validity.2, Step.vacuity ?_⟩
  exact ⟨holeWires, Vacuity.Pin.plain locals items,
    Vacuity.Pin.present locals items signature wire, occurrence,
    validity.1, validity.2, OpenDiagramIso.refl _,
    atPolarity_symmetric_of occurrence.context.polarity
      (.mk (.pin locals items signature wire))⟩

private def advanceAway
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    ItemSeq (outer ++ (state.locals ++ [signature])) :=
  (state.before.renameWires
      (Identification.retainWire outer state.locals signature 1)).append
    ((material.items.renameWires
      (redirectMaterial state.materialMap selected)).append
      ((state.after.renameWires
        (Identification.retainWire outer state.locals signature 1)).append
        (supportSuffix state selected)))

@[simp] private theorem State.advance_items
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (state.advance selected).items =
      .cons (equalityNode state selected) (advanceAway state selected) := rfl

private theorem ItemSeq.rename_retained_collapse
    (items : ItemSeq (outer ++ locals))
    (survivor : Var (outer ++ locals) signature) :
    (items.renameWires
      (Identification.retainWire outer locals signature 1)).renameWires
        (Identification.collapseLocal outer locals survivor 1) = items := by
  rw [ItemSeq.renameWires_comp]
  have maps : WireRenaming.comp
      (Identification.collapseLocal outer locals survivor 1)
      (Identification.retainWire outer locals signature 1) =
      WireRenaming.id := by
    apply WireRenaming.ext
    intro wireSignature wire
    exact Identification.collapseLocal_retained survivor 1 wire
  rw [maps, ItemSeq.renameWires_id]

private theorem supportSuffix_collapse
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (supportSuffix state selected).renameWires
      (Identification.collapseLocal outer state.locals
        (state.materialMap (selected.appendLeft material.locals)) 1) =
      sourceSupportSuffix state selected := by
  simp only [supportSuffix, sourceSupportSuffix]
  split
  · simp [ItemSeq.renameWires, Item.renameWires,
      Identification.collapseLocal_fresh]
  · rfl

private theorem advanceAway_collapse
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (advanceAway state selected).renameWires
      (Identification.collapseLocal outer state.locals
        (state.materialMap (selected.appendLeft material.locals)) 1) =
      state.items.append (sourceSupportSuffix state selected) := by
  let collapse := Identification.collapseLocal outer state.locals
    (state.materialMap (selected.appendLeft material.locals)) 1
  have beforeEq :
      (state.before.renameWires
        (Identification.retainWire outer state.locals signature 1)).renameWires
          collapse = state.before := by
    exact ItemSeq.rename_retained_collapse state.before
      (state.materialMap (selected.appendLeft material.locals))
  have materialEq :
      (material.items.renameWires
        (redirectMaterial state.materialMap selected)).renameWires collapse =
          material.items.renameWires state.materialMap := by
    have maps : WireRenaming.comp collapse
        (redirectMaterial state.materialMap selected) = state.materialMap := by
      apply WireRenaming.ext
      intro wireSignature wire
      exact redirectMaterial_collapse state.materialMap selected wire
    calc
      _ = material.items.renameWires
          (WireRenaming.comp collapse
            (redirectMaterial state.materialMap selected)) :=
        ItemSeq.renameWires_comp _ _ _
      _ = material.items.renameWires state.materialMap :=
        congrArg (fun rename => material.items.renameWires rename) maps
  have afterEq :
      (state.after.renameWires
        (Identification.retainWire outer state.locals signature 1)).renameWires
          collapse = state.after := by
    exact ItemSeq.rename_retained_collapse state.after
      (state.materialMap (selected.appendLeft material.locals))
  have suffixEq :
      (supportSuffix state selected).renameWires collapse =
        sourceSupportSuffix state selected := by
    exact supportSuffix_collapse state selected
  change
    ((state.before.renameWires
      (Identification.retainWire outer state.locals signature 1)).append
      ((material.items.renameWires
        (redirectMaterial state.materialMap selected)).append
        ((state.after.renameWires
          (Identification.retainWire outer state.locals signature 1)).append
          (supportSuffix state selected)))).renameWires collapse =
      (state.before.append
        ((material.items.renameWires state.materialMap).append
          state.after)).append (sourceSupportSuffix state selected)
  calc
    _ = ((state.before.renameWires
            (Identification.retainWire outer state.locals signature 1)).renameWires
              collapse).append
        (((material.items.renameWires
            (redirectMaterial state.materialMap selected)).append
            ((state.after.renameWires
              (Identification.retainWire outer state.locals signature 1)).append
              (supportSuffix state selected))).renameWires collapse) :=
      ItemSeq.renameWires_append _ _ _
    _ = state.before.append
        ((material.items.renameWires state.materialMap).append
          (state.after.append (sourceSupportSuffix state selected))) := by
      rw [beforeEq]
      apply congrArg (fun rest => state.before.append rest)
      calc
        _ = ((material.items.renameWires
                (redirectMaterial state.materialMap selected)).renameWires
                  collapse).append
            (((state.after.renameWires
                (Identification.retainWire outer state.locals signature 1)).append
                (supportSuffix state selected)).renameWires collapse) :=
          ItemSeq.renameWires_append _ _ _
        _ = (material.items.renameWires state.materialMap).append
            (state.after.append (sourceSupportSuffix state selected)) := by
          rw [materialEq]
          apply congrArg (fun rest =>
            (material.items.renameWires state.materialMap).append rest)
          calc
            _ = ((state.after.renameWires
                    (Identification.retainWire outer state.locals signature 1)).renameWires
                      collapse).append
                ((supportSuffix state selected).renameWires collapse) :=
              ItemSeq.renameWires_append _ _ _
            _ = state.after.append (sourceSupportSuffix state selected) :=
              by rw [afterEq, suffixEq]
    _ = _ := by rw [ItemSeq.append_assoc, ItemSeq.append_assoc]

private def exposureNodeData
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    Identification.NodeData (outer ++ state.locals) signature 1 where
  survivor := state.materialMap (selected.appendLeft material.locals)
  retainedArity := 1
  retainedPorts := fun _ =>
    state.materialMap (selected.appendLeft material.locals)
  survivorPort := ⟨0, rfl⟩
  exposedArity := 2
  expansion := .retain (.absorb 0 .nil)
  absorbedPort := by
    intro wire
    refine ⟨1, ?_⟩
    have wireEq : wire = (0 : Fin 1) := Fin.ext (by omega)
    subst wire
    rfl

private theorem exposureNodeData_exposedNode
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureNodeData state selected).exposedNode
      (Identification.retainWire outer state.locals signature 1)
      (Identification.freshLocalWire outer state.locals signature) =
        equalityNode state selected := by
  apply congrArg (Item.identity signature 2)
  funext position
  refine Fin.cases rfl (fun rest => ?_) position
  have restEq : rest = (0 : Fin 1) := Fin.ext (by omega)
  subst rest
  rfl

@[simp] private theorem exposureNodeData_survivor
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureNodeData state selected).survivor =
      state.materialMap (selected.appendLeft material.locals) := rfl

private noncomputable def exposurePartition
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    ItemSeq.PortPartition
      (Identification.collapseLocal outer state.locals
        (state.materialMap (selected.appendLeft material.locals)) 1)
      ((advanceAway state selected).renameWires
        (Identification.collapseLocal outer state.locals
          (state.materialMap (selected.appendLeft material.locals)) 1)) :=
  Classical.choose (ItemSeq.exists_partition_of_renamed
    (Identification.collapseLocal outer state.locals
      (state.materialMap (selected.appendLeft material.locals)) 1)
    (advanceAway state selected))

private theorem exposurePartition_output
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (((advanceAway state selected).renameWires
      (Identification.collapseLocal outer state.locals
        (state.materialMap (selected.appendLeft material.locals)) 1)).partitionOutput
      (Identification.collapseLocal outer state.locals
        (state.materialMap (selected.appendLeft material.locals)) 1)
      (exposurePartition state selected)) = advanceAway state selected :=
  Classical.choose_spec (ItemSeq.exists_partition_of_renamed
    (Identification.collapseLocal outer state.locals
      (state.materialMap (selected.appendLeft material.locals)) 1)
    (advanceAway state selected))

private noncomputable def exposureData
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    Identification.Local.Data outer where
  locals := state.locals
  signature := signature
  count := 1
  countPositive := Nat.zero_lt_succ 0
  node := exposureNodeData state selected
  away := (advanceAway state selected).renameWires
    (Identification.collapseLocal outer state.locals
      (state.materialMap (selected.appendLeft material.locals)) 1)
  awayPartition := exposurePartition state selected

@[simp] private theorem exposureData_survivor
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).node.survivor =
      state.materialMap (selected.appendLeft material.locals) := rfl

@[simp] private theorem exposureData_locals
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).locals = state.locals := rfl

@[simp] private theorem exposureData_signature
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).signature = signature := rfl

@[simp] private theorem exposureData_count
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).count = 1 := rfl

@[simp] private theorem exposureData_node
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).node = exposureNodeData state selected := rfl

@[simp] private theorem exposureData_away
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).away =
      (advanceAway state selected).renameWires
        (Identification.collapseLocal outer state.locals
          (state.materialMap (selected.appendLeft material.locals)) 1) := rfl

@[simp] private theorem exposureData_awayPartition
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).awayPartition =
      exposurePartition state selected := rfl

private theorem exposureData_collapsedRegion
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).collapsedRegion =
      .mk state.locals
        (.cons (.identity signature 1 (fun _ =>
          state.materialMap (selected.appendLeft material.locals)))
          (state.items.append (sourceSupportSuffix state selected))) := by
  simp only [Identification.Local.Data.collapsedRegion, exposureData,
    exposureNodeData, Identification.NodeData.collapsedNode]
  rw [advanceAway_collapse]

private theorem exposureData_exposedRegion
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (exposureData state selected).exposedRegion =
      (state.advance selected).region := by
  simp only [Identification.Local.Data.exposedRegion,
    Identification.Local.Data.exposedAway, exposureData_locals,
    exposureData_signature, exposureData_count, exposureData_node,
    exposureNodeData_survivor, exposureData_away,
    exposureData_awayPartition]
  rw [exposurePartition_output]
  rw [exposureNodeData_exposedNode]
  simp only [State.advance, State.region, State.items, advanceAway,
    List.replicate_succ, List.replicate_zero]
  rfl

private theorem collapseLocal_reflects_otherExternal
    (survivor : Var (outer ++ locals) signature)
    (wireIndex : Fin outer.length)
    (different : survivor.index.val ≠ wireIndex.val)
    (wire : Var (outer ++ (locals ++ [signature])) wireSignature) :
    (Identification.collapseLocal outer locals survivor 1 wire).index.val =
        wireIndex.val ↔
      wire.index.val = wireIndex.val := by
  apply Var.appendCases (left := outer) (right := locals ++ [signature])
    (motive := fun wire =>
      (Identification.collapseLocal outer locals survivor 1 wire).index.val =
          wireIndex.val ↔
        wire.index.val = wireIndex.val)
  · intro inheritedSignature inherited
    simp [Identification.collapseLocal]
  · intro localSignature localWire
    apply Var.appendCases (left := locals) (right := [signature])
      (motive := fun localWire =>
        (Identification.collapseLocal outer locals survivor 1
          (Var.appendRight outer localWire)).index.val = wireIndex.val ↔
        (Var.appendRight outer localWire).index.val = wireIndex.val)
    · intro retainedSignature retainedLocal
      simp [Identification.collapseLocal]
    · intro freshSignature fresh
      have freshEq : freshSignature = signature := by
        cases fresh with
        | here => rfl
        | there tail => nomatch tail
      subst freshSignature
      have freshPosition : fresh = (Var.here : Var [signature] signature) := by
        cases fresh with
        | here => rfl
        | there tail => nomatch tail
      subst fresh
      simp [Identification.collapseLocal]
      have bound := wireIndex.isLt
      constructor <;> intro equality
      · exact False.elim (different (by simpa using equality))
      · omega

private theorem collapseLocal_reflects_otherWire
    (survivor : Var (outer ++ locals) signature)
    (selectedWire : Var (outer ++ locals) selectedSignature)
    (different : survivor.index.val ≠ selectedWire.index.val)
    (wire : Var (outer ++ (locals ++ [signature])) wireSignature) :
    (Identification.collapseLocal outer locals survivor 1 wire).index.val =
        selectedWire.index.val ↔
      wire.index.val = selectedWire.index.val := by
  apply Var.appendCases (left := outer) (right := locals ++ [signature])
    (motive := fun wire =>
      (Identification.collapseLocal outer locals survivor 1 wire).index.val =
          selectedWire.index.val ↔
        wire.index.val = selectedWire.index.val)
  · intro inheritedSignature inherited
    simp [Identification.collapseLocal]
  · intro localSignature localWire
    apply Var.appendCases (left := locals) (right := [signature])
      (motive := fun localWire =>
        (Identification.collapseLocal outer locals survivor 1
          (Var.appendRight outer localWire)).index.val = selectedWire.index.val ↔
        (Var.appendRight outer localWire).index.val = selectedWire.index.val)
    · intro retainedSignature retainedLocal
      simp [Identification.collapseLocal]
    · intro freshSignature fresh
      have freshEq : freshSignature = signature := by
        cases fresh with
        | here => rfl
        | there tail => nomatch tail
      subst freshSignature
      have freshPosition : fresh = (Var.here : Var [signature] signature) := by
        cases fresh with
        | here => rfl
        | there tail => nomatch tail
      subst fresh
      simp [Identification.collapseLocal]
      have selectedBound := selectedWire.index.isLt
      constructor <;> intro equality
      · exact False.elim (different (by simpa using equality))
      · simp only [List.length_append] at selectedBound
        omega

private theorem exposureData_applicability
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    Identification.Local.Applicability (exposureData state selected) := by
  constructor
  intro wireIndex
  let data := exposureData state selected
  let survivor := state.materialMap
    (selected.appendLeft material.locals)
  by_cases equal : survivor.index.val = wireIndex.val
  · rw [exposureData_collapsedRegion, exposureData_exposedRegion]
    simp only [Region.incidencePaths, State.advance, State.region, State.items,
      ItemSeq.incidencePaths]
    constructor <;> intro _
    · intro empty
      have headEmpty := (List.append_eq_nil_iff.mp empty).1
      have selectedEq :
          (state.materialMap
            (selected.appendLeft material.locals)).index.val = wireIndex.val := by
        simpa [survivor] using equal
      have retainedSelected :
          (Identification.retainWire outer state.locals signature 1
            (state.materialMap
              (selected.appendLeft material.locals))).index.val =
            wireIndex.val :=
        (retainWire_index
          (signature := signature) (count := 1)
          (state.materialMap
            (selected.appendLeft material.locals))).trans selectedEq
      have headNonempty :
          (equalityNode state selected).incidencePaths wireIndex.val 0 ≠ [] := by
        simp only [equalityNode, Item.incidencePaths]
        intro empty
        have countZero := (List.replicate_eq_nil_iff []).mp empty
        exact (List.count_eq_zero.mp countZero)
          (List.mem_ofFn.mpr ⟨0, retainedSelected⟩)
      exact headNonempty headEmpty
    · intro empty
      have headEmpty := (List.append_eq_nil_iff.mp empty).1
      have selectedEq :
          (state.materialMap
            (selected.appendLeft material.locals)).index.val = wireIndex.val := by
        simpa [survivor] using equal
      have headNonempty :
          (Item.identity signature 1 (fun _ => state.materialMap
            (selected.appendLeft material.locals))).incidencePaths
              wireIndex.val 0 ≠ [] := by
        simp [Item.incidencePaths, selectedEq]
      exact headNonempty headEmpty
  · have renamedPaths :=
      ItemSeq.incidencePaths_renameWires_of_index_iff
        data.exposedAway
        (Identification.collapseLocal outer data.locals
          data.node.survivor data.count)
        wireIndex.val wireIndex.val 0
        (by
          have bound := wireIndex.isLt
          simp only [data, exposureData, List.length_append,
            List.length_replicate]
          omega)
        (by
          have bound := wireIndex.isLt
          simp only [data, exposureData, List.length_append]
          omega)
        (by
          intro wireSignature wire
          simpa [data, exposureData, exposureNodeData, survivor] using
            collapseLocal_reflects_otherExternal survivor wireIndex equal wire)
    rw [Identification.Local.collapsedRegion_rename] at renamedPaths
    simp only [Identification.Local.Data.collapsedRegion,
      Identification.Local.Data.exposedRegion, Region.incidencePaths,
      ItemSeq.incidencePaths, Identification.NodeData.collapsedNode,
      Identification.NodeData.exposedNode]
    have retainedDifferent :
        (Identification.retainWire outer state.locals signature 1 survivor).index.val ≠
          wireIndex.val := by
      have retainedIndex :
          (Identification.retainWire outer state.locals signature 1
            survivor).index.val = survivor.index.val := by
        exact retainWire_index (signature := signature) (count := 1) survivor
      rw [retainedIndex]
      exact equal
    have freshDifferent :
        (Identification.freshLocalWire outer state.locals signature
          (0 : Fin 1)).index.val ≠ wireIndex.val := by
      have bound := wireIndex.isLt
      simp [Identification.freshLocalWire]
      omega
    have awayNonempty :
        data.away.incidencePaths wireIndex.val 1 ≠ [] ↔
          data.exposedAway.incidencePaths wireIndex.val 1 ≠ [] :=
      by
        constructor
        · intro awayOneNonempty exposedOneEmpty
          have awayZeroNonempty :
              data.away.incidencePaths wireIndex.val 0 ≠ [] := by
            intro awayZeroEmpty
            exact awayOneNonempty
              ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex
                data.away wireIndex.val 0 1).mp awayZeroEmpty)
          have exposedZeroNonempty :
              data.exposedAway.incidencePaths wireIndex.val 0 ≠ [] := by
            rwa [← renamedPaths]
          exact exposedZeroNonempty
            ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex
              data.exposedAway wireIndex.val 0 1).mpr exposedOneEmpty)
        · intro exposedOneNonempty awayOneEmpty
          have exposedZeroNonempty :
              data.exposedAway.incidencePaths wireIndex.val 0 ≠ [] := by
            intro exposedZeroEmpty
            exact exposedOneNonempty
              ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex
                data.exposedAway wireIndex.val 0 1).mp exposedZeroEmpty)
          have awayZeroNonempty :
              data.away.incidencePaths wireIndex.val 0 ≠ [] := by
            rwa [renamedPaths]
          exact awayZeroNonempty
            ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex
              data.away wireIndex.val 0 1).mpr awayOneEmpty)
    have collapsedHeadEmpty :
        data.node.collapsedNode.incidencePaths wireIndex.val 0 = [] := by
      simp [data, exposureData, exposureNodeData, survivor, equal,
        Identification.NodeData.collapsedNode, Item.incidencePaths]
    have exposedHeadEmpty :
        (data.node.exposedNode
          (Identification.retainWire outer data.locals data.signature data.count)
          (Identification.freshLocalWire outer data.locals data.signature)).incidencePaths
            wireIndex.val 0 = [] := by
      have nodeEq :
          data.node.exposedNode
            (Identification.retainWire outer data.locals data.signature data.count)
            (Identification.freshLocalWire outer data.locals data.signature) =
              equalityNode state selected := by
        simpa [data, exposureData] using
          exposureNodeData_exposedNode state selected
      rw [nodeEq]
      simp only [equalityNode, Item.incidencePaths]
      apply (List.replicate_eq_nil_iff []).mpr
      apply List.count_eq_zero.mpr
      intro member
      obtain ⟨position, positionEq⟩ := List.mem_ofFn.mp member
      refine Fin.cases
        (fun equality => retainedDifferent equality)
        (fun rest equality => ?_) position positionEq
      have restEq : rest = (0 : Fin 1) := Fin.ext (by omega)
      subst rest
      exact freshDifferent equality
    change
      (data.node.collapsedNode.incidencePaths wireIndex.val 0 ++
          data.away.incidencePaths wireIndex.val 1 ≠ []) ↔
        ((data.node.exposedNode
          (Identification.retainWire outer data.locals data.signature data.count)
          (Identification.freshLocalWire outer data.locals data.signature)).incidencePaths
            wireIndex.val 0 ++
          data.exposedAway.incidencePaths wireIndex.val 1 ≠ [])
    rw [collapsedHeadEmpty, exposedHeadEmpty, List.nil_append, List.nil_append]
    exact awayNonempty

private theorem State.advance_childrenCanonical
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    (canonical : state.items.ChildrenCanonical) :
    (state.advance selected).items.ChildrenCanonical := by
  have sourceParts :=
    (ItemSeq.childrenCanonical_append state.before
      ((material.items.renameWires state.materialMap).append state.after)).mp
      canonical
  have sourceRest :=
    (ItemSeq.childrenCanonical_append
      (material.items.renameWires state.materialMap) state.after).mp
      sourceParts.2
  have beforeCanonical :
      (state.before.renameWires
        (Identification.retainWire outer state.locals signature 1)).ChildrenCanonical :=
    (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr sourceParts.1
  have materialCanonical :
      (material.items.renameWires
        (redirectMaterial state.materialMap selected)).ChildrenCanonical :=
    (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
      ((ItemSeq.ChildrenCanonical.renameWires_iff _ _).mp sourceRest.1)
  have afterCanonical :
      (state.after.renameWires
        (Identification.retainWire outer state.locals signature 1)).ChildrenCanonical :=
    (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr sourceRest.2
  have suffixCanonical :
      (supportSuffix state selected).ChildrenCanonical := by
    simp only [supportSuffix]
    split
    · exact ⟨True.intro, True.intro⟩
    · exact True.intro
  simp only [State.advance, State.items]
  exact ⟨True.intro,
    (ItemSeq.childrenCanonical_append _ _).mpr
      ⟨beforeCanonical,
        (ItemSeq.childrenCanonical_append _ _).mpr
          ⟨materialCanonical,
            (ItemSeq.childrenCanonical_append _ _).mpr
              ⟨afterCanonical, suffixCanonical⟩⟩⟩⟩

private theorem advanceAway_fresh_nonempty
    (state : State outer materialWires material)
    (selected : Var materialWires signature) :
    (advanceAway state selected).incidencePaths
      (Identification.freshLocalWire outer state.locals signature
        (0 : Fin 1)).index.val 1 ≠ [] := by
  let retain := Identification.retainWire outer state.locals signature 1
  let fresh := Identification.freshLocalWire outer state.locals signature
    (0 : Fin 1)
  let renamedBefore := state.before.renameWires retain
  let renamedMaterial := material.items.renameWires
    (redirectMaterial state.materialMap selected)
  let renamedAfter := state.after.renameWires retain
  by_cases unused : material.incidencePaths selected.index.val = []
  · have supportNonempty :
        (supportSuffix state selected).incidencePaths fresh.index.val
          (((1 + renamedBefore.length) + renamedMaterial.length) +
            renamedAfter.length) ≠ [] := by
      simp [supportSuffix, unused, fresh, ItemSeq.incidencePaths,
        Item.incidencePaths]
    have supportInAfter := ItemSeq.incidencePaths_append_right_sublist
      renamedAfter (supportSuffix state selected) fresh.index.val
      ((1 + renamedBefore.length) + renamedMaterial.length)
    have afterInMaterial := ItemSeq.incidencePaths_append_right_sublist
      renamedMaterial
      (renamedAfter.append (supportSuffix state selected)) fresh.index.val
      (1 + renamedBefore.length)
    have materialInBefore := ItemSeq.incidencePaths_append_right_sublist
      renamedBefore
      (renamedMaterial.append
        (renamedAfter.append (supportSuffix state selected)))
      fresh.index.val 1
    have supportSublist := supportInAfter.trans
      (afterInMaterial.trans materialInBefore)
    intro awayEmpty
    have supportEmpty :
        (supportSuffix state selected).incidencePaths fresh.index.val
          (((1 + renamedBefore.length) + renamedMaterial.length) +
            renamedAfter.length) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro path member
      have targetMember := supportSublist.mem member
      have targetMember' : path ∈
          (advanceAway state selected).incidencePaths fresh.index.val 1 := by
        simpa [advanceAway, renamedBefore, renamedMaterial,
          renamedAfter, retain] using targetMember
      rw [awayEmpty] at targetMember'
      simp at targetMember'
    exact supportNonempty supportEmpty
  · have materialPaths' :
        renamedMaterial.incidencePaths fresh.index.val 0 =
          material.items.incidencePaths
            (selected.appendLeft material.locals).index.val 0 := by
      apply ItemSeq.incidencePaths_renameWires_of_index_iff
      · exact (selected.appendLeft material.locals).index.isLt
      · exact fresh.index.isLt
      · intro wireSignature wire
        simpa [renamedMaterial, fresh] using
          (redirectMaterial_fresh_index_iff state.materialMap selected wire)
    have materialPaths :
        renamedMaterial.incidencePaths fresh.index.val 0 =
          material.items.incidencePaths selected.index.val 0 := by
      simpa using materialPaths'
    have materialNonemptyZero :
        renamedMaterial.incidencePaths fresh.index.val 0 ≠ [] := by
      rw [materialPaths]
      rw [Region.incidencePaths_eq_items] at unused
      exact unused
    have materialNonempty :
        renamedMaterial.incidencePaths fresh.index.val
          (1 + renamedBefore.length) ≠ [] := by
      intro empty
      exact materialNonemptyZero
        ((ItemSeq.incidencePaths_eq_nil_iff_itemIndex renamedMaterial
          fresh.index.val 0 (1 + renamedBefore.length)).mpr empty)
    have materialInRest := ItemSeq.incidencePaths_append_left_sublist
      renamedMaterial
      (renamedAfter.append (supportSuffix state selected)) fresh.index.val
      (1 + renamedBefore.length)
    have restInBefore := ItemSeq.incidencePaths_append_right_sublist
      renamedBefore
      (renamedMaterial.append
        (renamedAfter.append (supportSuffix state selected)))
      fresh.index.val 1
    have materialSublist := materialInRest.trans restInBefore
    intro awayEmpty
    have materialEmpty :
        renamedMaterial.incidencePaths fresh.index.val
          (1 + renamedBefore.length) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro path member
      have targetMember := materialSublist.mem member
      have targetMember' : path ∈
          (advanceAway state selected).incidencePaths fresh.index.val 1 := by
        simpa [advanceAway, renamedBefore, renamedMaterial,
          renamedAfter, retain] using targetMember
      rw [awayEmpty] at targetMember'
      simp at targetMember'
    exact materialNonempty materialEmpty

private theorem State.advance_canonical
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    (canonical : state.region.Canonical)
    (survivorSupported : ∀ localIndex : Fin state.locals.length,
      (state.materialMap
        (selected.appendLeft material.locals)).index.val =
          outer.length + localIndex.val →
      RegionPath.RootedTwo
        (state.before.incidencePaths
          (outer.length + localIndex.val) 0)) :
    (state.advance selected).region.Canonical := by
  constructor
  · intro localIndex
    by_cases old : localIndex.val < state.locals.length
    · let oldIndex : Fin state.locals.length := ⟨localIndex.val, old⟩
      let wireIndex := outer.length + oldIndex.val
      by_cases equal :
          (state.materialMap
            (selected.appendLeft material.locals)).index.val = wireIndex
      · have sourceRoot := survivorSupported oldIndex equal
        change RegionPath.RootedTwo
          ((state.advance selected).items.incidencePaths wireIndex 0)
        have shiftedRoot :=
          (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff
            state.before wireIndex 0 1).mpr sourceRoot
        have renamedPaths :
            (state.before.renameWires
              (Identification.retainWire outer state.locals signature 1)).incidencePaths
                wireIndex 1 =
              state.before.incidencePaths wireIndex 1 := by
          apply ItemSeq.incidencePaths_renameWires_of_index_iff
          · have bound := oldIndex.isLt
            simp only [wireIndex, List.length_append]
            omega
          · have bound := oldIndex.isLt
            simp only [wireIndex, List.length_append]
            omega
          · intro wireSignature wire
            rw [retainWire_index]
        rw [← renamedPaths] at shiftedRoot
        apply RegionPath.RootedTwo.of_sublist ?_ shiftedRoot
        rw [State.advance_items]
        simp only [ItemSeq.incidencePaths, Nat.zero_add]
        exact (ItemSeq.incidencePaths_append_left_sublist
          (state.before.renameWires
            (Identification.retainWire outer state.locals signature 1))
          ((material.items.renameWires
            (redirectMaterial state.materialMap selected)).append
            ((state.after.renameWires
              (Identification.retainWire outer state.locals signature 1)).append
              (supportSuffix state selected))) wireIndex 1).trans
          (List.sublist_append_right _ _)
      · let oldWire := Var.appendRight outer (Var.ofIndex oldIndex)
        have oldWireIndex : oldWire.index.val = wireIndex := by
          simp [oldWire, wireIndex]
        have sourceRoot : RegionPath.RootedTwo
            (state.items.incidencePaths wireIndex 0) := by
          simpa [State.region, wireIndex] using canonical.1 oldIndex
        have shiftedRoot :=
          (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff
            state.items wireIndex 0 1).mpr sourceRoot
        have collapsedRoot : RegionPath.RootedTwo
            ((state.items.append
              (sourceSupportSuffix state selected)).incidencePaths wireIndex 1) :=
          RegionPath.RootedTwo.of_sublist
            (ItemSeq.incidencePaths_append_left_sublist _ _ wireIndex 1)
            shiftedRoot
        rw [← advanceAway_collapse state selected] at collapsedRoot
        have different :
            (state.materialMap
              (selected.appendLeft material.locals)).index.val ≠
              oldWire.index.val := by
          simpa only [oldWireIndex] using equal
        have awayPaths :
            ((advanceAway state selected).renameWires
              (Identification.collapseLocal outer state.locals
                (state.materialMap
                  (selected.appendLeft material.locals)) 1)).incidencePaths
                wireIndex 1 =
              (advanceAway state selected).incidencePaths wireIndex 1 := by
          apply ItemSeq.incidencePaths_renameWires_of_index_iff
          · have bound := oldIndex.isLt
            simp only [wireIndex, List.length_append]
            omega
          · have bound := oldIndex.isLt
            simp only [wireIndex, List.length_append]
            omega
          · intro wireSignature wire
            simpa only [oldWireIndex] using
              (collapseLocal_reflects_otherWire
                (state.materialMap
                  (selected.appendLeft material.locals)) oldWire different wire)
        rw [awayPaths] at collapsedRoot
        change RegionPath.RootedTwo
          ((state.advance selected).items.incidencePaths wireIndex 0)
        apply RegionPath.RootedTwo.of_sublist ?_ collapsedRoot
        rw [State.advance_items]
        simp only [ItemSeq.incidencePaths, Nat.zero_add]
        exact List.sublist_append_right _ _
    · have localBound := localIndex.isLt
      change localIndex.val < (state.locals ++ [signature]).length at localBound
      have freshValue : localIndex.val = state.locals.length := by
        simp only [List.length_append, List.length_singleton] at localBound
        omega
      let fresh := Identification.freshLocalWire outer state.locals signature
        (0 : Fin 1)
      have freshIndex : fresh.index.val = outer.length + localIndex.val := by
        simp [fresh, Identification.freshLocalWire, freshValue]
      change RegionPath.RootedTwo
        ((state.advance selected).items.incidencePaths
          (outer.length + localIndex.val) 0)
      rw [← freshIndex]
      have survivorBound :=
        (state.materialMap
          (selected.appendLeft material.locals)).index.isLt
      have survivorDifferent :
          (Identification.retainWire outer state.locals signature 1
            (state.materialMap
              (selected.appendLeft material.locals))).index.val ≠
            fresh.index.val := by
        rw [retainWire_index]
        have freshAtEnd : fresh.index.val = (outer ++ state.locals).length := by
          simp [fresh, Identification.freshLocalWire, List.length_append]
        rw [freshAtEnd]
        omega
      have headPaths :
          (equalityNode state selected).incidencePaths fresh.index.val 0 =
            [[]] := by
        simp [equalityNode, Item.incidencePaths, fresh]
        rw [List.count_cons, List.count_singleton]
        have survivorDifferent' :
            (Identification.retainWire outer state.locals signature 1
              (state.materialMap
                (selected.appendLeft material.locals))).index.val ≠
              (Identification.freshLocalWire outer state.locals signature
                (0 : Fin 1)).index.val := by
          simpa [fresh] using survivorDifferent
        simp only [beq_iff_eq]
        simp only [if_true]
        split
        · rename_i equality
          exact False.elim (survivorDifferent' equality)
        · rfl
      have awayNonempty :
          (advanceAway state selected).incidencePaths fresh.index.val 1 ≠ [] := by
        simpa [fresh] using advanceAway_fresh_nonempty state selected
      rw [State.advance_items]
      simp only [ItemSeq.incidencePaths, Nat.zero_add]
      have targetPaths :
          (equalityNode state selected).incidencePaths fresh.index.val 0 ++
              (advanceAway state selected).incidencePaths fresh.index.val 1 =
            [] :: (advanceAway state selected).incidencePaths fresh.index.val 1 :=
        calc
          _ = [[]] ++
              (advanceAway state selected).incidencePaths fresh.index.val 1 :=
            congrArg (fun paths => paths ++
              (advanceAway state selected).incidencePaths fresh.index.val 1)
              headPaths
          _ = _ := rfl
      have targetRoot : RegionPath.RootedTwo
          ([] :: (advanceAway state selected).incidencePaths
            fresh.index.val 1) := by
        constructor
        · simp only [List.length_cons]
          exact Nat.succ_le_succ (List.length_pos_iff.mpr awayNonempty)
        · exact RegionPath.deepestCommonAncestor_cons_nil _
      exact targetPaths.symm ▸ targetRoot
  · apply State.advance_childrenCanonical state selected
    exact canonical.2

private def State.Supports
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures) : Prop :=
  ∀ position : Fin signatures.length,
    ∀ localIndex : Fin state.locals.length,
      (state.materialMap
        ((variables.get position).appendLeft material.locals)).index.val =
          outer.length + localIndex.val →
      RegionPath.RootedTwo
        (state.before.incidencePaths
          (outer.length + localIndex.val) 0)

private theorem State.advance_before_rooted
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    (localIndex : Fin state.locals.length)
    (rooted : RegionPath.RootedTwo
      (state.before.incidencePaths
        (outer.length + localIndex.val) 0)) :
    RegionPath.RootedTwo
      ((state.advance selected).before.incidencePaths
        (outer.length + localIndex.val) 0) := by
  let wireIndex := outer.length + localIndex.val
  have shiftedRoot :=
    (ItemSeq.rootedTwo_incidencePaths_add_itemIndex_iff
      state.before wireIndex 0 1).mpr rooted
  have renamedPaths :
      (state.before.renameWires
        (Identification.retainWire outer state.locals signature 1)).incidencePaths
          wireIndex 1 =
        state.before.incidencePaths wireIndex 1 := by
    apply ItemSeq.incidencePaths_renameWires_of_index_iff
    · have bound := localIndex.isLt
      simp only [wireIndex, List.length_append]
      omega
    · have bound := localIndex.isLt
      simp only [wireIndex, List.length_append]
      omega
    · intro wireSignature wire
      rw [retainWire_index]
  rw [← renamedPaths] at shiftedRoot
  apply RegionPath.RootedTwo.of_sublist ?_ shiftedRoot
  simp only [State.advance, ItemSeq.incidencePaths, Nat.zero_add]
  exact List.sublist_append_right _ _

private theorem State.supports_advance_tail
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    (tail : Vars materialWires signatures)
    (injective : VariablesIndexInjective (Vars.cons selected tail))
    (supported : state.Supports (.cons selected tail)) :
    (state.advance selected).Supports tail := by
  intro position localIndex targetIndex
  let wire := tail.get position
  have different : wire.index.val ≠ selected.index.val := by
    intro equality
    have positionsEqual :
        (Fin.succ position : Fin (signature :: signatures).length) = 0 := by
      apply injective
      simpa [wire] using equality
    have values := congrArg Fin.val positionsEqual
    simp at values
  have redirected := redirectMaterial_other_external state.materialMap
    selected wire different
  have retainedIndex := congrArg (fun mapped => mapped.index.val) redirected
  change
    (redirectMaterial state.materialMap selected
      (wire.appendLeft material.locals)).index.val =
      (Identification.retainWire outer state.locals signature 1
        (state.materialMap
          (wire.appendLeft material.locals))).index.val at retainedIndex
  rw [retainWire_index] at retainedIndex
  have old : localIndex.val < state.locals.length := by
    by_cases isOld : localIndex.val < state.locals.length
    · exact isOld
    have bound := localIndex.isLt
    change localIndex.val < (state.locals ++ [signature]).length at bound
    have freshValue : localIndex.val = state.locals.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    have freshIndex :
        (Identification.freshLocalWire outer state.locals signature
          (0 : Fin 1)).index.val = outer.length + localIndex.val := by
      simp [Identification.freshLocalWire, freshValue]
    have redirectedFresh :
        (redirectMaterial state.materialMap selected
          (wire.appendLeft material.locals)).index.val =
            (Identification.freshLocalWire outer state.locals signature
              (0 : Fin 1)).index.val := targetIndex.trans freshIndex.symm
    have sourceEqual :=
      (redirectMaterial_fresh_index_iff state.materialMap selected
        (wire.appendLeft material.locals)).mp redirectedFresh
    have externalEqual : wire.index.val = selected.index.val := by
      simpa only [Var.index_appendLeft] using sourceEqual
    exact False.elim (different externalEqual)
  let oldIndex : Fin state.locals.length := ⟨localIndex.val, old⟩
  have oldTarget :
      (state.materialMap
        (wire.appendLeft material.locals)).index.val =
          outer.length + oldIndex.val := by
    rw [← retainedIndex]
    simpa [oldIndex] using targetIndex
  exact State.advance_before_rooted state selected oldIndex
    (supported (Fin.succ position) oldIndex (by
      simpa [wire] using oldTarget))

private theorem oneWire
    (state : State outer materialWires material)
    (selected : Var materialWires signature)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence state.region source)
    (targetCanonical : (state.advance selected).region.Canonical)
    (applicability :
      Identification.Local.Applicability (exposureData state selected)) :
    ∃ filledCanonical :
        (occurrence.context.fill (state.advance selected).region).Canonical,
      ∃ filledExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill (state.advance selected).region),
        Relation.ReflTransGen Step source
          (occurrence.interface.withBody
            (occurrence.context.fill (state.advance selected).region)
            filledCanonical filledExternalTwoEnded) := by
  change Occurrence
    (Vacuity.Pin.plain state.locals state.items) source at occurrence
  let survivor :=
    state.materialMap (selected.appendLeft material.locals)
  let baseItems := state.items.append (sourceSupportSuffix state selected)
  have equality :
      ∃ equalityCanonical :
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)).Canonical,
        ∃ equalityExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (Vacuity.Pin.present state.locals baseItems signature survivor)),
          Relation.ReflTransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Vacuity.Pin.present state.locals baseItems signature survivor))
              equalityCanonical equalityExternalTwoEnded) := by
    by_cases unused : material.incidencePaths selected.index.val = []
    · obtain ⟨supportCanonical, supportExternalTwoEnded, supportStep⟩ :=
        pinStep occurrence signature survivor
      let supportEndpoint := occurrence.interface.withBody
        (occurrence.context.fill
          (Vacuity.Pin.present state.locals state.items signature survivor))
        supportCanonical supportExternalTwoEnded
      let supportOccurrence : Occurrence
          (Vacuity.Pin.plain state.locals baseItems) supportEndpoint := {
        interface := occurrence.interface
        context := occurrence.context
        sourceCanonical := by
          simpa [baseItems, sourceSupportSuffix, unused, survivor,
            Vacuity.Pin.plain, Vacuity.Pin.present] using supportCanonical
        sourceExternalTwoEnded := by
          intro wireSignature wire
          simpa [baseItems, sourceSupportSuffix, unused, survivor,
            Vacuity.Pin.plain, Vacuity.Pin.present] using
              supportExternalTwoEnded wire
        host_iso := by
          simpa [supportEndpoint, baseItems, sourceSupportSuffix, unused,
            survivor, Vacuity.Pin.plain, Vacuity.Pin.present] using
              OpenDiagramIso.refl supportEndpoint
      }
      obtain ⟨equalityCanonical, equalityExternalTwoEnded, equalityStep⟩ :=
        pinStep supportOccurrence signature survivor
      have equalityCanonical' :
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)).Canonical := by
        simpa [supportOccurrence] using equalityCanonical
      have equalityExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)) := by
        intro wireSignature wire
        simpa [supportOccurrence] using equalityExternalTwoEnded wire
      have equalityStep' : Step supportEndpoint
          (occurrence.interface.withBody
            (occurrence.context.fill
              (Vacuity.Pin.present state.locals baseItems signature survivor))
            equalityCanonical' equalityExternalTwoEnded') := by
        simpa [supportOccurrence] using equalityStep
      refine ⟨equalityCanonical', equalityExternalTwoEnded', ?_⟩
      exact .tail (.tail .refl
        (by simpa [supportEndpoint] using supportStep)) equalityStep'
    · obtain ⟨equalityCanonical, equalityExternalTwoEnded, equalityStep⟩ :=
        pinStep occurrence signature survivor
      have equalityExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Vacuity.Pin.present state.locals baseItems signature survivor)) := by
        intro wireSignature wire
        simpa [baseItems, sourceSupportSuffix, unused] using
          equalityExternalTwoEnded wire
      refine ⟨?_, ?_, ?_⟩
      · simpa [baseItems, sourceSupportSuffix, unused] using equalityCanonical
      · exact equalityExternalTwoEnded'
      · exact .tail .refl (by
          simpa [baseItems, sourceSupportSuffix, unused] using equalityStep)
  obtain ⟨equalityCanonical, equalityExternalTwoEnded, equalitySteps⟩ :=
    equality
  let equalityEndpoint := occurrence.interface.withBody
    (occurrence.context.fill
      (Vacuity.Pin.present state.locals baseItems signature survivor))
    equalityCanonical equalityExternalTwoEnded
  let appendOccurrence : Occurrence
      (Vacuity.Pin.present state.locals baseItems signature survivor)
      equalityEndpoint :=
    exactOccurrence occurrence.interface occurrence.context
      (Vacuity.Pin.present state.locals baseItems signature survivor)
      equalityCanonical equalityExternalTwoEnded
  have frontValidity := Vacuity.Pin.frontValidity appendOccurrence
  have frontCanonical :
      (occurrence.context.fill
        (Vacuity.Pin.front state.locals baseItems signature survivor)).Canonical := by
    simpa [appendOccurrence] using frontValidity.1
  have frontExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Vacuity.Pin.front state.locals baseItems signature survivor)) := by
    intro wireSignature wire
    simpa [appendOccurrence] using frontValidity.2 wire
  have collapsedEq :
      Vacuity.Pin.front state.locals baseItems signature survivor =
        (exposureData state selected).collapsedRegion := by
    rw [exposureData_collapsedRegion]
    rfl
  have collapsedCanonical :
      (occurrence.context.fill
        (exposureData state selected).collapsedRegion).Canonical := by
    simpa only [← collapsedEq] using frontCanonical
  have collapsedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (exposureData state selected).collapsedRegion) := by
    intro wireSignature wire
    simpa only [← collapsedEq] using frontExternalTwoEnded wire
  have appendFrontIso : RegionIso
      (WireEquiv.refl occurrence.interface.external)
      (occurrence.context.fill
        (Vacuity.Pin.present state.locals baseItems signature survivor))
      (occurrence.context.fill
        (Vacuity.Pin.front state.locals baseItems signature survivor)) :=
    DiagramContext.fillIso occurrence.context
      (RegionIso.appendSingletonFront state.locals baseItems
        (.identity signature 1 (fun _ => survivor)))
  have equalityCollapsedIso : OpenDiagramIso equalityEndpoint
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposureData state selected).collapsedRegion)
        collapsedCanonical collapsedExternalTwoEnded) := by
    simpa only [equalityEndpoint, ← collapsedEq] using
      OpenDiagram.withBody_iso equalityCanonical frontCanonical
        equalityExternalTwoEnded frontExternalTwoEnded appendFrontIso
  let collapsedOccurrence : Occurrence
      (exposureData state selected).collapsedRegion equalityEndpoint := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := collapsedCanonical
    sourceExternalTwoEnded := collapsedExternalTwoEnded
    host_iso := equalityCollapsedIso
  }
  have exposedValidity := Identification.Local.exposedValidity
    (exposureData state selected) applicability collapsedOccurrence
    (by simpa only [exposureData_exposedRegion] using targetCanonical)
  dsimp only [collapsedOccurrence] at exposedValidity
  have identificationStep : Step equalityEndpoint
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposureData state selected).exposedRegion)
        exposedValidity.1 exposedValidity.2) := by
    apply Step.identification
    exact Or.inl ⟨outer, (exposureData state selected).collapsedRegion,
      (exposureData state selected).exposedRegion, collapsedOccurrence,
      exposedValidity.1, exposedValidity.2, OpenDiagramIso.refl _,
      atPolarity_symmetric_of occurrence.context.polarity
        (.expose (exposureData state selected) applicability)⟩
  have filledExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill (state.advance selected).region) := by
    intro wireSignature wire
    simpa only [exposureData_exposedRegion] using exposedValidity.2 wire
  refine ⟨?_, filledExternalTwoEnded, ?_⟩
  · simpa only [exposureData_exposedRegion] using exposedValidity.1
  · have equalityTail : Relation.ReflTransGen Step source equalityEndpoint :=
      by simpa [equalityEndpoint] using equalitySteps
    have exposedTail := Relation.ReflTransGen.tail equalityTail identificationStep
    simpa only [exposureData_exposedRegion] using exposedTail

private theorem advanceAllDerives
    (state : State outer materialWires material)
    (variables : Vars materialWires signatures)
    (injective : VariablesIndexInjective variables)
    (supported : state.Supports variables)
    (canonical : state.region.Canonical)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (sourceCanonical : (context.fill state.region).Canonical)
    (sourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill state.region)) :
    ∃ targetCanonical :
        (context.fill (state.advanceAll variables).region).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          interface.boundaryWire
          (context.fill (state.advanceAll variables).region),
        Relation.ReflTransGen Step
          (interface.withBody (context.fill state.region)
            sourceCanonical sourceExternalTwoEnded)
          (interface.withBody
            (context.fill (state.advanceAll variables).region)
            targetCanonical targetExternalTwoEnded) := by
  induction variables generalizing state with
  | nil =>
      exact ⟨sourceCanonical, sourceExternalTwoEnded, .refl⟩
  | @cons signature signatures selected tail induction =>
      let source := interface.withBody (context.fill state.region)
        sourceCanonical sourceExternalTwoEnded
      let occurrence : Occurrence state.region source :=
        exactOccurrence interface context state.region sourceCanonical
          sourceExternalTwoEnded
      have selectedSupported : ∀ localIndex : Fin state.locals.length,
          (state.materialMap
            (selected.appendLeft material.locals)).index.val =
              outer.length + localIndex.val →
          RegionPath.RootedTwo
            (state.before.incidencePaths
              (outer.length + localIndex.val) 0) := by
        intro localIndex equality
        exact supported 0 localIndex equality
      have nextCanonical := State.advance_canonical state selected canonical
        selectedSupported
      obtain ⟨filledCanonical, filledExternalTwoEnded, firstSteps⟩ :=
        oneWire state selected occurrence nextCanonical
          (exposureData_applicability state selected)
      let nextSource := occurrence.interface.withBody
        (occurrence.context.fill (state.advance selected).region)
        filledCanonical filledExternalTwoEnded
      have tailInjective : VariablesIndexInjective tail := by
        intro first second equality
        have positions := injective (Fin.succ first) (Fin.succ second) (by
          simpa using equality)
        apply Fin.ext
        have values := congrArg Fin.val positions
        simp only [Fin.val_succ] at values
        omega
      have tailSupported := State.supports_advance_tail state selected tail
        injective supported
      obtain ⟨targetCanonical, targetExternalTwoEnded, restSteps⟩ :=
        induction (state := state.advance selected) tailInjective tailSupported
          nextCanonical filledCanonical filledExternalTwoEnded
      refine ⟨?_, ?_, ?_⟩
      · simpa only [State.advanceAll] using targetCanonical
      · intro wireSignature wire
        simpa only [State.advanceAll] using targetExternalTwoEnded wire
      · have firstSteps' : Relation.ReflTransGen Step source nextSource := by
          simpa only [nextSource] using firstSteps
        have combined := firstSteps'.trans restSteps
        simpa only [source, occurrence, exactOccurrence, State.advanceAll]
          using combined

def applicationPorts (description : Rule.Erasure.Description outer) :
    Vars (outer ++ description.hostLocals) description.materialWires :=
  (identityBoundary description.materialWires).map
    (fun wire => description.wireMap wire)

def exposedRegion (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) : Region outer :=
  Region.adjoinAt description.hostLocals description.hostItems
    (Comprehension.Instantiation.instantiate
      (supportPattern description.material materialCanonical)
      (applicationPorts description))

private def endpointHostWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming (outer ++ description.hostLocals)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++ description.material.locals))) :=
  Region.adjoinHostWire outer description.hostLocals
    (description.materialWires ++ description.material.locals)

private def endpointMaterialWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      (description.materialWires ++ description.material.locals)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++ description.material.locals))) :=
  ⟨fun wire => Var.appendRight outer
    (Var.appendRight description.hostLocals wire)⟩

private def endpointEqualityWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      ((outer ++ description.hostLocals) ++ description.materialWires)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++ description.material.locals))) :=
  ⟨Var.appendMap
    (fun wire => endpointHostWire description wire)
    (fun wire => endpointMaterialWire description
      (wire.appendLeft description.material.locals))⟩

private def endpointEqualityItems
    (description : Rule.Erasure.Description outer) :
    ItemSeq (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals))) :=
  (Comprehension.Instantiation.equalityItems
    ((applicationPorts description).map
      (fun wire => wire.appendLeft description.materialWires))
    ((identityBoundary description.materialWires).map
      (fun wire => Var.appendRight
        (outer ++ description.hostLocals) wire))).renameWires
    (endpointEqualityWire description)

private def endpointLeft
    (description : Rule.Erasure.Description outer) :
    Vars (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals)))
      description.materialWires :=
  (applicationPorts description).map
    (fun wire => endpointHostWire description wire)

private def endpointRight
    (description : Rule.Erasure.Description outer) :
    Vars (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals)))
      description.materialWires :=
  (identityBoundary description.materialWires).map
    (fun wire => endpointMaterialWire description
      (wire.appendLeft description.material.locals))

private theorem endpointEqualityItems_eq
    (description : Rule.Erasure.Description outer) :
    endpointEqualityItems description =
      Comprehension.Instantiation.equalityItems
        (endpointLeft description) (endpointRight description) := by
  have leftEq :
      ((applicationPorts description).map
        (fun wire => wire.appendLeft description.materialWires)).map
          (fun wire => endpointEqualityWire description wire) =
        endpointLeft description := by
    calc
      _ = (applicationPorts description).map (fun wire =>
            endpointEqualityWire description
              (wire.appendLeft description.materialWires)) :=
        Vars.map_map _ _ _
      _ = (applicationPorts description).map (fun wire =>
            endpointHostWire description wire) := by
        apply Vars.map_congr
        intro signature wire
        simp [endpointEqualityWire]
      _ = _ := rfl
  have rightEq :
      ((identityBoundary description.materialWires).map
        (fun wire => Var.appendRight
          (outer ++ description.hostLocals) wire)).map
          (fun wire => endpointEqualityWire description wire) =
        endpointRight description := by
    calc
      _ = (identityBoundary description.materialWires).map (fun wire =>
            endpointEqualityWire description
              (Var.appendRight (outer ++ description.hostLocals) wire)) :=
        Vars.map_map _ _ _
      _ = (identityBoundary description.materialWires).map (fun wire =>
            endpointMaterialWire description
              (wire.appendLeft description.material.locals)) := by
        apply Vars.map_congr
        intro signature wire
        simp [endpointEqualityWire]
      _ = _ := rfl
  unfold endpointEqualityItems
  rw [Comprehension.Instantiation.equalityItems_renameWires]
  rw [leftEq, rightEq]

private def endpointItems
    (description : Rule.Erasure.Description outer) :
    ItemSeq (outer ++ (description.hostLocals ++
      (description.materialWires ++ description.material.locals))) :=
  (description.hostItems.renameWires
      (endpointHostWire description)).append
    ((description.material.items.renameWires
        (endpointMaterialWire description)).append
      (((supportPins description.material description.materialWires
          (identityBoundary description.materialWires)).renameWires
          (endpointMaterialWire description)).append
        (endpointEqualityItems description)))

private def instantiatedBodyWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      (description.materialWires ++ description.material.locals)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++
          (description.material.locals ++ [])))) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire outer description.hostLocals
      (description.materialWires ++ (description.material.locals ++ [])))
    (WireRenaming.comp
      (Region.adjoinMaterialWire (outer ++ description.hostLocals)
        description.materialWires (description.material.locals ++ []))
      (WireRenaming.comp
        (Region.conjoinLeftWire
          (outer ++ description.hostLocals ++ description.materialWires)
          description.material.locals [])
        ((⟨fun wire => Var.appendRight
            (outer ++ description.hostLocals) wire⟩ :
          WireRenaming description.materialWires
            ((outer ++ description.hostLocals) ++
              description.materialWires)).appendRight
          description.material.locals)))

private def instantiatedEqualityWire
    (description : Rule.Erasure.Description outer) :
    WireRenaming
      ((outer ++ description.hostLocals) ++ description.materialWires)
      (outer ++ (description.hostLocals ++
        (description.materialWires ++
          (description.material.locals ++ [])))) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire outer description.hostLocals
      (description.materialWires ++ (description.material.locals ++ [])))
    (WireRenaming.comp
      (Region.adjoinMaterialWire (outer ++ description.hostLocals)
        description.materialWires (description.material.locals ++ []))
      (WireRenaming.comp
        (Region.conjoinRightWire
          (outer ++ description.hostLocals ++ description.materialWires)
          description.material.locals [])
        ⟨fun wire => wire.appendLeft []⟩))

private noncomputable def exposedRegionEndpointIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      (exposedRegion description materialCanonical)
      (.mk (description.hostLocals ++
        (description.materialWires ++ description.material.locals))
        (endpointItems description)) := by
  cases description with
  | mk materialWires hostLocals hostItems material wireMap =>
      cases material with
      | mk materialLocals materialItems =>
          unfold exposedRegion endpointItems endpointEqualityItems
            endpointHostWire endpointMaterialWire applicationPorts
            supportPattern supportBody
            Comprehension.Instantiation.instantiate
          rw [Comprehension.Instantiation.Equalities_eq_ofItems]
          unfold Region.adjoinAt Region.conjoin Region.renameWires
            Region.ofItems
          simp only [Region.locals, Region.items]
          simp only [ItemSeq.renameWires_append,
            ItemSeq.renameWires_comp,
            ItemSeq.renameWires, ItemSeq.nil_append]
          let description : Rule.Erasure.Description outer := {
            materialWires := materialWires
            hostLocals := hostLocals
            hostItems := hostItems
            material := .mk materialLocals materialItems
            wireMap := wireMap
          }
          let actualLocals := hostLocals ++
            (materialWires ++ (materialLocals ++ []))
          let targetLocals := hostLocals ++
            (materialWires ++ materialLocals)
          have localsEq : actualLocals = targetLocals :=
            congrArg (fun tail => hostLocals ++ (materialWires ++ tail))
              (List.append_nil materialLocals)
          let localsIso : WireEquiv
              actualLocals targetLocals :=
            WireEquiv.ofEq localsEq
          let ambient := (WireEquiv.refl outer).append localsIso
          let actualHost := Region.adjoinHostWire outer hostLocals
            (materialWires ++ (materialLocals ++ []))
          let targetHost := endpointHostWire description
          let actualBody := instantiatedBodyWire description
          let targetBody := endpointMaterialWire description
          let actualEquality := instantiatedEqualityWire description
          let targetEquality := endpointEqualityWire description
          let baseEquality := Comprehension.Instantiation.equalityItems
            (((identityBoundary materialWires).map
              (fun wire => wireMap wire)).map
              (fun wire => wire.appendLeft materialWires))
            ((identityBoundary materialWires).map
              (fun wire => Var.appendRight (outer ++ hostLocals) wire))
          have ambientIndex : ∀ {signature}
              (wire : Var (outer ++ actualLocals) signature),
              (ambient wire).index.val = wire.index.val := by
            intro signature wire
            apply Var.appendCases (left := outer) (right := actualLocals)
              (motive := fun wire =>
                (ambient wire).index.val = wire.index.val)
            · intro inheritedSignature inherited
              simp [ambient]
            · intro localSignature localWire
              simp [ambient, localsIso]
          have hostCommutes : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              ambient (actualHost wire) = targetHost wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [ambientIndex]
            simp [actualHost, targetHost, endpointHostWire, description,
              Region.locals]
          have bodyCommutes : ∀ {signature}
              (wire : Var (materialWires ++ materialLocals) signature),
              ambient (actualBody wire) = targetBody wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [ambientIndex]
            apply Var.appendCases (left := materialWires)
              (right := materialLocals)
              (motive := fun wire =>
                (actualBody wire).index.val = (targetBody wire).index.val)
            · intro inheritedSignature inherited
              simp [actualBody, targetBody, instantiatedBodyWire,
                endpointMaterialWire, WireRenaming.comp,
                WireRenaming.appendRight, description, Region.locals]
              omega
            · intro localSignature localWire
              simp [actualBody, targetBody, instantiatedBodyWire,
                endpointMaterialWire, WireRenaming.comp,
                WireRenaming.appendRight, description, Region.locals]
              omega
          have equalityCommutes : ∀ {signature}
              (wire : Var ((outer ++ hostLocals) ++ materialWires) signature),
              ambient (actualEquality wire) = targetEquality wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            rw [ambientIndex]
            apply Var.appendCases (left := outer ++ hostLocals)
              (right := materialWires)
              (motive := fun wire =>
                (actualEquality wire).index.val =
                  (targetEquality wire).index.val)
            · intro inheritedSignature inherited
              simp [actualEquality, targetEquality,
                instantiatedEqualityWire, endpointEqualityWire,
                endpointHostWire, endpointMaterialWire,
                WireRenaming.comp, Region.conjoinRightWire,
                Region.locals, description]
            · intro localSignature localWire
              simp [actualEquality, targetEquality,
                instantiatedEqualityWire, endpointEqualityWire,
                endpointHostWire, endpointMaterialWire,
                WireRenaming.comp, Region.conjoinRightWire,
                Region.locals, description]
              omega
          refine .mk localsIso ?_
          let hostIso := ItemSeqIso.renameWires hostItems
            actualHost targetHost ambient hostCommutes
          let materialIso := ItemSeqIso.renameWires materialItems
            actualBody targetBody ambient bodyCommutes
          let supportIso := ItemSeqIso.renameWires
            (supportPins (Region.mk materialLocals materialItems)
              materialWires (identityBoundary materialWires))
            actualBody targetBody ambient bodyCommutes
          let equalityIso := ItemSeqIso.renameWires baseEquality
            actualEquality targetEquality ambient equalityCommutes
          let combined := ItemSeqIso.append hostIso
            (ItemSeqIso.append materialIso
              (ItemSeqIso.append supportIso equalityIso))
          simpa [description, actualLocals, targetLocals, actualHost,
            targetHost, actualBody, targetBody, actualEquality,
            targetEquality, baseEquality, endpointHostWire,
            endpointMaterialWire, instantiatedBodyWire,
            endpointEqualityWire, instantiatedEqualityWire,
            ItemSeq.append_assoc] using combined

private def initialState
    (description : Rule.Erasure.Description outer) :
    State outer description.materialWires description.material where
  locals := description.hostLocals ++ description.material.locals
  before := description.hostItems.renameWires
    (Region.adjoinHostWire outer description.hostLocals
      description.material.locals)
  after := .nil
  materialMap := WireRenaming.comp
    (Region.adjoinMaterialWire outer description.hostLocals
      description.material.locals)
    (description.wireMap.appendRight description.material.locals)

private theorem initialState_region
    (description : Rule.Erasure.Description outer) :
    (initialState description).region = description.source := by
  cases description with
  | mk materialWires hostLocals hostItems material wireMap =>
      cases material with
      | mk materialLocals materialItems =>
          simp [initialState, State.region, State.items,
            Rule.Erasure.Description.source, Region.spliceAt, Region.adjoinAt,
            Region.renameWires, Region.locals, Region.items,
            ItemSeq.renameWires_comp]

private theorem initialState_supports
    (description : Rule.Erasure.Description outer)
    (targetCanonical : description.target.Canonical) :
    (initialState description).Supports
      (identityBoundary description.materialWires) := by
  intro position localIndex targetIndex
  let external := (identityBoundary description.materialWires).get position
  let mapped := description.wireMap external
  have materialMapIndex :
      ((initialState description).materialMap
        (external.appendLeft description.material.locals)).index.val =
          mapped.index.val := by
    change
      (Region.adjoinMaterialWire outer description.hostLocals
        description.material.locals
        ((description.wireMap.appendRight description.material.locals)
          (external.appendLeft description.material.locals))).index.val =
        mapped.index.val
    have inherited :
        (description.wireMap.appendRight description.material.locals)
            (external.appendLeft description.material.locals) =
          mapped.appendLeft description.material.locals := by
      simp [mapped, WireRenaming.appendRight]
    rw [inherited]
    apply Var.appendCases (left := outer) (right := description.hostLocals)
      (motive := fun mapped =>
        (Region.adjoinMaterialWire outer description.hostLocals
          description.material.locals
          (mapped.appendLeft description.material.locals)).index.val =
            mapped.index.val)
    · intro mappedSignature inheritedWire
      simp [Region.adjoinMaterialWire]
    · intro mappedSignature localWire
      simp [Region.adjoinMaterialWire]
  have mappedTarget : mapped.index.val = outer.length + localIndex.val :=
    materialMapIndex.symm.trans targetIndex
  have hostBound : localIndex.val < description.hostLocals.length := by
    have mappedBound := mapped.index.isLt
    simp only [List.length_append] at mappedBound
    omega
  let hostIndex : Fin description.hostLocals.length :=
    ⟨localIndex.val, hostBound⟩
  have hostRoot : RegionPath.RootedTwo
      (description.hostItems.incidencePaths
        (outer.length + hostIndex.val) 0) := by
    simpa only [Rule.Erasure.Description.target, Region.Canonical] using
      targetCanonical.1 hostIndex
  have renamedPaths :=
    ItemSeq.incidencePaths_renameWires_adjoinHost
      (addedLocals := description.material.locals)
      description.hostItems mapped 0
  rw [mappedTarget] at renamedPaths
  change RegionPath.RootedTwo
    ((description.hostItems.renameWires
      (Region.adjoinHostWire outer description.hostLocals
        description.material.locals)).incidencePaths
      (outer.length + localIndex.val) 0)
  rw [renamedPaths]
  simpa [hostIndex] using hostRoot

private theorem materialCanonical_of_source
    (description : Rule.Erasure.Description outer)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source) :
    description.material.Canonical := by
  have sourceCanonical := occurrence.context.holeCanonical
    description.source occurrence.sourceCanonical
  have renamedCanonical :
      (description.material.renameWires description.wireMap).Canonical := by
    apply Region.Canonical.material_of_adjoinAt
      description.hostLocals description.hostItems
    simpa only [Rule.Erasure.Description.source, Region.spliceAt] using
      sourceCanonical
  exact (Region.Canonical.renameWires_iff
    description.material description.wireMap).mp renamedCanonical

private noncomputable def endpointRegionIso
    (description : Rule.Erasure.Description outer)
    (materialCanonical : description.material.Canonical) :
    RegionIso (WireEquiv.refl outer)
      ((initialState description).advanceAll
        (identityBoundary description.materialWires)).region
      (exposedRegion description materialCanonical) := by
  cases description with
  | mk materialWires hostLocals hostItems material wireMap =>
      cases material with
      | mk materialLocals materialItems =>
          let description : Rule.Erasure.Description outer := {
            materialWires := materialWires
            hostLocals := hostLocals
            hostItems := hostItems
            material := .mk materialLocals materialItems
            wireMap := wireMap
          }
          let state := initialState description
          let variables := identityBoundary materialWires
          let finalState := state.advanceAll variables
          have localsEq : finalState.locals =
              (hostLocals ++ materialLocals) ++ materialWires := by
            simpa [finalState, state, description, initialState] using
              State.advanceAll_locals state variables
          let normalizeLocals := WireEquiv.ofEq localsEq
          let rotation := WireEquiv.rotate
            hostLocals materialLocals materialWires
          let localsIso := normalizeLocals.trans rotation
          let ambient := (WireEquiv.refl outer).append localsIso
          let normalizeAmbient :=
            (WireEquiv.refl outer).append normalizeLocals
          let rotateAmbient := (WireEquiv.refl outer).append rotation
          have ambientFactor : ambient =
              normalizeAmbient.trans rotateAmbient := by
            have factor := WireEquiv.append_trans
              (WireEquiv.refl outer) (WireEquiv.refl outer)
              normalizeLocals rotation
            simpa [ambient, normalizeAmbient, rotateAmbient, localsIso] using
              factor.symm
          let initialHost := Region.adjoinHostWire outer hostLocals
            materialLocals
          let rawHost := WireRenaming.comp (state.retainAll variables)
            initialHost
          let rawMaterial := finalState.materialMap
          let targetHost := endpointHostWire description
          let targetMaterial := endpointMaterialWire description
          let canonicalHost := WireRenaming.comp
            (Region.adjoinHostWire outer
              (hostLocals ++ materialLocals) materialWires)
            initialHost
          have normalizeIndex : ∀ {signature}
              (wire : Var (outer ++ finalState.locals) signature),
              (normalizeAmbient wire).index.val = wire.index.val := by
            intro signature wire
            apply Var.appendCases (left := outer)
              (right := finalState.locals)
              (motive := fun wire =>
                (normalizeAmbient wire).index.val = wire.index.val)
            · intro inheritedSignature inherited
              simp [normalizeAmbient]
            · intro localSignature localWire
              simp [normalizeAmbient, normalizeLocals]
          have initialMaterialExternal : ∀ {signature}
              (wire : Var materialWires signature),
              state.materialMap (wire.appendLeft materialLocals) =
                initialHost (wireMap wire) := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (state.materialMap
                    (wire.appendLeft materialLocals)).index.val =
                  (wireMap wire).index.val := by
                simp [state, description, initialState,
                  WireRenaming.comp, WireRenaming.appendRight,
                  Region.locals]
              _ = (initialHost (wireMap wire)).index.val :=
                (Region.adjoinHostWire_index_val (wireMap wire)).symm
          have normalizedHost : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              normalizeAmbient (rawHost wire) = canonicalHost wire := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (normalizeAmbient (rawHost wire)).index.val =
                  (rawHost wire).index.val := normalizeIndex _
              _ = (initialHost wire).index.val :=
                State.retainAll_index state variables _
              _ = wire.index.val :=
                Region.adjoinHostWire_index_val wire
              _ = (canonicalHost wire).index.val := by
                simp [canonicalHost, initialHost, WireRenaming.comp]
          have hostRotates : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              rotateAmbient (canonicalHost wire) = targetHost wire := by
            intro signature wire
            apply Var.appendCases (left := outer) (right := hostLocals)
              (motive := fun wire =>
                rotateAmbient (canonicalHost wire) = targetHost wire)
            · intro inheritedSignature inherited
              simp [rotateAmbient, rotation, canonicalHost, initialHost,
                targetHost, endpointHostWire, WireRenaming.comp,
                Region.adjoinHostWire, Region.conjoinLeftWire,
                description, Region.locals]
            · intro localSignature localWire
              simp [rotateAmbient, rotation, canonicalHost, initialHost,
                targetHost, endpointHostWire, WireRenaming.comp,
                Region.adjoinHostWire, Region.conjoinLeftWire,
                description, Region.locals]
          have hostCommutes : ∀ {signature}
              (wire : Var (outer ++ hostLocals) signature),
              ambient (rawHost wire) = targetHost wire := by
            intro signature wire
            rw [ambientFactor]
            change rotateAmbient (normalizeAmbient (rawHost wire)) = _
            rw [normalizedHost wire]
            exact hostRotates wire
          have normalizedExternal : ∀ {signature}
              (wire : Var materialWires signature),
              normalizeAmbient
                  (rawMaterial (wire.appendLeft materialLocals)) =
                Var.appendRight outer
                  (Var.appendRight (hostLocals ++ materialLocals) wire) := by
            intro signature wire
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (normalizeAmbient
                  (rawMaterial (wire.appendLeft materialLocals))).index.val =
                  (rawMaterial
                    (wire.appendLeft materialLocals)).index.val :=
                normalizeIndex _
              _ = (outer ++ state.locals).length + wire.index.val :=
                State.advanceAll_materialMap_get_index state variables
                  identityBoundary_indexInjective wire wire.index (by
                    have indexEq := identityBoundary_get_index
                      (wires := materialWires) wire.index
                    exact congrArg Fin.val indexEq.symm)
              _ = (Var.appendRight outer
                    (Var.appendRight (hostLocals ++ materialLocals)
                      wire)).index.val := by
                simp [state, description, initialState, Region.locals]
                omega
          have normalizedLocal : ∀ {signature}
              (wire : Var materialLocals signature),
              normalizeAmbient
                  (rawMaterial (Var.appendRight materialWires wire)) =
                Var.appendRight outer
                  ((Var.appendRight hostLocals wire).appendLeft
                    materialWires) := by
            intro signature wire
            have different : ∀ position : Fin materialWires.length,
                (Var.appendRight materialWires wire).index.val ≠
                  ((variables.get position).appendLeft
                    materialLocals).index.val := by
              intro position equality
              have bound := (variables.get position).index.isLt
              simp only [Var.index_appendRight, Var.index_appendLeft] at equality
              omega
            have retained := State.advanceAll_materialMap_other state
              variables (Var.appendRight materialWires wire) different
            apply Var.eq_of_index_eq
            apply Fin.ext
            calc
              (normalizeAmbient
                  (rawMaterial
                    (Var.appendRight materialWires wire))).index.val =
                  (rawMaterial
                    (Var.appendRight materialWires wire)).index.val :=
                normalizeIndex _
              _ = (state.retainAll variables
                    (state.materialMap
                      (Var.appendRight materialWires wire))).index.val :=
                congrArg (fun mapped => mapped.index.val) retained
              _ = (state.materialMap
                    (Var.appendRight materialWires wire)).index.val :=
                State.retainAll_index state variables _
              _ = (Var.appendRight outer
                    ((Var.appendRight hostLocals wire).appendLeft
                      materialWires)).index.val := by
                simp [state, description, initialState,
                  WireRenaming.comp, WireRenaming.appendRight,
                  Region.locals]
                omega
          have materialCommutes : ∀ {signature}
              (wire : Var (materialWires ++ materialLocals) signature),
              ambient (rawMaterial wire) = targetMaterial wire := by
            intro signature wire
            apply Var.appendCases (left := materialWires)
              (right := materialLocals)
              (motive := fun wire =>
                ambient (rawMaterial wire) = targetMaterial wire)
            · intro inheritedSignature inherited
              rw [ambientFactor]
              change rotateAmbient
                (normalizeAmbient
                  (rawMaterial (inherited.appendLeft materialLocals))) = _
              rw [normalizedExternal inherited]
              simp [rotateAmbient, rotation, targetMaterial,
                endpointMaterialWire, description, Region.locals]
            · intro localSignature localWire
              rw [ambientFactor]
              change rotateAmbient
                (normalizeAmbient
                  (rawMaterial
                    (Var.appendRight materialWires localWire))) = _
              rw [normalizedLocal localWire]
              simp [rotateAmbient, rotation, targetMaterial,
                endpointMaterialWire, description, Region.locals]
          have leftCommutes :
              (state.batchLeft variables).map
                  (fun wire => ambient wire) =
                endpointLeft description := by
            unfold State.batchLeft endpointLeft applicationPorts
            rw [Vars.map_map, Vars.map_map]
            apply Vars.map_congr
            intro signature wire
            change ambient
                (state.retainAll variables
                  (state.materialMap
                    (wire.appendLeft materialLocals))) =
              targetHost (wireMap wire)
            rw [initialMaterialExternal wire]
            exact hostCommutes (wireMap wire)
          have rightCommutes :
              (state.batchRight variables).map
                  (fun wire => ambient wire) =
                endpointRight description := by
            unfold State.batchRight endpointRight
            rw [Vars.map_map]
            apply Vars.map_congr
            intro signature wire
            exact materialCommutes (wire.appendLeft materialLocals)
          have supportEq := State.batchSupports_eq state variables
            identityBoundary_indexInjective
          have equalitiesEq := State.batchEqualities_eq state variables
            identityBoundary_indexInjective
          have rawPresentation : ItemSeqIso
              (WireEquiv.refl (outer ++ finalState.locals))
              finalState.items
              ((hostItems.renameWires rawHost).append
                ((materialItems.renameWires rawMaterial).append
                  (((supportPins (Region.mk materialLocals materialItems)
                      materialWires variables).renameWires rawMaterial).append
                    (Comprehension.Instantiation.equalityItems
                      (state.batchLeft variables)
                      (state.batchRight variables))))) := by
            have presentation := State.advanceAll_itemsIso state variables rfl
            rw [supportEq, equalitiesEq] at presentation
            simpa [finalState, rawMaterial, state, description, initialState,
              rawHost, initialHost, ItemSeq.renameWires_comp,
              ItemSeq.append_assoc] using presentation
          let hostIso := ItemSeqIso.renameWires hostItems
            rawHost targetHost ambient hostCommutes
          let materialIso := ItemSeqIso.renameWires materialItems
            rawMaterial targetMaterial ambient materialCommutes
          let supportIso := ItemSeqIso.renameWires
            (supportPins (Region.mk materialLocals materialItems)
              materialWires variables)
            rawMaterial targetMaterial ambient materialCommutes
          let equalityIso :=
            Comprehension.Instantiation.equalityItemsIso ambient
            (state.batchLeft variables) (state.batchRight variables)
            (endpointLeft description) (endpointRight description)
            leftCommutes rightCommutes
          have blocks : ItemSeqIso ambient
              ((hostItems.renameWires rawHost).append
                ((materialItems.renameWires rawMaterial).append
                  (((supportPins (Region.mk materialLocals materialItems)
                      materialWires variables).renameWires rawMaterial).append
                    (Comprehension.Instantiation.equalityItems
                      (state.batchLeft variables)
                      (state.batchRight variables)))))
              (endpointItems description) := by
            let combined := ItemSeqIso.append hostIso
              (ItemSeqIso.append materialIso
                (ItemSeqIso.append supportIso equalityIso))
            simpa [endpointItems, endpointEqualityItems_eq,
              ItemSeq.append_assoc] using combined
          have itemIso := rawPresentation.trans blocks
          have itemIso' := itemIso.castAmbient
            (WireEquiv.refl_trans ambient)
          let directIso : RegionIso (WireEquiv.refl outer)
              finalState.region
              (.mk (hostLocals ++ (materialWires ++ materialLocals))
                (endpointItems description)) :=
            .mk localsIso itemIso'
          let exposedIso := exposedRegionEndpointIso description
            materialCanonical
          have composed := directIso.trans exposedIso.symm
          have composed' : RegionIso (WireEquiv.refl outer)
              finalState.region
              (exposedRegion description materialCanonical) :=
            RegionIso.castAmbient (by rfl) composed
          simpa [description, state, variables, finalState] using composed'

/-- Erasure material can be exposed as one exact comprehension-instantiation
block without assuming that its external-to-host wire map is injective. -/
theorem derives
    {boundary outer : List Sig}
    (description : Rule.Erasure.Description outer)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source)
    (erasedCanonical :
      (occurrence.context.fill description.target).Canonical)
    (erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill description.target)) :
    ∃ materialCanonical : description.material.Canonical,
      ∃ exposedCanonical :
          (occurrence.context.fill
            (exposedRegion description materialCanonical)).Canonical,
        ∃ exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill
              (exposedRegion description materialCanonical)),
          Relation.ReflTransGen Step source
            (occurrence.interface.withBody
              (occurrence.context.fill
                (exposedRegion description materialCanonical))
              exposedCanonical exposedExternalTwoEnded) := by
  let materialCanonical := materialCanonical_of_source description occurrence
  refine ⟨materialCanonical, ?_⟩
  have targetCanonical : description.target.Canonical := by
    exact occurrence.context.holeCanonical description.target erasedCanonical
  have instantiatedCanonical :
      (Comprehension.Instantiation.instantiate
        (supportPattern description.material materialCanonical)
        (applicationPorts description)).Canonical :=
    supportInstantiation_canonical description.material materialCanonical
      (applicationPorts description)
  have exposedLocalCanonical :
      (exposedRegion description materialCanonical).Canonical := by
    simpa only [exposedRegion] using
      Region.Canonical.adjoinAt description.hostLocals description.hostItems
        (Comprehension.Instantiation.instantiate
          (supportPattern description.material materialCanonical)
          (applicationPorts description))
        targetCanonical instantiatedCanonical
  have extension := occurrence.context.extendCanonical description.target
    (exposedRegion description materialCanonical) erasedCanonical
    exposedLocalCanonical (by
      intro signature wire
      simpa only [Rule.Erasure.Description.target, exposedRegion] using
        Region.incidencePaths_adjoinAt_host_sublist
          description.hostLocals description.hostItems
          (Comprehension.Instantiation.instantiate
            (supportPattern description.material materialCanonical)
            (applicationPorts description)) wire)
  let exposedCanonical := extension.1
  have exposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (exposedRegion description materialCanonical)) := by
    intro signature wire
    have sourceFloor := erasedExternalTwoEnded wire
    have pathSublist := extension.2 wire
    exact Nat.le_trans sourceFloor
      (Nat.add_le_add_left pathSublist.length_le _)
  refine ⟨exposedCanonical, exposedExternalTwoEnded, ?_⟩
  let state := initialState description
  let variables := identityBoundary description.materialWires
  have stateRegionEq : state.region = description.source := by
    simpa only [state] using initialState_region description
  have initialFilledCanonical :
      (occurrence.context.fill state.region).Canonical := by
    rw [stateRegionEq]
    exact occurrence.sourceCanonical
  have initialFilledExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill state.region) := by
    rw [stateRegionEq]
    exact occurrence.sourceExternalTwoEnded
  have initialHostIso : OpenDiagramIso source
      (occurrence.interface.withBody
        (occurrence.context.fill state.region)
        initialFilledCanonical initialFilledExternalTwoEnded) := by
    simpa only [stateRegionEq] using occurrence.host_iso
  let initialOccurrence : Occurrence state.region source := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := initialFilledCanonical
    sourceExternalTwoEnded := initialFilledExternalTwoEnded
    host_iso := initialHostIso
  }
  have stateCanonical : state.region.Canonical :=
    initialOccurrence.context.holeCanonical state.region
      initialOccurrence.sourceCanonical
  have supported : state.Supports variables := by
    simpa only [state, variables] using
      initialState_supports description targetCanonical
  have regionEta :
      Vacuity.Point.plain state.region.locals state.region.items =
        state.region := by
    cases state.region
    rfl
  let pointOccurrence : Occurrence
      (Vacuity.Point.plain state.region.locals state.region.items) source := by
    rw [regionEta]
    exact initialOccurrence
  have pointValidity :=
    Vacuity.Point.introduceValidity pointOccurrence Sig.iota
  let pointEndpoint := pointOccurrence.interface.withBody
    (pointOccurrence.context.fill
      (Vacuity.Point.present state.region.locals state.region.items Sig.iota))
    pointValidity.1 pointValidity.2
  have pointIntroduction : Vacuity source pointEndpoint := by
    exact ⟨outer, Vacuity.Point.plain state.region.locals state.region.items,
      Vacuity.Point.present state.region.locals state.region.items Sig.iota,
      pointOccurrence, pointValidity.1, pointValidity.2,
      OpenDiagramIso.refl _,
      atPolarity_symmetric_of pointOccurrence.context.polarity
        (.mk (.point state.region.locals state.region.items Sig.iota))⟩
  let initialExact := initialOccurrence.interface.withBody
    (initialOccurrence.context.fill state.region)
    initialOccurrence.sourceCanonical initialOccurrence.sourceExternalTwoEnded
  have exactIntroduction : Vacuity initialExact pointEndpoint := by
    exact Vacuity.iso initialOccurrence.host_iso pointIntroduction
      (OpenDiagramIso.refl pointEndpoint)
  have bridge : Relation.TransGen Step source initialExact := by
    exact (Relation.TransGen.single
      (Step.vacuity pointIntroduction)).tail
      (Step.vacuity exactIntroduction.symm)
  obtain ⟨foldCanonical, foldExternalTwoEnded, rawFoldSteps⟩ :=
    advanceAllDerives state variables identityBoundary_indexInjective
      supported stateCanonical initialOccurrence.interface
      initialOccurrence.context initialOccurrence.sourceCanonical
      initialOccurrence.sourceExternalTwoEnded
  have foldSteps : Relation.ReflTransGen Step initialExact
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill (state.advanceAll variables).region)
        foldCanonical foldExternalTwoEnded) := by
    simpa only [initialExact] using rawFoldSteps
  have exactExposedCanonical :
      (initialOccurrence.context.fill
        (exposedRegion description materialCanonical)).Canonical := by
    simpa only [initialOccurrence] using exposedCanonical
  have exactExposedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      initialOccurrence.interface.boundaryWire
      (initialOccurrence.context.fill
        (exposedRegion description materialCanonical)) := by
    intro signature wire
    simpa only [initialOccurrence] using exposedExternalTwoEnded wire
  let endpointBodyIso : RegionIso
      (WireEquiv.refl initialOccurrence.interface.external)
      (initialOccurrence.context.fill
        (state.advanceAll variables).region)
      (initialOccurrence.context.fill
        (exposedRegion description materialCanonical)) := by
    simpa only [state, variables] using
      DiagramContext.fillIso initialOccurrence.context
        (endpointRegionIso description materialCanonical)
  let endpointIso : OpenDiagramIso
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill (state.advanceAll variables).region)
        foldCanonical foldExternalTwoEnded)
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill
          (exposedRegion description materialCanonical))
        exactExposedCanonical exactExposedExternalTwoEnded) :=
    OpenDiagram.withBody_iso foldCanonical exactExposedCanonical
      foldExternalTwoEnded exactExposedExternalTwoEnded endpointBodyIso
  have foldCore : Relation.TransGen Step source
      (initialOccurrence.interface.withBody
        (initialOccurrence.context.fill (state.advanceAll variables).region)
        foldCanonical foldExternalTwoEnded) :=
    bridge.reflTransGen foldSteps
  have exposedCore : Relation.TransGen Step source
      (occurrence.interface.withBody
        (occurrence.context.fill
          (exposedRegion description materialCanonical))
        exposedCanonical exposedExternalTwoEnded) := by
    have transported := transGen_iso (OpenDiagramIso.refl source)
      foldCore endpointIso
    simpa only [initialOccurrence] using transported
  have transToRefl : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last →
        Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail steps step induction => exact .tail induction step
  exact transToRefl exposedCore

end VisualProof.Rule.Completeness.Erasure.Exposure
