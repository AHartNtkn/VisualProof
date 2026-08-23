import VisualProof.Rule.Completeness.Comprehension.Sites
import VisualProof.Rule.Completeness.Erasure.Exposure

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace EqualityNormalization

def formalPorts (arguments : List Sig) : Vars arguments arguments :=
  Erasure.Exposure.identityBoundary arguments

theorem formalPorts_append (left right : List Sig) :
    formalPorts (left ++ right) =
      Vars.extend
        ((formalPorts left).map fun wire => wire.appendLeft right)
        ((formalPorts right).map fun wire => Var.appendRight left wire) := by
  induction left with
  | nil =>
      simp [formalPorts, Erasure.Exposure.identityBoundary, Vars.map,
        Vars.extend, Var.appendRight]
  | cons head tail induction =>
      change Vars.cons .here
          ((formalPorts (tail ++ right)).map fun wire => .there wire) = _
      rw [induction, Vars.map_extend, Vars.map_map, Vars.map_map]
      apply congrArg (Vars.cons .here)
      congr 1
      · rw [Vars.map_map]
        apply Vars.map_congr
        intro signature wire
        rfl

theorem Vars.get_map
    (variables : Vars source signatures)
    (rename : ∀ {signature}, Var source signature → Var target signature)
    (position : Fin signatures.length) :
    (variables.map rename).get position = rename (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun rest => induction rest) position

theorem formalPorts_get_index (position : Fin arguments.length) :
    ((formalPorts arguments).get position).index = position := by
  exact Erasure.Exposure.identityBoundary_get_index position

theorem formalPorts_surjective (wire : Fin arguments.length) :
    ∃ position : Fin arguments.length,
      ((formalPorts arguments).get position).index = wire :=
  ⟨wire, formalPorts_get_index wire⟩

theorem equalityItems_left_mem_nil
    (left right : Vars wires signatures)
    (position : Fin signatures.length) (itemIndex : Nat) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      left right).incidencePaths (left.get position).index.val itemIndex := by
  induction left generalizing itemIndex with
  | nil => cases right; exact Fin.elim0 position
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          revert itemIndex
          refine Fin.cases (fun itemIndex => ?_)
            (fun rest itemIndex => ?_) position
          · change [] ∈
              (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
                (.cons leftHead leftTail)
                (.cons rightHead rightTail)).incidencePaths
                  leftHead.index.val itemIndex
            simp only [
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems,
              ItemSeq.incidencePaths, Item.incidencePaths,
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityPorts,
              List.mem_append, List.mem_replicate]
            apply Or.inl
            constructor
            · intro countZero
              have absent := List.count_eq_zero.mp countZero
              exact absent (by simp)
            · trivial
          · simp only [
              _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems,
              ItemSeq.incidencePaths, List.mem_append]
            exact Or.inr (induction rightTail rest (itemIndex + 1))

/-- Exact local list produced by the defining instantiation operations. -/
def locals (pattern : OpenDiagram arguments) : List Sig :=
  pattern.external ++ (pattern.body.locals ++ [])

def bodyEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming (pattern.external ++ pattern.body.locals)
      (targetWires ++ locals pattern) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire targetWires pattern.external
      (pattern.body.locals ++ []))
    (WireRenaming.comp
      (Region.conjoinLeftWire (targetWires ++ pattern.external)
        pattern.body.locals [])
      ((⟨fun wire => Var.appendRight targetWires wire⟩ :
        WireRenaming pattern.external
          (targetWires ++ pattern.external)).appendRight pattern.body.locals))

def equalityEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming ((targetWires ++ pattern.external) ++ [])
      (targetWires ++ locals pattern) :=
  WireRenaming.comp
    (Region.adjoinMaterialWire targetWires pattern.external
      (pattern.body.locals ++ []))
    (Region.conjoinRightWire (targetWires ++ pattern.external)
      pattern.body.locals [])

def actualEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming targetWires (targetWires ++ locals pattern) :=
  ⟨fun wire => equalityEmbedding pattern targetWires
    ((wire.appendLeft pattern.external).appendLeft [])⟩

def patternEmbedding (pattern : OpenDiagram arguments)
    (targetWires : List Sig) :
    WireRenaming pattern.external (targetWires ++ locals pattern) :=
  ⟨fun wire => equalityEmbedding pattern targetWires
    ((Var.appendRight targetWires wire).appendLeft [])⟩

def items (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    ItemSeq (targetWires ++ locals pattern) :=
  (pattern.body.items.renameWires (bodyEmbedding pattern targetWires)).append
    (_root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems
      (ports.map fun wire => actualEmbedding pattern targetWires wire)
      (pattern.boundaryWire.map
        fun wire => patternEmbedding pattern targetWires wire))

theorem bodyEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (bodyEmbedding pattern sourceWires) =
      bodyEmbedding pattern targetWires := by
  apply WireRenaming.ext
  intro signature wire
  apply Var.appendCases (left := pattern.external)
    (right := pattern.body.locals)
    (motive := fun wire =>
      WireRenaming.comp (rename.appendRight (locals pattern))
          (bodyEmbedding pattern sourceWires) wire =
        bodyEmbedding pattern targetWires wire)
  · intro externalSignature external
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]

theorem actualEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (actualEmbedding pattern sourceWires) =
      WireRenaming.comp (actualEmbedding pattern targetWires) rename := by
  apply WireRenaming.ext
  intro signature wire
  simp [actualEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    WireRenaming.appendRight, Region.adjoinMaterialWire,
    Region.conjoinRightWire]

theorem patternEmbedding_natural
    (pattern : OpenDiagram arguments)
    (rename : WireRenaming sourceWires targetWires) :
    WireRenaming.comp (rename.appendRight (locals pattern))
      (patternEmbedding pattern sourceWires) =
      patternEmbedding pattern targetWires := by
  apply WireRenaming.ext
  intro signature wire
  simp [patternEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    WireRenaming.appendRight, Region.adjoinMaterialWire,
    Region.conjoinRightWire]

@[simp] theorem actualEmbedding_index_val
    (pattern : OpenDiagram arguments)
    (wire : Var targetWires signature) :
    (actualEmbedding pattern targetWires wire).index.val = wire.index.val := by
  simp [actualEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    Region.adjoinMaterialWire, Region.conjoinRightWire]

theorem bodyEmbedding_index_lower
    (pattern : OpenDiagram arguments)
    (wire : Var (pattern.external ++ pattern.body.locals) signature) :
    targetWires.length ≤
      (bodyEmbedding pattern targetWires wire).index.val := by
  apply Var.appendCases (left := pattern.external)
    (right := pattern.body.locals)
    (motive := fun wire => targetWires.length ≤
      (bodyEmbedding pattern targetWires wire).index.val)
  · intro externalSignature external
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [bodyEmbedding, locals, WireRenaming.comp,
      WireRenaming.appendRight, Region.adjoinMaterialWire,
      Region.conjoinLeftWire]

theorem patternEmbedding_index_lower
    (pattern : OpenDiagram arguments)
    (wire : Var pattern.external signature) :
    targetWires.length ≤
      (patternEmbedding pattern targetWires wire).index.val := by
  simp [patternEmbedding, equalityEmbedding, locals, WireRenaming.comp,
    Region.adjoinMaterialWire, Region.conjoinRightWire]

theorem Vars.map_comp4
    (variables : Vars first signatures)
    (firstMap : ∀ {signature}, Var first signature → Var second signature)
    (secondMap : ∀ {signature}, Var second signature → Var third signature)
    (thirdMap : ∀ {signature}, Var third signature → Var fourth signature)
    (fourthMap : ∀ {signature}, Var fourth signature → Var fifth signature) :
    (((variables.map fun wire => firstMap wire).map
      fun wire => secondMap wire).map fun wire => thirdMap wire).map
        (fun wire => fourthMap wire) =
      variables.map fun wire =>
        fourthMap (thirdMap (secondMap (firstMap wire))) := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons
        (fourthMap (thirdMap (secondMap (firstMap head))))) induction

theorem instantiate_eq_presentation
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports = .mk (locals pattern) (items pattern ports) := by
  cases pattern with
  | mk external boundaryWire boundarySurjective body canonical
      externalTwoEnded =>
    cases body with
    | mk bodyLocals bodyItems =>
      simp only [
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate,
        _root_.VisualProof.Rule.Comprehension.Instantiation.Equalities_eq_ofItems,
        items, bodyEmbedding, actualEmbedding, patternEmbedding,
        equalityEmbedding, locals,
        Region.locals, Region.items, Region.renameWires, Region.conjoin,
        Region.adjoinAt, Region.ofItems, ItemSeq.renameWires_append,
        ItemSeq.renameWires_comp,
        _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires]
      simp only [ItemSeq.renameWires, ItemSeq.nil_append,
        Vars.map_comp4, WireRenaming.comp]

theorem instantiate_renameWires
    (pattern : OpenDiagram arguments)
    (ports : Vars sourceWires arguments)
    (rename : WireRenaming sourceWires targetWires) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).renameWires rename =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate pattern
        (ports.map fun wire => rename wire) := by
  have actualMap :
      (ports.map fun wire => actualEmbedding pattern sourceWires wire).map
          (fun wire => rename.appendRight (locals pattern) wire) =
        (ports.map fun wire => rename wire).map
          (fun wire => actualEmbedding pattern targetWires wire) := by
    calc
      _ = ports.map (fun wire =>
          rename.appendRight (locals pattern)
            (actualEmbedding pattern sourceWires wire)) :=
        Diagram.vars_map_comp ports (actualEmbedding pattern sourceWires)
          (rename.appendRight (locals pattern))
      _ = ports.map (fun wire =>
          actualEmbedding pattern targetWires (rename wire)) := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming sourceWires
              (targetWires ++ locals pattern) =>
            ports.map fun wire => map wire)
          (actualEmbedding_natural pattern rename)
      _ = _ := (Diagram.vars_map_comp ports rename
        (actualEmbedding pattern targetWires)).symm
  have patternMap :
      (pattern.boundaryWire.map
          fun wire => patternEmbedding pattern sourceWires wire).map
            (fun wire => rename.appendRight (locals pattern) wire) =
        pattern.boundaryWire.map
          (fun wire => patternEmbedding pattern targetWires wire) := by
    calc
      _ = pattern.boundaryWire.map (fun wire =>
          rename.appendRight (locals pattern)
            (patternEmbedding pattern sourceWires wire)) :=
        Diagram.vars_map_comp pattern.boundaryWire
          (patternEmbedding pattern sourceWires)
          (rename.appendRight (locals pattern))
      _ = _ := by
        simpa only [WireRenaming.comp] using congrArg
          (fun map : WireRenaming pattern.external
              (targetWires ++ locals pattern) =>
            pattern.boundaryWire.map fun wire => map wire)
          (patternEmbedding_natural pattern rename)
  rw [instantiate_eq_presentation, instantiate_eq_presentation]
  simp only [Region.renameWires, items, ItemSeq.renameWires_append,
    ItemSeq.renameWires_comp,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_renameWires]
  rw [bodyEmbedding_natural, actualMap, patternMap]

/-- Every actual port of an instantiation has a root-level equality
incidence. -/
theorem instantiate_port_incidence_mem_nil
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (position : Fin arguments.length) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths (ports.get position).index.val := by
  rw [instantiate_eq_presentation]
  simp only [Region.incidencePaths, items, ItemSeq.incidencePaths_append]
  have selected := equalityItems_left_mem_nil
    (ports.map fun wire => actualEmbedding pattern targetWires wire)
    (pattern.boundaryWire.map
      fun wire => patternEmbedding pattern targetWires wire)
    position (pattern.body.items.renameWires
      (bodyEmbedding pattern targetWires)).length
  have selectedIndex :
      ((ports.map fun wire => actualEmbedding pattern targetWires wire).get
        position).index.val = (ports.get position).index.val := by
    rw [Vars.get_map]
    simp [actualEmbedding, equalityEmbedding, WireRenaming.comp,
      Region.conjoinRightWire, Region.adjoinMaterialWire, locals]
  rw [selectedIndex] at selected
  exact List.mem_append_right _ (by
    simpa only [Nat.zero_add] using selected)

/-- Every actual port of an instantiation has an equality incidence. -/
theorem instantiate_port_incidence_nonempty
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (position : Fin arguments.length) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths (ports.get position).index.val ≠ [] :=
  List.ne_nil_of_mem (instantiate_port_incidence_mem_nil pattern ports position)

theorem Vars.countIndex_map_zero_of_lower
    (variables : Vars source signatures)
    (rename : WireRenaming source target)
    (floor wireIndex : Nat)
    (lower : ∀ {signature} (wire : Var source signature),
      floor ≤ (rename wire).index.val)
    (below : wireIndex < floor) :
    (variables.map fun wire => rename wire).countIndex wireIndex = 0 := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex]
      have different : (rename head).index.val ≠ wireIndex := by
        intro equality
        have := lower head
        omega
      simp only [different, if_false, Nat.zero_add]
      exact induction

theorem Vars.countIndex_map_actual
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires signatures)
    (wireIndex : Nat) :
    (ports.map fun wire => actualEmbedding pattern targetWires wire).countIndex
        wireIndex = ports.countIndex wireIndex := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex, actualEmbedding_index_val,
        induction]

theorem instantiate_incidencePaths_length
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val).length =
      ports.countIndex wire.index.val := by
  have bodyEmpty :
      (pattern.body.items.renameWires
        (bodyEmbedding pattern targetWires)).incidencePaths
          wire.index.val 0 = [] := by
    apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
    · have bound := wire.index.isLt
      simp only [List.length_append]
      omega
    · intro bodySignature bodyWire equality
      have lower := bodyEmbedding_index_lower
        (targetWires := targetWires) pattern bodyWire
      have bound := wire.index.isLt
      omega
  have rightZero :
      (pattern.boundaryWire.map
        fun boundaryWire => patternEmbedding pattern targetWires
          boundaryWire).countIndex wire.index.val = 0 := by
    apply Vars.countIndex_map_zero_of_lower pattern.boundaryWire
      (patternEmbedding pattern targetWires) targetWires.length
        wire.index.val
    · exact patternEmbedding_index_lower
        (targetWires := targetWires) pattern
    · exact wire.index.isLt
  rw [instantiate_eq_presentation]
  simp only [Region.incidencePaths, items, ItemSeq.incidencePaths_append,
    List.length_append,
    _root_.VisualProof.Rule.Comprehension.Instantiation.equalityItems_incidencePaths_length,
    bodyEmpty,
    List.length_nil, Nat.zero_add, Vars.countIndex_map_actual, rightZero,
    Nat.add_zero]

theorem instantiate_incidence_nonempty_iff
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val ≠ [] ↔
      0 < ports.countIndex wire.index.val := by
  rw [← List.length_pos_iff, instantiate_incidencePaths_length]

/-- Replace an arbitrary valid pattern boundary by the ordered identity
boundary over its argument context. Its body is the exact existing-syntax
instantiation of the original pattern on those formal variables. -/
def identityBoundary (pattern : OpenDiagram arguments) :
    OpenDiagram arguments where
  external := arguments
  boundaryWire := formalPorts arguments
  boundarySurjective := formalPorts_surjective
  body := _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
    pattern (formalPorts arguments)
  canonical :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
      pattern (formalPorts arguments)
  externalTwoEnded := by
    intro signature wire
    have boundaryPositive :
        0 < (formalPorts arguments).countIndex wire.index.val := by
      obtain ⟨position, maps⟩ := formalPorts_surjective wire.index
      have positive := (formalPorts arguments).countIndex_get_positive position
      rw [maps] at positive
      exact positive
    have bodyPositive : 0 <
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (formalPorts arguments)).incidencePaths
            wire.index.val).length := by
      have nonempty := instantiate_port_incidence_nonempty pattern
        (formalPorts arguments) wire.index
      rw [formalPorts_get_index] at nonempty
      exact List.length_pos_iff.mpr nonempty
    omega

def formalSubstitution : {arguments : List Sig} →
    Vars targetWires arguments → WireRenaming arguments targetWires
  | [], .nil => ⟨fun wire => nomatch wire⟩
  | _ :: _, .cons head tail => ⟨fun wire =>
      match wire with
      | .here => head
      | .there rest => formalSubstitution tail rest⟩

@[simp] theorem formalSubstitution_here
    (head : Var targetWires signature)
    (tail : Vars targetWires arguments) :
    formalSubstitution (.cons head tail) (.here : Var (signature :: arguments)
      signature) = head := rfl

theorem formalPorts_map_substitution
    (ports : Vars targetWires arguments) :
    (formalPorts arguments).map
      (fun wire => formalSubstitution ports wire) = ports := by
  induction ports with
  | nil => rfl
  | cons head tail induction =>
      simp only [formalPorts, Erasure.Exposure.identityBoundary, Vars.map,
        formalSubstitution_here]
      congr 1
      rw [Diagram.vars_map_comp
        (Erasure.Exposure.identityBoundary _) ⟨fun wire => .there wire⟩
          (formalSubstitution (.cons head tail))]
      change (formalPorts _).map
        (fun wire => formalSubstitution tail wire) = tail
      exact induction

theorem formalSubstitution_formalPorts_map
    (rename : WireRenaming arguments targetWires)
    {signature : Sig} (wire : Var arguments signature) :
    formalSubstitution
        ((formalPorts arguments).map fun formalWire => rename formalWire) wire =
      rename wire := by
  induction arguments with
  | nil => exact nomatch wire
  | cons head rest induction =>
      cases wire with
      | here => rfl
      | there wire =>
          simp only [formalPorts, Erasure.Exposure.identityBoundary, Vars.map]
          let restRename : WireRenaming rest targetWires :=
            ⟨fun restWire => rename (.there restWire)⟩
          have tailEq :
              ((Erasure.Exposure.identityBoundary rest).map
                  fun restWire => (.there restWire : Var (head :: rest) _)).map
                    (fun restWire => rename restWire) =
                (formalPorts rest).map fun restWire => restRename restWire := by
            exact Diagram.vars_map_comp
              (Erasure.Exposure.identityBoundary rest)
              ⟨fun restWire => .there restWire⟩ rename
          simp only [formalSubstitution]
          rw [tailEq]
          exact induction restRename wire

theorem formalSubstitution_map
    (application : Vars source arguments)
    (rename : WireRenaming source target)
    {signature : Sig} (wire : Var arguments signature) :
    formalSubstitution (application.map fun applicationWire =>
        rename applicationWire) wire =
      rename (formalSubstitution application wire) := by
  induction application with
  | nil => exact nomatch wire
  | cons head tail induction =>
      cases wire with
      | here => rfl
      | there wire => exact induction wire

theorem formalPorts_eq_exposure :
    formalPorts arguments = Erasure.Exposure.identityBoundary arguments := by
  rfl

theorem supportPins_eq_nil
    (material : Region materialWires)
    (variables : Vars materialWires signatures)
    (supported : ∀ position : Fin signatures.length,
      material.incidencePaths (variables.get position).index.val ≠ []) :
    Erasure.Exposure.supportPins material signatures variables = .nil := by
  induction variables with
  | nil => rfl
  | @cons signature rest head tail induction =>
      have headSupported : material.incidencePaths head.index.val ≠ [] := by
        simpa only [Vars.get] using supported 0
      have tailSupported : ∀ position : Fin rest.length,
          material.incidencePaths (tail.get position).index.val ≠ [] := by
        intro position
        simpa only [Vars.get] using supported position.succ
      simp only [Erasure.Exposure.supportPins, headSupported, ↓reduceIte]
      exact induction tailSupported

theorem normalized_supportPins_eq_nil
    (pattern : OpenDiagram arguments) :
    Erasure.Exposure.supportPins
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments))
      arguments (Erasure.Exposure.identityBoundary arguments) = .nil := by
  apply supportPins_eq_nil
  intro position
  simpa only [← formalPorts_eq_exposure] using
    instantiate_port_incidence_nonempty pattern
      (formalPorts arguments) position

theorem supportBody_eq_of_supportPins_nil
    (material : Region materialWires)
    (empty : Erasure.Exposure.supportPins material materialWires
      (Erasure.Exposure.identityBoundary materialWires) = .nil) :
    Erasure.Exposure.supportBody material = material := by
  unfold Erasure.Exposure.supportBody
  rw [empty]
  cases material with
  | mk locals materialItems =>
      change Region.mk locals (materialItems.append .nil) =
        Region.mk locals materialItems
      rw [ItemSeq.append_nil]

theorem OpenDiagram.eq_of_data
    (left right : OpenDiagram boundary)
    (externalEq : left.external = right.external)
    (boundaryEq : HEq left.boundaryWire right.boundaryWire)
    (bodyEq : HEq left.body right.body) : left = right := by
  cases left with
  | mk leftExternal leftBoundary leftSurjective leftBody leftCanonical
      leftTwoEnded =>
    cases right with
    | mk rightExternal rightBoundary rightSurjective rightBody rightCanonical
        rightTwoEnded =>
      simp only at externalEq boundaryEq bodyEq
      cases externalEq
      cases boundaryEq
      cases bodyEq
      rfl

theorem normalized_supportBody_eq
    (pattern : OpenDiagram arguments) :
    Erasure.Exposure.supportBody
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments)) =
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments) := by
  apply supportBody_eq_of_supportPins_nil
  exact normalized_supportPins_eq_nil pattern

theorem supportPattern_eq_identityBoundary
    (pattern : OpenDiagram arguments)
    (materialCanonical :
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern (formalPorts arguments)).Canonical) :
    Erasure.Exposure.supportPattern
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (formalPorts arguments)) materialCanonical =
      identityBoundary pattern := by
  apply OpenDiagram.eq_of_data
  · rfl
  · rfl
  · exact heq_of_eq (normalized_supportBody_eq pattern)

def exposureDescriptionWithHost
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    Rule.Erasure.Description outer where
  materialWires := arguments
  hostLocals := hostLocals
  hostItems := hostItems
  material := _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
    pattern (formalPorts arguments)
  wireMap := formalSubstitution ports

theorem exposureDescriptionWithHost_source
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    (exposureDescriptionWithHost pattern hostLocals hostItems ports).source =
      Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports) := by
  simp only [Rule.Erasure.Description.source,
    exposureDescriptionWithHost, Region.spliceAt]
  rw [instantiate_renameWires, formalPorts_map_substitution]

theorem exposureDescriptionWithHost_applicationPorts
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments) :
    Erasure.Exposure.applicationPorts
      (exposureDescriptionWithHost pattern hostLocals hostItems ports) =
      ports := by
  simp only [Erasure.Exposure.applicationPorts,
    exposureDescriptionWithHost]
  rw [← formalPorts_eq_exposure, formalPorts_map_substitution]

theorem exposureDescriptionWithHost_exposedRegion
    (pattern : OpenDiagram arguments)
    (hostLocals : List Sig) (hostItems : ItemSeq (outer ++ hostLocals))
    (ports : Vars (outer ++ hostLocals) arguments)
    (materialCanonical :
      (exposureDescriptionWithHost pattern hostLocals hostItems ports).material.Canonical) :
    Erasure.Exposure.exposedRegion
        (exposureDescriptionWithHost pattern hostLocals hostItems ports)
        materialCanonical =
      Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (identityBoundary pattern) ports) := by
  simp only [Erasure.Exposure.exposedRegion]
  change Region.adjoinAt hostLocals hostItems
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern (formalPorts arguments)) materialCanonical)
        (Erasure.Exposure.applicationPorts
          (exposureDescriptionWithHost pattern hostLocals hostItems ports))) =
    _
  rw [supportPattern_eq_identityBoundary pattern materialCanonical,
    exposureDescriptionWithHost_applicationPorts]

theorem Vars.exists_get_index_of_countIndex_pos
    (variables : Vars context signatures) (wireIndex : Nat)
    (positive : 0 < variables.countIndex wireIndex) :
    ∃ position : Fin signatures.length,
      (variables.get position).index.val = wireIndex := by
  induction variables with
  | nil => simp [Vars.countIndex] at positive
  | @cons signature rest head tail induction =>
      by_cases headEq : head.index.val = wireIndex
      · exact ⟨0, headEq⟩
      · have tailPositive : 0 < tail.countIndex wireIndex := by
          simpa [Vars.countIndex, headEq] using positive
        obtain ⟨position, positionEq⟩ := induction tailPositive
        exact ⟨position.succ, by
          simpa only [Vars.get] using positionEq⟩

theorem instantiate_incidence_mem_nil_of_nonempty
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature)
    (nonempty :
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports).incidencePaths wire.index.val ≠ []) :
    [] ∈ (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports).incidencePaths wire.index.val := by
  have positive := (instantiate_incidence_nonempty_iff pattern ports wire).mp
    nonempty
  obtain ⟨position, positionEq⟩ :=
    Vars.exists_get_index_of_countIndex_pos ports wire.index.val positive
  have rootIncidence := instantiate_port_incidence_mem_nil pattern ports position
  rw [positionEq] at rootIncidence
  exact rootIncidence

theorem instantiate_rootedTwo_iff
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments)
    (wire : Var targetWires signature) :
    RegionPath.RootedTwo
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports).incidencePaths wire.index.val) ↔
      2 ≤ ports.countIndex wire.index.val := by
  constructor
  · intro rooted
    have lengthBound := rooted.1
    rw [instantiate_incidencePaths_length] at lengthBound
    exact lengthBound
  · intro countBound
    have nonempty :
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports).incidencePaths wire.index.val ≠ [] :=
      (instantiate_incidence_nonempty_iff pattern ports wire).mpr (by omega)
    constructor
    · rw [instantiate_incidencePaths_length]
      exact countBound
    · exact RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil _
        (instantiate_incidence_mem_nil_of_nonempty pattern ports wire nonempty)

mutual
  def normalizedRegion
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .mk childSites =>
        let childOutput := normalizedItems pattern _ childSites
        ⟨Region.adjoinAt _ .nil childOutput.1,
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            childOutput.2⟩
  termination_by structural sites

  def normalizedItems
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .nil _ =>
        ⟨Region.blank common,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil⟩
    | .cons itemSites tailSites =>
        let itemOutput := normalizedItem pattern _ itemSites
        let tailOutput := normalizedItems pattern _ tailSites
        ⟨itemOutput.1.conjoin tailOutput.1,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            itemOutput.2 tailOutput.2⟩
  termination_by structural sites

  def normalizedItem
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      { normalized : Region common //
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized } :=
    match sites with
    | .atom head ports =>
        ⟨Region.singleton (.atom head ports),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            head ports⟩
    | .selectedAtom ports _ =>
        ⟨_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports,
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            ports⟩
    | .identity signature arity ports =>
        ⟨Region.singleton (.identity signature arity ports),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            signature arity ports⟩
    | .cut childSites =>
        let childOutput := normalizedRegion pattern _ childSites
        ⟨Region.singleton (.cut childOutput.1),
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            childOutput.2⟩
  termination_by structural sites
end

mutual
  /-- Whether the exact site annotation contains any selected application. -/
  def regionHasSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : RegionSites operation data evidence) : Bool :=
    match sites with
    | .mk childSites => itemsHaveSelection childSites
  termination_by structural sites

  def itemsHaveSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemsSites operation data evidence) : Bool :=
    match sites with
    | .nil _ => false
    | .cons itemSites tailSites =>
        itemHasSelection itemSites || itemsHaveSelection tailSites
  termination_by structural sites

  def itemHasSelection
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      {evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result}
      (sites : ItemSites operation data evidence) : Bool :=
    match sites with
    | .atom _ _ => false
    | .selectedAtom _ _ => true
    | .identity _ _ _ => false
    | .cut childSites => regionHasSelection childSites
  termination_by structural sites
end

mutual
  theorem normalizedRegion_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (none : regionHasSelection sites = false) :
      (normalizedRegion pattern evidence sites).1 = result :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        change Region.adjoinAt locals .nil
            (normalizedItems pattern childEvidence childSites).1 =
          Region.adjoinAt locals .nil childResult
        rw [normalizedItems_eq_of_noSelection pattern childEvidence
          childSites (by simpa only [regionHasSelection] using none)]
  termination_by structural sites

  theorem normalizedItems_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (none : itemsHaveSelection sites = false) :
      (normalizedItems pattern evidence sites).1 = result :=
    match sites with
    | .nil _ => rfl
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemEndpoint tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        have itemNone : itemHasSelection itemSites = false := by
          cases selected : itemHasSelection itemSites with
          | false => rfl
          | true => simp_all only [itemsHaveSelection, Bool.true_or,
              Bool.true_eq_false]
        have tailNone : itemsHaveSelection tailSites = false := by
          cases selected : itemsHaveSelection tailSites with
          | false => rfl
          | true => simp_all only [itemsHaveSelection, Bool.or_true,
              Bool.true_eq_false]
        change
          (normalizedItem pattern itemEvidence itemSites).1.conjoin
              (normalizedItems pattern tailEvidence tailSites).1 =
            itemEndpoint.conjoin tailResult
        rw [normalizedItem_eq_of_noSelection pattern itemEvidence itemSites
          itemNone]
        rw [normalizedItems_eq_of_noSelection pattern tailEvidence tailSites
          tailNone]
  termination_by structural sites

  theorem normalizedItem_eq_of_noSelection
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (none : itemHasSelection sites = false) :
      (normalizedItem pattern evidence sites).1 = result :=
    match sites with
    | .atom _ _ => rfl
    | .selectedAtom _ _ => by
        simp only [itemHasSelection, Bool.true_eq_false] at none
    | .identity _ _ _ => rfl
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        change Region.singleton
            (.cut (normalizedRegion pattern childEvidence childSites).1) =
          Region.singleton (.cut childResult)
        rw [normalizedRegion_eq_of_noSelection pattern childEvidence
          childSites (by simpa only [itemHasSelection] using none)]
  termination_by structural sites
end

mutual
  theorem normalizedRegion_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence) :
      ScopePreservation result (normalizedRegion pattern evidence sites).1 :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        let childOutput := normalizedItems pattern childEvidence childSites
        let childPreservation :=
          normalizedItems_scope pattern childEvidence childSites
        change ScopePreservation
          (Region.adjoinAt locals .nil childResult)
          (Region.adjoinAt locals .nil childOutput.1)
        constructor
        · intro sourceCanonical
          have sourceChildCanonical : childResult.Canonical :=
            Region.Canonical.material_of_adjoinAt locals .nil childResult
              sourceCanonical
          have targetChildCanonical : childOutput.1.Canonical :=
            childPreservation.canonical sourceChildCanonical
          apply Region.Canonical.adjoinAt_of_material_roots locals .nil
            childOutput.1 True.intro targetChildCanonical
          intro localIndex
          let localWire := Var.appendRight common (Var.ofIndex localIndex)
          have sourceRoot : RegionPath.RootedTwo
              (childResult.incidencePaths localWire.index.val) := by
            simpa [localWire] using
              Region.Canonical.rootedTwo_materialHost_of_adjoinAt_nil
                childResult sourceCanonical localIndex
          have targetRoot := childPreservation.rootedTwo localWire sourceRoot
          simpa [localWire] using targetRoot
        · intro signature wire
          let childWire := wire.appendLeft locals
          have sourcePaths := Region.incidencePaths_adjoinAt_nil childResult
            childWire
          have targetPaths := Region.incidencePaths_adjoinAt_nil childOutput.1
            childWire
          have childIndex : childWire.index.val = wire.index.val := by
            simp [childWire]
          rw [childIndex] at sourcePaths targetPaths
          rw [sourcePaths, targetPaths]
          simpa only [childWire, Var.index_appendLeft] using
            childPreservation.incidenceNonempty childWire
        · intro signature wire sourceRoot
          let childWire := wire.appendLeft locals
          have sourcePaths := Region.incidencePaths_adjoinAt_nil childResult
            childWire
          have targetPaths := Region.incidencePaths_adjoinAt_nil childOutput.1
            childWire
          have childIndex : childWire.index.val = wire.index.val := by
            simp [childWire]
          rw [childIndex] at sourcePaths targetPaths
          rw [sourcePaths] at sourceRoot
          rw [targetPaths]
          simpa only [childWire, Var.index_appendLeft] using
            childPreservation.rootedTwo childWire (by
              simpa only [childWire, Var.index_appendLeft] using sourceRoot)
  termination_by structural sites

  theorem normalizedItems_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence) :
      ScopePreservation result (normalizedItems pattern evidence sites).1 :=
    match sites with
    | .nil _ => by
        change ScopePreservation (Region.blank common) (Region.blank common)
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemEndpoint tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        let itemOutput := normalizedItem pattern itemEvidence itemSites
        let tailOutput := normalizedItems pattern tailEvidence tailSites
        let itemPreservation := normalizedItem_scope pattern itemEvidence
          itemSites
        let tailPreservation := normalizedItems_scope pattern tailEvidence
          tailSites
        change ScopePreservation (itemEndpoint.conjoin tailResult)
          (itemOutput.1.conjoin tailOutput.1)
        have combined := Region.conjoin_preserves_scope itemEndpoint tailResult
          itemOutput.1 tailOutput.1 itemPreservation.canonical
            tailPreservation.canonical itemPreservation.incidenceNonempty
              tailPreservation.incidenceNonempty itemPreservation.rootedTwo
                tailPreservation.rootedTwo
        exact {
          canonical := combined.1
          incidenceNonempty := fun wire => (combined.2 wire).1
          rootedTwo := fun wire => (combined.2 wire).2
        }
  termination_by structural sites

  theorem normalizedItem_scope
      {arguments common sourceWires targetWires : List Sig}
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence) :
      ScopePreservation result (normalizedItem pattern evidence sites).1 :=
    match sites with
    | .atom head ports => by
        change ScopePreservation (Region.singleton (.atom head ports))
          (Region.singleton (.atom head ports))
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | .selectedAtom ports _ => by
        change ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports)
        constructor
        · intro _
          exact
            _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
              (identityBoundary pattern) ports
        · intro signature wire
          rw [instantiate_incidence_nonempty_iff,
            instantiate_incidence_nonempty_iff]
        · intro signature wire sourceRoot
          rw [instantiate_rootedTwo_iff] at sourceRoot ⊢
          exact sourceRoot
    | .identity signature arity ports => by
        change ScopePreservation
          (Region.singleton (.identity signature arity ports))
          (Region.singleton (.identity signature arity ports))
        exact {
          canonical := fun canonical => canonical
          incidenceNonempty := fun _ => Iff.rfl
          rootedTwo := fun _ rooted => rooted
        }
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        let childOutput := normalizedRegion pattern childEvidence childSites
        let childPreservation := normalizedRegion_scope pattern childEvidence
          childSites
        change ScopePreservation (Region.singleton (.cut childResult))
          (Region.singleton (.cut childOutput.1))
        constructor
        · intro sourceCanonical
          apply (Region.singleton_cut_canonical_iff childOutput.1).mpr
          exact childPreservation.canonical
            ((Region.singleton_cut_canonical_iff childResult).mp
              sourceCanonical)
        · intro signature wire
          rw [Region.incidencePaths_singleton_cut,
            Region.incidencePaths_singleton_cut]
          constructor
          · intro sourceNonempty
            have childSourceNonempty :
                childResult.incidencePaths wire.index.val ≠ [] := by
              intro sourceEmpty
              exact sourceNonempty
                ((List.map_eq_nil_iff).mpr sourceEmpty)
            have childTargetNonempty :=
              (childPreservation.incidenceNonempty wire).mp
                childSourceNonempty
            intro targetEmpty
            exact childTargetNonempty
              ((List.map_eq_nil_iff).mp targetEmpty)
          · intro targetNonempty
            have childTargetNonempty :
                childOutput.1.incidencePaths wire.index.val ≠ [] := by
              intro targetEmpty
              exact targetNonempty
                ((List.map_eq_nil_iff).mpr targetEmpty)
            have childSourceNonempty :=
              (childPreservation.incidenceNonempty wire).mpr
                childTargetNonempty
            intro sourceEmpty
            exact childSourceNonempty
              ((List.map_eq_nil_iff).mp sourceEmpty)
        · intro signature wire sourceRoot
          have sameEmpty :
              childResult.incidencePaths wire.index.val = [] ↔
                childOutput.1.incidencePaths wire.index.val = [] := by
            constructor
            · intro sourceEmpty
              by_cases targetEmpty :
                  childOutput.1.incidencePaths wire.index.val = []
              · exact targetEmpty
              · exact False.elim
                  (((childPreservation.incidenceNonempty wire).mpr
                    targetEmpty) sourceEmpty)
            · intro targetEmpty
              by_cases sourceEmpty :
                  childResult.incidencePaths wire.index.val = []
              · exact sourceEmpty
              · exact False.elim
                  (((childPreservation.incidenceNonempty wire).mp
                    sourceEmpty) targetEmpty)
          rw [Region.incidencePaths_singleton_cut] at sourceRoot ⊢
          have replaced := RegionPath.rootedTwo_replace []
            (childResult.incidencePaths wire.index.val)
            (childOutput.1.incidencePaths wire.index.val) [] 0 sameEmpty
          simpa only [List.nil_append, List.append_nil] using
            replaced.mp (by simpa using sourceRoot)
  termination_by structural sites
end

def appendHostWire (outer hostLocals : List Sig) :
    WireRenaming outer (outer ++ hostLocals) :=
  ⟨fun wire => wire.appendLeft hostLocals⟩

theorem conjoin_eq_adjoinRename
    (host material : Region outer) :
    host.conjoin material =
      Region.adjoinAt host.locals host.items
        (material.renameWires (appendHostWire outer host.locals)) := by
  cases host with
  | mk hostLocals hostItems =>
      cases material with
      | mk materialLocals materialItems =>
          have materialMap : WireRenaming.comp
              (Region.adjoinMaterialWire outer hostLocals materialLocals)
              ((appendHostWire outer hostLocals).appendRight materialLocals) =
            Region.conjoinRightWire outer hostLocals materialLocals := by
            apply WireRenaming.ext
            intro signature wire
            apply Var.appendCases (left := outer)
              (right := materialLocals)
              (motive := fun wire =>
                WireRenaming.comp
                    (Region.adjoinMaterialWire outer hostLocals materialLocals)
                    ((appendHostWire outer hostLocals).appendRight
                      materialLocals) wire =
                  Region.conjoinRightWire outer hostLocals materialLocals
                    wire)
            · intro inheritedSignature inherited
              simp [WireRenaming.comp, WireRenaming.appendRight,
                appendHostWire, Region.adjoinMaterialWire,
                Region.conjoinRightWire]
            · intro localSignature localWire
              simp [WireRenaming.comp, WireRenaming.appendRight,
                appendHostWire, Region.adjoinMaterialWire,
                Region.conjoinRightWire]
          simp only [Region.conjoin, Region.adjoinAt, Region.renameWires,
            Region.locals, Region.items, ItemSeq.renameWires_comp,
            Region.adjoinHostWire]
          rw [materialMap]

noncomputable def instantiateRenameIso
    (pattern : OpenDiagram arguments)
    (ports : Vars sourceWires arguments)
    (rename : WireRenaming sourceWires targetWires) :
    RegionIso (WireEquiv.refl targetWires)
      ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports).renameWires rename)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate pattern
        (ports.map fun wire => rename wire)) := by
  rw [instantiate_renameWires]
  exact RegionIso.refl _

theorem canonical_conjoin
    {outer : List Sig} {first second : Region outer}
    (firstCanonical : first.Canonical)
    (secondCanonical : second.Canonical) :
    (first.conjoin second).Canonical := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          rw [conjoin_eq_adjoinRename]
          exact Region.Canonical.adjoinAt firstLocals firstItems
            ((Region.mk secondLocals secondItems).renameWires
              (appendHostWire _ firstLocals)) firstCanonical
            ((Region.Canonical.renameWires_iff
              (Region.mk secondLocals secondItems)
              (appendHostWire _ firstLocals)).mpr secondCanonical)

theorem canonical_right_of_conjoin
    {outer : List Sig} {first second : Region outer}
    (canonical : (first.conjoin second).Canonical) : second.Canonical := by
  rw [conjoin_eq_adjoinRename] at canonical
  have renamed := Region.Canonical.material_of_adjoinAt first.locals
    first.items (second.renameWires (appendHostWire _ first.locals)) canonical
  exact (Region.Canonical.renameWires_iff second
    (appendHostWire _ first.locals)).mp renamed

theorem canonical_left_of_conjoin
    {outer : List Sig} {first second : Region outer}
    (canonical : (first.conjoin second).Canonical) : first.Canonical := by
  cases first with
  | mk firstLocals firstItems =>
      cases second with
      | mk secondLocals secondItems =>
          simp only [Region.conjoin, Region.Canonical] at canonical ⊢
          constructor
          · intro localIndex
            let hostWire := Var.appendRight outer (Var.ofIndex localIndex)
            let combinedIndex : Fin (firstLocals ++ secondLocals).length :=
              ⟨localIndex.val, by
                simp only [List.length_append]
                exact Nat.lt_add_right _ localIndex.isLt⟩
            have combinedRoot := canonical.1 combinedIndex
            have combinedWireIndex :
                outer.length + combinedIndex.val = hostWire.index.val := by
              simp [combinedIndex, hostWire]
            rw [combinedWireIndex, ItemSeq.incidencePaths_append]
              at combinedRoot
            have hostMap :
                Region.conjoinLeftWire outer firstLocals secondLocals =
                  Region.adjoinHostWire outer firstLocals secondLocals := rfl
            rw [hostMap,
              ItemSeq.incidencePaths_renameWires_adjoinHost
              firstItems hostWire 0] at combinedRoot
            have secondEmpty :
                (secondItems.renameWires
                  (Region.conjoinRightWire outer firstLocals
                    secondLocals)).incidencePaths hostWire.index.val
                      (0 + (firstItems.renameWires
                        (Region.conjoinLeftWire outer firstLocals
                          secondLocals)).length) = [] := by
              apply ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
              · have hostBound := localIndex.isLt
                simp [hostWire, List.length_append]
                omega
              · intro signature wire
                apply Var.appendCases (left := outer)
                  (right := secondLocals)
                  (motive := fun wire =>
                    (Region.conjoinRightWire outer firstLocals secondLocals
                      wire).index.val ≠ hostWire.index.val)
                · intro inheritedSignature inherited
                  have bound := inherited.index.isLt
                  simp [Region.conjoinRightWire, hostWire]
                  omega
                · intro localSignature localWire
                  have hostBound := localIndex.isLt
                  simp [Region.conjoinRightWire, hostWire]
                  omega
            have secondEmpty' :
                (secondItems.renameWires
                  (Region.conjoinRightWire outer firstLocals
                    secondLocals)).incidencePaths hostWire.index.val
                      (0 + (firstItems.renameWires
                        (Region.adjoinHostWire outer firstLocals
                          secondLocals)).length) = [] := by
              simpa only [← hostMap] using secondEmpty
            rw [secondEmpty', List.append_nil] at combinedRoot
            simpa [hostWire, combinedIndex] using combinedRoot
          · have children :=
              (ItemSeq.childrenCanonical_append _ _).mp canonical.2 |>.1
            exact (ItemSeq.ChildrenCanonical.renameWires_adjoinHost_iff
              firstItems).mp children

end EqualityNormalization

end VisualProof.Rule.Completeness.Comprehension
