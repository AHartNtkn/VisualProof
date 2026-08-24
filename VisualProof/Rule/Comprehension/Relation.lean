import VisualProof.Diagram.Scope.Rename
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Comprehension

/-- Insert one relation wire between two local-context fragments. -/
def localRetain (before after : List Sig) (arguments : List Sig) :
    WireRenaming (before ++ after) (before ++ (.rel arguments :: after)) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (.rel arguments :: after))
    (fun wire => Var.appendRight before (.there wire))⟩

/-- Embed the retained outer and local wires into the quantified context. -/
def retain (outer before after : List Sig) (arguments : List Sig) :
    WireRenaming (outer ++ (before ++ after))
      (outer ++ (before ++ (.rel arguments :: after))) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (before ++ (.rel arguments :: after)))
    (fun wire => Var.appendRight outer
      (localRetain before after arguments wire))⟩

/-- The exact locally bound relation wire discharged by comprehension. -/
def selected (outer before after : List Sig) (arguments : List Sig) :
    Var (outer ++ (before ++ (.rel arguments :: after))) (.rel arguments) :=
  Var.appendRight outer (Var.appendRight before .here)

namespace Instantiation

def equalityPorts (left right : Var wires signature) :
    Fin 2 → Var wires signature :=
  Fin.cases left (fun _ => right)

def equalityItems : {signatures : List Sig} →
    Vars wires signatures → Vars wires signatures → ItemSeq wires
  | [], .nil, .nil => .nil
  | _ :: _, .cons left leftTail, .cons right rightTail =>
      .cons (.identity _ 2 (equalityPorts left right))
        (equalityItems leftTail rightTail)

theorem equalityItems_childrenCanonical
    (left right : Vars wires signatures) :
    (equalityItems left right).ChildrenCanonical := by
  induction left with
  | nil => cases right; trivial
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          exact ⟨True.intro, induction rightTail⟩

/-- The equality associated with any right-hand boundary position contributes
an incidence rooted at the current region. -/
theorem equalityItems_right_mem_nil
    (left right : Vars wires signatures)
    (position : Fin signatures.length) (itemIndex : Nat) :
    [] ∈ (equalityItems left right).incidencePaths
      (right.get position).index.val itemIndex := by
  induction left generalizing itemIndex with
  | nil => cases right; exact Fin.elim0 position
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          revert itemIndex
          refine Fin.cases (fun itemIndex => ?_)
            (fun rest itemIndex => ?_) position
          · change [] ∈
              (equalityItems (.cons leftHead leftTail)
                (.cons rightHead rightTail)).incidencePaths
                  rightHead.index.val itemIndex
            simp only [equalityItems, ItemSeq.incidencePaths,
              Item.incidencePaths, equalityPorts, List.mem_append,
              List.mem_replicate]
            apply Or.inl
            constructor
            · intro countZero
              have absent := List.count_eq_zero.mp countZero
              exact absent (by simp)
            · trivial
          · simp only [equalityItems, ItemSeq.incidencePaths,
              List.mem_append]
            exact Or.inr (induction rightTail rest (itemIndex + 1))

@[simp] theorem equalityItems_renameWires
    (left right : Vars source signatures)
    (rename : WireRenaming source target) :
    (equalityItems left right).renameWires rename =
      equalityItems (left.map fun wire => rename wire)
        (right.map fun wire => rename wire) := by
  induction left with
  | nil => cases right; rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [equalityItems, ItemSeq.renameWires, Item.renameWires,
            Vars.map]
          have portsEq :
              (fun index => rename (equalityPorts leftHead rightHead index)) =
                equalityPorts (rename leftHead) (rename rightHead) := by
            funext index
            exact Fin.cases rfl (fun _ => rfl) index
          rw [portsEq, induction rightTail]

/-- Equality-item presentations commute with a typed ambient wire
equivalence when both ordered port lists commute with that equivalence. -/
noncomputable def equalityItemsIso
    (ambient : WireEquiv source target)
    (sourceLeft sourceRight : Vars source signatures)
    (targetLeft targetRight : Vars target signatures)
    (leftEq : sourceLeft.map (fun wire => ambient wire) = targetLeft)
    (rightEq : sourceRight.map (fun wire => ambient wire) = targetRight) :
    ItemSeqIso ambient
      (equalityItems sourceLeft sourceRight)
      (equalityItems targetLeft targetRight) := by
  let renamed := ItemSeqIso.renameWires
    (equalityItems sourceLeft sourceRight)
    WireRenaming.id ambient.toRenaming ambient (fun _ => rfl)
  have sourceLeftEq :
      sourceLeft.map (fun wire => WireRenaming.id wire) = sourceLeft := by
    change sourceLeft.map (fun wire => wire) = sourceLeft
    exact vars_map_id sourceLeft
  have sourceRightEq :
      sourceRight.map (fun wire => WireRenaming.id wire) = sourceRight := by
    change sourceRight.map (fun wire => wire) = sourceRight
    exact vars_map_id sourceRight
  simpa only [ItemSeq.renameWires_id, equalityItems_renameWires,
    sourceLeftEq, sourceRightEq, leftEq, rightEq] using renamed

def Equalities : {signatures : List Sig} →
    Vars wires signatures → Vars wires signatures → Region wires
  | [], .nil, .nil => Region.blank wires
  | _ :: _, .cons left leftTail, .cons right rightTail =>
      (Region.singleton (.identity _ 2 (equalityPorts left right))).conjoin
        (Equalities leftTail rightTail)

theorem Equalities_eq_ofItems
    (left right : Vars wires signatures) :
    Equalities left right = Region.ofItems (equalityItems left right) := by
  induction left with
  | nil => cases right; rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [Equalities, equalityItems]
          rw [induction]
          change (Region.ofItems (.cons
            (.identity _ 2 (equalityPorts leftHead rightHead)) .nil)).conjoin
              (Region.ofItems (equalityItems leftTail rightTail)) = _
          rw [Region.ofItems_conjoin]
          rfl

/-- Instantiate an open pattern by binding its external wires locally and
equating its ordered boundary to the actual application ports. -/
def instantiate (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) : Region targetWires :=
  Region.adjoinAt pattern.external .nil
    ((pattern.body.renameWires
      ⟨fun wire => Var.appendRight targetWires wire⟩).conjoin
      (Equalities
        (ports.map fun wire => wire.appendLeft pattern.external)
        (pattern.boundaryWire.map
          fun wire => Var.appendRight targetWires wire)))

private theorem Vars.get_map
    (variables : Vars source signatures)
    (rename : ∀ {signature}, Var source signature → Var target signature)
    (position : Fin signatures.length) :
    (variables.map rename).get position = rename (variables.get position) := by
  induction variables with
  | nil => exact Fin.elim0 position
  | cons head tail induction =>
      exact Fin.cases rfl (fun rest => induction rest) position

private theorem Vars.countIndex_appendLeft_zero
    (variables : Vars source signatures) (added : List Sig)
    (index : Nat) (beyond : source.length ≤ index) :
    (variables.map fun wire => wire.appendLeft added).countIndex index = 0 := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      have different : head.index.val ≠ index := by
        have bound := head.index.isLt
        omega
      simp only [Vars.map, Vars.countIndex, Var.index_appendLeft]
      rw [if_neg different, induction]

private theorem Vars.countIndex_appendRight
    (variables : Vars source signatures) (addedBefore : List Sig)
    (index : Nat) :
    (variables.map fun wire => Var.appendRight addedBefore wire).countIndex
        (addedBefore.length + index) =
      variables.countIndex index := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.map, Vars.countIndex, Var.index_appendRight]
      split <;> rename_i equality
      · have sourceEquality : head.index.val = index := by omega
        simp [sourceEquality, induction]
      · have sourceDifferent : head.index.val ≠ index := by
          intro sourceEquality
          exact equality (by omega)
        simp [sourceDifferent, induction]

theorem equalityItems_incidencePaths_length
    (left right : Vars wires signatures)
    (wireIndex itemIndex : Nat) :
    ((VisualProof.Rule.Comprehension.Instantiation.equalityItems
      left right).incidencePaths wireIndex itemIndex).length =
      left.countIndex wireIndex + right.countIndex wireIndex := by
  induction left generalizing itemIndex with
  | nil => cases right; rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [
            VisualProof.Rule.Comprehension.Instantiation.equalityItems,
            ItemSeq.incidencePaths, Item.incidencePaths,
            VisualProof.Rule.Comprehension.Instantiation.equalityPorts,
            Vars.countIndex, List.length_append, List.length_replicate]
          rw [induction rightTail]
          by_cases leftEqual : leftHead.index.val = wireIndex <;>
            by_cases rightEqual : rightHead.index.val = wireIndex <;>
            simp [List.ofFn_succ, List.ofFn_zero, leftEqual, rightEqual] <;>
            omega

/-- Instantiation is canonical for every valid open pattern and every actual
port vector. The bound pattern externals are rooted by the exact equality
block together with the pattern's external-two-ended invariant. -/
theorem instantiate_canonical
    (pattern : OpenDiagram arguments)
    (ports : Vars targetWires arguments) :
    (instantiate
      pattern ports).Canonical := by
  let embed : WireRenaming pattern.external
      (targetWires ++ pattern.external) :=
    ⟨fun wire => Var.appendRight targetWires wire⟩
  let body := pattern.body.renameWires embed
  let left := ports.map (fun wire => wire.appendLeft pattern.external)
  let right := pattern.boundaryWire.map
    (fun wire => Var.appendRight targetWires wire)
  let equalityItems :=
    equalityItems left right
  have bodyCanonical : body.Canonical :=
    (Region.Canonical.renameWires_iff pattern.body embed).mpr
      pattern.canonical
  have equalityChildren : equalityItems.ChildrenCanonical :=
    equalityItems_childrenCanonical
      left right
  have joinedCanonical :
      (body.conjoin (Region.ofItems equalityItems)).Canonical :=
    Region.Canonical.conjoinRightItems body equalityItems bodyCanonical
      equalityChildren
  unfold instantiate
  rw [Equalities_eq_ofItems]
  change (Region.adjoinAt pattern.external .nil
    (body.conjoin (Region.ofItems equalityItems))).Canonical
  apply Region.Canonical.adjoinAt_of_material_roots pattern.external .nil
    (body.conjoin (Region.ofItems equalityItems)) True.intro joinedCanonical
  intro externalIndex
  let external := Var.ofIndex externalIndex
  let embedded := Var.appendRight targetWires external
  have embeddedIndex : embedded.index.val =
      targetWires.length + externalIndex.val := by
    simp [embedded, external]
  cases bodyEq : pattern.body with
  | mk bodyLocals bodyItems =>
      let firstItems :=
        (bodyItems.renameWires (embed.appendRight bodyLocals)).renameWires
        (Region.conjoinLeftWire (targetWires ++ pattern.external)
          bodyLocals [])
      let appendNil : WireRenaming (targetWires ++ pattern.external)
          ((targetWires ++ pattern.external) ++ []) :=
        ⟨fun wire => wire.appendLeft []⟩
      let rightItems := (equalityItems.renameWires appendNil).renameWires
        (Region.conjoinRightWire (targetWires ++ pattern.external)
          bodyLocals [])
      rw [← embeddedIndex]
      simp only [body, bodyEq, Region.renameWires]
      simp only [Region.conjoin, Region.ofItems, Region.incidencePaths]
      change RegionPath.RootedTwo
        ((firstItems.append rightItems).incidencePaths
          embedded.index.val 0)
      rw [ItemSeq.incidencePaths_append]
      simp only [Nat.zero_add]
      have bodyPathsEq :
          (bodyItems.renameWires
            (embed.appendRight bodyLocals)).incidencePaths
              embedded.index.val 0 =
            bodyItems.incidencePaths external.index.val 0 := by
        apply ItemSeq.incidencePaths_renameWires_of_index_iff
        · have bound := external.index.isLt
          simp only [List.length_append]
          omega
        · have bound := embedded.index.isLt
          simp only [List.length_append]
          omega
        · intro signature wire
          apply Var.appendCases (left := pattern.external)
            (right := bodyLocals)
            (motive := fun wire =>
              ((embed.appendRight bodyLocals) wire).index.val =
                    embedded.index.val ↔
                wire.index.val = external.index.val)
          · intro inheritedSignature inherited
            simp only [WireRenaming.appendRight, Var.appendMap_left,
              Var.index_appendLeft, embed, Var.index_appendRight,
              embedded, external]
            omega
          · intro localSignature localWire
            have externalBound := external.index.isLt
            have localBound := localWire.index.isLt
            simp only [WireRenaming.appendRight, Var.appendMap_right,
              Var.index_appendRight]
            omega
      have firstPathsEq :
          firstItems.incidencePaths embedded.index.val 0 =
            (bodyItems.renameWires
              (embed.appendRight bodyLocals)).incidencePaths
                embedded.index.val 0 := by
        have renamed := ItemSeq.incidencePaths_renameWires_adjoinHost
          (addedLocals := [])
          (bodyItems.renameWires (embed.appendRight bodyLocals))
          (embedded.appendLeft bodyLocals) 0
        simpa [firstItems, Region.adjoinHostWire] using renamed
      obtain ⟨boundaryPosition, boundaryMaps⟩ :=
        pattern.boundarySurjective externalIndex
      have rightGetIndex : (right.get boundaryPosition).index.val =
          embedded.index.val := by
        simp [right, Vars.get_map, embedded, external, boundaryMaps]
      have baseRightMem :=
        equalityItems_right_mem_nil
          left right boundaryPosition firstItems.length
      rw [rightGetIndex] at baseRightMem
      have rightPathsEq :
          rightItems.incidencePaths embedded.index.val firstItems.length =
            equalityItems.incidencePaths embedded.index.val
              firstItems.length := by
        simp only [rightItems, ItemSeq.renameWires_comp]
        apply ItemSeq.incidencePaths_renameWires_of_index_iff
        · exact embedded.index.isLt
        · simpa [body, Region.locals] using
            (embedded.appendLeft bodyLocals).index.isLt
        · intro signature wire
          simp [WireRenaming.comp, appendNil, Region.conjoinRightWire]
      have rightMem : [] ∈
          rightItems.incidencePaths embedded.index.val firstItems.length := by
        rw [rightPathsEq]
        exact baseRightMem
      constructor
      · simp only [List.length_append]
        rw [firstPathsEq, bodyPathsEq, rightPathsEq,
          equalityItems_incidencePaths_length]
        have leftZero : left.countIndex embedded.index.val = 0 := by
          simp only [left, embeddedIndex]
          exact Vars.countIndex_appendLeft_zero ports pattern.external
            (targetWires.length + externalIndex.val) (by omega)
        have rightCount : right.countIndex embedded.index.val =
            pattern.boundaryWire.countIndex external.index.val := by
          simp only [right, embeddedIndex, external]
          simpa [external] using
            Vars.countIndex_appendRight pattern.boundaryWire targetWires
              externalIndex.val
        rw [leftZero, rightCount]
        have twoEnded :
            2 ≤ pattern.boundaryWire.countIndex external.index.val +
              (bodyItems.incidencePaths external.index.val 0).length := by
          have valid := pattern.externalTwoEnded external
          rw [bodyEq] at valid
          simpa only [Region.incidencePaths] using valid
        omega
      · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
        exact List.mem_append_right _ rightMem

mutual
  /-- Recursive instantiation under cuts. The selected relation remains an
  inherited wire; locally bound wires are retained exactly. -/
  inductive RegionResult (pattern : OpenDiagram arguments) :
      {sourceWires targetWires : List Sig} →
      WireRenaming targetWires sourceWires →
      Var sourceWires (.rel arguments) →
      Region sourceWires → Region targetWires → Prop
    | mk
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        {locals : List Sig}
        {items : ItemSeq (sourceWires ++ locals)}
        {result : Region (targetWires ++ locals)}
        (itemsResult : ItemsResult pattern (retain.appendRight locals)
          (selected.appendLeft locals) items result) :
        RegionResult pattern retain selected (.mk locals items)
          (Region.adjoinAt locals .nil result)

  /-- An item sequence becomes a conjunction of its instantiated item
  regions. This is structural proof evidence, not a second syntax. -/
  inductive ItemsResult (pattern : OpenDiagram arguments) :
      {sourceWires targetWires : List Sig} →
      WireRenaming targetWires sourceWires →
      Var sourceWires (.rel arguments) →
      ItemSeq sourceWires → Region targetWires → Prop
    | nil
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)} :
        ItemsResult pattern retain selected .nil (Region.blank targetWires)
    | cons
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        {item : Item sourceWires} {tail : ItemSeq sourceWires}
        {itemResult tailResult : Region targetWires}
        (itemEvidence : ItemResult pattern retain selected item itemResult)
        (tailEvidence : ItemsResult pattern retain selected tail tailResult) :
        ItemsResult pattern retain selected (.cons item tail)
          (itemResult.conjoin tailResult)

  /-- One source item either uses only retained wires, expands an application
  headed by the selected relation wire, or recursively instantiates a cut. -/
  inductive ItemResult (pattern : OpenDiagram arguments) :
      {sourceWires targetWires : List Sig} →
      WireRenaming targetWires sourceWires →
      Var sourceWires (.rel arguments) →
      Item sourceWires → Region targetWires → Prop
    | atom
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        (head : Var targetWires (.rel atomArguments))
        (ports : Vars targetWires atomArguments) :
        ItemResult pattern retain selected
          (.atom (retain head) (ports.map (fun wire => retain wire)))
          (Region.singleton (.atom head ports))
    | selectedAtom
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        (ports : Vars targetWires arguments) :
        ItemResult pattern retain selected
          (.atom selected (ports.map (fun wire => retain wire)))
          (instantiate pattern ports)
    | identity
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var targetWires signature) :
        ItemResult pattern retain selected
          (.identity signature arity (fun index => retain (ports index)))
          (Region.singleton (.identity signature arity ports))
    | cut
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        {body : Region sourceWires} {result : Region targetWires}
        (bodyEvidence : RegionResult pattern retain selected body result) :
        ItemResult pattern retain selected (.cut body)
          (Region.singleton (.cut result))
end

end Instantiation

/-- Exact structural evidence that removes one locally bound relation wire and
instantiates every application headed by it with the supplied open pattern. -/
inductive Instantiates
    (pattern : OpenDiagram arguments) (before after : List Sig) :
    Region outer → Region outer → Prop
  | mk
      {items : ItemSeq
        (outer ++ (before ++ (.rel arguments :: after)))}
      {result : Region (outer ++ (before ++ after))}
      (itemsResult : Instantiation.ItemsResult pattern
        (retain outer before after arguments)
        (selected outer before after arguments) items result) :
      Instantiates pattern before after
        (.mk (before ++ (.rel arguments :: after)) items)
        (Region.adjoinAt (before ++ after) .nil result)

/-- Positive comprehension generalizes a specialized region by one local
relation wire. Context polarity supplies the contravariant direction. -/
inductive Local : LocalRule
  | comprehend
      (arguments before after : List Sig)
      (pattern : OpenDiagram arguments)
      {quantified specialized : Region wires}
      (instantiates : Instantiates pattern before after quantified specialized) :
      Local specialized quantified

end Comprehension

def Comprehension : Rule :=
  Contextual fun specialized quantified =>
    Comprehension.Local specialized quantified

theorem Comprehension.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Comprehension source target)
    (targetIso : OpenDiagramIso target target') :
    Comprehension source' target' := by
  exact Contextual.iso sourceIso step targetIso

end VisualProof.Rule
