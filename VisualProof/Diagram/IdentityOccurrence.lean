import VisualProof.Diagram.Algebra
import VisualProof.Diagram.Scope

namespace VisualProof.Diagram

open VisualProof.Theory

/-- A wire of a region, resolved into the existing recursive syntax. -/
inductive Region.Wire (region : Region outer) : Type
  | inherited (wire : Var outer signature) : Region.Wire region
  | internal (wire : Region.InternalWire region signature) : Region.Wire region

def Region.Wire.signature : {region : Region outer} →
    Region.Wire region → Sig
  | _, .inherited (signature := signature) _ => signature
  | _, .internal (signature := signature) _ => signature

/-- A wire visible to an item sequence, or owned below one of its cuts. -/
inductive ItemSeq.Wire (items : ItemSeq wires) : Type
  | inherited (wire : Var wires signature) : ItemSeq.Wire items
  | internal (wire : ItemSeq.InternalWire items signature) : ItemSeq.Wire items

mutual
  /-- One actual identity node in a recursive region. -/
  inductive Region.IdentityOccurrence : Region outer → Type
    | item {locals : List Sig} {items : ItemSeq (outer ++ locals)}
        (node : ItemSeq.IdentityOccurrence items) :
        Region.IdentityOccurrence (.mk locals items)

  /-- One actual identity node in a recursive item sequence. -/
  inductive ItemSeq.IdentityOccurrence : ItemSeq wires → Type
    | head : ItemSeq.IdentityOccurrence
        (.cons (.identity signature arity ports) tail)
    | headCut (node : Region.IdentityOccurrence body) :
        ItemSeq.IdentityOccurrence (.cons (.cut body) tail)
    | tail (node : ItemSeq.IdentityOccurrence tail) :
        ItemSeq.IdentityOccurrence (.cons item tail)
end

mutual
  /-- Enumerate the actual identity occurrences of a recursive region. -/
  def Region.identityOccurrences :
      (region : Region outer) → List (Region.IdentityOccurrence region)
    | .mk _ items => items.identityOccurrences.map .item

  /-- Enumerate the actual identity occurrences of a recursive item sequence. -/
  def ItemSeq.identityOccurrences :
      (items : ItemSeq wires) → List (ItemSeq.IdentityOccurrence items)
    | .nil => []
    | .cons (.atom _ _) tail => tail.identityOccurrences.map .tail
    | .cons (.identity _ _ _) tail =>
        .head :: tail.identityOccurrences.map .tail
    | .cons (.cut body) tail =>
        body.identityOccurrences.map .headCut ++
          tail.identityOccurrences.map .tail
end

private abbrev RegionIdentityMemMotive
    (region : Region outer) (node : Region.IdentityOccurrence region) :=
  node ∈ region.identityOccurrences

private abbrev ItemsIdentityMemMotive
    (items : ItemSeq wires) (node : ItemSeq.IdentityOccurrence items) :=
  node ∈ items.identityOccurrences

private theorem identityMemItem
    {outer locals : List Sig} {items : ItemSeq (outer ++ locals)}
    (node : ItemSeq.IdentityOccurrence items)
    (induction : ItemsIdentityMemMotive items node) :
    RegionIdentityMemMotive (.mk locals items) (.item node) := by
  simp only [RegionIdentityMemMotive, Region.identityOccurrences, List.mem_map]
  exact ⟨node, induction, rfl⟩

private theorem identityMemHead :
    ItemsIdentityMemMotive
      (.cons (.identity signature arity ports) tail) .head := by
  simp [ItemsIdentityMemMotive, ItemSeq.identityOccurrences]

private theorem identityMemHeadCut
    (node : Region.IdentityOccurrence body)
    (induction : RegionIdentityMemMotive body node) :
    ItemsIdentityMemMotive (.cons (.cut body) tail) (.headCut node) := by
  simp only [ItemsIdentityMemMotive, ItemSeq.identityOccurrences,
    List.mem_append, List.mem_map]
  exact Or.inl ⟨node, induction, rfl⟩

private theorem identityMemTail
    (node : ItemSeq.IdentityOccurrence tail)
    (induction : ItemsIdentityMemMotive tail node) :
    ItemsIdentityMemMotive (.cons item tail) (.tail node) := by
  cases item with
  | atom head ports =>
      simp only [ItemsIdentityMemMotive, ItemSeq.identityOccurrences,
        List.mem_map]
      exact ⟨node, induction, rfl⟩
  | identity signature arity ports =>
      simp only [ItemsIdentityMemMotive, ItemSeq.identityOccurrences,
        List.mem_cons, List.mem_map]
      exact Or.inr ⟨node, induction, rfl⟩
  | cut body =>
      simp only [ItemsIdentityMemMotive, ItemSeq.identityOccurrences,
        List.mem_append, List.mem_map]
      exact Or.inr ⟨node, induction, rfl⟩

theorem Region.mem_identityOccurrences
    (node : Region.IdentityOccurrence region) :
    node ∈ region.identityOccurrences :=
  Region.IdentityOccurrence.rec identityMemItem identityMemHead
    identityMemHeadCut identityMemTail node

theorem ItemSeq.mem_identityOccurrences
    (node : ItemSeq.IdentityOccurrence items) :
    node ∈ items.identityOccurrences :=
  ItemSeq.IdentityOccurrence.rec identityMemItem identityMemHead
    identityMemHeadCut identityMemTail node

/-- Focus the root item containing an identity occurrence. For a nested
occurrence this selects the containing cut; recursing on the occurrence selects
the exact identity at its owner. -/
def ItemSeq.IdentityOccurrence.focus :
    {items : ItemSeq wires} → ItemSeq.IdentityOccurrence items →
      ItemSeq.Focus items
  | _, .head => {
      before := .nil
      item := .identity _ _ _
      after := _
      rebuild := rfl
    }
  | _, .headCut _ => {
      before := .nil
      item := .cut _
      after := _
      rebuild := rfl
    }
  | _, .tail node =>
      let nested := node.focus
      {
        before := .cons _ nested.before
        item := nested.item
        after := nested.after
        rebuild := by
          simp only [ItemSeq.append]
          rw [nested.rebuild]
      }

mutual
  def Region.IdentityOccurrence.signature :
      {region : Region outer} → Region.IdentityOccurrence region → Sig
    | _, .item node => node.signature

  def ItemSeq.IdentityOccurrence.signature :
      {items : ItemSeq wires} → ItemSeq.IdentityOccurrence items → Sig
    | _, @ItemSeq.IdentityOccurrence.head _ signature _ _ _ => signature
    | _, .headCut node => node.signature
    | _, .tail node => node.signature
end

mutual
  def Region.IdentityOccurrence.path :
      {region : Region outer} → Region.IdentityOccurrence region → RegionPath
    | _, .item node => node.pathFrom 0

  def ItemSeq.IdentityOccurrence.pathFrom :
      {items : ItemSeq wires} → ItemSeq.IdentityOccurrence items →
        Nat → RegionPath
    | _, .head, _ => []
    | _, .headCut node, index => index :: node.path
    | _, .tail node, index => node.pathFrom (index + 1)
end

mutual
  /-- One actual port of an identity node in a recursive region. -/
  inductive Region.IdentityPortOccurrence : Region outer → Type
    | item {locals : List Sig} {items : ItemSeq (outer ++ locals)}
        (port : ItemSeq.IdentityPortOccurrence items) :
        Region.IdentityPortOccurrence (.mk locals items)

  /-- One actual port of an identity node in a recursive item sequence. -/
  inductive ItemSeq.IdentityPortOccurrence : ItemSeq wires → Type
    | head (port : Fin arity) : ItemSeq.IdentityPortOccurrence
        (.cons (.identity signature arity ports) tail)
    | headCut (port : Region.IdentityPortOccurrence body) :
        ItemSeq.IdentityPortOccurrence (.cons (.cut body) tail)
    | tail (port : ItemSeq.IdentityPortOccurrence tail) :
        ItemSeq.IdentityPortOccurrence (.cons item tail)
end

mutual
  /-- Enumerate the actual identity ports of a recursive region. -/
  def Region.identityPortOccurrences :
      (region : Region outer) → List (Region.IdentityPortOccurrence region)
    | .mk _ items => items.identityPortOccurrences.map .item

  /-- Enumerate the actual identity ports of a recursive item sequence. -/
  def ItemSeq.identityPortOccurrences :
      (items : ItemSeq wires) → List (ItemSeq.IdentityPortOccurrence items)
    | .nil => []
    | .cons (.atom _ _) tail => tail.identityPortOccurrences.map .tail
    | .cons (.identity _ arity _) tail =>
        (VisualProof.Data.Finite.allFin arity).map .head ++
          tail.identityPortOccurrences.map .tail
    | .cons (.cut body) tail =>
        body.identityPortOccurrences.map .headCut ++
          tail.identityPortOccurrences.map .tail
end

private abbrev RegionIdentityPortMemMotive
    (region : Region outer) (port : Region.IdentityPortOccurrence region) :=
  port ∈ region.identityPortOccurrences

private abbrev ItemsIdentityPortMemMotive
    (items : ItemSeq wires) (port : ItemSeq.IdentityPortOccurrence items) :=
  port ∈ items.identityPortOccurrences

private theorem identityPortMemItem
    {outer locals : List Sig} {items : ItemSeq (outer ++ locals)}
    (port : ItemSeq.IdentityPortOccurrence items)
    (induction : ItemsIdentityPortMemMotive items port) :
    RegionIdentityPortMemMotive (.mk locals items) (.item port) := by
  simp only [RegionIdentityPortMemMotive, Region.identityPortOccurrences,
    List.mem_map]
  exact ⟨port, induction, rfl⟩

private theorem identityPortMemHead (port : Fin arity) :
    ItemsIdentityPortMemMotive
      (.cons (.identity signature arity ports) tail) (.head port) := by
  simp only [ItemsIdentityPortMemMotive, ItemSeq.identityPortOccurrences,
    List.mem_append, List.mem_map]
  exact Or.inl ⟨port, VisualProof.Data.Finite.mem_allFin port, rfl⟩

private theorem identityPortMemHeadCut
    (port : Region.IdentityPortOccurrence body)
    (induction : RegionIdentityPortMemMotive body port) :
    ItemsIdentityPortMemMotive (.cons (.cut body) tail) (.headCut port) := by
  simp only [ItemsIdentityPortMemMotive, ItemSeq.identityPortOccurrences,
    List.mem_append, List.mem_map]
  exact Or.inl ⟨port, induction, rfl⟩

private theorem identityPortMemTail
    (port : ItemSeq.IdentityPortOccurrence tail)
    (induction : ItemsIdentityPortMemMotive tail port) :
    ItemsIdentityPortMemMotive (.cons item tail) (.tail port) := by
  cases item with
  | atom head ports =>
      simp only [ItemsIdentityPortMemMotive, ItemSeq.identityPortOccurrences,
        List.mem_map]
      exact ⟨port, induction, rfl⟩
  | identity signature arity ports =>
      simp only [ItemsIdentityPortMemMotive, ItemSeq.identityPortOccurrences,
        List.mem_append, List.mem_map]
      exact Or.inr ⟨port, induction, rfl⟩
  | cut body =>
      simp only [ItemsIdentityPortMemMotive, ItemSeq.identityPortOccurrences,
        List.mem_append, List.mem_map]
      exact Or.inr ⟨port, induction, rfl⟩

theorem Region.mem_identityPortOccurrences
    (port : Region.IdentityPortOccurrence region) :
    port ∈ region.identityPortOccurrences :=
  Region.IdentityPortOccurrence.rec identityPortMemItem identityPortMemHead
    identityPortMemHeadCut identityPortMemTail port

theorem ItemSeq.mem_identityPortOccurrences
    (port : ItemSeq.IdentityPortOccurrence items) :
    port ∈ items.identityPortOccurrences :=
  ItemSeq.IdentityPortOccurrence.rec identityPortMemItem identityPortMemHead
    identityPortMemHeadCut identityPortMemTail port

mutual
  def Region.IdentityPortOccurrence.node : {region : Region outer} →
      Region.IdentityPortOccurrence region → Region.IdentityOccurrence region
    | _, .item port => .item port.node

  def ItemSeq.IdentityPortOccurrence.node : {items : ItemSeq wires} →
      ItemSeq.IdentityPortOccurrence items → ItemSeq.IdentityOccurrence items
    | _, .head _ => .head
    | _, .headCut port => .headCut port.node
    | _, .tail port => .tail port.node
end

private def splitAppend : Var (left ++ right) signature →
    Var left signature ⊕ Var right signature :=
  match left with
  | [] => fun wire => .inr wire
  | _ :: rest => fun wire =>
      match wire with
      | .here => .inl .here
      | .there tail =>
          match splitAppend (left := rest) tail with
          | .inl inherited => .inl (.there inherited)
          | .inr localWire => .inr localWire

mutual
  def Region.IdentityPortOccurrence.wire : {region : Region outer} →
      Region.IdentityPortOccurrence region → Region.Wire region
    | _, @Region.IdentityPortOccurrence.item outer locals items port =>
        match port.wire with
        | .inherited wire =>
            match splitAppend (left := outer) (right := locals) wire with
            | .inl inherited => .inherited inherited
            | .inr localWire => .internal (.here localWire)
        | .internal wire => .internal (.nested wire)

  def ItemSeq.IdentityPortOccurrence.wire : {items : ItemSeq wires} →
      ItemSeq.IdentityPortOccurrence items → ItemSeq.Wire items
    | _, @ItemSeq.IdentityPortOccurrence.head _ _ _ ports _ index =>
        .inherited (ports index)
    | _, .headCut port =>
        match port.wire with
        | .inherited wire => .inherited wire
        | .internal wire => .internal (.headCut wire)
    | _, .tail port =>
        match port.wire with
        | .inherited wire => .inherited wire
        | .internal wire => .internal (.tail wire)
end

end VisualProof.Diagram
