import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

open VisualProof
open Theory

variable {locals : List Sig}

/-! Structural port labels indexed by their exact typed source wire. A port
partition chooses a wire in the corresponding fiber of one collapse. -/

mutual
  inductive Region.Port :
      {outer : List Sig} → (region : Region outer) →
      ∀ {signature}, Var outer signature → Type
    | item {outer locals : List Sig}
        {items : ItemSeq (outer ++ locals)}
        {signature : Sig} {wire : Var outer signature}
        (port : ItemSeq.Port items (wire.appendLeft locals)) :
        Region.Port (.mk locals items) wire

  inductive Item.Port :
      {wires : List Sig} → (item : Item wires) →
      ∀ {signature}, Var wires signature → Type
    | atomHead {wires arguments : List Sig}
        {head : Var wires (.rel arguments)} {ports : Vars wires arguments} :
        Item.Port (.atom head ports) head
    | atomArgument {wires arguments : List Sig}
        {head : Var wires (.rel arguments)} {ports : Vars wires arguments}
        (argument : Fin arguments.length) :
        Item.Port (.atom head ports) (ports.get argument)
    | identity {wires : List Sig} {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var wires signature} (argument : Fin arity) :
        Item.Port (.identity signature arity ports) (ports argument)
    | cut {wires : List Sig} {body : Region wires}
        {signature : Sig} {wire : Var wires signature}
        (port : Region.Port body wire) : Item.Port (.cut body) wire

  inductive ItemSeq.Port :
      {wires : List Sig} → (items : ItemSeq wires) →
      ∀ {signature}, Var wires signature → Type
    | head {wires : List Sig} {item : Item wires} {tail : ItemSeq wires}
        {signature : Sig} {wire : Var wires signature}
        (port : Item.Port item wire) :
        ItemSeq.Port (.cons item tail) wire
    | tail {wires : List Sig} {item : Item wires} {tail : ItemSeq wires}
        {signature : Sig} {wire : Var wires signature}
        (port : ItemSeq.Port tail wire) :
        ItemSeq.Port (.cons item tail) wire
end

structure Region.PortPartition
    (collapse : WireRenaming target source) (region : Region source) where
  output : ∀ {signature} (wire : Var source signature),
    Region.Port region wire →
      { result : Var target signature // collapse result = wire }

structure Item.PortPartition
    (collapse : WireRenaming target source) (item : Item source) where
  output : ∀ {signature} (wire : Var source signature),
    Item.Port item wire →
      { result : Var target signature // collapse result = wire }

structure ItemSeq.PortPartition
    (collapse : WireRenaming target source) (items : ItemSeq source) where
  output : ∀ {signature} (wire : Var source signature),
    ItemSeq.Port items wire →
      { result : Var target signature // collapse result = wire }

private inductive AppendView (left right : List Sig) :
    {signature : Sig} → Var (left ++ right) signature → Type
  | fromLeft (wire : Var left signature) :
      AppendView left right (wire.appendLeft right)
  | fromRight (wire : Var right signature) :
      AppendView left right (Var.appendRight left wire)

private def appendView (left right : List Sig) :
    {signature : Sig} → (wire : Var (left ++ right) signature) →
      AppendView left right wire :=
  match left with
  | [] => fun wire => .fromRight wire
  | _ :: tail => fun wire =>
      match wire with
      | .here => .fromLeft .here
      | .there rest =>
          match appendView tail right rest with
          | .fromLeft inherited => .fromLeft (.there inherited)
          | .fromRight localWire => .fromRight localWire

private def Var.appendElim
    (motive : ∀ {signature}, Var (left ++ right) signature → Sort u)
    (leftCase : ∀ {signature} (wire : Var left signature),
      motive (wire.appendLeft right))
    (rightCase : ∀ {signature} (wire : Var right signature),
      motive (Var.appendRight left wire)) :
    ∀ {signature} (wire : Var (left ++ right) signature), motive wire :=
  match left with
  | [] => rightCase
  | _ :: _ => fun wire =>
      match wire with
      | .here => leftCase .here
      | .there rest =>
          Var.appendElim
            (motive := fun wire => motive (.there wire))
            (leftCase := fun wire => leftCase (.there wire))
            (rightCase := rightCase) rest

@[simp] private theorem Var.appendElim_left
    (motive : ∀ {signature}, Var (left ++ right) signature → Sort u)
    (leftCase : ∀ {signature} (wire : Var left signature),
      motive (wire.appendLeft right))
    (rightCase : ∀ {signature} (wire : Var right signature),
      motive (Var.appendRight left wire))
    (wire : Var left signature) :
    Var.appendElim motive leftCase rightCase (wire.appendLeft right) =
      leftCase wire := by
  induction wire with
  | here => rfl
  | there wire induction =>
      exact induction
        (motive := fun wire => motive (.there wire))
        (leftCase := fun wire => leftCase (.there wire))
        (rightCase := rightCase)

@[simp] private theorem Var.appendElim_right
    (motive : ∀ {signature}, Var (left ++ right) signature → Sort u)
    (leftCase : ∀ {signature} (wire : Var left signature),
      motive (wire.appendLeft right))
    (rightCase : ∀ {signature} (wire : Var right signature),
      motive (Var.appendRight left wire))
    (wire : Var right signature) :
    Var.appendElim motive leftCase rightCase (Var.appendRight left wire) =
      rightCase wire := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      exact induction
        (motive := fun wire => motive (.there wire))
        (leftCase := fun wire => leftCase (.there wire))
        (rightCase := rightCase)

private def Region.itemPartition
    {collapse : WireRenaming target source}
    {items : ItemSeq (source ++ locals)}
    (partition : Region.PortPartition collapse (.mk locals items)) :
    ItemSeq.PortPartition (collapse.appendRight locals) items where
  output := fun wire port =>
    Var.appendElim
      (motive := fun wire => ItemSeq.Port items wire →
        { result : Var (target ++ locals) _ //
          collapse.appendRight locals result = wire })
      (fun inherited inheritedPort =>
        let result := partition.output inherited (.item inheritedPort)
        ⟨result.val.appendLeft locals, by
          simp [WireRenaming.appendRight, result.property]⟩)
      (fun localWire _ =>
        ⟨Var.appendRight target localWire, by
          simp [WireRenaming.appendRight]⟩)
      wire port

def Vars.partitionOutput
    (collapse : WireRenaming target source) :
    (variables : Vars source signatures) →
    (∀ argument : Fin signatures.length,
      { result : Var target (signatures.get argument) //
        collapse result = variables.get argument }) →
    Vars target signatures
  | .nil, _ => .nil
  | .cons _ tail, partition =>
      .cons (partition 0).val
        (Vars.partitionOutput collapse tail fun argument =>
          partition argument.succ)

mutual
  def Region.partitionOutput
      (collapse : WireRenaming target source) :
      (region : Region source) →
        Region.PortPartition collapse region → Region target
    | .mk locals items, partition =>
        .mk locals (ItemSeq.partitionOutput (collapse.appendRight locals)
          items (Region.itemPartition partition))

  def Item.partitionOutput
      (collapse : WireRenaming target source) :
      (item : Item source) →
        Item.PortPartition collapse item → Item target
    | .atom head ports, partition =>
        .atom (partition.output head .atomHead).val
          (Vars.partitionOutput collapse ports fun argument =>
            partition.output (ports.get argument) (.atomArgument argument))
    | .identity signature arity ports, partition =>
        .identity signature arity fun argument =>
          (partition.output (ports argument) (.identity argument)).val
    | .cut body, partition =>
        .cut (Region.partitionOutput collapse body {
          output := fun wire port => partition.output wire (.cut port) })

  def ItemSeq.partitionOutput
      (collapse : WireRenaming target source) :
      (items : ItemSeq source) →
        ItemSeq.PortPartition collapse items → ItemSeq target
    | .nil, _ => .nil
    | .cons head tail, partition =>
        .cons
          (Item.partitionOutput collapse head {
            output := fun wire port => partition.output wire (.head port) })
          (ItemSeq.partitionOutput collapse tail {
            output := fun wire port => partition.output wire (.tail port) })

end

private theorem Vars.partitionOutput_map
    (collapse : WireRenaming target source)
    (variables : Vars source signatures)
    (partition : ∀ argument : Fin signatures.length,
      { result : Var target (signatures.get argument) //
        collapse result = variables.get argument }) :
    (Vars.partitionOutput collapse variables partition).map
        (fun wire => collapse wire) = variables := by
  induction signatures with
  | nil => cases variables; rfl
  | cons signature rest induction =>
      cases variables with
      | cons head tail =>
          simp only [Vars.partitionOutput, Vars.map]
          have headProperty : collapse (partition 0).val = head := by
            simpa only [Vars.get] using (partition 0).property
          calc
            _ = Vars.cons head
                ((Vars.partitionOutput collapse tail fun argument =>
                  partition argument.succ).map fun wire => collapse wire) :=
              congrArg (fun wire => Vars.cons wire _) headProperty
            _ = Vars.cons head tail := congrArg (Vars.cons head)
              (induction tail (fun argument => partition argument.succ))

mutual
  theorem Region.partitionOutput_renameWires
      (collapse : WireRenaming target source) (region : Region source)
      (partition : Region.PortPartition collapse region) :
      (region.partitionOutput collapse partition).renameWires collapse =
        region := by
    cases region with
    | mk locals items =>
        simp only [Region.partitionOutput, Region.renameWires]
        rw [ItemSeq.partitionOutput_renameWires]

  theorem Item.partitionOutput_renameWires
      (collapse : WireRenaming target source) (item : Item source)
      (partition : Item.PortPartition collapse item) :
      (item.partitionOutput collapse partition).renameWires collapse = item := by
    cases item with
    | atom head ports =>
        simp only [Item.partitionOutput, Item.renameWires]
        rw [(partition.output head .atomHead).property,
          Vars.partitionOutput_map collapse ports]
    | identity signature arity ports =>
        simp only [Item.partitionOutput, Item.renameWires]
        apply congrArg (Item.identity signature arity)
        funext argument
        exact (partition.output (ports argument) (.identity argument)).property
    | cut body =>
        simp only [Item.partitionOutput, Item.renameWires]
        rw [Region.partitionOutput_renameWires]

  theorem ItemSeq.partitionOutput_renameWires
      (collapse : WireRenaming target source) (items : ItemSeq source)
      (partition : ItemSeq.PortPartition collapse items) :
      (items.partitionOutput collapse partition).renameWires collapse =
        items := by
    cases items with
    | nil => cases partition; rfl
    | cons head tail =>
        simp only [ItemSeq.partitionOutput, ItemSeq.renameWires]
        rw [Item.partitionOutput_renameWires,
          ItemSeq.partitionOutput_renameWires]
end

private theorem Var.appendLeft_injective
    (suffix : List Sig) {first second : Var source signature}
    (equality : first.appendLeft suffix = second.appendLeft suffix) :
    first = second := by
  induction first with
  | here =>
      cases second with
      | here => rfl
      | there tail => cases equality
  | there first induction =>
      cases second with
      | here => cases equality
      | there second =>
          exact congrArg Var.there (induction (Var.there.inj equality))

private theorem Var.appendRight_injective
    (left : List Sig) {first second : Var source signature}
    (equality : Var.appendRight left first = Var.appendRight left second) :
    first = second := by
  induction left with
  | nil => exact equality
  | cons head tail induction =>
      exact induction (Var.there.inj equality)

private def Var.takeLeft : (left : List Sig) →
    (wire : Var (left ++ right) signature) →
    wire.index.val < left.length → Var left signature
  | [], wire, bound => False.elim (Nat.not_lt_zero _ bound)
  | _ :: _, .here, _ => .here
  | _ :: tail, .there wire, bound =>
      .there (Var.takeLeft tail wire (by
        simp only [Var.index, Fin.val_succ, List.length_cons] at bound
        omega))

private theorem Var.appendLeft_takeLeft
    (left right : List Sig) (wire : Var (left ++ right) signature)
    (bound : wire.index.val < left.length) :
    (Var.takeLeft left wire bound).appendLeft right = wire := by
  induction left with
  | nil => exact False.elim (Nat.not_lt_zero _ bound)
  | cons head tail induction =>
      cases wire with
      | here => rfl
      | there wire =>
          simp only [Var.takeLeft, Var.appendLeft]
          exact congrArg Var.there (induction wire (by
            simp only [Var.index, Fin.val_succ, List.length_cons] at bound
            omega))

private def Region.outerOutput
    (collapse : WireRenaming target source)
    (wire : Var source signature)
    (result : { value : Var (target ++ locals) signature //
      collapse.appendRight locals value = wire.appendLeft locals }) :
    { output : Var target signature // collapse output = wire } := by
  rcases result with ⟨value, property⟩
  have bound : value.index.val < target.length := by
    cases appendView target locals value with
    | fromLeft output => simpa only [Var.index_appendLeft] using output.index.isLt
    | fromRight localWire =>
        have indices := congrArg (fun value => value.index.val) property
        simp only [WireRenaming.appendRight, Var.appendMap_right,
          Var.index_appendRight, Var.index_appendLeft] at indices
        have sourceBound := wire.index.isLt
        omega
  let output := Var.takeLeft target value bound
  refine ⟨output, ?_⟩
  apply Var.appendLeft_injective locals
  calc
    (collapse output).appendLeft locals =
        collapse.appendRight locals (output.appendLeft locals) := by
      simp [WireRenaming.appendRight]
    _ = collapse.appendRight locals value := by
      rw [Var.appendLeft_takeLeft target locals value bound]
    _ = wire.appendLeft locals := property

private theorem Region.outerOutput_appendLeft
    (collapse : WireRenaming target source)
    (wire : Var source signature)
    (result : { value : Var (target ++ locals) signature //
      collapse.appendRight locals value = wire.appendLeft locals }) :
    (Region.outerOutput collapse wire result).val.appendLeft locals =
      result.val := by
  rcases result with ⟨value, property⟩
  change (Var.takeLeft target value _).appendLeft locals = value
  exact Var.appendLeft_takeLeft target locals value _

private theorem Region.localOutput_eq
    (collapse : WireRenaming target source)
    (wire : Var locals signature)
    (result : { value : Var (target ++ locals) signature //
      collapse.appendRight locals value = Var.appendRight source wire }) :
    result.val = Var.appendRight target wire := by
  rcases result with ⟨value, property⟩
  cases appendView target locals value with
  | fromLeft inherited =>
    have indices := congrArg (fun value => value.index.val) property
    simp only [WireRenaming.appendRight, Var.appendMap_left,
      Var.index_appendLeft, Var.index_appendRight] at indices
    have collapsedBound := (collapse inherited).index.isLt
    omega
  | fromRight localWire =>
    have localEq : localWire = wire := by
      apply Var.appendRight_injective source
      simpa [WireRenaming.appendRight] using property
    exact congrArg (Var.appendRight target) localEq

private def Region.outerPartitionOfItems
    (collapse : WireRenaming target source)
    {items : ItemSeq (source ++ locals)}
    (partition : ItemSeq.PortPartition
      (collapse.appendRight locals) items) :
    Region.PortPartition collapse (.mk locals items) where
  output := fun wire (.item port) =>
    Region.outerOutput collapse wire
      (partition.output (wire.appendLeft locals) port)

private theorem Region.itemPartition_outerPartitionOfItems
    (collapse : WireRenaming target source)
    {items : ItemSeq (source ++ locals)}
    (partition : ItemSeq.PortPartition
      (collapse.appendRight locals) items) :
    Region.itemPartition (Region.outerPartitionOfItems collapse partition) =
      partition := by
  cases partition with
  | mk output =>
      apply congrArg ItemSeq.PortPartition.mk
      funext signature wire port
      apply Subtype.ext
      apply Var.appendCases
        (motive := fun {signature} wire => ∀ port : ItemSeq.Port items wire,
          ((Region.itemPartition
            (Region.outerPartitionOfItems collapse ⟨output⟩)).output
              wire port).val = (output wire port).val)
      · intro signature inherited inheritedPort
        simp only [Region.itemPartition, Var.appendElim_left,
          Region.outerPartitionOfItems]
        exact Region.outerOutput_appendLeft collapse inherited
          (output (inherited.appendLeft locals) inheritedPort)
      · intro signature localWire localPort
        simp only [Region.itemPartition, Var.appendElim_right]
        exact (Region.localOutput_eq collapse localWire
          (output (Var.appendRight source localWire) localPort)).symm

private theorem Vars.get_map
    (variables : Vars source signatures)
    (rename : WireRenaming source target)
    (argument : Fin signatures.length) :
    (variables.map (fun wire => rename wire)).get argument =
      rename (variables.get argument) := by
  induction variables with
  | nil => exact Fin.elim0 argument
  | cons head tail induction =>
      exact Fin.cases rfl (fun index => induction index) argument

private theorem Vars.partitionOutput_ofMapped
    (collapse : WireRenaming target source)
    (variables : Vars target signatures) :
    Vars.partitionOutput collapse
      (variables.map (fun wire => collapse wire))
      (fun argument => ⟨variables.get argument, by
        rw [Vars.get_map]⟩) = variables := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      exact congrArg (Vars.cons head) induction

private def Item.atomPartition
    (collapse : WireRenaming target source)
    (head : Var target (.rel arguments)) (ports : Vars target arguments) :
    Item.PortPartition collapse
      ((Item.atom head ports).renameWires collapse) where
  output
  | _, .atomHead => ⟨head, rfl⟩
  | _, .atomArgument argument => ⟨ports.get argument, by
      rw [Vars.get_map]⟩

private def Item.identityPartition
    (collapse : WireRenaming target source)
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var target signature) :
    Item.PortPartition collapse
      ((Item.identity signature arity ports).renameWires collapse) where
  output
  | _, .identity argument => ⟨ports argument, rfl⟩

private def Item.cutPartition
    (collapse : WireRenaming target source) {body : Region target}
    (partition : Region.PortPartition collapse (body.renameWires collapse)) :
    Item.PortPartition collapse ((Item.cut body).renameWires collapse) where
  output
  | _, .cut port => partition.output _ port

private def ItemSeq.nilPartition
    (collapse : WireRenaming target source) :
    ItemSeq.PortPartition collapse (ItemSeq.nil : ItemSeq source) where
  output
  | _, port => nomatch port

private def ItemSeq.consPartition
    (collapse : WireRenaming target source)
    {head : Item target} {tail : ItemSeq target}
    (headPartition : Item.PortPartition collapse
      (head.renameWires collapse))
    (tailPartition : ItemSeq.PortPartition collapse
      (tail.renameWires collapse)) :
    ItemSeq.PortPartition collapse
      ((ItemSeq.cons head tail).renameWires collapse) where
  output
  | _, .head port => headPartition.output _ port
  | _, .tail port => tailPartition.output _ port

mutual
  theorem Region.exists_partition_of_renamed
      (collapse : WireRenaming target source) (targetRegion : Region target) :
      ∃ partition : Region.PortPartition collapse
          (targetRegion.renameWires collapse),
        (targetRegion.renameWires collapse).partitionOutput collapse partition =
          targetRegion := by
    cases targetRegion with
    | mk locals items =>
        obtain ⟨itemsPartition, items_eq⟩ :=
          ItemSeq.exists_partition_of_renamed
            (collapse.appendRight locals) items
        let partition := Region.outerPartitionOfItems collapse itemsPartition
        refine ⟨partition, ?_⟩
        simp only [Region.renameWires, Region.partitionOutput, partition]
        rw [Region.itemPartition_outerPartitionOfItems]
        exact congrArg (Region.mk locals) items_eq

  theorem Item.exists_partition_of_renamed
      (collapse : WireRenaming target source) (targetItem : Item target) :
      ∃ partition : Item.PortPartition collapse
          (targetItem.renameWires collapse),
        (targetItem.renameWires collapse).partitionOutput collapse partition =
          targetItem := by
    cases targetItem with
    | atom head ports =>
        let partition := Item.atomPartition collapse head ports
        refine ⟨partition, ?_⟩
        simp only [Item.renameWires, Item.partitionOutput, partition,
          Item.atomPartition]
        exact congrArg (Item.atom head)
          (Vars.partitionOutput_ofMapped collapse ports)
    | identity signature arity ports =>
        let partition := Item.identityPartition collapse signature arity ports
        refine ⟨partition, ?_⟩
        simp only [Item.renameWires, Item.partitionOutput, partition,
          Item.identityPartition]
    | cut body =>
        obtain ⟨bodyPartition, body_eq⟩ :=
          Region.exists_partition_of_renamed collapse body
        let partition := Item.cutPartition collapse bodyPartition
        refine ⟨partition, ?_⟩
        simp only [Item.renameWires, Item.partitionOutput, partition,
          Item.cutPartition]
        rw [body_eq]

  theorem ItemSeq.exists_partition_of_renamed
      (collapse : WireRenaming target source) (targetItems : ItemSeq target) :
      ∃ partition : ItemSeq.PortPartition collapse
          (targetItems.renameWires collapse),
        (targetItems.renameWires collapse).partitionOutput collapse partition =
          targetItems := by
    cases targetItems with
    | nil => exact ⟨ItemSeq.nilPartition collapse, rfl⟩
    | cons head tail =>
        obtain ⟨headPartition, head_eq⟩ :=
          Item.exists_partition_of_renamed collapse head
        obtain ⟨tailPartition, tail_eq⟩ :=
          ItemSeq.exists_partition_of_renamed collapse tail
        let partition :=
          ItemSeq.consPartition collapse headPartition tailPartition
        refine ⟨partition, ?_⟩
        simp only [ItemSeq.renameWires, ItemSeq.partitionOutput, partition,
          ItemSeq.consPartition]
        rw [head_eq, tail_eq]
end

end VisualProof.Diagram
