import VisualProof.Diagram.Isomorphism

namespace VisualProof.Diagram

open VisualProof
open Theory

/-! Structural labels for ports, indexed by the wire to which each port is
attached.  A partition chooses a wire in the corresponding fiber of a join. -/

mutual
  inductive Region.Port :
      {wires : Nat} → {rels : RelCtx} →
      (region : Region wires rels) → Fin wires → Type
    | item {outer localWires : Nat} {rels : RelCtx}
        {items : ItemSeq (outer + localWires) rels} {wire : Fin outer}
        (port : ItemSeq.Port items (Fin.castAdd localWires wire)) :
        Region.Port (.mk localWires items) wire

  inductive Item.Port :
      {wires : Nat} → {rels : RelCtx} →
      (item : Item wires rels) → Fin wires → Type
    | atom {wires arity : Nat} {rels : RelCtx}
        {relation : RelVar rels arity}
        {arguments : Fin arity → Fin wires} (argument : Fin arity) :
        Item.Port (.atom relation arguments) (arguments argument)
    | identity {wires arity : Nat} {rels : RelCtx}
        {arguments : Fin arity → Fin wires} (argument : Fin arity) :
        Item.Port (Item.identity (rels := rels) arity arguments)
          (arguments argument)
    | cut {wires : Nat} {rels : RelCtx} {body : Region wires rels}
        {wire : Fin wires} (port : Region.Port body wire) :
        Item.Port (.cut body) wire
    | bubble {wires arity : Nat} {rels : RelCtx}
        {body : Region wires (arity :: rels)} {wire : Fin wires}
        (port : Region.Port body wire) :
        Item.Port (.bubble arity body) wire

  inductive ItemSeq.Port :
      {wires : Nat} → {rels : RelCtx} →
      (items : ItemSeq wires rels) → Fin wires → Type
    | head {wires : Nat} {rels : RelCtx} {item : Item wires rels}
        {tail : ItemSeq wires rels} {wire : Fin wires}
        (port : Item.Port item wire) :
        ItemSeq.Port (.cons item tail) wire
    | tail {wires : Nat} {rels : RelCtx} {item : Item wires rels}
        {tail : ItemSeq wires rels} {wire : Fin wires}
        (port : ItemSeq.Port tail wire) :
        ItemSeq.Port (.cons item tail) wire
end

abbrev Region.PortPartition
    (join : Fin targetWires → Fin sourceWires)
    (source : Region sourceWires rels) :=
  ∀ (wire : Fin sourceWires), Region.Port source wire →
    {output : Fin targetWires // join output = wire}

abbrev Item.PortPartition
    (join : Fin targetWires → Fin sourceWires)
    (source : Item sourceWires rels) :=
  ∀ (wire : Fin sourceWires), Item.Port source wire →
    {output : Fin targetWires // join output = wire}

abbrev ItemSeq.PortPartition
    (join : Fin targetWires → Fin sourceWires)
    (source : ItemSeq sourceWires rels) :=
  ∀ (wire : Fin sourceWires), ItemSeq.Port source wire →
    {output : Fin targetWires // join output = wire}

private def Region.itemPartition
    {join : Fin targetWires → Fin sourceWires}
    {items : ItemSeq (sourceWires + localWires) rels}
    (partition : Region.PortPartition join (.mk localWires items)) :
    ItemSeq.PortPartition (extendWireRenaming join localWires) items :=
  fun wire port =>
    Fin.addCases
      (motive := fun wire : Fin (sourceWires + localWires) =>
        ItemSeq.Port items wire →
          {output : Fin (targetWires + localWires) //
            extendWireRenaming join localWires output = wire})
      (fun inherited inheritedPort =>
        let output := partition inherited (.item inheritedPort)
        ⟨Fin.castAdd localWires output.val, by
          simp only [extendWireRenaming, Fin.addCases_left]
          exact congrArg (Fin.castAdd localWires) output.property⟩)
      (fun localWire _ =>
        ⟨Fin.natAdd targetWires localWire, by
          simp only [extendWireRenaming, Fin.addCases_right]⟩)
      wire port

mutual
  def Region.partitionOutput
      (join : Fin targetWires → Fin sourceWires) :
      (source : Region sourceWires rels) →
        Region.PortPartition join source → Region targetWires rels
    | .mk localWires items, partition =>
        .mk localWires
          (ItemSeq.partitionOutput (extendWireRenaming join localWires) items
            (Region.itemPartition partition))

  def Item.partitionOutput
      (join : Fin targetWires → Fin sourceWires) :
      (source : Item sourceWires rels) →
        Item.PortPartition join source → Item targetWires rels
    | .atom relation arguments, partition =>
        .atom relation fun argument =>
          (partition (arguments argument) (.atom argument)).val
    | .identity arity arguments, partition =>
        .identity arity fun argument =>
          (partition (arguments argument) (.identity argument)).val
    | .cut body, partition =>
        .cut (Region.partitionOutput join body fun wire port =>
          partition wire (.cut port))
    | .bubble arity body, partition =>
        .bubble arity (Region.partitionOutput join body fun wire port =>
          partition wire (.bubble port))

  def ItemSeq.partitionOutput
      (join : Fin targetWires → Fin sourceWires) :
      (source : ItemSeq sourceWires rels) →
        ItemSeq.PortPartition join source → ItemSeq targetWires rels
    | .nil, _ => .nil
    | .cons head tail, partition =>
        .cons
          (Item.partitionOutput join head fun wire port =>
            partition wire (.head port))
          (ItemSeq.partitionOutput join tail fun wire port =>
            partition wire (.tail port))
end

mutual
  theorem Region.partitionOutput_renameWires
      (join : Fin targetWires → Fin sourceWires)
      (source : Region sourceWires rels)
      (partition : Region.PortPartition join source) :
      (source.partitionOutput join partition).renameWires join = source := by
    cases source with
    | mk localWires items =>
        simp only [Region.partitionOutput, Region.renameWires]
        rw [ItemSeq.partitionOutput_renameWires]

  theorem Item.partitionOutput_renameWires
      (join : Fin targetWires → Fin sourceWires)
      (source : Item sourceWires rels)
      (partition : Item.PortPartition join source) :
      (source.partitionOutput join partition).renameWires join = source := by
    cases source with
    | atom relation arguments =>
        simp only [Item.partitionOutput, Item.renameWires]
        apply congrArg (Item.atom relation)
        funext argument
        exact (partition (arguments argument) (.atom argument)).property
    | identity arity arguments =>
        simp only [Item.partitionOutput, Item.renameWires]
        apply congrArg (Item.identity arity)
        funext argument
        exact (partition (arguments argument) (.identity argument)).property
    | cut body =>
        simp only [Item.partitionOutput, Item.renameWires]
        rw [Region.partitionOutput_renameWires]
    | bubble arity body =>
        simp only [Item.partitionOutput, Item.renameWires]
        rw [Region.partitionOutput_renameWires]

  theorem ItemSeq.partitionOutput_renameWires
      (join : Fin targetWires → Fin sourceWires)
      (source : ItemSeq sourceWires rels)
      (partition : ItemSeq.PortPartition join source) :
      (source.partitionOutput join partition).renameWires join = source := by
    cases source with
    | nil => rfl
    | cons head tail =>
        simp only [ItemSeq.partitionOutput, ItemSeq.renameWires]
        rw [Item.partitionOutput_renameWires,
          ItemSeq.partitionOutput_renameWires]
end

private def Region.outerOutput
    (join : Fin targetWires → Fin sourceWires)
    (wire : Fin sourceWires)
    (output : {value : Fin (targetWires + localWires) //
      extendWireRenaming join localWires value =
        Fin.castAdd localWires wire}) :
    {result : Fin targetWires // join result = wire} :=
  Fin.addCases
    (motive := fun value : Fin (targetWires + localWires) =>
      extendWireRenaming join localWires value =
          Fin.castAdd localWires wire →
        {result : Fin targetWires // join result = wire})
    (fun result equality => ⟨result, by
      apply Fin.ext
      have values := congrArg Fin.val equality
      simpa only [extendWireRenaming, Fin.addCases_left] using values⟩)
    (fun localWire equality => by
      have values := congrArg Fin.val equality
      simp only [extendWireRenaming, Fin.addCases_right] at values
      change sourceWires + localWire.val = wire.val at values
      omega)
    output.val output.property

private theorem Region.outerOutput_castAdd
    (join : Fin targetWires → Fin sourceWires)
    (wire : Fin sourceWires)
    (output : {value : Fin (targetWires + localWires) //
      extendWireRenaming join localWires value =
        Fin.castAdd localWires wire}) :
    Fin.castAdd localWires (Region.outerOutput join wire output).val =
      output.val := by
  rcases output with ⟨value, property⟩
  refine Fin.addCases
    (motive := fun value : Fin (targetWires + localWires) =>
      ∀ property : extendWireRenaming join localWires value =
          Fin.castAdd localWires wire,
        Fin.castAdd localWires
            (Region.outerOutput join wire ⟨value, property⟩).val = value)
    (fun result property => by
      simp only [Region.outerOutput, Fin.addCases_left])
    (fun localWire property => by
      have values := congrArg Fin.val property
      simp only [extendWireRenaming, Fin.addCases_right] at values
      change sourceWires + localWire.val = wire.val at values
      omega)
    value property

private theorem Region.localOutput_eq
    (join : Fin targetWires → Fin sourceWires)
    (wire : Fin localWires)
    (output : {value : Fin (targetWires + localWires) //
      extendWireRenaming join localWires value =
        Fin.natAdd sourceWires wire}) :
    output.val = Fin.natAdd targetWires wire := by
  rcases output with ⟨value, property⟩
  refine Fin.addCases
    (motive := fun value : Fin (targetWires + localWires) =>
      ∀ property : extendWireRenaming join localWires value =
          Fin.natAdd sourceWires wire,
        value = Fin.natAdd targetWires wire)
    (fun impossible property => by
      have values := congrArg Fin.val property
      simp only [extendWireRenaming, Fin.addCases_left] at values
      change (join impossible).val = sourceWires + wire.val at values
      omega)
    (fun result property => by
      apply Fin.ext
      have values := congrArg Fin.val property
      simp only [extendWireRenaming, Fin.addCases_right] at values
      change sourceWires + result.val = sourceWires + wire.val at values
      change targetWires + result.val = targetWires + wire.val
      omega)
    value property

private def Region.outerPartitionOfItems
    (join : Fin targetWires → Fin sourceWires)
    {items : ItemSeq (sourceWires + localWires) rels}
    (partition : ItemSeq.PortPartition
      (extendWireRenaming join localWires) items) :
    Region.PortPartition join (.mk localWires items) :=
  fun wire (.item port) =>
    let output := partition (Fin.castAdd localWires wire) port
    Region.outerOutput join wire output

private theorem Region.itemPartition_outerPartitionOfItems
    (join : Fin targetWires → Fin sourceWires)
    {items : ItemSeq (sourceWires + localWires) rels}
    (partition : ItemSeq.PortPartition
      (extendWireRenaming join localWires) items) :
    Region.itemPartition
        (Region.outerPartitionOfItems join partition) = partition := by
  funext wire port
  apply Subtype.ext
  refine Fin.addCases
    (motive := fun wire : Fin (sourceWires + localWires) =>
      ∀ port : ItemSeq.Port items wire,
        (Region.itemPartition
          (Region.outerPartitionOfItems join partition) wire port).val =
        (partition wire port).val)
    (fun inherited inheritedPort => ?_)
    (fun localWire localPort => ?_)
    wire port
  · simp only [Region.itemPartition, Fin.addCases_left,
      Region.outerPartitionOfItems]
    exact Region.outerOutput_castAdd join inherited
      (partition (Fin.castAdd localWires inherited) inheritedPort)
  · simp only [Region.itemPartition, Fin.addCases_right]
    exact (Region.localOutput_eq join localWire
      (partition (Fin.natAdd sourceWires localWire) localPort)).symm

private def Item.atomPartition
    (join : Fin targetWires → Fin sourceWires)
    (relation : RelVar rels arity)
    (arguments : Fin arity → Fin targetWires) :
    Item.PortPartition join (.atom relation (join ∘ arguments))
  | _, .atom argument => ⟨arguments argument, rfl⟩

private def Item.identityPartition
    (join : Fin targetWires → Fin sourceWires)
    (arguments : Fin arity → Fin targetWires) :
    Item.PortPartition join
      (Item.identity (rels := rels) arity (join ∘ arguments))
  | _, .identity argument => ⟨arguments argument, rfl⟩

private def Item.cutPartition
    (join : Fin targetWires → Fin sourceWires)
    {body : Region targetWires rels}
    (partition : Region.PortPartition join (body.renameWires join)) :
    Item.PortPartition join (.cut (body.renameWires join))
  | wire, .cut port => partition wire port

private def Item.bubblePartition
    (join : Fin targetWires → Fin sourceWires)
    {body : Region targetWires (arity :: rels)}
    (partition : Region.PortPartition join (body.renameWires join)) :
    Item.PortPartition join (.bubble arity (body.renameWires join))
  | wire, .bubble port => partition wire port

private def ItemSeq.nilPartition
    (join : Fin targetWires → Fin sourceWires) :
    ItemSeq.PortPartition join (ItemSeq.nil (wires := sourceWires) (rels := rels))
  | _, port => nomatch port

private def ItemSeq.consPartition
    (join : Fin targetWires → Fin sourceWires)
    {head : Item targetWires rels} {tail : ItemSeq targetWires rels}
    (headPartition : Item.PortPartition join (head.renameWires join))
    (tailPartition : ItemSeq.PortPartition join (tail.renameWires join)) :
    ItemSeq.PortPartition join
      (.cons (head.renameWires join) (tail.renameWires join))
  | wire, .head port => headPartition wire port
  | wire, .tail port => tailPartition wire port

mutual
  theorem Region.exists_partition_of_renamed
      (join : Fin targetWires → Fin sourceWires)
      (target : Region targetWires rels) :
      ∃ partition : Region.PortPartition join (target.renameWires join),
        (target.renameWires join).partitionOutput join partition = target := by
    cases target with
    | mk localWires items =>
        obtain ⟨itemsPartition, items_eq⟩ :=
          ItemSeq.exists_partition_of_renamed
            (extendWireRenaming join localWires) items
        let partition := Region.outerPartitionOfItems join itemsPartition
        refine ⟨partition, ?_⟩
        simp only [Region.renameWires, Region.partitionOutput, partition]
        rw [Region.itemPartition_outerPartitionOfItems]
        exact congrArg (Region.mk localWires) items_eq

  theorem Item.exists_partition_of_renamed
      (join : Fin targetWires → Fin sourceWires)
      (target : Item targetWires rels) :
      ∃ partition : Item.PortPartition join (target.renameWires join),
        (target.renameWires join).partitionOutput join partition = target := by
    cases target with
    | atom relation arguments =>
        let partition := Item.atomPartition join relation arguments
        refine ⟨partition, ?_⟩
        simp only [Item.renameWires, Item.partitionOutput, partition,
          Item.atomPartition]
        apply congrArg (Item.atom relation)
        funext argument
        rfl
    | identity arity arguments =>
        let partition := Item.identityPartition (rels := rels) join arguments
        refine ⟨partition, ?_⟩
        simp only [Item.renameWires, Item.partitionOutput, partition,
          Item.identityPartition]
        apply congrArg (Item.identity arity)
        funext argument
        rfl
    | cut body =>
        obtain ⟨bodyPartition, body_eq⟩ :=
          Region.exists_partition_of_renamed join body
        let partition := Item.cutPartition join bodyPartition
        refine ⟨partition, ?_⟩
        simp only [Item.renameWires, Item.partitionOutput, partition,
          Item.cutPartition]
        rw [body_eq]
    | bubble arity body =>
        obtain ⟨bodyPartition, body_eq⟩ :=
          Region.exists_partition_of_renamed join body
        let partition := Item.bubblePartition join bodyPartition
        refine ⟨partition, ?_⟩
        simp only [Item.renameWires, Item.partitionOutput, partition,
          Item.bubblePartition]
        rw [body_eq]

  theorem ItemSeq.exists_partition_of_renamed
      (join : Fin targetWires → Fin sourceWires)
      (target : ItemSeq targetWires rels) :
      ∃ partition : ItemSeq.PortPartition join (target.renameWires join),
        (target.renameWires join).partitionOutput join partition = target := by
    cases target with
    | nil =>
        exact ⟨ItemSeq.nilPartition (rels := rels) join, rfl⟩
    | cons head tail =>
        obtain ⟨headPartition, head_eq⟩ :=
          Item.exists_partition_of_renamed join head
        obtain ⟨tailPartition, tail_eq⟩ :=
          ItemSeq.exists_partition_of_renamed join tail
        let partition := ItemSeq.consPartition join headPartition tailPartition
        refine ⟨partition, ?_⟩
        simp only [ItemSeq.renameWires, ItemSeq.partitionOutput, partition,
          ItemSeq.consPartition]
        rw [head_eq, tail_eq]
end

end VisualProof.Diagram
