import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Diagram
open Theory

namespace WholeAssemblyVacuity

/-- An order-preserving inclusion of one typed wire context in another. -/
inductive WireExtension : List Sig → List Sig → Type
  | nil : WireExtension [] []
  | retain (extension : WireExtension source target) :
      WireExtension (signature :: source) (signature :: target)
  | insert (extension : WireExtension source target) :
      WireExtension source (signature :: target)

namespace WireExtension

def refl : (wires : List Sig) → WireExtension wires wires
  | [] => .nil
  | _ :: rest => .retain (refl rest)

def map : WireExtension source target →
    Var source signature → Var target signature
  | .retain _, .here => .here
  | .retain extension, .there wire => .there (extension.map wire)
  | .insert extension, wire => .there (extension.map wire)

def append : WireExtension source target →
    WireExtension source' target' →
    WireExtension (source ++ source') (target ++ target')
  | .nil, right => right
  | .retain left, right => .retain (left.append right)
  | .insert left, right => .insert (left.append right)

/-- A target wire introduced by this exact ordered extension. -/
inductive Fresh : WireExtension source target → Type
  | inserted (extension : WireExtension source target) :
      Fresh (@WireExtension.insert source target signature extension)
  | retainTail (fresh : Fresh extension) : Fresh (.retain extension)
  | insertTail (fresh : Fresh extension) : Fresh (.insert extension)

def Fresh.signature {source target : List Sig} :
    {extension : WireExtension source target} →
    Fresh extension → Sig
  | _, @Fresh.inserted _ _ signature _ => signature
  | _, .retainTail fresh => fresh.signature
  | _, .insertTail fresh => fresh.signature

def Fresh.target {source target : List Sig} :
    {extension : WireExtension source target} →
    (fresh : Fresh extension) → Var target fresh.signature
  | _, .inserted _ => .here
  | _, .retainTail fresh => .there fresh.target
  | _, .insertTail fresh => .there fresh.target

end WireExtension

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

  inductive ItemSeq.IdentityOccurrence : ItemSeq wires → Type
    | head : ItemSeq.IdentityOccurrence
        (.cons (.identity signature arity ports) tail)
    | headCut (node : Region.IdentityOccurrence body) :
        ItemSeq.IdentityOccurrence (.cons (.cut body) tail)
    | tail (node : ItemSeq.IdentityOccurrence tail) :
        ItemSeq.IdentityOccurrence (.cons item tail)
end

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

  inductive ItemSeq.IdentityPortOccurrence : ItemSeq wires → Type
    | head (port : Fin arity) : ItemSeq.IdentityPortOccurrence
        (.cons (.identity signature arity ports) tail)
    | headCut (port : Region.IdentityPortOccurrence body) :
        ItemSeq.IdentityPortOccurrence (.cons (.cut body) tail)
    | tail (port : ItemSeq.IdentityPortOccurrence tail) :
        ItemSeq.IdentityPortOccurrence (.cons item tail)
end

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

/-- Retained ports embed in order; every other target port is fresh. -/
structure IdentityPortExtension
    (wires : WireExtension sourceWires targetWires)
    (sourcePorts : Fin sourceArity → Var sourceWires signature)
    (targetPorts : Fin targetArity → Var targetWires signature) where
  retained : Fin sourceArity → Fin targetArity
  orderPreserving : ∀ left right,
    left.val < right.val → (retained left).val < (retained right).val
  retained_eq : ∀ index,
    wires.map (sourcePorts index) = targetPorts (retained index)
  addedFresh : ∀ targetIndex,
    (∀ sourceIndex, retained sourceIndex ≠ targetIndex) →
      ∃ fresh : wires.Fresh, HEq fresh.target (targetPorts targetIndex)

mutual
  /-- The single recursive witness for retaining arbitrary syntax while
  introducing only wires and identity apparatus. -/
  inductive IdentityOnlyExtension :
      {sourceOuter targetOuter : List Sig} →
      WireExtension sourceOuter targetOuter →
      Region sourceOuter → Region targetOuter → Type
    | region
        {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireExtension sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        (locals : WireExtension sourceLocals targetLocals)
        (items : IdentityOnlyItemsExtension (ambient.append locals)
          sourceItems targetItems) :
        IdentityOnlyExtension ambient
          (.mk sourceLocals sourceItems) (.mk targetLocals targetItems)

  inductive IdentityOnlyItemsExtension :
      {sourceWires targetWires : List Sig} →
      WireExtension sourceWires targetWires →
      ItemSeq sourceWires → ItemSeq targetWires → Type
    | nil : IdentityOnlyItemsExtension ambient .nil .nil
    | atom
        {sourceWires targetWires arguments : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {sourceHead : Var sourceWires (.rel arguments)}
        {targetHead : Var targetWires (.rel arguments)}
        {sourcePorts : Vars sourceWires arguments}
        {targetPorts : Vars targetWires arguments}
        {sourceTail : ItemSeq sourceWires}
        {targetTail : ItemSeq targetWires}
        (head_eq : ambient.map sourceHead = targetHead)
        (ports_eq : sourcePorts.map (fun wire => ambient.map wire) = targetPorts)
        (tail : IdentityOnlyItemsExtension ambient sourceTail targetTail) :
        IdentityOnlyItemsExtension ambient
          (.cons (.atom sourceHead sourcePorts) sourceTail)
          (.cons (.atom targetHead targetPorts) targetTail)
    | identity
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {signature : Sig} {sourceArity targetArity : Nat}
        {sourcePorts : Fin sourceArity → Var sourceWires signature}
        {targetPorts : Fin targetArity → Var targetWires signature}
        {sourceTail : ItemSeq sourceWires}
        {targetTail : ItemSeq targetWires}
        (ports : IdentityPortExtension ambient sourcePorts targetPorts)
        (tail : IdentityOnlyItemsExtension ambient sourceTail targetTail) :
        IdentityOnlyItemsExtension ambient
          (.cons (.identity signature sourceArity sourcePorts) sourceTail)
          (.cons (.identity signature targetArity targetPorts) targetTail)
    | cut
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {sourceBody : Region sourceWires}
        {targetBody : Region targetWires}
        {sourceTail : ItemSeq sourceWires}
        {targetTail : ItemSeq targetWires}
        (body : IdentityOnlyExtension ambient sourceBody targetBody)
        (tail : IdentityOnlyItemsExtension ambient sourceTail targetTail) :
        IdentityOnlyItemsExtension ambient
          (.cons (.cut sourceBody) sourceTail)
          (.cons (.cut targetBody) targetTail)
    | addIdentity
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {source : ItemSeq sourceWires}
        {targetTail : ItemSeq targetWires}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var targetWires signature}
        (tail : IdentityOnlyItemsExtension ambient source targetTail) :
        IdentityOnlyItemsExtension ambient source
          (.cons (.identity signature arity ports) targetTail)
end

mutual
  /-- A fresh wire, projected from one extension witness. -/
  inductive IdentityOnlyExtension.FreshWire :
      {ambient : WireExtension sourceOuter targetOuter} →
      {source : Region sourceOuter} → {target : Region targetOuter} →
      IdentityOnlyExtension ambient source target → Type
    | local
        {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireExtension sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        {locals : WireExtension sourceLocals targetLocals}
        {items : IdentityOnlyItemsExtension (ambient.append locals)
          sourceItems targetItems}
        (fresh : WireExtension.Fresh locals) :
        IdentityOnlyExtension.FreshWire
          (IdentityOnlyExtension.region locals items)
    | nested
        {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireExtension sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        {locals : WireExtension sourceLocals targetLocals}
        {items : IdentityOnlyItemsExtension (ambient.append locals)
          sourceItems targetItems}
        (fresh : IdentityOnlyItemsExtension.FreshWire items) :
        IdentityOnlyExtension.FreshWire
          (IdentityOnlyExtension.region locals items)

  inductive IdentityOnlyItemsExtension.FreshWire :
      {ambient : WireExtension sourceWires targetWires} →
      {source : ItemSeq sourceWires} → {target : ItemSeq targetWires} →
      IdentityOnlyItemsExtension ambient source target → Type
    | atomTail (fresh : IdentityOnlyItemsExtension.FreshWire tail) :
        IdentityOnlyItemsExtension.FreshWire
          (IdentityOnlyItemsExtension.atom head ports tail)
    | identityTail (fresh : IdentityOnlyItemsExtension.FreshWire tail) :
        IdentityOnlyItemsExtension.FreshWire
          (IdentityOnlyItemsExtension.identity ports tail)
    | cutHead (fresh : IdentityOnlyExtension.FreshWire body) :
        IdentityOnlyItemsExtension.FreshWire
          (IdentityOnlyItemsExtension.cut body tail)
    | cutTail (fresh : IdentityOnlyItemsExtension.FreshWire tail) :
        IdentityOnlyItemsExtension.FreshWire
          (IdentityOnlyItemsExtension.cut body tail)
    | addedIdentityTail
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {source : ItemSeq sourceWires} {targetTail : ItemSeq targetWires}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var targetWires signature}
        {tail : IdentityOnlyItemsExtension ambient source targetTail}
        (fresh : IdentityOnlyItemsExtension.FreshWire tail) :
        IdentityOnlyItemsExtension.FreshWire
          (@IdentityOnlyItemsExtension.addIdentity sourceWires targetWires
            ambient source targetTail signature arity ports tail)
end

mutual
  def IdentityOnlyExtension.FreshWire.signature
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      IdentityOnlyExtension.FreshWire extension → Sig
    | .local fresh => fresh.signature
    | .nested fresh => fresh.signature

  def IdentityOnlyItemsExtension.FreshWire.signature
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      IdentityOnlyItemsExtension.FreshWire extension → Sig
    | .atomTail fresh => fresh.signature
    | .identityTail fresh => fresh.signature
    | .cutHead fresh => fresh.signature
    | .cutTail fresh => fresh.signature
    | .addedIdentityTail fresh => fresh.signature
end

mutual
  def IdentityOnlyExtension.FreshWire.targetInternal
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      (wire : IdentityOnlyExtension.FreshWire extension) →
        Region.InternalWire target wire.signature
    | .local fresh => .here fresh.target
    | .nested fresh => .nested fresh.targetInternal

  def IdentityOnlyItemsExtension.FreshWire.targetInternal
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      (wire : IdentityOnlyItemsExtension.FreshWire extension) →
        ItemSeq.InternalWire target wire.signature
    | .atomTail fresh => .tail fresh.targetInternal
    | .identityTail fresh => .tail fresh.targetInternal
    | .cutHead fresh => .headCut fresh.targetInternal
    | .cutTail fresh => .tail fresh.targetInternal
    | .addedIdentityTail fresh => .tail fresh.targetInternal
end

def IdentityOnlyExtension.FreshWire.target
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    {extension : IdentityOnlyExtension ambient source target}
    (wire : IdentityOnlyExtension.FreshWire extension) : Region.Wire target :=
  .internal wire.targetInternal

mutual
  /-- A retained wire owned by the source region, with its exact target
  occurrence determined by the extension witness. -/
  inductive IdentityOnlyExtension.RetainedInternalWire :
      {ambient : WireExtension sourceOuter targetOuter} →
      {source : Region sourceOuter} → {target : Region targetOuter} →
      IdentityOnlyExtension ambient source target → Type
    | local
        {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireExtension sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        {locals : WireExtension sourceLocals targetLocals}
        {items : IdentityOnlyItemsExtension (ambient.append locals)
          sourceItems targetItems}
        (wire : Var sourceLocals signature) :
        IdentityOnlyExtension.RetainedInternalWire
          (IdentityOnlyExtension.region locals items)
    | nested
        {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireExtension sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        {locals : WireExtension sourceLocals targetLocals}
        {items : IdentityOnlyItemsExtension (ambient.append locals)
          sourceItems targetItems}
        (wire : IdentityOnlyItemsExtension.RetainedInternalWire items) :
        IdentityOnlyExtension.RetainedInternalWire
          (IdentityOnlyExtension.region locals items)

  inductive IdentityOnlyItemsExtension.RetainedInternalWire :
      {ambient : WireExtension sourceWires targetWires} →
      {source : ItemSeq sourceWires} → {target : ItemSeq targetWires} →
      IdentityOnlyItemsExtension ambient source target → Type
    | atomTail (wire : IdentityOnlyItemsExtension.RetainedInternalWire tail) :
        IdentityOnlyItemsExtension.RetainedInternalWire
          (IdentityOnlyItemsExtension.atom head ports tail)
    | identityTail
        (wire : IdentityOnlyItemsExtension.RetainedInternalWire tail) :
        IdentityOnlyItemsExtension.RetainedInternalWire
          (IdentityOnlyItemsExtension.identity ports tail)
    | cutHead (wire : IdentityOnlyExtension.RetainedInternalWire body) :
        IdentityOnlyItemsExtension.RetainedInternalWire
          (IdentityOnlyItemsExtension.cut body tail)
    | cutTail (wire : IdentityOnlyItemsExtension.RetainedInternalWire tail) :
        IdentityOnlyItemsExtension.RetainedInternalWire
          (IdentityOnlyItemsExtension.cut body tail)
    | addedIdentityTail
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {source : ItemSeq sourceWires} {targetTail : ItemSeq targetWires}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var targetWires signature}
        {tail : IdentityOnlyItemsExtension ambient source targetTail}
        (wire : IdentityOnlyItemsExtension.RetainedInternalWire tail) :
        IdentityOnlyItemsExtension.RetainedInternalWire
          (@IdentityOnlyItemsExtension.addIdentity sourceWires targetWires
            ambient source targetTail signature arity ports tail)
end

mutual
  def IdentityOnlyExtension.RetainedInternalWire.signature
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      IdentityOnlyExtension.RetainedInternalWire extension → Sig
    | .local (signature := signature) _ => signature
    | .nested wire => wire.signature

  def IdentityOnlyItemsExtension.RetainedInternalWire.signature
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      IdentityOnlyItemsExtension.RetainedInternalWire extension → Sig
    | .atomTail wire => wire.signature
    | .identityTail wire => wire.signature
    | .cutHead wire => wire.signature
    | .cutTail wire => wire.signature
    | .addedIdentityTail wire => wire.signature
end

mutual
  def IdentityOnlyExtension.RetainedInternalWire.source
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      (wire : IdentityOnlyExtension.RetainedInternalWire extension) →
        Region.InternalWire source wire.signature
    | .local wire => .here wire
    | .nested wire => .nested wire.source

  def IdentityOnlyItemsExtension.RetainedInternalWire.source
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      (wire : IdentityOnlyItemsExtension.RetainedInternalWire extension) →
        ItemSeq.InternalWire source wire.signature
    | .atomTail wire => .tail wire.source
    | .identityTail wire => .tail wire.source
    | .cutHead wire => .headCut wire.source
    | .cutTail wire => .tail wire.source
    | .addedIdentityTail wire => wire.source
end

mutual
  def IdentityOnlyExtension.RetainedInternalWire.target
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      (wire : IdentityOnlyExtension.RetainedInternalWire extension) →
        Region.InternalWire target wire.signature
    | .local (locals := locals) wire =>
        .here (WireExtension.map locals wire)
    | .nested wire => .nested wire.target

  def IdentityOnlyItemsExtension.RetainedInternalWire.target
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      (wire : IdentityOnlyItemsExtension.RetainedInternalWire extension) →
        ItemSeq.InternalWire target wire.signature
    | .atomTail wire => .tail wire.target
    | .identityTail wire => .tail wire.target
    | .cutHead wire => .headCut wire.target
    | .cutTail wire => .tail wire.target
    | .addedIdentityTail wire => .tail wire.target
end

/-- A source wire and the exact retained target wire determined by a witness. -/
inductive IdentityOnlyExtension.RetainedWire
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    (extension : IdentityOnlyExtension ambient source target) : Type
  | inherited (wire : Var sourceOuter signature) : RetainedWire extension
  | internal (wire : extension.RetainedInternalWire) : RetainedWire extension

def IdentityOnlyExtension.RetainedWire.source
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    {extension : IdentityOnlyExtension ambient source target} :
    RetainedWire extension → Region.Wire source
  | .inherited wire => @Region.Wire.inherited _ source _ wire
  | .internal wire => .internal wire.source

def IdentityOnlyExtension.RetainedWire.target
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    {extension : IdentityOnlyExtension ambient source target} :
    RetainedWire extension → Region.Wire target
  | .inherited wire =>
      @Region.Wire.inherited _ target _ (ambient.map wire)
  | .internal wire => .internal wire.target

mutual
  /-- An identity node introduced by the witness. -/
  inductive IdentityOnlyExtension.AddedIdentity :
      {ambient : WireExtension sourceOuter targetOuter} →
      {source : Region sourceOuter} → {target : Region targetOuter} →
      IdentityOnlyExtension ambient source target → Type
    | item
        {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireExtension sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        {locals : WireExtension sourceLocals targetLocals}
        {items : IdentityOnlyItemsExtension (ambient.append locals)
          sourceItems targetItems}
        (node : IdentityOnlyItemsExtension.AddedIdentity items) :
        IdentityOnlyExtension.AddedIdentity
          (IdentityOnlyExtension.region locals items)

  inductive IdentityOnlyItemsExtension.AddedIdentity :
      {ambient : WireExtension sourceWires targetWires} →
      {source : ItemSeq sourceWires} → {target : ItemSeq targetWires} →
      IdentityOnlyItemsExtension ambient source target → Type
    | atomTail (node : IdentityOnlyItemsExtension.AddedIdentity tail) :
        IdentityOnlyItemsExtension.AddedIdentity
          (IdentityOnlyItemsExtension.atom head ports tail)
    | identityTail (node : IdentityOnlyItemsExtension.AddedIdentity tail) :
        IdentityOnlyItemsExtension.AddedIdentity
          (IdentityOnlyItemsExtension.identity ports tail)
    | cutHead (node : IdentityOnlyExtension.AddedIdentity body) :
        IdentityOnlyItemsExtension.AddedIdentity
          (IdentityOnlyItemsExtension.cut body tail)
    | cutTail (node : IdentityOnlyItemsExtension.AddedIdentity tail) :
        IdentityOnlyItemsExtension.AddedIdentity
          (IdentityOnlyItemsExtension.cut body tail)
    | here
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {source : ItemSeq sourceWires} {targetTail : ItemSeq targetWires}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var targetWires signature}
        {tail : IdentityOnlyItemsExtension ambient source targetTail} :
        IdentityOnlyItemsExtension.AddedIdentity
          (@IdentityOnlyItemsExtension.addIdentity sourceWires targetWires
            ambient source targetTail signature arity ports tail)
    | addedIdentityTail
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {source : ItemSeq sourceWires} {targetTail : ItemSeq targetWires}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var targetWires signature}
        {tail : IdentityOnlyItemsExtension ambient source targetTail}
        (node : IdentityOnlyItemsExtension.AddedIdentity tail) :
        IdentityOnlyItemsExtension.AddedIdentity
          (@IdentityOnlyItemsExtension.addIdentity sourceWires targetWires
            ambient source targetTail signature arity ports tail)
end

mutual
  def IdentityOnlyExtension.AddedIdentity.target
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      IdentityOnlyExtension.AddedIdentity extension →
        Region.IdentityOccurrence target
    | .item node => .item node.target

  def IdentityOnlyItemsExtension.AddedIdentity.target
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      IdentityOnlyItemsExtension.AddedIdentity extension →
        ItemSeq.IdentityOccurrence target
    | .atomTail node => .tail node.target
    | .identityTail node => .tail node.target
    | .cutHead node => .headCut node.target
    | .cutTail node => .tail node.target
    | .here => .head
    | .addedIdentityTail node => .tail node.target
end

mutual
  /-- An identity node retained by the witness. -/
  inductive IdentityOnlyExtension.RetainedIdentity :
      {ambient : WireExtension sourceOuter targetOuter} →
      {source : Region sourceOuter} → {target : Region targetOuter} →
      IdentityOnlyExtension ambient source target → Type
    | item
        {sourceOuter targetOuter sourceLocals targetLocals : List Sig}
        {ambient : WireExtension sourceOuter targetOuter}
        {sourceItems : ItemSeq (sourceOuter ++ sourceLocals)}
        {targetItems : ItemSeq (targetOuter ++ targetLocals)}
        {locals : WireExtension sourceLocals targetLocals}
        {items : IdentityOnlyItemsExtension (ambient.append locals)
          sourceItems targetItems}
        (node : IdentityOnlyItemsExtension.RetainedIdentity items) :
        IdentityOnlyExtension.RetainedIdentity
          (IdentityOnlyExtension.region locals items)

  inductive IdentityOnlyItemsExtension.RetainedIdentity :
      {ambient : WireExtension sourceWires targetWires} →
      {source : ItemSeq sourceWires} → {target : ItemSeq targetWires} →
      IdentityOnlyItemsExtension ambient source target → Type
    | atomTail (node : IdentityOnlyItemsExtension.RetainedIdentity tail) :
        IdentityOnlyItemsExtension.RetainedIdentity
          (IdentityOnlyItemsExtension.atom head ports tail)
    | here : IdentityOnlyItemsExtension.RetainedIdentity
        (IdentityOnlyItemsExtension.identity ports tail)
    | identityTail
        (node : IdentityOnlyItemsExtension.RetainedIdentity tail) :
        IdentityOnlyItemsExtension.RetainedIdentity
          (IdentityOnlyItemsExtension.identity ports tail)
    | cutHead (node : IdentityOnlyExtension.RetainedIdentity body) :
        IdentityOnlyItemsExtension.RetainedIdentity
          (IdentityOnlyItemsExtension.cut body tail)
    | cutTail (node : IdentityOnlyItemsExtension.RetainedIdentity tail) :
        IdentityOnlyItemsExtension.RetainedIdentity
          (IdentityOnlyItemsExtension.cut body tail)
    | addedIdentityTail
        {sourceWires targetWires : List Sig}
        {ambient : WireExtension sourceWires targetWires}
        {source : ItemSeq sourceWires} {targetTail : ItemSeq targetWires}
        {signature : Sig} {arity : Nat}
        {ports : Fin arity → Var targetWires signature}
        {tail : IdentityOnlyItemsExtension ambient source targetTail}
        (node : IdentityOnlyItemsExtension.RetainedIdentity tail) :
        IdentityOnlyItemsExtension.RetainedIdentity
          (@IdentityOnlyItemsExtension.addIdentity sourceWires targetWires
            ambient source targetTail signature arity ports tail)
end

mutual
  def IdentityOnlyExtension.RetainedIdentity.source
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      IdentityOnlyExtension.RetainedIdentity extension →
        Region.IdentityOccurrence source
    | .item node => .item node.source

  def IdentityOnlyItemsExtension.RetainedIdentity.source
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      IdentityOnlyItemsExtension.RetainedIdentity extension →
        ItemSeq.IdentityOccurrence source
    | .atomTail node => .tail node.source
    | .here => .head
    | .identityTail node => .tail node.source
    | .cutHead node => .headCut node.source
    | .cutTail node => .tail node.source
    | .addedIdentityTail node => node.source
end

mutual
  def IdentityOnlyExtension.RetainedIdentity.target
      {sourceOuter targetOuter : List Sig}
      {ambient : WireExtension sourceOuter targetOuter}
      {source : Region sourceOuter} {target : Region targetOuter}
      {extension : IdentityOnlyExtension ambient source target} :
      IdentityOnlyExtension.RetainedIdentity extension →
        Region.IdentityOccurrence target
    | .item node => .item node.target

  def IdentityOnlyItemsExtension.RetainedIdentity.target
      {sourceWires targetWires : List Sig}
      {ambient : WireExtension sourceWires targetWires}
      {source : ItemSeq sourceWires} {target : ItemSeq targetWires}
      {extension : IdentityOnlyItemsExtension ambient source target} :
      IdentityOnlyItemsExtension.RetainedIdentity extension →
        ItemSeq.IdentityOccurrence target
    | .atomTail node => .tail node.target
    | .here => .head
    | .identityTail node => .tail node.target
    | .cutHead node => .headCut node.target
    | .cutTail node => .tail node.target
    | .addedIdentityTail node => .tail node.target
end

/-- The target identity nodes which can carry fresh-wire incidences. -/
inductive IdentityOnlyExtension.AssemblyIdentity
    (extension : IdentityOnlyExtension ambient source target) : Type
  | added (node : extension.AddedIdentity) : AssemblyIdentity extension
  | retained (node : extension.RetainedIdentity) : AssemblyIdentity extension

def IdentityOnlyExtension.AssemblyIdentity.target
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    {extension : IdentityOnlyExtension ambient source target} :
    IdentityOnlyExtension.AssemblyIdentity extension →
      Region.IdentityOccurrence target
  | .added node => node.target
  | .retained node => node.target

/-- An actual target incidence between a fresh wire and an added node. -/
structure IdentityOnlyExtension.AddedIncidence
    {extension : IdentityOnlyExtension ambient source target}
    (wire : extension.FreshWire) (node : extension.AddedIdentity) where
  port : Region.IdentityPortOccurrence target
  node_eq : port.node = node.target
  wire_eq : port.wire = wire.target

/-- An actual target incidence between a fresh wire and a retained node. -/
structure IdentityOnlyExtension.RetainedIncidence
    {extension : IdentityOnlyExtension ambient source target}
    (wire : extension.FreshWire) (node : extension.RetainedIdentity) where
  port : Region.IdentityPortOccurrence target
  node_eq : port.node = node.target
  wire_eq : port.wire = wire.target

/-- Every live incidence is one of the actual dependent projections above. -/
inductive IdentityOnlyExtension.FreshIncidence
    (extension : IdentityOnlyExtension ambient source target) : Type
  | added (wire : extension.FreshWire) (node : extension.AddedIdentity)
      (incidence : extension.AddedIncidence wire node) :
      FreshIncidence extension
  | retained (wire : extension.FreshWire) (node : extension.RetainedIdentity)
      (incidence : extension.RetainedIncidence wire node) :
      FreshIncidence extension

def IdentityOnlyExtension.FreshIncidence.wire
    {extension : IdentityOnlyExtension ambient source target} :
    extension.FreshIncidence → extension.FreshWire
  | .added wire _ _ => wire
  | .retained wire _ _ => wire

def IdentityOnlyExtension.FreshIncidence.node
    {extension : IdentityOnlyExtension ambient source target} :
    extension.FreshIncidence → extension.AssemblyIdentity
  | .added _ node _ => .added node
  | .retained _ node _ => .retained node

/-- An actual target incidence from an added node to a retained source wire. -/
structure IdentityOnlyExtension.RetainedWireIncidence
    {extension : IdentityOnlyExtension ambient source target}
    (wire : extension.RetainedWire) (node : extension.AddedIdentity) where
  port : Region.IdentityPortOccurrence target
  node_eq : port.node = node.target
  wire_eq : port.wire = wire.target

/-- Historical contacts are exact retained syntax, never semantic classes. -/
inductive Region.HistoricalAnchor (source : Region outer) : Type
  | wire (wire : Region.Wire source) : HistoricalAnchor source
  | identity (node : Region.IdentityOccurrence source) : HistoricalAnchor source

inductive IdentityOnlyExtension.AssemblyVertex
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    (extension : IdentityOnlyExtension ambient source target) : Type
  | wire (wire : extension.FreshWire) : AssemblyVertex extension
  | identity (node : extension.AddedIdentity) : AssemblyVertex extension

inductive IdentityOnlyExtension.Adjacent
    {extension : IdentityOnlyExtension ambient source target} :
    extension.AssemblyVertex → extension.AssemblyVertex → Prop
  | forward (incidence : extension.AddedIncidence wire node) :
      Adjacent (.wire wire) (.identity node)
  | backward (incidence : extension.AddedIncidence wire node) :
      Adjacent (.identity node) (.wire wire)

def IdentityOnlyExtension.Connected
    {extension : IdentityOnlyExtension ambient source target}
    (left right : extension.AssemblyVertex) : Prop :=
  left = right ∨ Relation.TransGen extension.Adjacent left right

inductive IdentityOnlyExtension.RetainedContact
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    (extension : IdentityOnlyExtension ambient source target) : Type
  | wire (retained : extension.RetainedWire)
      (node : extension.AddedIdentity)
      (incidence : extension.RetainedWireIncidence retained node) :
      RetainedContact extension
  | identity (wire : extension.FreshWire)
      (node : extension.RetainedIdentity)
      (incidence : extension.RetainedIncidence wire node) :
      RetainedContact extension

def IdentityOnlyExtension.RetainedContact.vertex
    {extension : IdentityOnlyExtension ambient source target} :
    extension.RetainedContact → extension.AssemblyVertex
  | .wire _ node _ => IdentityOnlyExtension.AssemblyVertex.identity node
  | .identity freshWire _ _ =>
      IdentityOnlyExtension.AssemblyVertex.wire freshWire

def IdentityOnlyExtension.RetainedContact.anchor
    {extension : IdentityOnlyExtension ambient source target} :
    extension.RetainedContact → Region.HistoricalAnchor source
  | .wire retainedWire _ _ =>
      Region.HistoricalAnchor.wire retainedWire.source
  | .identity _ node _ => Region.HistoricalAnchor.identity node.source

/-- Each actual assembly component has at most one retained syntactic anchor. -/
def IdentityOnlyExtension.SingleContact
    {extension : IdentityOnlyExtension ambient source target} : Prop :=
  ∀ left right : extension.RetainedContact,
    extension.Connected left.vertex right.vertex →
      left.anchor = right.anchor

def IdentityOnlyExtension.AddedIdentity.HasWireContact
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    {extension : IdentityOnlyExtension ambient source target}
    (node : extension.AddedIdentity) : Prop :=
  ∃ wire : extension.RetainedWire,
    Nonempty (extension.RetainedWireIncidence wire node)

/-- The live carrier of every incidence during historical absorption. -/
structure IdentityOnlyExtension.AbsorptionState
    (extension : IdentityOnlyExtension ambient source target) where
  live : extension.FreshWire → Prop
  carrier : extension.FreshIncidence → Option extension.FreshWire
  carrier_live : ∀ incidence wire,
    carrier incidence = some wire → live wire

def IdentityOnlyExtension.initialState
    (extension : IdentityOnlyExtension ambient source target) :
    extension.AbsorptionState where
  live := fun _ => True
  carrier := fun incidence => some incidence.wire
  carrier_live := by simp

def IdentityOnlyExtension.AbsorptionState.ActiveAt
    {extension : IdentityOnlyExtension ambient source target}
    (state : extension.AbsorptionState) (wire : extension.FreshWire)
    (node : extension.AssemblyIdentity) : Prop :=
  ∃ incidence : extension.FreshIncidence,
    state.carrier incidence = some wire ∧ incidence.node = node

def IdentityOnlyExtension.AbsorptionState.RemoveLive
    {extension : IdentityOnlyExtension ambient source target}
    (before after : extension.AbsorptionState)
    (wire : extension.FreshWire) : Prop :=
  ¬after.live wire ∧
    ∀ other, other ≠ wire → (after.live other ↔ before.live other)

def IdentityOnlyExtension.AbsorptionState.PreservesOtherCarriers
    {extension : IdentityOnlyExtension ambient source target}
    (before after : extension.AbsorptionState)
    (wire : extension.FreshWire) : Prop :=
  ∀ incidence, before.carrier incidence ≠ some wire →
    after.carrier incidence = before.carrier incidence

def RegionPath.Encloses (ancestor descendant : RegionPath) : Prop :=
  ∃ suffix, descendant = ancestor ++ suffix

/-- The destination of an equated absorption. -/
inductive IdentityOnlyExtension.AbsorptionDestination
    (extension : IdentityOnlyExtension ambient source target) : Type
  | contact : AbsorptionDestination extension
  | wire (survivor : extension.FreshWire) : AbsorptionDestination extension

def IdentityOnlyExtension.AbsorptionDestination.carrier
    {extension : IdentityOnlyExtension ambient source target} :
    extension.AbsorptionDestination → Option extension.FreshWire
  | .contact => none
  | .wire survivor => some survivor

/-- Exactly the historical bare and equated absorption moves. -/
inductive IdentityOnlyExtension.AbsorptionMove
    {sourceOuter targetOuter : List Sig}
    {ambient : WireExtension sourceOuter targetOuter}
    {source : Region sourceOuter} {target : Region targetOuter}
    {extension : IdentityOnlyExtension ambient source target} :
    extension.AbsorptionState → extension.AbsorptionState → Prop
  | bare (wire : extension.FreshWire)
      (live : before.live wire)
      (exclusive : ∀ incidence,
        before.carrier incidence = some wire →
          ∃ node : extension.AddedIdentity,
            incidence.node = .added node ∧
            ¬node.HasWireContact ∧
            ∀ other, other ≠ wire →
              ¬before.ActiveAt other (.added node))
      (removeLive : before.RemoveLive after wire)
      (drop : ∀ incidence, before.carrier incidence = some wire →
        after.carrier incidence = none)
      (preserve : before.PreservesOtherCarriers after wire) :
      AbsorptionMove before after
  | equated (wire : extension.FreshWire)
      (live : before.live wire)
      (candidate : extension.FreshIncidence)
      (candidateActive : before.carrier candidate = some wire)
      (destination : extension.AbsorptionDestination)
      (destinationValid : match destination with
        | .contact =>
            (∃ node, candidate.node = .retained node) ∨
            ∃ node, candidate.node = .added node ∧ node.HasWireContact
        | .wire survivor =>
            survivor ≠ wire ∧ before.live survivor ∧
            ∃ node, candidate.node = .added node ∧
              ¬node.HasWireContact ∧
              before.ActiveAt survivor (.added node))
      (underEquality : ∀ incidence,
        before.carrier incidence = some wire →
        incidence.node ≠ candidate.node →
          RegionPath.Encloses candidate.node.target.path
            incidence.node.target.path)
      (removeLive : before.RemoveLive after wire)
      (dropEquality : ∀ incidence,
        before.carrier incidence = some wire →
        incidence.node = candidate.node →
          after.carrier incidence = none)
      (transfer : ∀ incidence,
        before.carrier incidence = some wire →
        incidence.node ≠ candidate.node →
          after.carrier incidence = destination.carrier)
      (preserve : before.PreservesOtherCarriers after wire) :
      AbsorptionMove before after

/-- Existential finite reachability to a state with no live fresh wire. -/
def IdentityOnlyExtension.Absorbable
    (extension : IdentityOnlyExtension ambient source target) : Prop :=
  ∃ final : extension.AbsorptionState,
    (extension.initialState = final ∨
      Relation.TransGen extension.AbsorptionMove
        extension.initialState final) ∧
    ∀ wire, ¬final.live wire

end WholeAssemblyVacuity

open WholeAssemblyVacuity

/-- One accepted identity-only assembly extension. -/
def VacuousExtension {wires : List Sig}
    (source target : Region wires) : Prop :=
  ∃ extension : IdentityOnlyExtension (WireExtension.refl wires) source target,
    extension.SingleContact ∧ extension.Absorbable

/-- Symmetric whole-assembly vacuity, lifted through one recursive context. -/
def WholeAssemblyVacuity : Rule :=
  Contextual (symmetric VacuousExtension)

end VisualProof.Rule
