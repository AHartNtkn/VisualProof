import VisualProof.Diagram.Boundary
import VisualProof.Diagram.Context
import VisualProof.Diagram.PortPartition

namespace VisualProof.Diagram

open VisualProof.Theory


/-- Stable identity of a wire in recursive syntax. External wires are indexed
at the open boundary; internal wires are indexed by their owner-region path and
their position in that region's local context. -/
inductive WireAddress where
  | external (index : Nat)
  | internal (owner : RegionPath) (index : Nat)
  deriving DecidableEq, BEq

inductive PortLabel where
  | atomHead
  | atomArgument (index : Nat)
  | identity (index : Nat)
  | termOutput
  | termPort (index : Nat)
  deriving DecidableEq

structure EndpointAddress where
  region : RegionPath
  item : Nat
  port : PortLabel
  deriving DecidableEq

def EndpointAddress.under (ancestor : RegionPath)
    (address : EndpointAddress) : EndpointAddress :=
  { address with region := ancestor ++ address.region }

mutual
  def Region.Port.endpointAddress
      {region : Region outer} {wire : Var outer signature}
      (port : Region.Port region wire) : EndpointAddress :=
    match port with
    | .item itemPort => itemPort.endpointAddressFrom 0

  def ItemSeq.Port.endpointAddressFrom
      {items : ItemSeq wires} {wire : Var wires signature}
      (port : ItemSeq.Port items wire) (itemIndex : Nat) : EndpointAddress :=
    match port with
    | .head itemPort => itemPort.endpointAddressAt itemIndex
    | .tail tailPort => tailPort.endpointAddressFrom (itemIndex + 1)

  def Item.Port.endpointAddressAt
      {item : Item wires} {wire : Var wires signature}
      (port : Item.Port item wire) (itemIndex : Nat) : EndpointAddress :=
    match port with
    | .atomHead => ⟨[], itemIndex, .atomHead⟩
    | .atomArgument argument =>
        ⟨[], itemIndex, .atomArgument argument.val⟩
    | @Item.Port.identity identityWires identitySignature identityArity
        identityPorts argument =>
        ⟨[], itemIndex, PortLabel.identity argument.val⟩
    | .termOutput => ⟨[], itemIndex, .termOutput⟩
    | @Item.Port.termPort termWires termOutput termArity termPorts term slot =>
        ⟨[], itemIndex, .termPort slot.val⟩
    | .cut nested =>
        (nested.endpointAddress).under [itemIndex]
end

mutual
  def Region.InternalWire.ownerAddress :
      {region : Region outer} → Region.InternalWire region signature →
        RegionPath × Nat
    | _, .here wire => ([], wire.index.val)
    | _, .nested wire => wire.ownerAddressFrom 0

  def ItemSeq.InternalWire.ownerAddressFrom :
      {items : ItemSeq wires} → ItemSeq.InternalWire items signature → Nat →
        RegionPath × Nat
    | _, .headCut wire, itemIndex =>
        (itemIndex :: wire.ownerAddress.1, wire.ownerAddress.2)
    | _, .tail wire, itemIndex => wire.ownerAddressFrom (itemIndex + 1)
end

def Region.InternalWire.address
    (wire : Region.InternalWire region signature) : WireAddress :=
  .internal wire.ownerAddress.1 wire.ownerAddress.2

def OpenDiagram.Wire.address
    (wire : OpenDiagram.Wire diagram signature) : WireAddress :=
  match wire with
  | OpenDiagram.Wire.external externalWire =>
      .external externalWire.index.val
  | OpenDiagram.Wire.internal internalWire => internalWire.address

private def ItemSeq.cutBodyAt? : ItemSeq wires → Nat → Option (Region wires)
  | .nil, _ => none
  | .cons head _, 0 =>
      match head with
      | .cut body => some body
      | _ => none
  | .cons _ tail, index + 1 => tail.cutBodyAt? index

private def Region.internalIncidencePathsAt :
    (region : Region outer) → RegionPath → Nat → List RegionPath
  | .mk _ items, [], localIndex =>
      items.incidencePaths (outer.length + localIndex) 0
  | .mk _ items, itemIndex :: rest, localIndex =>
      match items.cutBodyAt? itemIndex with
      | none => []
      | some body =>
          (body.internalIncidencePathsAt rest localIndex).map
            (List.cons itemIndex)

/-- Actual incidences of one stable address in a raw recursive region. Invalid
addresses totalize to the empty list; rule witnesses separately prove their
addresses by constructing the corresponding scoped wire. -/
def Region.incidencePathsAtAddress (region : Region outer) :
    WireAddress → List RegionPath
  | .external index => region.incidencePaths index
  | .internal owner index => region.internalIncidencePathsAt owner index

namespace DiagramContext

/-- The exact region address selected by a one-hole context. -/
def holePath : DiagramContext outer holeWires → RegionPath
  | .hole => []
  | .cut _ before _ child => before.length :: child.holePath

private def ItemSeq.embedCutInternal
    (before after : ItemSeq wires) {body : Region wires}
    (wire : Region.InternalWire body signature) :
    ItemSeq.InternalWire (before.append (.cons (.cut body) after)) signature :=
  match before with
  | .nil => .headCut wire
  | .cons _ tail => .tail (ItemSeq.embedCutInternal tail after wire)

private def embedChildInternal
    (locals : List Sig) (before after : ItemSeq (outer ++ locals))
    (child : DiagramContext (outer ++ locals) holeWires)
    {body : Region holeWires}
    (wire : Region.InternalWire (child.fill body) signature) :
    Region.InternalWire
      ((DiagramContext.cut locals before after child).fill body) signature :=
  .nested (ItemSeq.embedCutInternal before after wire)

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

/-- Classify a wire visible at a selected region as either inherited from the
root context or introduced at one exact enclosing region. -/
def classifyHoleWire :
    (context : DiagramContext outer holeWires) →
    (body : Region holeWires) →
    {signature : Sig} → Var holeWires signature →
      Sum (Var outer signature)
        (Region.InternalWire (context.fill body) signature)
  | .hole, _, _, wire => .inl wire
  | .cut locals before after child, body, _, wire =>
      match child.classifyHoleWire body wire with
      | .inr internal =>
          .inr (embedChildInternal locals before after child internal)
      | .inl visible =>
          match appendView outer locals visible with
          | .fromLeft inherited => .inl inherited
          | .fromRight localWire => .inr (.here localWire)

end DiagramContext

/-- A proof-relevant valid address of one region inside an existing recursive
region. The equality is the address-validity certificate; replacement rebuilds
the root through the original one-hole context. -/
structure ScopedRegion (root : Region outer) where
  wires : List Sig
  body : Region wires
  context : DiagramContext outer wires
  root_eq : context.fill body = root

namespace ScopedRegion

def path {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root) : RegionPath := site.context.holePath

def replace {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root) (after : Region site.wires) :
    Region outer := site.context.fill after

private def castInternal {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root)
    (wire : Region.InternalWire (site.context.fill site.body) signature) :
    Region.InternalWire root signature := by
  rw [site.root_eq] at wire
  exact wire

def visibleWire {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root)
    (wire : Var site.wires signature) :
    Sum (Var outer signature) (Region.InternalWire root signature) :=
  match site.context.classifyHoleWire site.body wire with
  | .inl inherited => .inl inherited
  | .inr internal => .inr (site.castInternal internal)

def visibleAddress {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root)
    (wire : Var site.wires signature) : WireAddress :=
  match site.visibleWire wire with
  | Sum.inl inherited => .external inherited.index.val
  | Sum.inr internal => internal.address

/-- Address a wire used by an item in the selected region, including a wire
owned by that region's local context. -/
def itemAddress {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root)
    (wire : Var (site.wires ++ site.body.locals) signature) : WireAddress :=
  match DiagramContext.appendView site.wires site.body.locals wire with
  | .fromLeft visible => site.visibleAddress visible
  | .fromRight localWire => .internal site.path localWire.index.val

def endpointAddress {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root)
    {wire : Var (site.wires ++ site.body.locals) signature}
    (port : ItemSeq.Port site.body.items wire) : EndpointAddress :=
  (port.endpointAddressFrom 0).under site.path

theorem replace_self {outer : List Sig} {root : Region outer}
    (site : ScopedRegion root) :
    site.replace site.body = root := site.root_eq

end ScopedRegion

/-- One scoped replacement in a raw recursive region. Raw regions admit the
temporary one-ended intermediates needed by an enclosing exact nested rewrite;
only the final open diagram is required to be canonical and two-ended. -/
structure ScopedReplacement (source target : Region outer) where
  site : ScopedRegion source
  after : Region site.wires
  target_eq : site.replace after = target

/-- One exact `completeWireEnds` request, using a stable wire address and the
derived scope retained from the source diagram. -/
structure CompletionRequirement where
  address : WireAddress
  scope : RegionPath
  deriving DecidableEq, BEq

def completionCount (root : Region outer)
    (requirement : CompletionRequirement) : Nat :=
  let paths := root.incidencePathsAtAddress requirement.address
  max
    (if RegionPath.deepestCommonAncestor paths = requirement.scope then 0 else 1)
    (2 - paths.length)

private def insertCompletion
    (requirement : CompletionRequirement) :
    List CompletionRequirement → List CompletionRequirement
  | [] => [requirement]
  | head :: tail =>
      if head.scope.length ≤ requirement.scope.length
      then requirement :: head :: tail
      else head :: insertCompletion requirement tail

private def orderCompletions :
    List CompletionRequirement → List CompletionRequirement
  | [] => []
  | head :: tail => insertCompletion head (orderCompletions tail)

def requiredCompletions (root : Region outer)
    (requirements : List CompletionRequirement) :
    List CompletionRequirement :=
  orderCompletions <| requirements.flatMap fun requirement =>
    List.replicate (completionCount root requirement) requirement

namespace CompletionPin

structure Description (source target : Region outer) where
  siteWires : List Sig
  context : DiagramContext outer siteWires
  locals : List Sig
  items : ItemSeq (siteWires ++ locals)
  signature : Sig
  wire : Var (siteWires ++ locals) signature
  requirement : CompletionRequirement
  source_eq : context.fill (.mk locals items) = source
  address_eq :
    (ScopedRegion.itemAddress {
      wires := siteWires
      body := .mk locals items
      context := context
      root_eq := source_eq
    } wire) = requirement.address
  scope_eq : context.holePath = requirement.scope
  target_eq : context.fill (.mk locals
    (items.append (.cons (.identity signature 1 (fun _ => wire)) .nil))) =
      target

def Description.site (description : Description source target) :
    ScopedRegion source := {
  wires := description.siteWires
  body := .mk description.locals description.items
  context := description.context
  root_eq := description.source_eq
}

end CompletionPin

/-- Exact deepest-first insertion sequence emitted by `completeWireEnds`. -/
inductive CompletionPlan : Nat → Region outer → Region outer → Type
  | done (region : Region outer) : CompletionPlan maximum region region
  | step {source middle target : Region outer}
      (pin : CompletionPin.Description source middle)
      (scopeEncloses : ∀ path,
        path ∈ source.incidencePathsAtAddress pin.requirement.address →
          pin.requirement.scope.IsPrefix path)
      (atMost : pin.requirement.scope.length ≤ maximum)
      (rest : CompletionPlan pin.requirement.scope.length middle target) :
      CompletionPlan maximum source target

def CompletionPlan.requirements :
    CompletionPlan maximum source target → List CompletionRequirement
  | .done _ => []
  | .step pin _ _ rest => pin.requirement :: rest.requirements

end VisualProof.Diagram
