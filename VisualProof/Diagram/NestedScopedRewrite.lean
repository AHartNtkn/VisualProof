import VisualProof.Diagram.NestedOccurrence
import VisualProof.Diagram.ScopedRewrite

namespace VisualProof.Diagram

open VisualProof.Theory

private inductive Var.AppendView (left right : List Sig) :
    {signature : Sig} → Var (left ++ right) signature → Type
  | fromLeft (wire : Var left signature) :
      AppendView left right (wire.appendLeft right)
  | fromRight (wire : Var right signature) :
      AppendView left right (Var.appendRight left wire)

private def Var.appendView (left right : List Sig) :
    {signature : Sig} → (wire : Var (left ++ right) signature) →
      Var.AppendView left right wire :=
  match left with
  | [] => fun wire => .fromRight wire
  | _ :: tail => fun wire =>
      match wire with
      | .here => .fromLeft .here
      | .there rest =>
          match Var.appendView tail right rest with
          | .fromLeft inherited => .fromLeft (.there inherited)
          | .fromRight localWire => .fromRight localWire

def RegionPath.shiftRoot (offset : Nat) : RegionPath → RegionPath
  | [] => []
  | item :: rest => (offset + item) :: rest

namespace NestedOccurrence

private def anchorMaterial (occurrence : NestedOccurrence source)
    (body : Region occurrence.descendantWires) :
    Region (occurrence.ancestorWires ++ occurrence.anchorLocals) :=
  occurrence.selected.conjoin (occurrence.descendant.fill body)

private def anchorRegion (occurrence : NestedOccurrence source)
    (body : Region occurrence.descendantWires) :
    Region occurrence.ancestorWires :=
  Region.adjoinAt occurrence.anchorLocals .nil
    (occurrence.anchorMaterial body)

def anchorSite (occurrence : NestedOccurrence source)
    (body : Region occurrence.descendantWires) :
    ScopedRegion (occurrence.targetBody body) := {
  wires := occurrence.ancestorWires
  body := occurrence.anchorRegion body
  context := occurrence.outer
  root_eq := rfl
}

/-- Stable whole-body address of a wire visible where the selected ancestor
lives. -/
def anchorAddress (occurrence : NestedOccurrence source)
    (body : Region occurrence.descendantWires)
    (wire : Var (occurrence.ancestorWires ++ occurrence.anchorLocals)
      signature) : WireAddress :=
  match Var.appendView occurrence.ancestorWires occurrence.anchorLocals wire with
  | .fromLeft inherited =>
      (occurrence.anchorSite body).visibleAddress inherited
  | .fromRight localWire =>
      .internal occurrence.outer.holePath localWire.index.val

private def embeddedDescendantOwner (occurrence : NestedOccurrence source)
    (owner : RegionPath) : RegionPath :=
  occurrence.outer.holePath ++
    (occurrence.descendant.holePath ++ owner).shiftRoot
      occurrence.selected.items.length

private def embeddedFilledOwner (occurrence : NestedOccurrence source)
    (owner : RegionPath) : RegionPath :=
  occurrence.outer.holePath ++
    owner.shiftRoot occurrence.selected.items.length

private def descendantWireAddress (occurrence : NestedOccurrence source)
    (wire : Var occurrence.descendantWires signature) : WireAddress :=
  match occurrence.descendant.classifyHoleWire occurrence.before wire with
  | .inl anchorWire => occurrence.anchorAddress occurrence.before anchorWire
  | .inr internal =>
      .internal (occurrence.embeddedFilledOwner internal.ownerAddress.1)
        internal.ownerAddress.2

/-- Compose an exact item-wire address from a site inside `before` through
the descendant frame, same-region selected prefix, and outer frame. -/
def nestedItemAddress (occurrence : NestedOccurrence source)
    (site : ScopedRegion occurrence.before)
    (wire : Var (site.wires ++ site.body.locals) signature) : WireAddress :=
  match Var.appendView site.wires site.body.locals wire with
  | .fromLeft visible =>
      match site.visibleWire visible with
      | .inl descendantWire => occurrence.descendantWireAddress descendantWire
      | .inr internal =>
          .internal (occurrence.embeddedDescendantOwner
            internal.ownerAddress.1) internal.ownerAddress.2
  | .fromRight localWire =>
      .internal (occurrence.embeddedDescendantOwner site.path)
        localWire.index.val

def beforePath (occurrence : NestedOccurrence source) : RegionPath :=
  occurrence.embeddedDescendantOwner []

def nestedSitePath (occurrence : NestedOccurrence source)
    (site : ScopedRegion occurrence.before) : RegionPath :=
  occurrence.embeddedDescendantOwner site.path

def nestedEndpointAddress (occurrence : NestedOccurrence source)
    (site : ScopedRegion occurrence.before)
    {wire : Var (site.wires ++ site.body.locals) signature}
    (port : ItemSeq.Port site.body.items wire) : EndpointAddress :=
  let localAddress := site.endpointAddress port
  { localAddress with
    region := occurrence.embeddedDescendantOwner localAddress.region }

/-- One proof-relevant multi-site rewrite rooted at an exact descendant site.
The indexed primary replacement rebuilds the descendant through its existing
context. Completion sites are then validated against each current whole-body
intermediate and are ordered no shallower-to-deeper than the primary site. -/
structure ScopedRewrite (occurrence : NestedOccurrence source)
    (primarySite : ScopedRegion occurrence.before)
    (primaryAfter : Region primarySite.wires) where
  targetBody : Region occurrence.interface.external
  completion : CompletionPlan (occurrence.nestedSitePath primarySite).length
    (occurrence.targetBody (primarySite.replace primaryAfter)) targetBody

def ScopedRewrite.primaryReplacement
    (_rewrite : ScopedRewrite occurrence primarySite primaryAfter) :
    ScopedReplacement occurrence.before
      (primarySite.replace primaryAfter) := {
  site := primarySite
  after := primaryAfter
  target_eq := rfl
}

end NestedOccurrence

end VisualProof.Diagram
