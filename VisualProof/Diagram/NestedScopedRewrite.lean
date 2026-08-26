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

private theorem Var.appendView_appendRight
    (left right : List Sig) (wire : Var right signature) :
    Var.appendView left right (Var.appendRight left wire) = .fromRight wire := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [Var.appendRight, Var.appendView, induction]

def RegionPath.shiftRoot (offset : Nat) : RegionPath → RegionPath
  | [] => []
  | item :: rest => (offset + item) :: rest

namespace DiagramContext

private def ItemSeq.renameWires_length
    (items : ItemSeq sourceWires)
    (rename : WireRenaming sourceWires targetWires) :
    (items.renameWires rename).length = items.length :=
  match items with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ (ItemSeq.renameWires_length tail rename)

/-- The exact recursive extension of a descendant context by one wire owned
at an ancestor. Every existing frame item is retained through the inherited
wire embedding, while the distinguished wire stays inherited through every
cut down to the selected descendant. -/
structure WireExtension
    (context : DiagramContext targetOuter targetWires)
    (sourceOuter : List Sig)
    (outerRetain : WireRenaming targetOuter sourceOuter)
    (outerWire : Var sourceOuter signature) where
  sourceWires : List Sig
  source : DiagramContext sourceOuter sourceWires
  retain : WireRenaming targetWires sourceWires
  wire : Var sourceWires signature

def extendWire
    (context : DiagramContext targetOuter targetWires)
    (sourceOuter : List Sig)
    (outerRetain : WireRenaming targetOuter sourceOuter)
    (outerWire : Var sourceOuter signature) :
    WireExtension context sourceOuter outerRetain outerWire :=
  match context with
  | .hole => {
      sourceWires := sourceOuter
      source := .hole
      retain := outerRetain
      wire := outerWire
    }
  | .cut locals before after child =>
      let childExtension := child.extendWire (sourceOuter ++ locals)
        (outerRetain.appendRight locals) (outerWire.appendLeft locals)
      {
        sourceWires := childExtension.sourceWires
        source := .cut locals
          (before.renameWires (outerRetain.appendRight locals))
          (after.renameWires (outerRetain.appendRight locals))
          childExtension.source
        retain := childExtension.retain
        wire := childExtension.wire
      }

/-- Extending a recursive context by an inherited ancestor wire preserves the
exact selected descendant region address. -/
theorem extendWire_source_holePath
    (context : DiagramContext targetOuter targetWires)
    (sourceOuter : List Sig)
    (outerRetain : WireRenaming targetOuter sourceOuter)
    (outerWire : Var sourceOuter signature) :
    (context.extendWire sourceOuter outerRetain outerWire).source.holePath =
      context.holePath := by
  induction context generalizing sourceOuter with
  | hole => rfl
  | cut locals before after child induction =>
      simp only [extendWire, holePath]
      rw [ItemSeq.renameWires_length]
      exact congrArg (List.cons before.length)
        (induction (sourceOuter := sourceOuter ++ locals)
          (outerRetain.appendRight locals) (outerWire.appendLeft locals))

end DiagramContext

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

private def descendantRootLocalIndex (occurrence : NestedOccurrence source)
    (index : Nat) : Nat :=
  occurrence.anchorLocals.length + occurrence.selected.locals.length + index

private def embeddedFilledAddress (occurrence : NestedOccurrence source)
    (owner : RegionPath) (index : Nat) : WireAddress :=
  match owner with
  | [] => .internal occurrence.outer.holePath
      (occurrence.descendantRootLocalIndex index)
  | _ :: _ => .internal (occurrence.embeddedFilledOwner owner) index

private def embeddedDescendantAddress (occurrence : NestedOccurrence source)
    (owner : RegionPath) (index : Nat) : WireAddress :=
  match occurrence.descendant.holePath ++ owner with
  | [] => .internal occurrence.outer.holePath
      (occurrence.descendantRootLocalIndex index)
  | relativeOwner@(_ :: _) =>
      .internal
        (occurrence.outer.holePath ++
          relativeOwner.shiftRoot occurrence.selected.items.length)
        index

def descendantWireAddress (occurrence : NestedOccurrence source)
    (wire : Var occurrence.descendantWires signature) : WireAddress :=
  match occurrence.descendant.classifyHoleWire occurrence.before wire with
  | .inl anchorWire => occurrence.anchorAddress occurrence.before anchorWire
  | .inr internal =>
      occurrence.embeddedFilledAddress internal.ownerAddress.1
        internal.ownerAddress.2

/-- A descendant-context wire owned at the combined anchor root is indexed
after the anchor and selected-region local prefixes. -/
theorem descendantWireAddress_internal_root
    (occurrence : NestedOccurrence source)
    (wire : Var occurrence.descendantWires signature)
    (internal : Region.InternalWire
      (occurrence.descendant.fill occurrence.before) signature)
    (classified : occurrence.descendant.classifyHoleWire occurrence.before
      wire = .inr internal)
    (ownerRoot : internal.ownerAddress.1 = []) :
    occurrence.descendantWireAddress wire =
      .internal occurrence.outer.holePath
        (occurrence.anchorLocals.length +
          occurrence.selected.locals.length + internal.ownerAddress.2) := by
  unfold descendantWireAddress
  rw [classified]
  unfold embeddedFilledAddress descendantRootLocalIndex
  simp [ownerRoot]

/-- A descendant-context wire owned by an actual cut retains its cut-local
index; embedding changes only its global owner path. -/
theorem descendantWireAddress_internal_cut
    (occurrence : NestedOccurrence source)
    (wire : Var occurrence.descendantWires signature)
    (internal : Region.InternalWire
      (occurrence.descendant.fill occurrence.before) signature)
    (classified : occurrence.descendant.classifyHoleWire occurrence.before
      wire = .inr internal)
    (head : Nat) (tail : RegionPath)
    (ownerCut : internal.ownerAddress.1 = head :: tail) :
    occurrence.descendantWireAddress wire =
      .internal
        (occurrence.outer.holePath ++
          RegionPath.shiftRoot occurrence.selected.items.length
            (head :: tail))
        internal.ownerAddress.2 := by
  unfold descendantWireAddress
  rw [classified]
  unfold embeddedFilledAddress embeddedFilledOwner
  simp [ownerCut]

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
          occurrence.embeddedDescendantAddress internal.ownerAddress.1
            internal.ownerAddress.2
  | .fromRight localWire =>
      occurrence.embeddedDescendantAddress site.path localWire.index.val

/-- A local owned at the combined descendant root follows the anchor locals
and the selected ancestor's locals in the authoritative root context. -/
theorem nestedItemAddress_local_root
    (occurrence : NestedOccurrence source)
    (site : ScopedRegion occurrence.before)
    (localWire : Var site.body.locals signature)
    (descendantRoot : occurrence.descendant.holePath = [])
    (siteRoot : site.path = []) :
    occurrence.nestedItemAddress site
        (Var.appendRight site.wires localWire) =
      .internal occurrence.outer.holePath
        (occurrence.anchorLocals.length +
          occurrence.selected.locals.length + localWire.index.val) := by
  unfold nestedItemAddress
  rw [Var.appendView_appendRight]
  unfold embeddedDescendantAddress descendantRootLocalIndex
  rw [siteRoot, descendantRoot]
  simp

/-- A local owned by an actual descendant cut retains its cut-local index;
only its owner path crosses the same-region selected-item prefix. -/
theorem nestedItemAddress_local_cut
    (occurrence : NestedOccurrence source)
    (site : ScopedRegion occurrence.before)
    (localWire : Var site.body.locals signature)
    (head : Nat) (tail : RegionPath)
    (owner : occurrence.descendant.holePath ++ site.path = head :: tail) :
    occurrence.nestedItemAddress site
        (Var.appendRight site.wires localWire) =
      .internal
        (occurrence.outer.holePath ++
          RegionPath.shiftRoot occurrence.selected.items.length
            (head :: tail))
        localWire.index.val := by
  unfold nestedItemAddress
  rw [Var.appendView_appendRight]
  unfold embeddedDescendantAddress
  rw [owner]

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
