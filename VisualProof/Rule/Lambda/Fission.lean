import VisualProof.Diagram.Algebra
import VisualProof.Diagram.NestedScopedRewrite
import VisualProof.Lambda.Substitute
import VisualProof.Rule.Relation

namespace VisualProof.Rule.Lambda

open Diagram
open Theory

namespace Fission

/-- A structural path to a subterm occurrence selected for fission. -/
inductive PathSegment
  | fn
  | arg
  | body
  deriving DecidableEq, Repr

/-- Exact capture-avoiding replacement of one bound-closed subterm by the
last free slot.  The selected term is intrinsically closed with respect to
every binder crossed by `path`; untouched siblings retain their native free
slots through `Fin.castSucc`. -/
inductive At (selected : VisualProof.Lambda.Term 0 (Fin arity)) :
    {bound : Nat} → VisualProof.Lambda.Term bound (Fin arity) →
      List PathSegment →
      VisualProof.Lambda.Term bound (Fin (arity + 1)) → Prop
  | root : At selected (selected.renameBound Fin.elim0) []
      (.port (Fin.last arity))
  | body : At selected body path residual →
      At selected (.lam body) (.body :: path) (.lam residual)
  | fn : At selected fn path residual →
      At selected (.app fn argument) (.fn :: path)
        (.app residual (argument.mapFree Fin.castSucc))
  | arg : At selected argument path residual →
      At selected (.app fn argument) (.arg :: path)
        (.app (fn.mapFree Fin.castSucc) residual)

/-- Substitution that fuses the appended bridge slot back to the extracted
term and leaves every native slot unchanged. -/
def bridgeSubstitution
    (selected : VisualProof.Lambda.Term 0 (Fin arity)) :
    Fin (arity + 1) → VisualProof.Lambda.Term 0 (Fin arity) :=
  Fin.lastCases selected (fun slot => .port slot)

/-- Exact source-indexed fission data. `pathEvidence` fixes the selected
occurrence, while `reconstruct` is the capture-avoiding fusion certificate
used by the semantic proof. -/
structure Description (outer : List Sig) where
  locals : List Sig
  arity : Nat
  whole : VisualProof.Lambda.Term 0 (Fin arity)
  selected : VisualProof.Lambda.Term 0 (Fin arity)
  residual : VisualProof.Lambda.Term 0 (Fin (arity + 1))
  path : List PathSegment
  pathEvidence : At selected whole path residual
  reconstruct : residual.bindFree (bridgeSubstitution selected) = whole
  output : Var (outer ++ locals) .iota
  ports : Fin arity → Var (outer ++ locals) .iota
  rest : ItemSeq (outer ++ locals)

def Description.retain (description : Description outer) :
    WireRenaming (outer ++ description.locals)
      (outer ++ (description.locals ++ [.iota])) :=
  Region.adjoinHostWire outer description.locals [.iota]

def Description.bridge (description : Description outer) :
    Var (outer ++ (description.locals ++ [.iota])) .iota :=
  Var.appendRight outer (Var.appendRight description.locals .here)

def Description.residualPorts (description : Description outer) :
    Fin (description.arity + 1) →
      Var (outer ++ (description.locals ++ [.iota])) .iota :=
  Fin.lastCases description.bridge
    (fun slot => description.retain (description.ports slot))

def Description.source (description : Description outer) : Region outer :=
  .mk description.locals
    (.cons (.term description.output description.arity description.ports
      description.whole) description.rest)

def Description.target (description : Description outer) : Region outer :=
  .mk (description.locals ++ [.iota])
    (.cons
      (.term (description.retain description.output)
        (description.arity + 1) description.residualPorts
        description.residual)
      (.cons
        (.term description.bridge description.arity
          (fun slot => description.retain (description.ports slot))
          description.selected)
        (description.rest.renameWires description.retain)))

inductive Local : LocalRule
  | split (description : Description outer) :
      Local description.source description.target

structure OpenDescription (source : OpenDiagram boundary) where
  outer : List Sig
  primary : Description outer
  occurrence : Occurrence primary.source source
  targetCanonical : (occurrence.context.fill primary.target).Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire
      (occurrence.context.fill primary.target)

def OpenDescription.target {boundary : List Sig}
    {source : OpenDiagram boundary} (description : OpenDescription source) :
    OpenDiagram boundary :=
  description.occurrence.interface.withBody
    (description.occurrence.context.fill description.primary.target)
    description.targetCanonical description.targetExternalTwoEnded

end Fission

/-- Extract one exact bound-closed subterm onto a fresh producer and a fresh
binary bridge at the producer's derived scope. -/
inductive Fission : Rule
  | split (canonicalSource : OpenDiagram boundary)
      (description : Fission.OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource)
      (targetIso : OpenDiagramIso description.target target) :
      Fission source target

theorem Fission.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Fission source target)
    (targetIso : OpenDiagramIso target target') :
    Fission source' target' := by
  cases step with
  | split canonicalSource description toCanonical fromCanonical =>
      exact .split canonicalSource description
        (sourceIso.symm.trans toCanonical) (fromCanonical.trans targetIso)

namespace Fusion

private def removeAt : List α → Nat → List α
  | [], _ => []
  | _ :: tail, 0 => tail
  | head :: tail, index + 1 => head :: removeAt tail index

private def insertPhysical [DecidableEq α] (carriers : List α)
    (wire : α) : List α :=
  if wire ∈ carriers then carriers else carriers ++ [wire]

/-- The exact consumer-first carrier order built by TypeScript before producer
slots are folded through first physical-wire occurrence. -/
def carrierWires [DecidableEq α]
    (consumerNative : Fin consumerArity → α)
    (producerNative : Fin producerArity → α)
    (consumed : Fin consumerArity) : List α :=
  (List.ofFn producerNative).foldl insertPhysical
    (removeAt (List.ofFn consumerNative) consumed.val)

private def firstPhysicalIndex [DecidableEq α]
    (wire : α) : List α → Nat
  | [] => 0
  | head :: tail => if wire = head then 0 else firstPhysicalIndex wire tail + 1

private def consumerCarrierIndex (consumed slot : Fin consumerArity) : Nat :=
  if slot.val < consumed.val then slot.val else slot.val - 1

private def producerCarrierIndex [DecidableEq α]
    (consumerNative : Fin consumerArity → α)
    (producerNative : Fin producerArity → α)
    (consumed : Fin consumerArity) (carriers : List α)
    (slot : Fin producerArity) : Nat :=
  if valid : slot.val < consumerArity then
    let consumerSlot : Fin consumerArity := ⟨slot.val, valid⟩
    if consumerSlot ≠ consumed ∧
        consumerNative consumerSlot = producerNative slot
    then consumerCarrierIndex consumed consumerSlot
    else firstPhysicalIndex (producerNative slot) carriers
  else firstPhysicalIndex (producerNative slot) carriers

/-- Rebase one exact region path through a recursive rewrite. Paths inside the
rewritten descendant keep their suffix under the target descendant address;
paths at or above the selected ancestor remain unchanged. -/
def rebaseScope (sourcePrefix targetPrefix path : RegionPath) : RegionPath :=
  if sourcePrefix.IsPrefix path
  then targetPrefix ++ path.drop sourcePrefix.length
  else path

theorem rebaseScope_source
    (sourcePrefix targetPrefix suffix : RegionPath) :
    rebaseScope sourcePrefix targetPrefix (sourcePrefix ++ suffix) =
      targetPrefix ++ suffix := by
  simp [rebaseScope]

/-- Exact source-indexed fusion data. The producer lives at the ancestor that
owns the private bridge, while `descendant` selects the consumer's own region.
Extending that recursive context carries the bridge down as an inherited wire;
the target rebuilds the same context without the bridge and therefore leaves a
descendant consumer in its original region. `consumerMap` and `producerMap`
are the positional carrier maps computed by the TypeScript operation, and
their port equalities retain aliased physical carriers. -/
structure Description (outer : List Sig) where
  anchorLocals : List Sig
  descendantWires : List Sig
  descendant : DiagramContext (outer ++ anchorLocals) descendantWires
  consumerLocals : List Sig
  producerArity : Nat
  consumerArity : Nat
  producerTerm : VisualProof.Lambda.Term 0 (Fin producerArity)
  consumerTerm : VisualProof.Lambda.Term 0 (Fin consumerArity)
  consumed : Fin consumerArity
  carrierArity : Nat
  consumerMap : Fin consumerArity → Fin (carrierArity + 1)
  producerMap : Fin producerArity → Fin carrierArity
  consumed_eq : consumerMap consumed = Fin.last carrierArity
  carrierSlot : ∀ slot : Fin consumerArity,
    slot ≠ consumed → Fin carrierArity
  consumerNative : Fin consumerArity →
    Var (descendantWires ++ consumerLocals) .iota
  producerNative : Fin producerArity → Var (outer ++ anchorLocals) .iota
  carrier : Fin carrierArity →
    Var (descendantWires ++ consumerLocals) .iota
  consumer_port : ∀ slot (different : slot ≠ consumed),
    consumerMap slot = (carrierSlot slot different).castSucc
  producer_port : ∀ slot,
    carrier (producerMap slot) =
      (descendant.outerWire (producerNative slot)).appendLeft consumerLocals
  consumer_carrier : ∀ slot (different : slot ≠ consumed),
    carrier (carrierSlot slot different) = consumerNative slot
  carrier_exact : List.ofFn carrier =
    carrierWires consumerNative
      (fun slot =>
        (descendant.outerWire (producerNative slot)).appendLeft consumerLocals)
      consumed
  consumer_index : ∀ slot (different : slot ≠ consumed),
    (carrierSlot slot different).val = consumerCarrierIndex consumed slot
  producer_index : ∀ slot, (producerMap slot).val =
    producerCarrierIndex consumerNative
      (fun producerSlot =>
        (descendant.outerWire
          (producerNative producerSlot)).appendLeft consumerLocals)
      consumed
      (List.ofFn carrier) slot
  consumerOutput : Var (descendantWires ++ consumerLocals) .iota
  anchorRest : ItemSeq (outer ++ anchorLocals)
  consumerRest : ItemSeq (descendantWires ++ consumerLocals)

def Description.anchorRetain (description : Description outer) :
    WireRenaming (outer ++ description.anchorLocals)
      (outer ++ (description.anchorLocals ++ [.iota])) :=
  Region.adjoinHostWire outer description.anchorLocals [.iota]

def Description.bridge (description : Description outer) :
    Var (outer ++ (description.anchorLocals ++ [.iota])) .iota :=
  Var.appendRight outer (Var.appendRight description.anchorLocals .here)

def Description.extension (description : Description outer) :
    description.descendant.WireExtension
      (outer ++ (description.anchorLocals ++ [.iota]))
      description.anchorRetain description.bridge :=
  description.descendant.extendWire
    (outer ++ (description.anchorLocals ++ [.iota]))
    description.anchorRetain description.bridge

/-- Removing the ancestor bridge changes the inherited context but never the
selected consumer's region address; this covers both the hole (same-region)
and recursive-cut (descendant) cases. -/
theorem Description.consumerRegion_preserved
    (description : Description outer) :
    description.extension.source.holePath =
      description.descendant.holePath := by
  exact DiagramContext.extendWire_source_holePath description.descendant
    (outer ++ (description.anchorLocals ++ [.iota]))
    description.anchorRetain description.bridge

def Description.consumerRetain (description : Description outer) :
    WireRenaming
      (description.descendantWires ++ description.consumerLocals)
      (description.extension.sourceWires ++ description.consumerLocals) :=
  description.extension.retain.appendRight description.consumerLocals

def Description.consumerPorts (description : Description outer) :
    Fin description.consumerArity →
      Var (description.extension.sourceWires ++
        description.consumerLocals) .iota :=
  fun slot => if slot = description.consumed then
      description.extension.wire.appendLeft description.consumerLocals
    else description.consumerRetain (description.consumerNative slot)

def Description.producerPorts (description : Description outer) :
    Fin description.producerArity →
      Var (outer ++ (description.anchorLocals ++ [.iota])) .iota :=
  fun slot => description.anchorRetain (description.producerNative slot)

def Description.mergedTerm (description : Description outer) :
    VisualProof.Lambda.Term 0 (Fin description.carrierArity) :=
  (description.consumerTerm.mapFree description.consumerMap).bindFree
    (Fin.lastCases (description.producerTerm.mapFree description.producerMap)
      (fun slot => .port slot))

def Description.sourceSelected (description : Description outer) :
    Region (outer ++ (description.anchorLocals ++ [.iota])) :=
  Region.ofItems (.cons
    (.term description.bridge description.producerArity
      description.producerPorts description.producerTerm)
    (description.anchorRest.renameWires description.anchorRetain))

def Description.sourceConsumer (description : Description outer) :
    Region description.extension.sourceWires :=
  .mk description.consumerLocals
    (.cons
      (.term (description.consumerRetain description.consumerOutput)
        description.consumerArity description.consumerPorts
        description.consumerTerm)
      (description.consumerRest.renameWires description.consumerRetain))

def Description.source (description : Description outer) : Region outer :=
  Region.adjoinAt (description.anchorLocals ++ [.iota]) .nil
    (description.sourceSelected.conjoin
      (description.extension.source.fill description.sourceConsumer))

def Description.targetConsumer (description : Description outer) :
    Region description.descendantWires :=
  .mk description.consumerLocals
    (.cons
      (.term description.consumerOutput description.carrierArity
        description.carrier description.mergedTerm)
      description.consumerRest)

def Description.target (description : Description outer) : Region outer :=
  Region.adjoinAt description.anchorLocals .nil
    ((Region.ofItems description.anchorRest).conjoin
      (description.descendant.fill description.targetConsumer))

inductive Local : LocalRule
  | fuse (description : Description outer) :
      Local description.source description.target

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

private def Description.sourceEmbeddedOwner (description : Description outer)
    (context : DiagramContext interfaceWires outer)
    (owner : RegionPath) (index : Nat) : WireAddress :=
  match owner with
  | [] => .internal context.holePath
      ((description.anchorLocals ++ [Sig.iota]).length + index)
  | relative@(_ :: _) =>
      .internal
        (context.holePath ++
          relative.shiftRoot description.sourceSelected.items.length)
        index

private def Description.targetEmbeddedOwner (description : Description outer)
    (context : DiagramContext interfaceWires outer)
    (owner : RegionPath) (index : Nat) : WireAddress :=
  match owner with
  | [] => .internal context.holePath
      (description.anchorLocals.length + index)
  | relative@(_ :: _) =>
      .internal
        (context.holePath ++
          relative.shiftRoot description.anchorRest.length)
        index

private def Description.anchorAddress (description : Description outer)
    (context : DiagramContext interfaceWires outer)
    (wire : Var (outer ++ (description.anchorLocals ++ [.iota]))
      signature) : WireAddress :=
  match Var.appendView outer (description.anchorLocals ++ [Sig.iota]) wire with
  | .fromLeft inherited =>
      let site : ScopedRegion (context.fill description.source) := {
        wires := outer
        body := description.source
        context := context
        root_eq := rfl
      }
      site.visibleAddress inherited
  | .fromRight localWire =>
      .internal context.holePath localWire.index.val

private def Description.targetAnchorAddress (description : Description outer)
    (context : DiagramContext interfaceWires outer)
    (wire : Var (outer ++ description.anchorLocals) signature) : WireAddress :=
  match Var.appendView outer description.anchorLocals wire with
  | .fromLeft inherited =>
      let site : ScopedRegion (context.fill description.target) := {
        wires := outer
        body := description.target
        context := context
        root_eq := rfl
      }
      site.visibleAddress inherited
  | .fromRight localWire =>
      .internal context.holePath localWire.index.val

def Description.consumerAddress (description : Description outer)
    (context : DiagramContext interfaceWires outer)
    (wire : Var (description.extension.sourceWires ++
      description.consumerLocals) signature) : WireAddress :=
  match Var.appendView description.extension.sourceWires
      description.consumerLocals wire with
  | .fromLeft visible =>
      match description.extension.source.classifyHoleWire
          description.sourceConsumer visible with
      | .inl anchorWire => description.anchorAddress context anchorWire
      | .inr internal => description.sourceEmbeddedOwner context
          internal.ownerAddress.1 internal.ownerAddress.2
  | .fromRight localWire =>
      description.sourceEmbeddedOwner context
        description.extension.source.holePath localWire.index.val

def Description.targetConsumerAddress (description : Description outer)
    (context : DiagramContext interfaceWires outer)
    (wire : Var (description.descendantWires ++
      description.consumerLocals) signature) : WireAddress :=
  match Var.appendView description.descendantWires
      description.consumerLocals wire with
  | .fromLeft visible =>
      match description.descendant.classifyHoleWire
          description.targetConsumer visible with
      | .inl anchorWire => description.targetAnchorAddress context anchorWire
      | .inr internal => description.targetEmbeddedOwner context
          internal.ownerAddress.1 internal.ownerAddress.2
  | .fromRight localWire =>
      description.targetEmbeddedOwner context description.descendant.holePath
        localWire.index.val

/-- The stable physical carrier correspondence across deletion of the
ancestor bridge. Source and target addresses may differ at the combined root;
aliases retain one identical correspondence after deduplication. -/
structure CarrierAddress where
  source : WireAddress
  target : WireAddress
  deriving DecidableEq, BEq

def Description.touchedCarriers (description : Description outer)
    (context : DiagramContext interfaceWires outer) : List CarrierAddress :=
  (List.ofFn fun slot => {
    source := description.consumerAddress context
      (description.consumerRetain (description.carrier slot))
    target := description.targetConsumerAddress context
      (description.carrier slot)
  }).eraseDups

def Description.sourceDescendantPath (description : Description outer)
    (context : DiagramContext interfaceWires outer) : RegionPath :=
  context.holePath ++
    description.extension.source.holePath.shiftRoot
      description.sourceSelected.items.length

def Description.targetDescendantPath (description : Description outer)
    (context : DiagramContext interfaceWires outer) : RegionPath :=
  context.holePath ++
    description.descendant.holePath.shiftRoot description.anchorRest.length

def Description.sourceRewritePrefix (description : Description outer)
    (context : DiagramContext interfaceWires outer) : RegionPath :=
  match description.descendant.holePath with
  | [] => context.holePath
  | head :: _ => context.holePath ++
      [description.sourceSelected.items.length + head]

def Description.targetRewritePrefix (description : Description outer)
    (context : DiagramContext interfaceWires outer) : RegionPath :=
  match description.descendant.holePath with
  | [] => context.holePath
  | head :: _ => context.holePath ++ [description.anchorRest.length + head]

/-- The old consumer region is transported to the exact target consumer
region, including the producer-item index shift in the descendant case. -/
theorem Description.descendantScope_preserved
    (description : Description outer)
    (context : DiagramContext interfaceWires outer) :
    rebaseScope (description.sourceRewritePrefix context)
        (description.targetRewritePrefix context)
        (description.sourceDescendantPath context) =
      description.targetDescendantPath context := by
  have pathEq := description.consumerRegion_preserved
  cases descendantPath : description.descendant.holePath with
  | nil =>
      have sourceEq : description.sourceDescendantPath context =
          description.sourceRewritePrefix context ++ [] := by
        simp [Description.sourceDescendantPath,
          Description.sourceRewritePrefix, pathEq, descendantPath,
          RegionPath.shiftRoot]
      have targetEq : description.targetDescendantPath context =
          description.targetRewritePrefix context ++ [] := by
        simp [Description.targetDescendantPath,
          Description.targetRewritePrefix, descendantPath,
          RegionPath.shiftRoot]
      rw [sourceEq, targetEq]
      exact rebaseScope_source _ _ []
  | cons head tail =>
      have sourceEq : description.sourceDescendantPath context =
          description.sourceRewritePrefix context ++ tail := by
        simp [Description.sourceDescendantPath,
          Description.sourceRewritePrefix, pathEq, descendantPath,
          RegionPath.shiftRoot, List.append_assoc]
      have targetEq : description.targetDescendantPath context =
          description.targetRewritePrefix context ++ tail := by
        simp [Description.targetDescendantPath,
          Description.targetRewritePrefix, descendantPath,
          RegionPath.shiftRoot, List.append_assoc]
      rw [sourceEq, targetEq]
      exact rebaseScope_source _ _ tail

def Description.oldTargetScope (description : Description outer)
    (context : DiagramContext interfaceWires outer)
    (carrier : CarrierAddress) : RegionPath :=
  rebaseScope (description.sourceRewritePrefix context)
    (description.targetRewritePrefix context)
    (RegionPath.deepestCommonAncestor
      ((context.fill description.source).incidencePathsAtAddress
        carrier.source))

structure OpenDescription (source : OpenDiagram boundary) where
  outer : List Sig
  primary : Description outer
  occurrence : Occurrence primary.source source
  targetBody : Region occurrence.interface.external
  completion : CompletionPlan
    (occurrence.context.cutDepth + primary.descendant.cutDepth)
    (occurrence.context.fill primary.target) targetBody
  completion_exact : completion.requirements =
    requiredCompletions (occurrence.context.fill primary.target)
      ((primary.touchedCarriers occurrence.context).map fun carrier => {
        address := carrier.target
        scope := primary.oldTargetScope occurrence.context carrier
      })
  targetCanonical : targetBody.Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire targetBody

def OpenDescription.target {boundary : List Sig}
    {source : OpenDiagram boundary} (description : OpenDescription source) :
    OpenDiagram boundary :=
  description.occurrence.interface.withBody description.targetBody
    description.targetCanonical description.targetExternalTwoEnded

end Fusion

/-- Inline a producer along an exact private output/free-slot bridge, then
replay the exact old-scope completion destinations. -/
inductive Fusion : Rule
  | fuse (canonicalSource : OpenDiagram boundary)
      (description : Fusion.OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource)
      (targetIso : OpenDiagramIso description.target target) :
      Fusion source target

theorem Fusion.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Fusion source target)
    (targetIso : OpenDiagramIso target target') :
    Fusion source' target' := by
  cases step with
  | fuse canonicalSource description toCanonical fromCanonical =>
      exact .fuse canonicalSource description
        (sourceIso.symm.trans toCanonical) (fromCanonical.trans targetIso)

end VisualProof.Rule.Lambda
