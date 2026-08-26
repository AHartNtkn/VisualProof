import VisualProof.Diagram.Algebra
import VisualProof.Diagram.ScopedRewrite
import VisualProof.Lambda.Certificate
import VisualProof.Rule.Relation

namespace VisualProof.Rule.Lambda

open Diagram
open Theory

namespace Fission

/-- Exact capture-avoiding replacement of one bound-closed subterm by the
last free slot.  The selected term is intrinsically closed with respect to
every binder crossed by `path`; untouched siblings retain their native free
slots through `Fin.castSucc`. -/
inductive At (selected : VisualProof.Lambda.Term 0 (Fin arity)) :
    {bound : Nat} → VisualProof.Lambda.Term bound (Fin arity) →
      List VisualProof.Lambda.PathSegment →
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
  path : List VisualProof.Lambda.PathSegment
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

/-- Exact source-indexed fusion data. The producer output and one consumer
slot are the two incidences of the final local bridge. `consumerMap` and
`producerMap` are the positional carrier maps computed by the TypeScript
operation; their port equalities retain aliased physical carriers. -/
structure Description (outer : List Sig) where
  locals : List Sig
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
  consumerNative : Fin consumerArity → Var (outer ++ locals) .iota
  producerNative : Fin producerArity → Var (outer ++ locals) .iota
  carrier : Fin carrierArity → Var (outer ++ locals) .iota
  consumer_port : ∀ slot (different : slot ≠ consumed),
    consumerMap slot = (carrierSlot slot different).castSucc
  producer_port : ∀ slot,
    carrier (producerMap slot) = producerNative slot
  consumer_carrier : ∀ slot (different : slot ≠ consumed),
    carrier (carrierSlot slot different) = consumerNative slot
  carrier_exact : List.ofFn carrier =
    carrierWires consumerNative producerNative consumed
  consumer_index : ∀ slot (different : slot ≠ consumed),
    (carrierSlot slot different).val = consumerCarrierIndex consumed slot
  producer_index : ∀ slot, (producerMap slot).val =
    producerCarrierIndex consumerNative producerNative consumed
      (List.ofFn carrier) slot
  consumerOutput : Var (outer ++ locals) .iota
  rest : ItemSeq (outer ++ locals)

def Description.bridge (description : Description outer) :
    Var (outer ++ (description.locals ++ [.iota])) .iota :=
  Var.appendRight outer (Var.appendRight description.locals .here)

def Description.retain (description : Description outer) :
    WireRenaming (outer ++ description.locals)
      (outer ++ (description.locals ++ [.iota])) :=
  Region.adjoinHostWire outer description.locals [.iota]

def Description.consumerPorts (description : Description outer) :
    Fin description.consumerArity →
      Var (outer ++ (description.locals ++ [.iota])) .iota :=
  fun slot => if slot = description.consumed then description.bridge
    else description.retain (description.consumerNative slot)

def Description.producerPorts (description : Description outer) :
    Fin description.producerArity →
      Var (outer ++ (description.locals ++ [.iota])) .iota :=
  fun slot => description.retain (description.producerNative slot)

def Description.mergedTerm (description : Description outer) :
    VisualProof.Lambda.Term 0 (Fin description.carrierArity) :=
  (description.consumerTerm.mapFree description.consumerMap).bindFree
    (Fin.lastCases (description.producerTerm.mapFree description.producerMap)
      (fun slot => .port slot))

def Description.source (description : Description outer) : Region outer :=
  .mk (description.locals ++ [.iota])
    (.cons
      (.term description.bridge description.producerArity
        description.producerPorts description.producerTerm)
      (.cons
        (.term (description.retain description.consumerOutput)
          description.consumerArity description.consumerPorts
          description.consumerTerm)
        (description.rest.renameWires description.retain)))

def Description.target (description : Description outer) : Region outer :=
  .mk description.locals
    (.cons
      (.term description.consumerOutput description.carrierArity
        description.carrier description.mergedTerm)
      description.rest)

inductive Local : LocalRule
  | fuse (description : Description outer) :
      Local description.source description.target

def Description.touchedAddresses (description : Description outer)
    (context : DiagramContext interfaceWires outer) : List WireAddress :=
  let site : ScopedRegion (context.fill description.source) := {
    wires := outer
    body := description.source
    context := context
    root_eq := rfl
  }
  (List.ofFn fun slot => site.itemAddress
    (description.retain (description.carrier slot))).eraseDups

structure OpenDescription (source : OpenDiagram boundary) where
  outer : List Sig
  primary : Description outer
  occurrence : Occurrence primary.source source
  targetBody : Region occurrence.interface.external
  completion : CompletionPlan occurrence.context.cutDepth
    (occurrence.context.fill primary.target) targetBody
  completion_exact : completion.requirements =
    requiredCompletions (occurrence.context.fill primary.target)
      ((primary.touchedAddresses occurrence.context).map fun address => {
        address := address
        scope := RegionPath.deepestCommonAncestor
          ((occurrence.context.fill primary.source).incidencePathsAtAddress
            address)
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
