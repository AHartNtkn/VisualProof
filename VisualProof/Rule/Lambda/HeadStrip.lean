import VisualProof.Data.Finite
import VisualProof.Diagram.Algebra
import VisualProof.Diagram.ScopedRewrite
import VisualProof.Rule.Identification
import VisualProof.Rule.Lambda.Congruence

namespace VisualProof.Rule.Lambda

open Diagram
open Theory
open VisualProof.Data.Finite

namespace HeadStrip

def ItemSeq.ofList : List (Item wires) → ItemSeq wires
  | [] => .nil
  | item :: rest => .cons item (ItemSeq.ofList rest)

/-- Proof-relevant quotient from a common positional argument interface to
the exact first-occurrence physical-wire compaction emitted by TypeScript.
The empty case covers arguments with no occurring free position; the
supported case records the quotient slot used by every occurring common
position without requiring distinct common columns to denote distinct wires. -/
inductive PhysicalCompaction
    (commonTerm : VisualProof.Lambda.Term 0 (Fin commonArity))
    (commonPorts : Fin commonArity → Var wires .iota)
    (physicalTerm : VisualProof.Lambda.Term 0 (Var wires .iota)) : Prop
  | empty (closed : VisualProof.Lambda.ClosedTerm)
      (common_eq : commonTerm = closed.mapFree Empty.elim)
      (compact_eq : physicalTerm.compact = closed.mapFree Empty.elim) :
      PhysicalCompaction commonTerm commonPorts physicalTerm
  | supported
      (rename : Fin commonArity → Fin physicalTerm.freeSupport.length)
      (compact_eq : physicalTerm.compact = commonTerm.mapFree rename)
      (ports_eq : ∀ slot, slot ∈ commonTerm.freeSupport →
        physicalTerm.freeSupport.get (rename slot) = commonPorts slot) :
      PhysicalCompaction commonTerm commonPorts physicalTerm

/-- Exact rigid-head equation data. Both native interfaces are quotiented
through the same covered carrier, so repeated correspondence columns and
aliased physical wires are preserved rather than normalized away. -/
structure Description (outer : List Sig) where
  locals : List Sig
  leftArity : Nat
  rightArity : Nat
  leftTerm : VisualProof.Lambda.Term 0 (Fin leftArity)
  rightTerm : VisualProof.Lambda.Term 0 (Fin rightArity)
  correspondence : Congruence.Correspondence leftArity rightArity
  carrier : Fin correspondence.commonArity → Var (outer ++ locals) .iota
  leftSpine : VisualProof.Lambda.HeadSpine 0 (Fin leftArity)
  rightSpine : VisualProof.Lambda.HeadSpine 0 (Fin rightArity)
  leftSpine_eq : VisualProof.Lambda.headSpine leftTerm = some leftSpine
  rightSpine_eq : VisualProof.Lambda.headSpine rightTerm = some rightSpine
  sameBinders : leftSpine.binders = rightSpine.binders
  headIndex : Fin leftSpine.binders
  leftHead : leftSpine.head = .bound headIndex
  rightHead : rightSpine.head = .bound (Fin.cast sameBinders headIndex)
  sameArgumentCount : leftSpine.args.length = rightSpine.args.length
  rest : ItemSeq (outer ++ locals)
  leftCompaction : ∀ index,
    PhysicalCompaction
      ((VisualProof.Lambda.prefixClose leftSpine.binders
        (leftSpine.args.get index)).mapFree correspondence.left)
      carrier
      ((VisualProof.Lambda.prefixClose leftSpine.binders
        (leftSpine.args.get index)).mapFree
          (fun slot => carrier (correspondence.left slot)))
  rightCompaction : ∀ index,
    PhysicalCompaction
      ((VisualProof.Lambda.prefixClose rightSpine.binders
        (rightSpine.args.get
          (Fin.cast sameArgumentCount index))).mapFree correspondence.right)
      carrier
      ((VisualProof.Lambda.prefixClose rightSpine.binders
        (rightSpine.args.get
          (Fin.cast sameArgumentCount index))).mapFree
            (fun slot => carrier (correspondence.right slot)))

def Description.leftPorts (description : Description outer) :
    Fin description.leftArity → Var (outer ++ description.locals) .iota :=
  fun slot => description.carrier (description.correspondence.left slot)

def Description.rightPorts (description : Description outer) :
    Fin description.rightArity → Var (outer ++ description.locals) .iota :=
  fun slot => description.carrier (description.correspondence.right slot)

def Description.leftArgument (description : Description outer)
    (index : Fin description.leftSpine.args.length) :
    VisualProof.Lambda.Term 0 (Fin description.leftArity) :=
  VisualProof.Lambda.prefixClose description.leftSpine.binders
    (description.leftSpine.args.get index)

def Description.rightArgument (description : Description outer)
    (index : Fin description.leftSpine.args.length) :
    VisualProof.Lambda.Term 0 (Fin description.rightArity) :=
  VisualProof.Lambda.prefixClose description.rightSpine.binders
    (description.rightSpine.args.get
      (Fin.cast description.sameArgumentCount index))

def Description.leftCommonArgument (description : Description outer)
    (index : Fin description.leftSpine.args.length) :
    VisualProof.Lambda.Term 0
      (Fin description.correspondence.commonArity) :=
  (description.leftArgument index).mapFree description.correspondence.left

def Description.rightCommonArgument (description : Description outer)
    (index : Fin description.leftSpine.args.length) :
    VisualProof.Lambda.Term 0
      (Fin description.correspondence.commonArity) :=
  (description.rightArgument index).mapFree description.correspondence.right

def Description.argumentIndices (description : Description outer) :
    List (Fin description.leftSpine.args.length) :=
  filterFin fun index => decide
    (description.leftCommonArgument index ≠
      description.rightCommonArgument index)

def Description.sourceRetain (description : Description outer) :
    WireRenaming (outer ++ description.locals)
      (outer ++ (description.locals ++ [.iota])) :=
  Region.adjoinHostWire outer description.locals [.iota]

def Description.equation (description : Description outer) :
    Var (outer ++ (description.locals ++ [.iota])) .iota :=
  Var.appendRight outer (Var.appendRight description.locals .here)

def Description.targetRetain (description : Description outer) :
    WireRenaming (outer ++ description.locals)
      (outer ++ (description.locals ++
        List.replicate description.argumentIndices.length .iota)) :=
  Region.adjoinHostWire outer description.locals
    (List.replicate description.argumentIndices.length .iota)

def Description.argumentWire (description : Description outer)
    (position : Fin description.argumentIndices.length) :
    Var (outer ++ (description.locals ++
      List.replicate description.argumentIndices.length .iota)) .iota :=
  Identification.freshLocalWire outer description.locals .iota position

def Description.leftPhysicalArgument (description : Description outer)
    (index : Fin description.leftSpine.args.length) :
    VisualProof.Lambda.Term 0 (Var (outer ++ description.locals) .iota) :=
  (description.leftArgument index).mapFree description.leftPorts

def Description.rightPhysicalArgument (description : Description outer)
    (index : Fin description.leftSpine.args.length) :
    VisualProof.Lambda.Term 0 (Var (outer ++ description.locals) .iota) :=
  (description.rightArgument index).mapFree description.rightPorts

def Description.leftArgumentItem (description : Description outer)
    (position : Fin description.argumentIndices.length) :
    Item (outer ++ (description.locals ++
      List.replicate description.argumentIndices.length .iota)) :=
  let argument := description.leftPhysicalArgument
    (description.argumentIndices.get position)
  .term (description.argumentWire position) argument.freeSupport.length
    (fun slot => description.targetRetain (argument.freeSupport.get slot))
    argument.compact

def Description.rightArgumentItem (description : Description outer)
    (position : Fin description.argumentIndices.length) :
    Item (outer ++ (description.locals ++
      List.replicate description.argumentIndices.length .iota)) :=
  let argument := description.rightPhysicalArgument
    (description.argumentIndices.get position)
  .term (description.argumentWire position) argument.freeSupport.length
    (fun slot => description.targetRetain (argument.freeSupport.get slot))
    argument.compact

def Description.argumentItems (description : Description outer) :
    ItemSeq (outer ++ (description.locals ++
      List.replicate description.argumentIndices.length .iota)) :=
  ItemSeq.ofList <| (List.ofFn fun position => [
    description.leftArgumentItem position,
    description.rightArgumentItem position]).flatten

def Description.source (description : Description outer) : Region outer :=
  .mk (description.locals ++ [.iota])
    (.cons
      (.term description.equation description.leftArity
        (fun slot => description.sourceRetain (description.leftPorts slot))
        description.leftTerm)
      (.cons
        (.term description.equation description.rightArity
          (fun slot => description.sourceRetain (description.rightPorts slot))
          description.rightTerm)
        (description.rest.renameWires description.sourceRetain)))

def Description.target (description : Description outer) : Region outer :=
  .mk (description.locals ++
      List.replicate description.argumentIndices.length .iota)
    (description.argumentItems.append
      (description.rest.renameWires description.targetRetain))

inductive Local : LocalRule
  | strip (description : Description outer) :
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
    (description.sourceRetain (description.carrier slot))).eraseDups

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

end HeadStrip

/-- Replace one local binary equation between aligned bound-rigid heads by
the ordered non-reflexive equations between their compacted arguments, then
replay the exact old-scope completion destinations. -/
inductive HeadStrip : Rule
  | strip (canonicalSource : OpenDiagram boundary)
      (description : HeadStrip.OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource)
      (targetIso : OpenDiagramIso description.target target) :
      HeadStrip source target

theorem HeadStrip.iso
    (sourceIso : OpenDiagramIso source source')
    (step : HeadStrip source target)
    (targetIso : OpenDiagramIso target target') :
    HeadStrip source' target' := by
  cases step with
  | strip canonicalSource description toCanonical fromCanonical =>
      exact .strip canonicalSource description
        (sourceIso.symm.trans toCanonical) (fromCanonical.trans targetIso)

end VisualProof.Rule.Lambda
