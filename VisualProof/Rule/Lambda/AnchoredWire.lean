import VisualProof.Diagram.ScopedRewrite
import VisualProof.Diagram.NestedScopedRewrite
import VisualProof.Diagram.Algebra
import VisualProof.Diagram.NestedOccurrence
import VisualProof.Lambda.Reduction
import VisualProof.Rule.WireSever

namespace VisualProof.Rule.Lambda

open Diagram
open Theory

namespace AnchoredWire

structure ClosedInterfaceTerm (arity : Nat) where
  term : VisualProof.Lambda.Term 0 (Fin arity)
  closed : VisualProof.Lambda.ClosedTerm
  term_eq : term = closed.mapFree Empty.elim

abbrev CompletionRequirement := Diagram.CompletionRequirement
abbrev CompletionPlan {outer : List Sig} (maximum : Nat)
    (source target : Region outer) :=
  Diagram.CompletionPlan maximum source target

def completionCount := @Diagram.completionCount
def requiredCompletions := @Diagram.requiredCompletions

namespace Pin
abbrev Description {outer : List Sig} (source target : Region outer) :=
  Diagram.CompletionPin.Description source target

end Pin

/-- Exact deepest-first insertion of the unary identities selected by
`completeWireEnds`. Each constructor validates its region address against the
current raw intermediate region and ties its wire and region to one original
completion requirement. -/
def CompletionPlan.requirements :
    CompletionPlan maximum source target → List CompletionRequirement
  | plan => Diagram.CompletionPlan.requirements plan

namespace Witness

/-- One exact closed term witness selected at the availability region. Its
output and declared interface are inherited by the separately selected target
body, expressing that the selected body supplies the output and interface
visible at that target. -/
structure Description (selected : Region outer) where
  locals : List Sig
  before : ItemSeq (outer ++ locals)
  after : ItemSeq (outer ++ locals)
  arity : Nat
  witness : ClosedInterfaceTerm arity
  output : Var outer .iota
  ports : Fin arity → Var outer .iota
  selected_eq : selected = .mk locals
    (before.append (.cons
      (.term (output.appendLeft locals) arity
        (fun slot => (ports slot).appendLeft locals) witness.term) after))

end Witness

namespace Split

structure Primary (source : Region outer) where
  siteWires : List Sig
  context : DiagramContext outer siteWires
  locals : List Sig
  arity : Nat
  witness : ClosedInterfaceTerm arity
  anchor : Var (siteWires ++ locals) .iota
  ports : Fin arity → Var (siteWires ++ locals) .iota
  away : ItemSeq (siteWires ++ locals)
  partition : ItemSeq.PortPartition
    (WireSever.collapseLocal siteWires locals anchor) away
  moved : ∃ (wire : Var (siteWires ++ locals) .iota)
      (port : ItemSeq.Port away wire),
    (partition.output wire port).val =
      Var.appendRight siteWires (Var.appendRight locals .here)
  source_eq : context.fill (.mk locals away) = source

def Primary.sourceBody (primary : Primary source) : Region primary.siteWires :=
  .mk primary.locals primary.away

def Primary.site (primary : Primary source) : ScopedRegion source := {
  wires := primary.siteWires
  body := primary.sourceBody
  context := primary.context
  root_eq := primary.source_eq
}

def Primary.retain (primary : Primary source) :
    WireRenaming (primary.siteWires ++ primary.locals)
      (primary.siteWires ++ (primary.locals ++ [.iota])) :=
  Region.adjoinHostWire primary.siteWires primary.locals [.iota]

def Primary.fresh (primary : Primary source) :
    Var (primary.siteWires ++ (primary.locals ++ [.iota])) .iota :=
  Var.appendRight primary.siteWires (Var.appendRight primary.locals .here)

def Primary.targetBody (primary : Primary source) : Region primary.siteWires :=
  .mk (primary.locals ++ [.iota])
    (.cons (.term primary.fresh primary.arity
      (fun slot => primary.retain (primary.ports slot)) primary.witness.term)
      (primary.away.partitionOutput
        (WireSever.collapseLocal primary.siteWires primary.locals
          primary.anchor) primary.partition))

def Primary.targetRoot {outer : List Sig} {source : Region outer}
    (primary : Primary source) : Region outer :=
  primary.context.fill primary.targetBody

def Primary.anchorAddress (primary : Primary source) : WireAddress :=
  primary.site.itemAddress primary.anchor

def Primary.MovesEndpoint (primary : Primary source)
    (address : EndpointAddress) : Prop :=
  ∃ (wire : Var (primary.siteWires ++ primary.locals) .iota)
      (port : ItemSeq.Port primary.away wire),
    primary.site.endpointAddress port = address ∧
      (primary.partition.output wire port).val = primary.fresh

structure Description (source : OpenDiagram boundary) where
  occurrence : NestedOccurrence source
  witness : Witness.Description occurrence.selected
  primary : Primary occurrence.before
  sameArity : primary.arity = witness.arity
  sameWitness : primary.witness = sameArity ▸ witness.witness
  anchorVisible : primary.anchor =
    (primary.context.outerWire
      (occurrence.descendant.outerWire witness.output)).appendLeft primary.locals
  portsVisible : ∀ slot, primary.ports slot =
    (primary.context.outerWire (occurrence.descendant.outerWire
      (witness.ports (Fin.cast sameArity slot)))).appendLeft primary.locals
  rewrite : occurrence.ScopedRewrite primary.site primary.targetBody
  completion_exact : rewrite.completion.requirements =
    requiredCompletions (occurrence.targetBody primary.targetRoot) [{
      address := occurrence.nestedItemAddress primary.site primary.anchor
      scope := RegionPath.deepestCommonAncestor
        ((occurrence.targetBody occurrence.before).incidencePathsAtAddress
          (occurrence.nestedItemAddress primary.site primary.anchor))
    }]
  targetCanonical : rewrite.targetBody.Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire rewrite.targetBody

def Description.targetBody (description : Description source) :
    Region description.occurrence.interface.external :=
  description.rewrite.targetBody

def Description.completion (description : Description source) :
    CompletionPlan
      (description.occurrence.nestedSitePath description.primary.site).length
      (description.occurrence.targetBody description.primary.targetRoot)
      description.targetBody :=
  description.rewrite.completion

def Description.target {boundary : List Sig}
    {source : OpenDiagram boundary} (description : Description source) :
    OpenDiagram boundary :=
  description.occurrence.interface.withBody description.targetBody
    description.targetCanonical
    description.targetExternalTwoEnded

end Split

namespace Contract

structure Primary (source : Region outer) where
  siteWires : List Sig
  context : DiagramContext outer siteWires
  locals : List Sig
  redundantArity : Nat
  redundant : ClosedInterfaceTerm redundantArity
  redundantPorts : Fin redundantArity →
    Var (siteWires ++ (locals ++ [.iota])) .iota
  survivorOutput : Var (siteWires ++ locals) .iota
  away : ItemSeq (siteWires ++ (locals ++ [.iota]))
  source_eq : context.fill (.mk (locals ++ [.iota])
    (.cons (.term
      (Var.appendRight siteWires (Var.appendRight locals .here))
      redundantArity redundantPorts redundant.term) away)) = source

def Primary.sourceBody (primary : Primary source) : Region primary.siteWires :=
  .mk (primary.locals ++ [.iota])
    (.cons (.term
      (Var.appendRight primary.siteWires
        (Var.appendRight primary.locals .here))
      primary.redundantArity primary.redundantPorts primary.redundant.term)
      primary.away)

def Primary.site (primary : Primary source) : ScopedRegion source := {
  wires := primary.siteWires
  body := primary.sourceBody
  context := primary.context
  root_eq := primary.source_eq
}

def Primary.retain (primary : Primary source) :
    WireRenaming (primary.siteWires ++ primary.locals)
      (primary.siteWires ++ (primary.locals ++ [.iota])) :=
  Region.adjoinHostWire primary.siteWires primary.locals [.iota]

def Primary.drop (primary : Primary source) :
    Var (primary.siteWires ++ (primary.locals ++ [.iota])) .iota :=
  Var.appendRight primary.siteWires (Var.appendRight primary.locals .here)

def Primary.collapse (primary : Primary source) :
    WireRenaming (primary.siteWires ++ (primary.locals ++ [.iota]))
      (primary.siteWires ++ primary.locals) :=
  WireSever.collapseLocal primary.siteWires primary.locals
    primary.survivorOutput

def Primary.targetBody (primary : Primary source) : Region primary.siteWires :=
  .mk primary.locals (primary.away.renameWires primary.collapse)

def Primary.targetRoot {outer : List Sig} {source : Region outer}
    (primary : Primary source) : Region outer :=
  primary.context.fill primary.targetBody

def Primary.survivorAddress (primary : Primary source) : WireAddress :=
  primary.site.itemAddress (primary.retain primary.survivorOutput)

def Primary.dropAddress (primary : Primary source) : WireAddress :=
  primary.site.itemAddress primary.drop

def Primary.touchedAddresses (primary : Primary source) : List WireAddress :=
  (List.ofFn fun slot => primary.site.itemAddress
    (primary.redundantPorts slot)).eraseDups

def completionRequirements (source : Region outer)
    (addresses : List WireAddress) : List CompletionRequirement :=
  addresses.map fun address => {
    address := address
    scope := RegionPath.deepestCommonAncestor
      (source.incidencePathsAtAddress address)
  }

structure Description (source : OpenDiagram boundary) where
  occurrence : NestedOccurrence source
  survivor : Witness.Description occurrence.selected
  primary : Primary occurrence.before
  conversion : VisualProof.Lambda.BetaEta
    primary.redundant.closed survivor.witness.closed
  sameSurvivorWire : primary.survivorOutput =
    (primary.context.outerWire
      (occurrence.descendant.outerWire survivor.output)).appendLeft primary.locals
  distinctOutputs :
    occurrence.nestedItemAddress primary.site primary.drop ≠
      occurrence.nestedItemAddress primary.site
        (primary.retain primary.survivorOutput)
  dropScopeDepth :
    (RegionPath.deepestCommonAncestor
      ((occurrence.targetBody occurrence.before).incidencePathsAtAddress
        (occurrence.nestedItemAddress primary.site primary.drop))).length =
        (occurrence.nestedSitePath primary.site).length
  movedWithinAvailability :
    ∀ {wire : Var (primary.siteWires ++
          (primary.locals ++ [.iota])) .iota}
        (port : ItemSeq.Port primary.away wire),
      wire = primary.drop →
        occurrence.outer.holePath.IsPrefix
          (occurrence.nestedEndpointAddress primary.site (.tail port)).region
  rewrite : occurrence.ScopedRewrite primary.site primary.targetBody
  completion_exact : rewrite.completion.requirements =
    requiredCompletions (occurrence.targetBody primary.targetRoot)
      (completionRequirements (occurrence.targetBody occurrence.before)
        (((List.ofFn fun slot => occurrence.nestedItemAddress primary.site
          (primary.redundantPorts slot)).eraseDups).filter fun address =>
            decide (address ≠ occurrence.nestedItemAddress primary.site
              primary.drop)))
  targetCanonical : rewrite.targetBody.Canonical
  targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire rewrite.targetBody

def Description.targetBody (description : Description source) :
    Region description.occurrence.interface.external :=
  description.rewrite.targetBody

def Description.completion (description : Description source) :
    CompletionPlan
      (description.occurrence.nestedSitePath description.primary.site).length
      (description.occurrence.targetBody description.primary.targetRoot)
      description.targetBody :=
  description.rewrite.completion

def Description.target {boundary : List Sig}
    {source : OpenDiagram boundary} (description : Description source) :
    OpenDiagram boundary :=
  description.occurrence.interface.withBody description.targetBody
    description.targetCanonical
    description.targetExternalTwoEnded

end Contract

end AnchoredWire

inductive AnchoredWire : Rule
  | split (canonicalSource : OpenDiagram boundary)
      (description : AnchoredWire.Split.Description canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource)
      (targetIso : OpenDiagramIso description.target target) :
      AnchoredWire source target
  | contract (canonicalSource : OpenDiagram boundary)
      (description : AnchoredWire.Contract.Description canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource)
      (targetIso : OpenDiagramIso description.target target) :
      AnchoredWire source target

theorem AnchoredWire.iso
    (sourceIso : OpenDiagramIso source source')
    (step : AnchoredWire source target)
    (targetIso : OpenDiagramIso target target') :
    AnchoredWire source' target' := by
  cases step with
  | split canonical description toCanonical fromCanonical =>
      exact .split canonical description (sourceIso.symm.trans toCanonical)
        (fromCanonical.trans targetIso)
  | contract canonical description toCanonical fromCanonical =>
      exact .contract canonical description (sourceIso.symm.trans toCanonical)
        (fromCanonical.trans targetIso)

end VisualProof.Rule.Lambda
