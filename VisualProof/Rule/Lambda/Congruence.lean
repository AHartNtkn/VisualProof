import VisualProof.Diagram.Algebra
import VisualProof.Diagram.ScopedRewrite
import VisualProof.Rule.WireSever
import VisualProof.Lambda.Reduction

namespace VisualProof.Rule.Lambda

open Diagram
open Theory

namespace Congruence

/-- The exact quotient interface accepted by the TypeScript Lambda rules.
Mappings need not be injective: repeated native slots may be carried by one
physical wire. Coverage excludes unused carrier columns. -/
structure Correspondence (leftArity rightArity : Nat) where
  commonArity : Nat
  left : Fin leftArity → Fin commonArity
  right : Fin rightArity → Fin commonArity
  covered : ∀ commonSlot,
    (∃ leftSlot, left leftSlot = commonSlot) ∨
      (∃ rightSlot, right rightSlot = commonSlot)

/-- Two same-region terms on distinct local output wires, together with the
common physical carrier used to check beta-eta conversion. The final local
wire is the right output that the operation merges into `survivor`. -/
structure Description (outer : List Sig) where
  locals : List Sig
  leftArity : Nat
  rightArity : Nat
  leftTerm : VisualProof.Lambda.Term 0 (Fin leftArity)
  rightTerm : VisualProof.Lambda.Term 0 (Fin rightArity)
  correspondence : Correspondence leftArity rightArity
  survivor : Var (outer ++ locals) .iota
  carrier : Fin correspondence.commonArity →
    Var (outer ++ (locals ++ [.iota])) .iota
  betaEta : VisualProof.Lambda.BetaEta
    (leftTerm.mapFree correspondence.left)
    (rightTerm.mapFree correspondence.right)
  rest : ItemSeq (outer ++ (locals ++ [.iota]))

def Description.collapse (description : Description outer) :
    WireRenaming (outer ++ (description.locals ++ [.iota]))
      (outer ++ description.locals) :=
  WireSever.collapseLocal outer description.locals description.survivor

def Description.retain (description : Description outer) :
    WireRenaming (outer ++ description.locals)
      (outer ++ (description.locals ++ [.iota])) :=
  Region.adjoinHostWire outer description.locals [.iota]

def Description.removed (description : Description outer) :
    Var (outer ++ (description.locals ++ [.iota])) .iota :=
  Var.appendRight outer (Var.appendRight description.locals .here)

def Description.leftItem (description : Description outer) :
    Item (outer ++ (description.locals ++ [.iota])) :=
  .term (description.retain description.survivor) description.leftArity
    (fun slot => description.carrier (description.correspondence.left slot))
    description.leftTerm

def Description.rightItem (description : Description outer) :
    Item (outer ++ (description.locals ++ [.iota])) :=
  .term description.removed description.rightArity
    (fun slot => description.carrier (description.correspondence.right slot))
    description.rightTerm

def Description.items (description : Description outer) :
    ItemSeq (outer ++ (description.locals ++ [.iota])) :=
  .cons description.leftItem (.cons description.rightItem description.rest)

def Description.source (description : Description outer) : Region outer :=
  .mk (description.locals ++ [.iota]) description.items

def Description.target (description : Description outer) : Region outer :=
  .mk description.locals
    (description.items.renameWires description.collapse)

inductive Local : LocalRule
  | join (description : Description outer) :
      Local description.source description.target

def Description.site (description : Description outer)
    (context : DiagramContext interfaceWires outer) :
    ScopedRegion (context.fill description.source) := {
  wires := outer
  body := description.source
  context := context
  root_eq := rfl
}

structure OpenDescription (source : OpenDiagram boundary) where
  outer : List Sig
  primary : Description outer
  occurrence : Occurrence primary.source source
  distinctOutputs :
    (primary.site occurrence.context).itemAddress
        (primary.retain primary.survivor) ≠
      (primary.site occurrence.context).itemAddress primary.removed
  survivorScopeDepth :
    (RegionPath.deepestCommonAncestor
      ((occurrence.context.fill primary.source).incidencePathsAtAddress
        ((primary.site occurrence.context).itemAddress
          (primary.retain primary.survivor)))).length =
      occurrence.context.holePath.length
  removedScopeDepth :
    (RegionPath.deepestCommonAncestor
      ((occurrence.context.fill primary.source).incidencePathsAtAddress
        ((primary.site occurrence.context).itemAddress primary.removed))).length =
      occurrence.context.holePath.length
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

end Congruence

/-- Join two locally beta-eta-convertible term outputs after quotienting both
native interfaces through their exact shared physical carrier. -/
inductive Congruence : Rule
  | join (canonicalSource : OpenDiagram boundary)
      (description : Congruence.OpenDescription canonicalSource)
      (sourceIso : OpenDiagramIso source canonicalSource)
      (targetIso : OpenDiagramIso description.target target) :
      Congruence source target

theorem Congruence.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Congruence source target)
    (targetIso : OpenDiagramIso target target') :
    Congruence source' target' := by
  cases step with
  | join canonicalSource description toCanonical fromCanonical =>
      exact .join canonicalSource description
        (sourceIso.symm.trans toCanonical) (fromCanonical.trans targetIso)

end VisualProof.Rule.Lambda
