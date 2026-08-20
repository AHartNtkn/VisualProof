import VisualProof.Diagram.Algebra
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Theory
open Diagram

namespace Comprehension

/-- Insert one relation wire between two local-context fragments. -/
def localRetain (before after : List Sig) (arguments : List Sig) :
    WireRenaming (before ++ after) (before ++ (.rel arguments :: after)) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (.rel arguments :: after))
    (fun wire => Var.appendRight before (.there wire))⟩

/-- Embed the retained outer and local wires into the quantified context. -/
def retain (outer before after : List Sig) (arguments : List Sig) :
    WireRenaming (outer ++ (before ++ after))
      (outer ++ (before ++ (.rel arguments :: after))) :=
  ⟨Var.appendMap
    (fun wire => wire.appendLeft (before ++ (.rel arguments :: after)))
    (fun wire => Var.appendRight outer
      (localRetain before after arguments wire))⟩

/-- The exact locally bound relation wire discharged by comprehension. -/
def selected (outer before after : List Sig) (arguments : List Sig) :
    Var (outer ++ (before ++ (.rel arguments :: after))) (.rel arguments) :=
  Var.appendRight outer (Var.appendRight before .here)

/-- A pattern-boundary attachment. Surjectivity of the pattern boundary makes
this assignment determine every external pattern wire. -/
structure BoundaryAssignment (pattern : OpenDiagram arguments)
    (targetWires : List Sig) where
  wire : WireRenaming pattern.external targetWires

namespace Instantiation

mutual
  /-- Recursive instantiation under cuts. The selected relation remains an
  inherited wire; locally bound wires are retained exactly. -/
  inductive RegionResult (pattern : OpenDiagram arguments) :
      {sourceWires targetWires : List Sig} →
      WireRenaming targetWires sourceWires →
      Var sourceWires (.rel arguments) →
      Region sourceWires → Region targetWires → Prop
    | mk
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        {locals : List Sig}
        {items : ItemSeq (sourceWires ++ locals)}
        {result : Region (targetWires ++ locals)}
        (itemsResult : ItemsResult pattern (retain.appendRight locals)
          (selected.appendLeft locals) items result) :
        RegionResult pattern retain selected (.mk locals items)
          (Region.adjoinAt locals .nil result)

  /-- An item sequence becomes a conjunction of its instantiated item
  regions. This is structural proof evidence, not a second syntax. -/
  inductive ItemsResult (pattern : OpenDiagram arguments) :
      {sourceWires targetWires : List Sig} →
      WireRenaming targetWires sourceWires →
      Var sourceWires (.rel arguments) →
      ItemSeq sourceWires → Region targetWires → Prop
    | nil
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)} :
        ItemsResult pattern retain selected .nil (Region.blank targetWires)
    | cons
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        {item : Item sourceWires} {tail : ItemSeq sourceWires}
        {itemResult tailResult : Region targetWires}
        (itemEvidence : ItemResult pattern retain selected item itemResult)
        (tailEvidence : ItemsResult pattern retain selected tail tailResult) :
        ItemsResult pattern retain selected (.cons item tail)
          (itemResult.conjoin tailResult)

  /-- One source item either uses only retained wires, expands an application
  headed by the selected relation wire, or recursively instantiates a cut. -/
  inductive ItemResult (pattern : OpenDiagram arguments) :
      {sourceWires targetWires : List Sig} →
      WireRenaming targetWires sourceWires →
      Var sourceWires (.rel arguments) →
      Item sourceWires → Region targetWires → Prop
    | atom
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        (head : Var targetWires (.rel atomArguments))
        (ports : Vars targetWires atomArguments) :
        ItemResult pattern retain selected
          (.atom (retain head) (ports.map (fun wire => retain wire)))
          (Region.singleton (.atom head ports))
    | selectedAtom
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        (assignment : BoundaryAssignment pattern targetWires) :
        ItemResult pattern retain selected
          (.atom selected
            ((pattern.boundaryWire.map
              (fun wire => assignment.wire wire)).map
                (fun wire => retain wire)))
          (pattern.body.renameWires assignment.wire)
    | identity
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        (signature : Sig) (arity : Nat)
        (ports : Fin arity → Var targetWires signature) :
        ItemResult pattern retain selected
          (.identity signature arity (fun index => retain (ports index)))
          (Region.singleton (.identity signature arity ports))
    | cut
        {retain : WireRenaming targetWires sourceWires}
        {selected : Var sourceWires (.rel arguments)}
        {body : Region sourceWires} {result : Region targetWires}
        (bodyEvidence : RegionResult pattern retain selected body result) :
        ItemResult pattern retain selected (.cut body)
          (Region.singleton (.cut result))
end

end Instantiation

/-- Exact structural evidence that removes one locally bound relation wire and
instantiates every application headed by it with the supplied open pattern. -/
inductive Instantiates
    (pattern : OpenDiagram arguments) (before after : List Sig) :
    Region outer → Region outer → Prop
  | mk
      {items : ItemSeq
        (outer ++ (before ++ (.rel arguments :: after)))}
      {result : Region (outer ++ (before ++ after))}
      (itemsResult : Instantiation.ItemsResult pattern
        (retain outer before after arguments)
        (selected outer before after arguments) items result) :
      Instantiates pattern before after
        (.mk (before ++ (.rel arguments :: after)) items)
        (Region.adjoinAt (before ++ after) .nil result)

/-- Positive comprehension generalizes a specialized region by one local
relation wire. Context polarity supplies the contravariant direction. -/
inductive Local : LocalRule
  | comprehend
      (arguments before after : List Sig)
      (pattern : OpenDiagram arguments)
      {quantified specialized : Region wires}
      (instantiates : Instantiates pattern before after quantified specialized) :
      Local specialized quantified

end Comprehension

def Comprehension : Rule :=
  Contextual fun specialized quantified =>
    Comprehension.Local specialized quantified

theorem Comprehension.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Comprehension source target)
    (targetIso : OpenDiagramIso target target') :
    Comprehension source' target' := by
  exact Contextual.iso sourceIso step targetIso

end VisualProof.Rule
