import VisualProof.Diagram.Algebra
import VisualProof.Diagram.UnaryIdentity
import VisualProof.Rule.Relation

namespace VisualProof.Rule

open Diagram
open Theory

namespace Lambda
namespace Spawn

/-- The fresh homogeneous wire context owned by a spawned whole term. The
first wire is the result and the remaining wires are its ordered free slots. -/
def wires (freeArity : Nat) : List Sig :=
  List.replicate (freeArity + 1) .iota

/-- A positional variable in a homogeneous `IOTA` context. -/
def wire : (arity : Nat) -> Fin arity -> Var (List.replicate arity .iota) .iota
  | 0, position => Fin.elim0 position
  | _ + 1, position =>
      Fin.cases .here (fun rest => .there (wire _ rest)) position

def output (freeArity : Nat) : Var (wires freeArity) .iota :=
  wire (freeArity + 1) 0

def port (freeArity : Nat) (slot : Fin freeArity) :
    Var (wires freeArity) .iota :=
  wire (freeArity + 1) slot.succ

@[simp] theorem output_eq (freeArity : Nat) :
    output freeArity = .here := rfl

@[simp] theorem port_eq (freeArity : Nat) (slot : Fin freeArity) :
    port freeArity slot = .there (wire freeArity slot) := rfl

def intoRegion (outer : List Sig) (freeArity : Nat) :
    WireRenaming (wires freeArity) (outer ++ wires freeArity) :=
  ⟨fun selected => Var.appendRight outer selected⟩

def item (outer : List Sig) (freeArity : Nat)
    (term : VisualProof.Lambda.Term 0 (Fin freeArity)) :
    Item (outer ++ wires freeArity) :=
  .term (intoRegion outer freeArity (output freeArity)) freeArity
    (fun slot => intoRegion outer freeArity (port freeArity slot)) term

/-- Each fresh term incidence is born with its unary identity cap. -/
def caps (outer : List Sig) (freeArity : Nat) :
    ItemSeq (outer ++ wires freeArity) :=
  ItemSeq.pinWires (wires freeArity) (intoRegion outer freeArity)
    (fun _ => true)

def spawned (outer : List Sig) (freeArity : Nat)
    (term : VisualProof.Lambda.Term 0 (Fin freeArity)) : Region outer :=
  .mk (wires freeArity) (.cons (item outer freeArity term)
    (caps outer freeArity))

structure Description (outer : List Sig) where
  freeArity : Nat
  term : VisualProof.Lambda.Term 0 (Fin freeArity)

def Description.source (_description : Description outer) : Region outer :=
  Region.blank outer

def Description.target (description : Description outer) : Region outer :=
  spawned outer description.freeArity description.term

inductive Local : LocalRule
  | spawn (description : Description outer) :
      Local description.source description.target

end Spawn

/-- Spawn or remove one closed, freshly capped whole Lambda term at an exact
diagram occurrence. -/
def Spawn : Rule :=
  Contextual (fun {wires} before after =>
    symmetric (@Spawn.Local wires) before after)

theorem Spawn.iso
    (sourceIso : OpenDiagramIso source source')
    (step : Spawn source target)
    (targetIso : OpenDiagramIso target target') :
    Spawn source' target' :=
  Contextual.iso sourceIso step targetIso

theorem Spawn.symm (step : Spawn source target) : Spawn target source := by
  rcases step with ⟨context, before, after, occurrence, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  let reverseOccurrence : Occurrence after target := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := targetCanonical
    sourceExternalTwoEnded := targetExternalTwoEnded
    host_iso := targetIso
  }
  refine ⟨context, after, before, reverseOccurrence,
    occurrence.sourceCanonical, occurrence.sourceExternalTwoEnded,
    occurrence.host_iso, ?_⟩
  cases polarity : occurrence.context.polarity <;>
    simp only [polarity, atPolarity, converse, symmetric] at localEvidence ⊢
  · exact localEvidence.elim Or.inr Or.inl
  · exact localEvidence.elim Or.inr Or.inl

end Lambda
end VisualProof.Rule
